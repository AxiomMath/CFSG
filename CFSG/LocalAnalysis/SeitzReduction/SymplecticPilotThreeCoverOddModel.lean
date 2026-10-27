module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotOrthCoordBlock
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeRecogModel

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.QuasithinUnique.Lin2.Five (tauSp)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear mem_blockSpecialLinear blockDiagSL
  mem_blockDiagSL)
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect perfectCore_perfect)
open LinearFlag
open scoped MatrixGroups

section Model

variable {F : Type} [Field F] [CharP F 2]

theorem coe_ctEmbed_diagSp_two (t : Fin 2 → Fˣ) :
    ((ctEmbed 1 (diagSp F 2 t) : SpecialLinearGroup (Fin (2 * 2 + 1)) F) :
        Matrix (Fin (2 * 2 + 1)) (Fin (2 * 2 + 1)) F) =
      diagonal ![((t 0 : Fˣ) : F), (((t 0)⁻¹ : Fˣ) : F), ((t 1 : Fˣ) : F),
        (((t 1)⁻¹ : Fˣ) : F), 1] := by
  ext a b
  obtain ⟨w, rfl⟩ := (q2Coord 2 1).surjective a
  obtain ⟨w', rfl⟩ := (q2Coord 2 1).surjective b
  by_cases hww : w = w'
  · subst hww
    rw [ctEmbed_diagSp_apply_self, diagonal_apply_eq]
    rcases w with (p | p) | i
    · fin_cases p <;> rfl
    · fin_cases p <;> rfl
    · fin_cases i
      rfl
  · have hne : q2Coord 2 1 w ≠ q2Coord 2 1 w' := fun h => hww ((q2Coord 2 1).injective h)
    rw [ctEmbed_diagSp_apply_ne _ hne, diagonal_apply_ne _ hne]

variable (F) in
@[expose] noncomputable def oddStdTorus : Subgroup (SpecialLinearGroup (Fin (2 * 2 + 1)) F) :=
  (rootTorusSp F 0).map (ctEmbed 1)

variable (F) in
@[expose] noncomputable def oddTwTorus : Subgroup (SpecialLinearGroup (Fin (2 * 2 + 1)) F) :=
  ((rootTorusSp F 0).map tauSp).map (ctEmbed 1)

theorem coe_ctEmbed_rootTorusHom_zero (κ : Fˣ) :
    ((ctEmbed 1 (rootTorusHom F 2 0 κ) : SpecialLinearGroup (Fin (2 * 2 + 1)) F) :
        Matrix (Fin (2 * 2 + 1)) (Fin (2 * 2 + 1)) F) =
      diagonal ![(κ : F), ((κ⁻¹ : Fˣ) : F), 1, 1, 1] := by
  rw [rootTorusHom_apply, coe_ctEmbed_diagSp_two]
  simp

theorem coe_ctEmbed_tauSp_rootTorusHom_zero (κ : Fˣ) :
    ((ctEmbed 1 (tauSp (rootTorusHom F 2 0 κ)) : SpecialLinearGroup (Fin (2 * 2 + 1)) F) :
        Matrix (Fin (2 * 2 + 1)) (Fin (2 * 2 + 1)) F) =
      diagonal ![(κ : F), ((κ⁻¹ : Fˣ) : F), (κ : F), ((κ⁻¹ : Fˣ) : F), 1] := by
  rw [tauSp_rootTorusHom_zero, coe_ctEmbed_diagSp_two]
  simp

@[expose] def oddFixBlock : Finset (Fin (2 * 2 + 1)) := {2, 3, 4}

@[expose] def oddTwA : Finset (Fin (2 * 2 + 1)) := {0, 2}

@[expose] def oddTwB : Finset (Fin (2 * 2 + 1)) := {1, 3}

end Model

section Std

variable {F : Type} [Field F] [Finite F] [CharP F 2]

omit [Finite F] [CharP F 2] in
theorem natCard_blockSpecialLinear_of_card {n m : ℕ} {I : Finset (Fin n)} (hI : I.card = m) :
    Nat.card (blockSpecialLinear (K := F) I) = Nat.card (SpecialLinearGroup (Fin m) F) := by
  rw [← LinearPilot.range_blockEmbed,
    ← Nat.card_congr (MonoidHom.ofInjective (LinearPilot.blockEmbed_injective (K := F) I)).toEquiv]
  exact Nat.card_congr
    (LinearPilot.reindexSpecialLinear (K := F) (I.equivFin.trans (finCongr hI))).toEquiv

omit [CharP F 2] in
theorem cube_dvd_natCard_SL_three :
    Nat.card F ^ 3 ∣ Nat.card (SpecialLinearGroup (Fin 3) F) := by
  have h := card_unitriangular (K := F) 3
  norm_num at h
  rw [← h]
  exact Subgroup.card_subgroup_dvd_card _

omit [Finite F] in
theorem blockSpecialLinear_oddFix_le_centralizer :
    blockSpecialLinear (K := F) oddFixBlock ≤
      centralizer (oddStdTorus F : Set (SpecialLinearGroup (Fin (2 * 2 + 1)) F)) := by
  intro x hx
  rw [mem_centralizer_iff]
  rintro _ ⟨_, ⟨κ, rfl⟩, rfl⟩
  refine (commute_of_mem_blockSpecialLinear_of_diagonal hx
    (coe_ctEmbed_rootTorusHom_zero κ) ?_).symm
  intro i hi j hj
  simp only [oddFixBlock, Finset.mem_insert, Finset.mem_singleton] at hi hj
  rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;> rfl

theorem blockSpecialLinear_oddFix_le_perfectCore_centralizer (hF : 4 ≤ Nat.card F) :
    blockSpecialLinear (K := F) oddFixBlock ≤
      perfectCore (centralizer (oddStdTorus F : Set (SpecialLinearGroup (Fin (2 * 2 + 1)) F))) :=
  le_perfectCore_of_perfect blockSpecialLinear_oddFix_le_centralizer
    (LinearPilot.commutator_blockSpecialLinear_eq_of_two_le (by decide) hF)

omit [Finite F] [CharP F 2] in
theorem natCard_blockSpecialLinear_oddFix :
    Nat.card (blockSpecialLinear (K := F) oddFixBlock) =
      Nat.card (SpecialLinearGroup (Fin 3) F) :=
  natCard_blockSpecialLinear_of_card (by decide)

end Std

section Tw

variable {F : Type} [Field F] [Finite F] [CharP F 2]

omit [Finite F] [CharP F 2] in
theorem eq_zero_of_commute_diagonal {n : ℕ} {g d : SpecialLinearGroup (Fin n) F}
    {v : Fin n → F} (hd : (d : Matrix (Fin n) (Fin n) F) = diagonal v) (hc : d * g = g * d)
    {i j : Fin n} (hij : v i ≠ v j) : (g : Matrix (Fin n) (Fin n) F) i j = 0 := by
  have hm := congrArg (fun M : SpecialLinearGroup (Fin n) F => (M : Matrix (Fin n) (Fin n) F) i j)
    hc
  simp only [Matrix.SpecialLinearGroup.coe_mul, hd, diagonal_mul, mul_diagonal] at hm
  have h1 : (v i - v j) * (g : Matrix (Fin n) (Fin n) F) i j = 0 := by linear_combination hm
  exact (mul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 hij)

theorem centralizer_oddTwTorus_le_blockDiagSL (hF : 4 ≤ Nat.card F)
    {I : Finset (Fin (2 * 2 + 1))} (hI : I = oddTwA ∨ I = ({4} : Finset (Fin (2 * 2 + 1)))) :
    centralizer (oddTwTorus F : Set (SpecialLinearGroup (Fin (2 * 2 + 1)) F)) ≤
      blockDiagSL (K := F) I := by
  obtain ⟨κ₀, hκ₀⟩ := exists_units_ne_one_of_four_le hF
  have e3 := coe_units_ne_inv_of_ne_one hκ₀
  have e1 : (κ₀ : F) ≠ 1 := fun h => hκ₀ (Units.ext h)
  have e2 : ((κ₀⁻¹ : Fˣ) : F) ≠ 1 := fun h => hκ₀ (inv_eq_one.1 (Units.ext h))
  have e4 : (κ₀ : F) ≠ (κ₀ : F)⁻¹ := by simpa using e3
  intro g hg
  have hd : ctEmbed 1 (tauSp (rootTorusHom F 2 0 κ₀)) ∈ oddTwTorus F :=
    ⟨_, ⟨_, ⟨κ₀, rfl⟩, rfl⟩, rfl⟩
  have hc := mem_centralizer_iff.1 hg _ hd
  rw [mem_blockDiagSL]
  intro i j hij
  apply eq_zero_of_commute_diagonal (coe_ctEmbed_tauSp_rootTorusHom_zero κ₀) hc
  rcases hI with rfl | rfl <;> fin_cases i <;> fin_cases j <;>
    simp [oddTwA] at hij ⊢ <;>
    first | exact hκ₀ | exact e1 | exact e1.symm | exact e2 | exact e2.symm | exact e3 |
      exact e3.symm | exact e4 | exact e4.symm

omit [Finite F] [CharP F 2] in
theorem blockSpecialLinear_singleton_eq_bot {n : ℕ} (i : Fin n) :
    blockSpecialLinear (K := F) ({i} : Finset (Fin n)) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [mem_blockSpecialLinear] at hx
  have hdiag : (x : Matrix (Fin n) (Fin n) F) = diagonal fun j => if j = i then
      (x : Matrix (Fin n) (Fin n) F) i i else 1 := by
    ext a b
    by_cases hab : a = b
    · subst hab
      by_cases hai : a = i
      · subst hai
        simp
      · rw [hx a a (Or.inl (by simpa using hai)), diagonal_apply_eq, ite_eq_right hai]
        simp
    · rw [hx a b (by by_contra h; push Not at h; simp at h; exact hab (h.1.trans h.2.symm)),
        diagonal_apply_ne _ hab, Matrix.one_apply_ne hab]
  have hdet : (x : Matrix (Fin n) (Fin n) F) i i = 1 := by
    have h1 := x.2
    rw [hdiag, det_diagonal, Finset.prod_eq_single i (fun j _ hj => by rw [ite_eq_right hj])
      (fun h => absurd (Finset.mem_univ i) h), ite_eq_left rfl] at h1
    exact h1
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [hdiag]
  ext a b
  by_cases hab : a = b
  · subst hab
    by_cases hai : a = i
    · subst hai
      simp [hdet]
    · simp [hai]
  · rw [diagonal_apply_ne _ hab, Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_ne hab]

theorem perfectCore_centralizer_oddTwTorus_le (hF : 4 ≤ Nat.card F) :
    perfectCore (centralizer (oddTwTorus F : Set (SpecialLinearGroup (Fin (2 * 2 + 1)) F))) ≤
      blockSpecialLinear (K := F) oddTwA ⊔ blockSpecialLinear (K := F) oddTwB := by
  set C := centralizer (oddTwTorus F : Set (SpecialLinearGroup (Fin (2 * 2 + 1)) F))
  have hC : perfectCore C ≤ ⁅C, C⁆ := by
    rw [← perfectCore_perfect C]
    exact Subgroup.commutator_mono (perfectCore_le C) (perfectCore_le C)
  have hA : ⁅C, C⁆ ≤ blockSpecialLinear (K := F) oddTwA ⊔ blockSpecialLinear oddTwAᶜ :=
    (Subgroup.commutator_mono (centralizer_oddTwTorus_le_blockDiagSL hF (Or.inl rfl))
      (centralizer_oddTwTorus_le_blockDiagSL hF (Or.inl rfl))).trans
      (LinearPilot.commutator_blockDiagSL_le _)
  have h4 : ⁅C, C⁆ ≤ blockSpecialLinear (K := F) ({4} : Finset (Fin (2 * 2 + 1)))ᶜ := by
    have h := (Subgroup.commutator_mono (centralizer_oddTwTorus_le_blockDiagSL hF (Or.inr rfl))
      (centralizer_oddTwTorus_le_blockDiagSL hF (Or.inr rfl))).trans
      (LinearPilot.commutator_blockDiagSL_le (K := F) ({4} : Finset (Fin (2 * 2 + 1))))
    rwa [blockSpecialLinear_singleton_eq_bot, bot_sup_eq] at h
  intro g hg
  have hgA := hA (hC hg)
  have hg4 := h4 (hC hg)
  have hcomm : ∀ (x : blockSpecialLinear (K := F) oddTwA)
      (y : blockSpecialLinear (K := F) oddTwAᶜ),
      Commute ((blockSpecialLinear (K := F) oddTwA).subtype x)
        ((blockSpecialLinear (K := F) oddTwAᶜ).subtype y) := fun x y =>
    LinearPilot.commute_blockSpecialLinear_of_disjoint disjoint_compl_right x.2 y.2
  have hr := MonoidHom.noncommCoprod_range _ _ hcomm
  simp only [range_subtype] at hr
  rw [← hr] at hgA
  obtain ⟨⟨a, b⟩, rfl⟩ := hgA
  change (a : SpecialLinearGroup (Fin (2 * 2 + 1)) F) * b ∈ _ at hg4 ⊢
  have ha4 : (a : SpecialLinearGroup (Fin (2 * 2 + 1)) F) ∈
      blockSpecialLinear (K := F) ({4} : Finset (Fin (2 * 2 + 1)))ᶜ :=
    LinearPilot.blockSpecialLinear_mono (by decide) a.2
  have hb4 : (b : SpecialLinearGroup (Fin (2 * 2 + 1)) F) ∈
      blockSpecialLinear (K := F) ({4} : Finset (Fin (2 * 2 + 1)))ᶜ := by
    have := mul_mem (inv_mem ha4) hg4
    rwa [inv_mul_cancel_left] at this
  have hbB : (b : SpecialLinearGroup (Fin (2 * 2 + 1)) F) ∈ blockSpecialLinear (K := F) oddTwB := by
    have h1 := mem_blockSpecialLinear.1 b.2
    have h2 := mem_blockSpecialLinear.1 hb4
    have key : ∀ i j : Fin (2 * 2 + 1), (i ∉ oddTwB ∨ j ∉ oddTwB) →
        (i ∉ oddTwAᶜ ∨ j ∉ oddTwAᶜ) ∨
          (i ∉ ({4} : Finset (Fin (2 * 2 + 1)))ᶜ ∨ j ∉ ({4} : Finset (Fin (2 * 2 + 1)))ᶜ) := by
      decide
    rw [mem_blockSpecialLinear]
    intro i j hij
    rcases key i j hij with h | h
    · exact h1 i j h
    · exact h2 i j h
  exact mul_mem (mem_sup_left a.2) (mem_sup_right hbB)

omit [Finite F] [CharP F 2] in
theorem natCard_sup_oddTw :
    Nat.card (blockSpecialLinear (K := F) oddTwA ⊔ blockSpecialLinear (K := F) oddTwB :
        Subgroup (SpecialLinearGroup (Fin (2 * 2 + 1)) F)) =
      Nat.card (SpecialLinearGroup (Fin 2) F) * Nat.card (SpecialLinearGroup (Fin 2) F) := by
  rw [natCard_sup_blockSpecialLinear_of_disjoint (by decide),
    natCard_blockSpecialLinear_of_card_two (by decide),
    natCard_blockSpecialLinear_of_card_two (by decide)]

theorem not_cube_dvd_sq_mul_sq_sub_one {q : ℕ} (hq2 : 2 ∣ q) (hq : 0 < q) :
    ¬ q ^ 3 ∣ (q * (q ^ 2 - 1)) * (q * (q ^ 2 - 1)) := by
  intro h
  have h1 : q * q * q ∣ q * q * ((q ^ 2 - 1) * (q ^ 2 - 1)) := by
    have e1 : q ^ 3 = q * q * q := by ring
    have e2 : (q * (q ^ 2 - 1)) * (q * (q ^ 2 - 1)) = q * q * ((q ^ 2 - 1) * (q ^ 2 - 1)) := by
      ring
    rwa [e1, e2] at h
  have h2 : q ∣ (q ^ 2 - 1) * (q ^ 2 - 1) := Nat.dvd_of_mul_dvd_mul_left (by positivity) h1
  have hev : Even (q ^ 2) := Nat.even_pow.2 ⟨even_iff_two_dvd.2 hq2, two_ne_zero⟩
  have hq1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
  have hodd : Odd (q ^ 2 - 1) := Nat.Even.sub_odd hq1 hev odd_one
  exact (Nat.not_even_iff_odd.2 (hodd.mul hodd)) (even_iff_two_dvd.2 (hq2.trans h2))

end Tw

end CFSG.SeitzReduction.SymplecticPilot
