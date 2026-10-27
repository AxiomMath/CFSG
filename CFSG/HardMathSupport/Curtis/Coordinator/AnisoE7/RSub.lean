module

public import CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7.PlaneAssembly
public import CFSG.RankThree.PartOne.KE.E7ThreeLayerProof
public import CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7.Geometry

public noncomputable section

namespace CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7

open Matrix CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.Classical CFSG.RankThree.PartOne.KGD
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE
  CFSG.RankThree.Lattice CFSG.LieType.SeitzGeneration CFSG.LocalAnalysis.ComponentInitial
open scoped Matrix MatrixGroups Pointwise commutatorElement

set_option linter.unusedSectionVars false


section Unipotent

variable {L : Type} [Field L]

@[expose] def uMat (a : L) : SL(2, L) := ⟨!![1, a; 0, 1], by simp [Matrix.det_fin_two_of]⟩

@[expose] def lMat (a : L) : SL(2, L) := ⟨!![1, 0; a, 1], by simp [Matrix.det_fin_two_of]⟩

theorem coe_uMat (a : L) : ((uMat a : SL(2, L)) : Matrix (Fin 2) (Fin 2) L) = !![1, a; 0, 1] :=
  rfl

theorem uMat_add (a b : L) : uMat a * uMat b = uMat (a + b) := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;> simp [uMat, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem uMat_zero : uMat (0 : L) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat]

theorem uMat_pow (a : L) (m : ℕ) : uMat a ^ m = uMat (m * a) := by
  induction m with
  | zero => simp [uMat_zero]
  | succ m ih => rw [pow_succ, ih, uMat_add, Nat.cast_succ, add_mul, one_mul]

theorem uMat_one_pow_char {ℓ : ℕ} [CharP L ℓ] : uMat (1 : L) ^ ℓ = 1 := by
  rw [uMat_pow, CharP.cast_eq_zero, zero_mul, uMat_zero]

theorem uMat_one_not_mem_center : uMat (1 : L) ∉ Subgroup.center SL(2, L) := by
  intro h
  have h1 := Subgroup.mem_center_iff.1 h (lMat 1)
  have h2 := congrArg (fun Y : SL(2, L) => (Y : Matrix (Fin 2) (Fin 2) L) 0 0) h1
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at h2
  simp [uMat, lMat, Matrix.mul_apply, Fin.sum_univ_two] at h2

theorem conjSL_injective (M : GL (Fin 2) L) : Function.Injective (conjSL M) := by
  intro A B h
  have h1 := congrArg (conjSL M⁻¹) h
  rwa [← conjSL_mul, ← conjSL_mul, inv_mul_cancel, conjSL_one, conjSL_one] at h1

theorem conj_uMat_one {ℓ : ℕ} [CharP L ℓ] (Pm : GL (Fin 2) L) :
    conjSL Pm (uMat (1 : L)) ∉ Subgroup.center SL(2, L) ∧ conjSL Pm (uMat (1 : L)) ^ ℓ = 1 := by
  refine ⟨fun h => uMat_one_not_mem_center (L := L) ?_, by rw [← map_pow, uMat_one_pow_char, map_one]⟩
  rw [Subgroup.mem_center_iff] at h ⊢
  intro D
  apply conjSL_injective Pm
  rw [map_mul, map_mul]
  exact h (conjSL Pm D)

end Unipotent

section Generic

@[expose] def LFactor {τ : Tag} {L : Type} [Field L] (ℓ : ℕ) (n : ModGL τ L) (Fr : L →+* L)
    (S : Set (Fin τ.rank → ℤ)) : Prop :=
  ∃ P : Subgroup (ModGL τ L), Finite P ∧ ⁅P, P⁆ = P ∧ P ≤ rootSpan τ L S ∧
    P ≤ twistedFixedPoints n (Units.map (entrywiseHom Fr)) ∧ P ≤ adjointGroup τ L ∧
    ∃ y ∈ P, y ≠ 1 ∧ y ^ ℓ = 1

variable {τ : Tag} {L : Type} [Field L] {r₁ r₂ r₃ : Fin τ.rank → ℤ}

theorem commutator_self_of_isQuasisimple {G : Type*} [Group G] {P : Subgroup G}
    (h : CFSG.IsQuasisimple P) : ⁅P, P⁆ = P := by
  have : Group.IsPerfect P := h.1
  exact Subgroup.commutator_eq_self

theorem three_A1_twisted_lfactor
    (hc12 : ∀ A B : SL2 L, Commute (rootSL2 τ L r₁ A) (rootSL2 τ L r₂ B))
    (hc13 : ∀ A C : SL2 L, Commute (rootSL2 τ L r₁ A) (rootSL2 τ L r₃ C))
    (hc23 : ∀ B C : SL2 L, Commute (rootSL2 τ L r₂ B) (rootSL2 τ L r₃ C))
    (h₁ : IsRoot τ r₁) (h₂ : IsRoot τ r₂) (h₃ : IsRoot τ r₃)
    (μ : SL2 L × SL2 L × SL2 L →* ModGL τ L)
    (hμ : ∀ A B C, μ (A, B, C) = rootSL2 τ L r₁ A * rootSL2 τ L r₂ B * rootSL2 τ L r₃ C)
    (Fr : L →+* L) (n : ModGL τ L) (G₁ G₂ G₃ : SL2 L →* SL2 L)
    (hΘ : ∀ A B C : SL2 L, n * Units.map (entrywiseHom Fr) (μ (A, B, C)) * n⁻¹ =
      μ (G₃ C, G₁ A, G₂ B))
    (S₃ : Subgroup (SL2 L)) [Finite S₃]
    (hS₃ : ∀ B : SL2 L, B ∈ S₃ ↔ G₃ (G₂ (G₁ B)) = B) (hq₃ : CFSG.IsQuasisimple S₃)
    {ℓ : ℕ} {x : SL2 L} (hx : x ∈ S₃) (hxc : x ∉ Subgroup.center (SL2 L)) (hxℓ : x ^ ℓ = 1) :
    LFactor ℓ n Fr (threeRootSet r₁ r₂ r₃) := by
  classical
  have hker : ∀ A B C : SL2 L, μ (A, B, C) = 1 → A ∈ Subgroup.center (SL2 L) ∧
      B ∈ Subgroup.center (SL2 L) ∧ C ∈ Subgroup.center (SL2 L) := fun A B C h =>
    threeA1Tw_mem_center_of_mul_eq_one hc12 hc13 hc23 (by rw [← hμ]; exact h)
  obtain ⟨ν, hν⟩ : ∃ ν : SL2 L →* ModGL τ L, ∀ X, ν X = μ (X, G₁ X, G₂ (G₁ X)) :=
    ⟨μ.comp ((MonoidHom.id (SL2 L)).prod (G₁.prod (G₂.comp G₁))), fun X => rfl⟩
  obtain ⟨hPfin, hPq⟩ := threeA1Tw_map_isQuasisimple μ hker G₁ G₂ S₃ hq₃ ν hν
  have hρadj : ∀ r (A : SL2 L), rootSL2 τ L r A ∈ adjointGroup τ L := fun r A =>
    (exceptional_Lang_root_rank_one_data τ L r).2.2.2.2.1 A
  refine ⟨S₃.map ν, hPfin, commutator_self_of_isQuasisimple hPq, ?_, ?_, ?_, ν x, ⟨x, hx, rfl⟩,
    ?_, ?_⟩
  · rintro _ ⟨X, -, rfl⟩
    rw [hν]
    exact threeA1Tw_diag_mem_rootSpan h₁ h₂ h₃ μ hμ G₁ G₂ X
  · rintro _ ⟨X, hX, rfl⟩
    rw [hν]
    exact threeA1Tw_diag_mem_fixed μ (Units.map (entrywiseHom Fr)) n G₁ G₂ G₃ hΘ ((hS₃ X).1 hX)
  · rintro _ ⟨X, -, rfl⟩
    rw [hν, hμ]
    exact mul_mem (mul_mem (hρadj _ _) (hρadj _ _)) (hρadj _ _)
  · intro h1
    rw [hν] at h1
    exact hxc (hker _ _ _ h1).1
  · rw [← map_pow, hxℓ, map_one]

variable [IsAlgClosed L]

theorem three_A1_lang_data_elem {ℓ : ℕ} [CharP L ℓ] {Fr : L →+* L}
    (M₁ M₂ M₃ : GL (Fin 2) L) {k : Type} [Field k] [Finite k] [Algebra k L]
    (hk4 : 4 ≤ Nat.card k) {Fr₃ : L →+* L} (hFr₃ : ∀ c, Fr₃ c = c ^ Nat.card k)
    (hFr3eq : Fr.comp (Fr.comp Fr) = Fr₃) (Pm : GL (Fin 2) L)
    (hPm : Pm * Matrix.GeneralLinearGroup.map Fr₃ Pm⁻¹ =
      M₃ * Matrix.GeneralLinearGroup.map Fr (M₂ * Matrix.GeneralLinearGroup.map Fr M₁)) :
    ∃ S₃ : Subgroup (SL2 L), Finite S₃ ∧
      (∀ B : SL2 L, B ∈ S₃ ↔ twHom Fr M₃ (twHom Fr M₂ (twHom Fr M₁ B)) = B) ∧
      CFSG.IsQuasisimple S₃ ∧
      ∃ x ∈ S₃, x ∉ Subgroup.center (SL2 L) ∧ x ^ ℓ = 1 := by
  classical
  refine ⟨(Matrix.SpecialLinearGroup.map (algebraMap k L)).range.map (conjSL Pm), ?_⟩
  obtain ⟨hfin₃, hq₃⟩ := sl2_conj_range_quasisimple (K := k) (L := L) hk4 Pm
  refine ⟨hfin₃, fun B => ?_, hq₃, ?_⟩
  · rw [twHom_comp_three, hFr3eq, ← hPm]
    exact (sl2_twistedFixed_iff Fr₃ (frobenius_fixed_iff Fr₃ hFr₃) Pm B).symm
  · have hu : Matrix.SpecialLinearGroup.map (algebraMap k L) (uMat (1 : k)) = uMat (1 : L) := by
      ext i j
      rw [Matrix.SpecialLinearGroup.map_apply_coe, coe_uMat, coe_uMat]
      fin_cases i <;> fin_cases j <;> simp
    refine ⟨conjSL Pm (uMat (1 : L)), ⟨_, ⟨uMat (1 : k), rfl⟩, by rw [hu]⟩, ?_⟩
    exact conj_uMat_one Pm

theorem three_A1_cyclic_lfactor {ℓ : ℕ} [CharP L ℓ]
    (hc12 : ∀ A B : SL2 L, Commute (rootSL2 τ L r₁ A) (rootSL2 τ L r₂ B))
    (hc13 : ∀ A C : SL2 L, Commute (rootSL2 τ L r₁ A) (rootSL2 τ L r₃ C))
    (hc23 : ∀ B C : SL2 L, Commute (rootSL2 τ L r₂ B) (rootSL2 τ L r₃ C))
    (h₁ : IsRoot τ r₁) (h₂ : IsRoot τ r₂) (h₃ : IsRoot τ r₃)
    {Fr : L →+* L} (n : ModGL τ L) (M₁ M₂ M₃ : GL (Fin 2) L)
    (e₁ : ∀ A : SL2 L, n * rootSL2 τ L r₁ A * n⁻¹ = rootSL2 τ L r₂ (conjSL M₁ A))
    (e₂ : ∀ B : SL2 L, n * rootSL2 τ L r₂ B * n⁻¹ = rootSL2 τ L r₃ (conjSL M₂ B))
    (e₃ : ∀ C : SL2 L, n * rootSL2 τ L r₃ C * n⁻¹ = rootSL2 τ L r₁ (conjSL M₃ C))
    {k : Type} [Field k] [Finite k] [Algebra k L] (hk4 : 4 ≤ Nat.card k) {Fr₃ : L →+* L}
    (hFr₃ : ∀ c, Fr₃ c = c ^ Nat.card k) (hFr3eq : Fr.comp (Fr.comp Fr) = Fr₃)
    (Pm : GL (Fin 2) L)
    (hPm : Pm * Matrix.GeneralLinearGroup.map Fr₃ Pm⁻¹ =
      M₃ * Matrix.GeneralLinearGroup.map Fr (M₂ * Matrix.GeneralLinearGroup.map Fr M₁)) :
    LFactor ℓ n Fr (threeRootSet r₁ r₂ r₃) := by
  classical
  obtain ⟨μ, hμ⟩ : ∃ μ : SL2 L × SL2 L × SL2 L →* ModGL τ L, ∀ A B C,
      μ (A, B, C) = rootSL2 τ L r₁ A * rootSL2 τ L r₂ B * rootSL2 τ L r₃ C :=
    ⟨(rootSL2 τ L r₁).noncommCoprod ((rootSL2 τ L r₂).noncommCoprod (rootSL2 τ L r₃) hc23)
      fun A BC => (hc12 A BC.1).mul_right (hc13 A BC.2), fun A B C => (mul_assoc _ _ _).symm⟩
  obtain ⟨S₃, hfin₃, hS₃, hq₃, x, hx, hxc, hxℓ⟩ :=
    three_A1_lang_data_elem (Fr := Fr) M₁ M₂ M₃ hk4 hFr₃ hFr3eq Pm hPm
  exact three_A1_twisted_lfactor hc12 hc13 hc23 h₁ h₂ h₃ μ hμ Fr n (twHom Fr M₁)
    (twHom Fr M₂) (twHom Fr M₃) (three_A1_theta hc12 hc13 μ hμ Fr n M₁ M₂ M₃ e₁ e₂ e₃) S₃ hS₃
    hq₃ hx hxc hxℓ

end Generic

section Std

variable {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ]

theorem e7_a1_std_lfactor (hf : 1 ≤ f) {n : ModGL Tag.E7 L} (hn : n ∈ monomialSubgroup Tag.E7 L)
    (h₁ : weylQuotientHom Tag.E7 L ⟨n, hn⟩ • (Pi.single (1 : Fin Tag.E7.rank) 1 :
      Fin Tag.E7.rank → ℤ) = -Pi.single 6 1)
    (h₂ : weylQuotientHom Tag.E7 L ⟨n, hn⟩ • (Pi.single (6 : Fin Tag.E7.rank) 1 :
      Fin Tag.E7.rank → ℤ) = -Pi.single 4 1)
    (h₃ : weylQuotientHom Tag.E7 L ⟨n, hn⟩ • (Pi.single (4 : Fin Tag.E7.rank) 1 :
      Fin Tag.E7.rank → ℤ) = -Pi.single 1 1) :
    LFactor ℓ n (iterateFrobenius L ℓ f)
      (threeRootSet (Pi.single (1 : Fin Tag.E7.rank) 1) (Pi.single 6 1) (Pi.single 4 1)) := by
  classical
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFrbij : Function.Bijective Fr := iterateFrobenius_bijective
  have hr₁ : IsRoot Tag.E7 (Pi.single (1 : Fin Tag.E7.rank) 1) := isRoot_single _ _
  have hr₂ : IsRoot Tag.E7 (Pi.single (6 : Fin Tag.E7.rank) 1) := isRoot_single _ _
  have hr₃ : IsRoot Tag.E7 (Pi.single (4 : Fin Tag.E7.rank) 1) := isRoot_single _ _
  have hc12 := e7_commute_of_orth (L := L) hr₁ hr₂ (e7_a1_orth_check 1 6 (by decide) (by decide)
    (by decide))
  have hc13 := e7_commute_of_orth (L := L) hr₁ hr₃ (e7_a1_orth_check 1 4 (by decide) (by decide)
    (by decide))
  have hc23 := e7_commute_of_orth (L := L) hr₂ hr₃ (e7_a1_orth_check 6 4 (by decide) (by decide)
    (by decide))
  obtain ⟨k, _, _, _, Fr₃, hk4, hFr₃, hFr3eq⟩ := exists_frob_three (L := L) (ℓ := ℓ) (f := f) hf
  obtain ⟨s₁, e₁⟩ := exists_conj_rootSL2_eq_neg hn hr₁ hr₂ h₁
  obtain ⟨s₂, e₂⟩ := exists_conj_rootSL2_eq_neg hn hr₂ hr₃ h₂
  obtain ⟨s₃, e₃⟩ := exists_conj_rootSL2_eq_neg hn hr₃ hr₁ h₃
  obtain ⟨Pm, hPm⟩ := exists_twist_antidiag (K := k) Fr₃ hFr₃ (Units.map Fr.toMonoidHom s₂)
    (s₃ * Units.map Fr.toMonoidHom (Units.map Fr.toMonoidHom s₁)) _
    (coe_antidiag_triple (Units.map Fr.toMonoidHom (Units.map Fr.toMonoidHom s₁))
      (Units.map Fr.toMonoidHom s₂) s₃)
  refine three_A1_cyclic_lfactor hc12 hc13 hc23 hr₁ hr₂ hr₃ n _ _ _ e₁ e₂ e₃ hk4 hFr₃
    hFr3eq Pm ?_
  rw [hPm]
  simp only [map_mul, glMap_swapGL, glMap_diagUnitOne]

end Std

section Transport

variable {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ]

theorem e7_a1_lfactor_of_cycle (hf : 1 ≤ f) (v : WeylGroup Tag.E7) (n : ModGL Tag.E7 L)
    (hnm : n ∈ monomialSubgroup Tag.E7 L)
    (hset : parabolicRoots Tag.E7 (a1Nodes Tag.E7) =
      threeRootSet (Pi.single (1 : Fin Tag.E7.rank) 1) (Pi.single 6 1) (Pi.single 4 1))
    (h₁ : (v⁻¹ * weylQuotientHom Tag.E7 L ⟨n, hnm⟩ * v) •
      (Pi.single (1 : Fin Tag.E7.rank) 1 : Fin Tag.E7.rank → ℤ) = -Pi.single 6 1)
    (h₂ : (v⁻¹ * weylQuotientHom Tag.E7 L ⟨n, hnm⟩ * v) •
      (Pi.single (6 : Fin Tag.E7.rank) 1 : Fin Tag.E7.rank → ℤ) = -Pi.single 4 1)
    (h₃ : (v⁻¹ * weylQuotientHom Tag.E7 L ⟨n, hnm⟩ * v) •
      (Pi.single (4 : Fin Tag.E7.rank) 1 : Fin Tag.E7.rank → ℤ) = -Pi.single 1 1) :
    LFactor ℓ n (iterateFrobenius L ℓ f)
      ((fun γ => v • γ) '' parabolicRoots Tag.E7 (a1Nodes Tag.E7)) := by
  classical
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFrbij : Function.Bijective Fr := iterateFrobenius_bijective
  set Φ : ModGL Tag.E7 L →* ModGL Tag.E7 L := Units.map (entrywiseHom Fr) with hΦ
  set V : ModGL Tag.E7 L := canonicalRep (coxeterSystem Tag.E7) L v with hV
  have hVm : V ∈ monomialSubgroup Tag.E7 L := canonicalRep_mem_monomialSubgroup L v
  have hΦV : Φ V = V := by
    have h1 := entrywise_canonicalRep (RingEquiv.ofBijective Fr hFrbij) v
    have h2 : (RingEquiv.ofBijective Fr hFrbij).toRingHom = Fr := RingHom.ext fun _ => rfl
    rw [h2] at h1
    exact h1
  have hVadj : V ∈ adjointGroup Tag.E7 L := canonicalRep_mem_adjointGroup _ L v
  set n' : ModGL Tag.E7 L := V⁻¹ * n * V with hn'
  have hn'm : n' ∈ monomialSubgroup Tag.E7 L := mul_mem (mul_mem (inv_mem hVm) hnm) hVm
  have hπV : weylQuotientHom Tag.E7 L ⟨V, hVm⟩ = v :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep v)
  have hπn' : weylQuotientHom Tag.E7 L ⟨n', hn'm⟩ =
      v⁻¹ * weylQuotientHom Tag.E7 L ⟨n, hnm⟩ * v := by
    have : (⟨n', hn'm⟩ : monomialSubgroup Tag.E7 L) = ⟨V, hVm⟩⁻¹ * ⟨n, hnm⟩ * ⟨V, hVm⟩ :=
      Subtype.ext rfl
    rw [this, map_mul, map_mul, map_inv, hπV]
  obtain ⟨P', hfin, hperf, hroot, hfix, hadj, y, hy, hy1, hyℓ⟩ :=
    e7_a1_std_lfactor (L := L) (ℓ := ℓ) hf hn'm (by rw [hπn']; exact h₁) (by rw [hπn']; exact h₂)
      (by rw [hπn']; exact h₃)
  have hroots : ∀ r ∈ parabolicRoots Tag.E7 (a1Nodes Tag.E7), IsRoot Tag.E7 r := fun r hr => hr.1
  set c₀ : ModGL Tag.E7 L →* ModGL Tag.E7 L := (MulAut.conj V).toMonoidHom with hc₀
  have hcapp : ∀ x, c₀ x = V * x * V⁻¹ := fun x => by simp [hc₀, MulAut.conj_apply]
  have hcinj : Function.Injective c₀ := (MulAut.conj V).injective
  have hQmap : (rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a1Nodes Tag.E7))).map c₀ =
      rootSpan Tag.E7 L ((fun γ => v • γ) '' parabolicRoots Tag.E7 (a1Nodes Tag.E7)) :=
    map_conj_rootSpan v hroots
  have hRiff : ∀ x, x ∈ twistedFixedPoints n' Φ ↔ c₀ x ∈ twistedFixedPoints n Φ := fun x => by
    rw [hcapp]
    exact mem_twistedFixedPoints_conj hΦV
  have hroot' : P' ≤ rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a1Nodes Tag.E7)) := by
    rw [hset]
    exact hroot
  refine ⟨P'.map c₀, ?_, ?_, ?_, ?_, ?_, c₀ y, ⟨y, hy, rfl⟩, ?_, ?_⟩
  · have := hfin
    exact Finite.of_equiv P' (Subgroup.equivMapOfInjective P' c₀ hcinj).toEquiv
  · rw [← Subgroup.map_commutator, hperf]
  · rw [← hQmap]
    exact Subgroup.map_mono hroot'
  · rintro _ ⟨x, hx, rfl⟩
    exact (hRiff x).1 (hfix hx)
  · rintro _ ⟨x, hx, rfl⟩
    rw [hcapp]
    exact mul_mem (mul_mem hVadj (hadj hx)) (inv_mem hVadj)
  · intro h1
    exact hy1 (hcinj (by rw [h1, map_one]))
  · rw [← map_pow, hyℓ, map_one]

theorem e7_a1_lfactor (hf : 1 ≤ f) (v : WeylGroup Tag.E7) (n : ModGL Tag.E7 L)
    (hnm : n ∈ monomialSubgroup Tag.E7 L)
    (hcert : ∀ α ∈ parabolicRoots Tag.E7 (a1Nodes Tag.E7),
      (v⁻¹ * weylQuotientHom Tag.E7 L ⟨n, hnm⟩ * v) • α =
        (-1 : ℤ) • permLattice (List.formPerm [(1 : Fin Tag.E7.rank), 6, 4]) α) :
    LFactor ℓ n (iterateFrobenius L ℓ f)
      ((fun γ => v • γ) '' parabolicRoots Tag.E7 (a1Nodes Tag.E7)) := by
  have hset := parabolicRoots_a1Nodes_eq
  have hmem : ∀ x : Fin Tag.E7.rank → ℤ, x ∈ threeRootSet (Pi.single (1 : Fin Tag.E7.rank) 1)
      (Pi.single 4 1) (Pi.single 6 1) → x ∈ parabolicRoots Tag.E7 (a1Nodes Tag.E7) :=
    fun x hx => hset ▸ hx
  have m1 := hmem (Pi.single 1 1) (by simp [threeRootSet])
  have m4 := hmem (Pi.single 4 1) (by simp [threeRootSet])
  have m6 := hmem (Pi.single 6 1) (by simp [threeRootSet])
  refine e7_a1_lfactor_of_cycle hf v n hnm (by rw [hset, threeRootSet_swap₂₃]) ?_ ?_ ?_
  · rw [hcert _ m1, permLattice_single, show (List.formPerm [(1 : Fin Tag.E7.rank), 6, 4]) 1 = 6
      from by decide, neg_one_smul]
  · rw [hcert _ m6, permLattice_single, show (List.formPerm [(1 : Fin Tag.E7.rank), 6, 4]) 6 = 4
      from by decide, neg_one_smul]
  · rw [hcert _ m4, permLattice_single, show (List.formPerm [(1 : Fin Tag.E7.rank), 6, 4]) 4 = 1
      from by decide, neg_one_smul]

end Transport

section Final

@[expose] def cert0 : E7T3Cert := e7T3Certs.getD 0 default

theorem cert0_mem : cert0 ∈ e7T3Certs := by
  unfold cert0 e7T3Certs
  exact List.mem_cons_self

theorem cert0_comps : cert0.comps = [{ kind := 1, u := [], rot := true }] := rfl

theorem cert0_good_comp :
    E7T3Comp.Good e7T3Word cert0.w { kind := 1, u := [], rot := true } := by
  unfold cert0
  decide +kernel

theorem cert0_good : cert0.Good := by
  unfold cert0
  decide +kernel

theorem sigma0_mem_cert0 : sigma0 ∈ cert0.rootList := by
  unfold cert0
  decide +kernel

theorem cert0_orbit : ∀ l ∈ cert0.rootList, ∃ j < 6, l = negWorbit j := by
  rcases cert_cases cert0 cert0_mem sigma0_mem_cert0 with ⟨-, h⟩ | h | h
  · exact h
  · rw [cert0_comps] at h
    simp at h
  · rw [cert0_comps] at h
    simp at h

theorem e7SixRSub : E7SixRSub := by
  intro K _ _ ℓ f p _ _ L _ _ _ _ F hK c
  classical
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Fintype K := Fintype.ofFinite K
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · rw [pow_zero] at hK
      omega
    · exact h
  have hFr : ∀ x, iterateFrobenius L ℓ f x = x ^ (ℓ ^ f) := fun x => iterateFrobenius_def ℓ f x
  have hFrK : ∀ x, iterateFrobenius L ℓ f x = x ^ Nat.card K := fun x => by rw [hK]; exact hFr x
  have hcomp : (iterateFrobenius L ℓ f).comp (algebraMap K L) = algebraMap K L := by
    refine RingHom.ext fun a => ?_
    rw [RingHom.comp_apply, hFrK, ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hfixι : ∀ z : adjointGroup .E7 K,
      Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (adjEmb .E7 K L z) = adjEmb .E7 K L z := by
    intro z
    have e : Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (adjEmb .E7 K L z) =
        baseChangeGL (iterateFrobenius L ℓ f) (baseChangeGL (algebraMap K L) (z : ModGL .E7 K)) := by
      rw [adjEmb_apply]
      exact Units.ext rfl
    rw [e, baseChangeGL_baseChangeGL, hcomp, ← adjEmb_apply]
  have hcert : ∀ α ∈ parabolicRoots Tag.E7 (a1Nodes Tag.E7),
      (((coxeterSystem Tag.E7).wordProd cert0.w)⁻¹ * weylQuotientHom Tag.E7 L ⟨F.n, F.hnm⟩ *
        (coxeterSystem Tag.E7).wordProd cert0.w) • α =
        (-1 : ℤ) • permLattice (List.formPerm [(1 : Fin Tag.E7.rank), 6, 4]) α := by
    intro α hα
    obtain ⟨-, hact⟩ := e7T3_comp_eps (Or.inr rfl) F.hnW cert0_good_comp
    rw [hact α hα]
    simp [e7T3Beta]
  have hLF := e7_a1_lfactor (ℓ := ℓ) hf ((coxeterSystem Tag.E7).wordProd cert0.w) F.n F.hnm hcert
  have hS := e7T3_rootSet_single (c := cert0) cert0_comps (by decide : (1 : ℕ) < 4)
  have hLF' : LFactor ℓ F.n (iterateFrobenius L ℓ f)
      {α | ∃ l ∈ cert0.rootList, α = toVec Tag.E7.rank l} := by
    rw [hS]
    exact hLF
  obtain ⟨P, hPfin, hPperf, hProot, hPfix, hPadj, y, hyP, hy1, hyℓ⟩ := hLF'
  have hcj : ∀ x, (MulAut.conj F.g0).toMonoidHom x = F.g0 * x * F.g0⁻¹ := fun x => by
    simp [MulAut.conj_apply]
  have hcjinj : Function.Injective (MulAut.conj F.g0).toMonoidHom := (MulAut.conj F.g0).injective
  have hP₁ : P.map (MulAut.conj F.g0).toMonoidHom ≤ (adjEmb .E7 K L).range := by
    refine F.hperf _ ?_ ?_ ?_ ?_
    · have := hPfin
      exact Finite.of_equiv P (Subgroup.equivMapOfInjective P _ hcjinj).toEquiv
    · rintro _ ⟨x, hx, rfl⟩
      rw [hcj]
      exact mul_mem (mul_mem F.hg0C (hPadj hx)) (inv_mem F.hg0C)
    · rintro _ ⟨x, hx, rfl⟩
      have hfx := mem_twistedFixedPoints.1 (hPfix hx)
      rw [hcj, map_mul, map_mul, map_inv, F.hg0]
      have : F.g0 * x * F.g0⁻¹ = F.g0 * (F.n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x *
          F.n⁻¹) * F.g0⁻¹ := by rw [hfx]
      rw [this]
      group
    · rw [← Subgroup.map_commutator, hPperf]
  have hy₁ : F.g0 * y * F.g0⁻¹ ∈ (adjEmb .E7 K L).range := by
    rw [← hcj]
    exact hP₁ ⟨y, hyP, rfl⟩
  obtain ⟨u₀, hu₀⟩ := hy₁
  obtain ⟨u, hψu⟩ : ∃ u : adjointGroup .E7 K, psiC F.g0 c u = y := by
    refine ⟨c⁻¹ * u₀ * c, ?_⟩
    rw [psiC_apply]
    have : c * (c⁻¹ * u₀ * c) * c⁻¹ = u₀ := by group
    rw [this, hu₀]
    group
  have hu1 : u ≠ 1 := fun h => hy1 (by rw [← hψu, h, map_one])
  have huℓ : u ^ ℓ = 1 := psiC_injective F.g0 c (by rw [map_pow, hψu, hyℓ, map_one])
  have hord : orderOf u = ℓ := orderOf_eq_prime huℓ hu1
  refine ⟨Subgroup.zpowers u, fun h => hu1 (Subgroup.zpowers_eq_bot.1 h),
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one]), ?_⟩
  rintro e ⟨b, hb, hbσ⟩ u' hu'
  have hTe : rootDiagUnit .E7 b ∈
      twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) := by
    rw [mem_twistedTorusOf]
    refine ⟨rootDiagUnit_mem_torusGroup b, ?_⟩
    rw [hb, psiC_apply, map_mul, map_mul, map_inv, F.hg0, hfixι]
    group
  rw [F.hT] at hTe
  obtain ⟨b', hb', hbb'⟩ := hTe
  have hbb : b' = b := rootDiagUnit_injective hbb'
  rw [hbb] at hb'
  have hsub : {α | ∃ l ∈ cert0.rootList, α = toVec Tag.E7.rank l} ⊆ rootCharKernel b := by
    rintro _ ⟨l, hl, rfl⟩
    refine ⟨isRoot_toVec (cert0_good.2.2.1 l hl), ?_⟩
    obtain ⟨j, -, rfl⟩ := cert0_orbit l hl
    rw [toVec_negWorbit j, rootChar_pow_mulVec_of_mem_fixedCharTuples (hFr := hFr) hb' j, hbσ,
      one_pow]
  have hcent := rootSpan_le_centralizer b hsub
  have hyc := Subgroup.mem_centralizer_singleton_iff.1 (hcent (hProot hyP))
  have hcomm : e * u = u * e := by
    apply psiC_injective F.g0 c
    rw [map_mul, map_mul, hψu, ← hb]
    exact hyc.symm
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu'
  exact (Commute.zpow_right hcomm m).eq

end Final

end CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7
