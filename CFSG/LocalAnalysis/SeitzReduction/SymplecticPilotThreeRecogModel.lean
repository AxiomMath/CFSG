module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveTauGrp
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelTorus

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open CFSG.QuasithinUnique.Lin2.Five (tauSp coe_tauSp tauMat_apply tauPair)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear mem_blockSpecialLinear)
open CFSG.SeitzReduction.F4Pilot (statedSpMap coe_statedSpMap)
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect perfectCore_perfect)
open scoped MatrixGroups

section Torus

variable {K : Type} [Field K]

theorem tauSp_diagSp_two [CharP K 2] (t : Fin 2 → Kˣ) :
    tauSp (diagSp K 2 t) = diagSp K 2 ![t 0 * t 1, t 0 * (t 1)⁻¹] := by
  apply CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.statedSp_ext
  rw [coe_tauSp]
  have h1 : ∀ s : Fin 2 → Kˣ, (((diagSp K 2 s : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = diagonal (diagSpEntry s) := fun s =>
    mat_diagSp s
  rw [h1, h1]
  ext r c
  rw [tauMat_apply]
  fin_cases r <;> fin_cases c <;> simp [tauPair, diagSpEntry, mul_comm]

theorem tauSp_rootTorusHom_zero [CharP K 2] (κ : Kˣ) :
    tauSp (rootTorusHom K 2 0 κ) = diagSp K 2 ![κ, κ] := by
  rw [rootTorusHom_apply, tauSp_diagSp_two]
  congr 1
  funext i
  fin_cases i <;> simp

theorem tauSp_rootTorusHom_one [CharP K 2] (κ : Kˣ) :
    tauSp (rootTorusHom K 2 1 κ) = diagSp K 2 ![κ, κ⁻¹] := by
  rw [rootTorusHom_apply, tauSp_diagSp_two]
  congr 1
  funext i
  fin_cases i <;> simp

theorem spEmbed_rootTorusHom {m n : ℕ} {σ : Fin m → Fin n} (hσ : Function.Injective σ)
    (a : Fin m) (κ : Kˣ) : spEmbed σ hσ (rootTorusHom K m a κ) = rootTorusHom K n (σ a) κ := by
  have hinj : Function.Injective (Sum.map σ σ : Fin m ⊕ Fin m → Fin n ⊕ Fin n) :=
    Sum.map_injective.2 ⟨hσ, hσ⟩
  have hentry : ∀ u : Fin m ⊕ Fin m, diagSpEntry (Pi.mulSingle (σ a) κ) (Sum.map σ σ u) =
      diagSpEntry (Pi.mulSingle a κ) u := by
    intro u
    rcases u with i | i
    · simp only [Sum.map_inl, diagSpEntry_inl]
      by_cases h : i = a
      · subst h
        simp
      · rw [Pi.mulSingle_eq_of_ne (fun h' => h (hσ h')), Pi.mulSingle_eq_of_ne h]
    · simp only [Sum.map_inr, diagSpEntry_inr]
      by_cases h : i = a
      · subst h
        simp
      · rw [Pi.mulSingle_eq_of_ne (fun h' => h (hσ h')), Pi.mulSingle_eq_of_ne h]
  apply mat_injective
  rw [mat_spEmbed]
  ext x y
  rw [mat_rootTorusHom_apply]
  by_cases h : x ∈ Set.range (Sum.map σ σ) ∧ y ∈ Set.range (Sum.map σ σ)
  · obtain ⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩ := h
    rw [spEmbedMat_apply_image hσ, mat_rootTorusHom_apply]
    simp only [hinj.eq_iff, hentry]
  · rw [spEmbedMat_apply_of_not_mem _ h, Matrix.one_apply]
    by_cases hxy : x = y
    · subst hxy
      rw [ite_eq_left rfl, ite_eq_left rfl]
      have hx : x ∉ Set.range (Sum.map σ σ) := fun hx => h ⟨hx, hx⟩
      rcases x with i | i
      · have hi : i ≠ σ a := fun hi => hx ⟨Sum.inl a, by simp [hi]⟩
        simp [Pi.mulSingle_eq_of_ne hi]
      · have hi : i ≠ σ a := fun hi => hx ⟨Sum.inr a, by simp [hi]⟩
        simp [Pi.mulSingle_eq_of_ne hi]
    · rw [ite_eq_right hxy, ite_eq_right hxy]

theorem coe_complSpEquiv_rootTorusHom {m : ℕ} (k : Fin (m + 1)) (a : Fin m) (κ : Kˣ) :
    ((complSpEquiv k (rootTorusHom K m a κ) : complSp K k) : StatedSp (m + 1) K) =
      rootTorusHom K (m + 1) (k.succAbove a) κ := by
  rw [coe_complSpEquiv_apply, spEmbed_rootTorusHom]

end Torus


section SLFour

variable {F : Type} [Field F] [CharP F 2]

variable (F) in
@[expose] noncomputable def stdTorusSL (a : Fin 2) :
    Subgroup (SpecialLinearGroup (Fin (2 * 2)) F) :=
  (rootTorusSp F a).map (spModelSL 2 F)

variable (F) in
@[expose] noncomputable def twTorusSL (a : Fin 2) :
    Subgroup (SpecialLinearGroup (Fin (2 * 2)) F) :=
  ((rootTorusSp F a).map tauSp).map (spModelSL 2 F)

@[expose] def offPlaneSL (a : Fin 2) : Finset (Fin (2 * 2)) :=
  if a = 0 then {1, 3} else {0, 2}

@[expose] def twBlockSL (a : Fin 2) : Finset (Fin (2 * 2)) :=
  if a = 0 then {0, 1} else {0, 3}

theorem card_offPlaneSL (a : Fin 2) : (offPlaneSL a).card = 2 := by
  fin_cases a <;> decide

theorem card_twBlockSL (a : Fin 2) : (twBlockSL a).card = 2 := by
  fin_cases a <;> decide

theorem card_compl_twBlockSL (a : Fin 2) : (twBlockSL a)ᶜ.card = 2 := by
  fin_cases a <;> decide

theorem mem_stdTorusSL {a : Fin 2} {d : SpecialLinearGroup (Fin (2 * 2)) F} :
    d ∈ stdTorusSL F a ↔ ∃ κ : Fˣ, spModelSL 2 F (rootTorusHom F 2 a κ) = d := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨κ, rfl⟩ := mem_rootTorusSp.1 hx
    exact ⟨κ, rfl⟩
  · rintro ⟨κ, rfl⟩
    exact ⟨_, rootTorusHom_mem_rootTorusSp a κ, rfl⟩

theorem mem_twTorusSL {a : Fin 2} {d : SpecialLinearGroup (Fin (2 * 2)) F} :
    d ∈ twTorusSL F a ↔ ∃ κ : Fˣ, spModelSL 2 F (tauSp (rootTorusHom F 2 a κ)) = d := by
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    obtain ⟨κ, rfl⟩ := mem_rootTorusSp.1 hx
    exact ⟨κ, rfl⟩
  · rintro ⟨κ, rfl⟩
    exact ⟨_, ⟨_, rootTorusHom_mem_rootTorusSp a κ, rfl⟩, rfl⟩

theorem coe_spModelSL_tauSp_rootTorusHom (a : Fin 2) (κ : Fˣ) :
    ((spModelSL 2 F (tauSp (rootTorusHom F 2 a κ)) : SpecialLinearGroup (Fin (2 * 2)) F) :
        Matrix (Fin (2 * 2)) (Fin (2 * 2)) F) =
      diagonal fun i => if i ∈ twBlockSL a then (κ : F) else ((κ⁻¹ : Fˣ) : F) := by
  fin_cases a
  · rw [show ((⟨0, by omega⟩ : Fin 2)) = 0 from rfl, tauSp_rootTorusHom_zero,
      coe_spModelSL_diagSp]
    congr 1
    funext i
    fin_cases i <;> rfl
  · rw [show ((⟨1, by omega⟩ : Fin 2)) = 1 from rfl, tauSp_rootTorusHom_one, coe_spModelSL_diagSp]
    congr 1
    funext i
    fin_cases i <;> rfl

theorem coe_spModelSL_rootTorusHom (a : Fin 2) (κ : Fˣ) :
    ((spModelSL 2 F (rootTorusHom F 2 a κ) : SpecialLinearGroup (Fin (2 * 2)) F) :
        Matrix (Fin (2 * 2)) (Fin (2 * 2)) F) =
      diagonal fun i => diagSpEntry (Pi.mulSingle a κ) ((spModelIdx 2).symm i) := by
  rw [rootTorusHom_apply, coe_spModelSL_diagSp]

end SLFour


section Levi

variable {F : Type} [Field F] [CharP F 2]

theorem coe_spModelSL_rootTorusHom_eq (a : Fin 2) (κ : Fˣ) :
    ((spModelSL 2 F (rootTorusHom F 2 a κ) : SpecialLinearGroup (Fin (2 * 2)) F) :
        Matrix (Fin (2 * 2)) (Fin (2 * 2)) F) =
      diagonal fun i => if i ∈ offPlaneSL a then 1 else
        if (i : ℕ) < 2 then (κ : F) else ((κ⁻¹ : Fˣ) : F) := by
  rw [coe_spModelSL_rootTorusHom]
  congr 1
  funext i
  fin_cases a <;> fin_cases i <;> rfl

omit [CharP F 2] in
theorem commute_of_mem_blockSpecialLinear_of_diagonal {n : ℕ} {I : Finset (Fin n)}
    {x d : SpecialLinearGroup (Fin n) F} (hx : x ∈ blockSpecialLinear I) {v : Fin n → F}
    (hd : (d : Matrix (Fin n) (Fin n) F) = diagonal v) (hconst : ∀ i ∈ I, ∀ j ∈ I, v i = v j) :
    x * d = d * x := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, hd]
  ext i j
  rw [mul_diagonal, diagonal_mul]
  by_cases hij : i ∈ I ∧ j ∈ I
  · rw [hconst i hij.1 j hij.2, mul_comm]
  · rw [(mem_blockSpecialLinear.mp hx) i j (by tauto)]
    by_cases h : i = j
    · subst h
      rw [one_apply_eq, mul_one, one_mul]
    · rw [one_apply_ne h, zero_mul, mul_zero]

omit [CharP F 2] in
theorem exists_units_ne_one_of_four_le [Finite F] (hF : 4 ≤ Nat.card F) : ∃ κ : Fˣ, κ ≠ 1 := by
  by_contra h
  push Not at h
  have hsub : Subsingleton Fˣ := ⟨fun x y => (h x).trans (h y).symm⟩
  have h1 : Nat.card Fˣ = 1 := Nat.card_unique
  rw [Nat.card_units] at h1
  omega

theorem coe_units_ne_inv_of_ne_one {κ : Fˣ} (hκ : κ ≠ 1) : (κ : F) ≠ ((κ⁻¹ : Fˣ) : F) := by
  intro h
  apply hκ
  have h2 : (κ : F) * κ = 1 := by
    calc (κ : F) * κ = κ * ((κ⁻¹ : Fˣ) : F) := by rw [← h]
      _ = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h3 : ((κ : F) - 1) * ((κ : F) - 1) = 0 := by
    have h4 : ((κ : F) - 1) * ((κ : F) - 1) = (κ : F) * κ - 2 * κ + 1 := by ring
    rw [h4, h2, CharTwo.two_eq_zero, zero_mul, sub_zero]
    exact CharTwo.add_self_eq_zero 1
  have h5 : (κ : F) - 1 = 0 := mul_self_eq_zero.1 h3
  exact Units.ext (sub_eq_zero.1 h5)

theorem perfectCore_centralizer_stdTorusSL [Finite F] (hF : 4 ≤ Nat.card F) (a : Fin 2) :
    perfectCore (centralizer (stdTorusSL F a : Set (SpecialLinearGroup (Fin (2 * 2)) F))) =
      blockSpecialLinear (offPlaneSL a) := by
  obtain ⟨κ₀, hκ₀⟩ := exists_units_ne_one_of_four_le hF
  have h1 : (κ₀ : F) ≠ 1 := fun h => hκ₀ (Units.ext h)
  have h2 : ((κ₀⁻¹ : Fˣ) : F) ≠ 1 := fun h => hκ₀ (inv_eq_one.1 (Units.ext h))
  have h3 := coe_units_ne_inv_of_ne_one hκ₀
  have h := LinearPilot.perfectCore_inf_centralizer_eq_blockSpecialLinear
    (N := Finset.univ) (I := offPlaneSL a) (Finset.subset_univ _)
    (stdTorusSL F a : Set (SpecialLinearGroup (Fin (2 * 2)) F)) ?_ ?_ ?_
    (LinearPilot.commutator_blockSpecialLinear_eq_of_two_le (card_offPlaneSL a).ge hF)
  · rwa [LinearPilot.blockSpecialLinear_univ, top_inf_eq] at h
  · intro d hd i j hij
    obtain ⟨κ, rfl⟩ := mem_stdTorusSL.1 hd
    rw [coe_spModelSL_rootTorusHom_eq, diagonal_apply_ne _ hij]
  · intro d hd i hi j hj
    obtain ⟨κ, rfl⟩ := mem_stdTorusSL.1 hd
    rw [coe_spModelSL_rootTorusHom_eq, diagonal_apply_eq, diagonal_apply_eq, ite_eq_left hi,
      ite_eq_left hj]
  · intro i _ j _ hij hIJ
    refine ⟨_, mem_stdTorusSL.2 ⟨κ₀, rfl⟩, ?_⟩
    rw [coe_spModelSL_rootTorusHom_eq, diagonal_apply_eq, diagonal_apply_eq]
    fin_cases a <;> fin_cases i <;> fin_cases j <;>
      simp_all [offPlaneSL, eq_comm]


omit [CharP F 2] in
theorem commutator_sup_eq_self_of_perfect {H : Type*} [Group H] {A B : Subgroup H}
    (hA : ⁅A, A⁆ = A) (hB : ⁅B, B⁆ = B) : ⁅A ⊔ B, A ⊔ B⁆ = A ⊔ B := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro x hx y hy
    exact (A ⊔ B).mul_mem ((A ⊔ B).mul_mem ((A ⊔ B).mul_mem hx hy) ((A ⊔ B).inv_mem hx))
      ((A ⊔ B).inv_mem hy)
  · refine sup_le ?_ ?_
    · calc A = ⁅A, A⁆ := hA.symm
        _ ≤ ⁅A ⊔ B, A ⊔ B⁆ := Subgroup.commutator_mono le_sup_left le_sup_left
    · calc B = ⁅B, B⁆ := hB.symm
        _ ≤ ⁅A ⊔ B, A ⊔ B⁆ := Subgroup.commutator_mono le_sup_right le_sup_right

omit [CharP F 2] in
theorem natCard_blockSpecialLinear_of_card_two {n : ℕ} {I : Finset (Fin n)} (hI : I.card = 2) :
    Nat.card (blockSpecialLinear (K := F) I) = Nat.card (SpecialLinearGroup (Fin 2) F) := by
  rw [← LinearPilot.range_blockEmbed,
    ← Nat.card_congr (MonoidHom.ofInjective (LinearPilot.blockEmbed_injective (K := F) I)).toEquiv]
  exact Nat.card_congr
    (LinearPilot.reindexSpecialLinear (K := F) (I.equivFin.trans (finCongr hI))).toEquiv

omit [CharP F 2] in
theorem natCard_sup_blockSpecialLinear_of_disjoint {n : ℕ} {I I' : Finset (Fin n)}
    (h : Disjoint I I') :
    Nat.card (blockSpecialLinear (K := F) I ⊔ blockSpecialLinear (K := F) I' :
        Subgroup (SpecialLinearGroup (Fin n) F)) =
      Nat.card (blockSpecialLinear (K := F) I) * Nat.card (blockSpecialLinear (K := F) I') := by
  have hcomm : ∀ (x : blockSpecialLinear (K := F) I) (y : blockSpecialLinear (K := F) I'),
      Commute ((blockSpecialLinear (K := F) I).subtype x)
        ((blockSpecialLinear (K := F) I').subtype y) := fun x y =>
    LinearPilot.commute_blockSpecialLinear_of_disjoint h x.2 y.2
  have hinj : Function.Injective
      ((blockSpecialLinear (K := F) I).subtype.noncommCoprod
        (blockSpecialLinear (K := F) I').subtype hcomm) := by
    rw [MonoidHom.noncommCoprod_injective]
    refine ⟨Subtype.val_injective, Subtype.val_injective, ?_⟩
    rw [disjoint_iff_inf_le]
    rintro x ⟨⟨u, rfl⟩, ⟨v, hv⟩⟩
    rw [mem_bot]
    have hv' : (v : SpecialLinearGroup (Fin n) F) = u := hv
    have hu : (u : SpecialLinearGroup (Fin n) F) ∈ blockSpecialLinear I' := hv' ▸ v.2
    change (u : SpecialLinearGroup (Fin n) F) = 1
    apply Subtype.ext
    ext a b
    by_cases ha : a ∈ I
    · rw [hu a b (Or.inl (Finset.disjoint_left.1 h ha))]
      rfl
    · rw [u.2 a b (Or.inl ha)]
      rfl
  have hr := MonoidHom.noncommCoprod_range _ _ hcomm
  simp only [range_subtype] at hr
  rw [← hr, ← Nat.card_prod, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]

theorem sup_twBlock_le_perfectCore_centralizer_twTorusSL [Finite F] (hF : 4 ≤ Nat.card F)
    (a : Fin 2) :
    blockSpecialLinear (K := F) (twBlockSL a) ⊔ blockSpecialLinear (K := F) (twBlockSL a)ᶜ ≤
      perfectCore (centralizer (twTorusSL F a : Set (SpecialLinearGroup (Fin (2 * 2)) F))) := by
  have hperf := commutator_sup_eq_self_of_perfect
    (LinearPilot.commutator_blockSpecialLinear_eq_of_two_le (F := F) (card_twBlockSL a).ge hF)
    (LinearPilot.commutator_blockSpecialLinear_eq_of_two_le (F := F) (card_compl_twBlockSL a).ge
      hF)
  refine le_perfectCore_of_perfect ?_ hperf
  have hc : ∀ (I : Finset (Fin (2 * 2))), (I = twBlockSL a ∨ I = (twBlockSL a)ᶜ) →
      blockSpecialLinear (K := F) I ≤
        centralizer (twTorusSL F a : Set (SpecialLinearGroup (Fin (2 * 2)) F)) := by
    intro I hI x hx
    rw [mem_centralizer_iff]
    intro d hd
    obtain ⟨κ, rfl⟩ := mem_twTorusSL.1 hd
    refine (commute_of_mem_blockSpecialLinear_of_diagonal hx
      (coe_spModelSL_tauSp_rootTorusHom a κ) ?_).symm
    intro i hi j hj
    rcases hI with rfl | rfl
    · rw [ite_eq_left hi, ite_eq_left hj]
    · rw [Finset.mem_compl] at hi hj
      rw [ite_eq_right hi, ite_eq_right hj]
  exact sup_le (hc _ (Or.inl rfl)) (hc _ (Or.inr rfl))

omit [CharP F 2] in
theorem natCard_sup_twBlock (a : Fin 2) :
    Nat.card (blockSpecialLinear (K := F) (twBlockSL a) ⊔
        blockSpecialLinear (K := F) (twBlockSL a)ᶜ :
          Subgroup (SpecialLinearGroup (Fin (2 * 2)) F)) =
      Nat.card (SpecialLinearGroup (Fin 2) F) * Nat.card (SpecialLinearGroup (Fin 2) F) := by
  rw [natCard_sup_blockSpecialLinear_of_disjoint disjoint_compl_right,
    natCard_blockSpecialLinear_of_card_two (card_twBlockSL a),
    natCard_blockSpecialLinear_of_card_two (card_compl_twBlockSL a)]

end Levi

end CFSG.SeitzReduction.SymplecticPilot
