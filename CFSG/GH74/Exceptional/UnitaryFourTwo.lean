module

public import CFSG.GH74.Exceptional.UnitaryFourTwoData
public import CFSG.Fischer.Classification.PartIII.Beta.Iso
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalSmallSourceUnitary
public import CFSG.LieType.Universal.Unitary.Clause0

public section

namespace CFSG.GH74.Exceptional

open Matrix CFSG.Assembly.LowTwoRank CFSG.Fischer CFSG.Fischer.Classification
open CFSG.Fischer.Classification.Beta

abbrev PSp43 := StatedProj (StatedSp 2 (ZMod 3))

@[expose] def sp43Unit (i : Fin 45) : GL (Fin 2 ⊕ Fin 2) (ZMod 3) :=
  ⟨sp43Mat i, sp43Mat i, sp43Mat_sq i, sp43Mat_sq i⟩

theorem sp43Unit_mem (i : Fin 45) : sp43Unit i ∈ StatedSp 2 (ZMod 3) :=
  Subgroup.subset_closure (sp43Mat_symp i)

@[expose] noncomputable def s43 (i : Fin 45) : PSp43 :=
  QuotientGroup.mk ⟨sp43Unit i, sp43Unit_mem i⟩

theorem neg_one_mem_statedSp : (-1 : GL (Fin 2 ⊕ Fin 2) (ZMod 3)) ∈ StatedSp 2 (ZMod 3) :=
  Subgroup.subset_closure (by simp)

theorem scalar_neg_one :
    Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) (-1 : (ZMod 3)ˣ) = -1 := by
  refine Units.ext ?_
  ext a b
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Units.val_neg, Units.val_one,
    Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.neg_apply, Matrix.one_apply]
  by_cases h : a = b
  · simp [h]
  · simp [h]
    decide

theorem neg_one_mem_statedScalars :
    (-1 : GL (Fin 2 ⊕ Fin 2) (ZMod 3)) ∈ StatedScalars (Fin 2 ⊕ Fin 2) (ZMod 3) :=
  ⟨-1, scalar_neg_one⟩

theorem mk_eq_mk_of_eq_neg {g h : StatedSp 2 (ZMod 3)}
    (hgh : (g : GL (Fin 2 ⊕ Fin 2) (ZMod 3)) = -(h : GL (Fin 2 ⊕ Fin 2) (ZMod 3))) :
    (QuotientGroup.mk g : PSp43) = QuotientGroup.mk h := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have : ((g⁻¹ * h : StatedSp 2 (ZMod 3)) : GL (Fin 2 ⊕ Fin 2) (ZMod 3)) = -1 := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_eq_iff_eq_mul, hgh, neg_mul_neg, mul_one]
  rw [this]
  exact neg_one_mem_statedScalars

theorem s43_mul_self (i : Fin 45) : s43 i * s43 i = 1 := by
  rw [s43, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
  have : (⟨sp43Unit i, sp43Unit_mem i⟩ * ⟨sp43Unit i, sp43Unit_mem i⟩ :
      StatedSp 2 (ZMod 3)) = 1 :=
    Subtype.ext (Units.ext (sp43Mat_sq i))
  rw [this]
  exact Subgroup.one_mem _

theorem s43_inv (i : Fin 45) : (s43 i)⁻¹ = s43 i :=
  inv_eq_of_mul_eq_one_right (s43_mul_self i)

theorem s43_tau (i j : Fin 45) : s43 i * s43 j * s43 i = s43 (uIdx (tU (uPt i) (uPt j))) := by
  simp only [s43, ← QuotientGroup.mk_mul]
  rcases sp43Mat_tau i j with h | h
  · congr 1
    exact Subtype.ext (Units.ext h)
  · exact mk_eq_mk_of_eq_neg (Units.ext (by
      simp only [Subgroup.coe_mul, Units.val_mul, Units.val_neg]
      exact h))

theorem units_zmod_three (c : (ZMod 3)ˣ) : c = 1 ∨ c = -1 := by
  revert c
  decide

theorem s43_injective : Function.Injective s43 := by
  intro i j hij
  rw [s43, s43, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hij
  obtain ⟨c, hc⟩ := hij
  have hc' : Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c = (sp43Unit i)⁻¹ * sp43Unit j :=
    hc
  have h1 : sp43Unit i * Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c = sp43Unit j := by
    rw [hc', mul_inv_cancel_left]
  refine (sp43Mat_inj ?_).symm
  rcases units_zmod_three c with rfl | rfl
  · left
    rw [map_one, mul_one] at h1
    exact (congrArg Units.val h1).symm
  · right
    rw [scalar_neg_one, mul_neg_one] at h1
    have := congrArg Units.val h1
    rw [Units.val_neg] at this
    exact this.symm

open Classical in
@[expose] noncomputable def s43Idx (x : PSp43) : Fin 45 :=
  if h : ∃ i, s43 i = x then h.choose else 0

theorem s43Idx_s43 (i : Fin 45) : s43Idx (s43 i) = i := by
  have h : ∃ k, s43 k = s43 i := ⟨i, rfl⟩
  rw [s43Idx, dite_eq_left h]
  exact s43_injective h.choose_spec

theorem s43_s43Idx {x : PSp43} (hx : x ∈ Set.range s43) : s43 (s43Idx x) = x := by
  obtain ⟨i, rfl⟩ := hx
  rw [s43Idx_s43]

noncomputable abbrev Y43 : Subgroup PSp43 := Subgroup.closure (Set.range s43)

theorem conj_mem_range {g : PSp43} (hg : g ∈ Y43) :
    ∀ j : Fin 45, g * s43 j * g⁻¹ ∈ Set.range s43 ∧ g⁻¹ * s43 j * g ∈ Set.range s43 := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    intro j
    rw [s43_inv]
    exact ⟨⟨_, (s43_tau i j).symm⟩, ⟨_, (s43_tau i j).symm⟩⟩
  | one => simp
  | mul x y _ _ hx hy =>
    intro j
    obtain ⟨k, hk⟩ := (hy j).1
    obtain ⟨l, hl⟩ := (hx j).2
    refine ⟨?_, ?_⟩
    · have : x * y * s43 j * (x * y)⁻¹ = x * (y * s43 j * y⁻¹) * x⁻¹ := by group
      rw [this, ← hk]
      exact (hx k).1
    · have : (x * y)⁻¹ * s43 j * (x * y) = y⁻¹ * (x⁻¹ * s43 j * x) * y := by group
      rw [this, ← hl]
      exact (hy l).2
  | inv x _ hx =>
    intro j
    rw [inv_inv]
    exact ⟨(hx j).2, (hx j).1⟩

@[expose] noncomputable def sigma43 : Y43 →* Equiv.Perm (Fin 45) where
  toFun g :=
    { toFun := fun j => s43Idx ((g : PSp43) * s43 j * (g : PSp43)⁻¹)
      invFun := fun j => s43Idx ((g : PSp43)⁻¹ * s43 j * g)
      left_inv := fun j => by
        simp only
        rw [s43_s43Idx (conj_mem_range g.2 j).1,
          show (g : PSp43)⁻¹ * ((g : PSp43) * s43 j * (g : PSp43)⁻¹) * g = s43 j by group,
          s43Idx_s43]
      right_inv := fun j => by
        simp only
        rw [s43_s43Idx (conj_mem_range g.2 j).2,
          show (g : PSp43) * ((g : PSp43)⁻¹ * s43 j * g) * (g : PSp43)⁻¹ = s43 j by group,
          s43Idx_s43] }
  map_one' := Equiv.ext fun j => by simp [s43Idx_s43]
  map_mul' g h := Equiv.ext fun j => by
    simp only [Equiv.Perm.coe_mul, Function.comp_apply, Subgroup.coe_mul, Equiv.coe_fn_mk]
    rw [s43_s43Idx (conj_mem_range h.2 j).1]
    congr 1
    group

theorem sigma43_apply (g : Y43) (j : Fin 45) :
    sigma43 g j = s43Idx ((g : PSp43) * s43 j * (g : PSp43)⁻¹) :=
  rfl

theorem s43_mem_Y43 (i : Fin 45) : s43 i ∈ Y43 :=
  Subgroup.subset_closure ⟨i, rfl⟩

theorem sigma43_s43 (i j : Fin 45) :
    sigma43 ⟨s43 i, s43_mem_Y43 i⟩ j = uIdx (tU (uPt i) (uPt j)) := by
  rw [sigma43_apply, s43_inv, s43_tau, s43Idx_s43]

theorem range_sigma43 :
    sigma43.range = Subgroup.closure (Set.range fun i => sigma43 ⟨s43 i, s43_mem_Y43 i⟩) := by
  rw [MonoidHom.range_eq_map, ← Subgroup.closure_closure_coe_preimage (k := Set.range s43),
    MonoidHom.map_closure]
  congr 1
  ext σ
  constructor
  · rintro ⟨y, ⟨i, hi⟩, rfl⟩
    refine ⟨i, ?_⟩
    exact congrArg sigma43 (Subtype.ext hi : (⟨s43 i, s43_mem_Y43 i⟩ : Y43) = y)
  · rintro ⟨i, rfl⟩
    exact ⟨_, ⟨i, rfl⟩, rfl⟩

@[expose] noncomputable def uEquiv45 : Fin 45 ≃ Unitary.DU 4 :=
  Equiv.ofBijective uElt uElt_bijective

@[expose] noncomputable def rho43 : Unitary.U2 4 →* Equiv.Perm (Fin 45) :=
  (Equiv.permCongrHom uEquiv45.symm).toMonoidHom.comp (Pair.conjPerm (pair_DU le_rfl))

theorem rho43_injective : Function.Injective rho43 :=
  (Equiv.permCongrHom uEquiv45.symm).injective.comp
    (Pair.conjPerm_injective (pair_DU le_rfl) (center_U2 le_rfl))

theorem rho43_uElt (i j : Fin 45) : rho43 (uElt i) j = uIdx (tU (uPt i) (uPt j)) := by
  show uEquiv45.symm (Pair.conjPerm (pair_DU le_rfl) (uElt i) (uEquiv45.symm.symm j)) = _
  rw [Equiv.symm_symm, show uEquiv45 j = uElt j from rfl, conjPerm_eq_tau, uElt_tau,
    show uElt (uIdx (tU (uPt i) (uPt j))) = uEquiv45 (uIdx (tU (uPt i) (uPt j))) from rfl,
    Equiv.symm_apply_apply]

theorem range_rho43 : rho43.range = Subgroup.closure (Set.range fun i => rho43 (uElt i)) := by
  rw [MonoidHom.range_eq_map, ← Pair.closure_eq (pair_DU le_rfl), MonoidHom.map_closure]
  congr 1
  ext σ
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨i, hi⟩ := uElt_bijective.2 ⟨x, hx⟩
    exact ⟨i, congrArg (fun u : Unitary.DU 4 => rho43 (u : Unitary.U2 4)) hi⟩
  · rintro ⟨i, rfl⟩
    exact ⟨_, (uElt i).2, rfl⟩

theorem range_sigma43_eq : sigma43.range = rho43.range := by
  rw [range_sigma43, range_rho43]
  congr 2
  ext i : 1
  exact Equiv.ext fun j => by rw [sigma43_s43, rho43_uElt]

theorem center_statedSU_four_two :
    Subgroup.center (StatedSU 4 (2 ^ 1) Blueprint.Fischer.K) =
      (StatedScalars (Fin 4) Blueprint.Fischer.K).subgroupOf
        (StatedSU 4 (2 ^ 1) Blueprint.Fischer.K) :=
  (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card Unitary.card_K (by norm_num)
    (by decide)).2

theorem SUm_four_eq : Unitary.SUm 4 = StatedSU 4 (2 ^ 1) Blueprint.Fischer.K :=
  (Unitary.SUm_eq 4).trans (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU Unitary.card_K 4)

@[expose] noncomputable def u2FourEquiv :
    Unitary.U2 4 ≃* StatedProj (StatedSU 4 (2 ^ 1) Blueprint.Fischer.K) :=
  QuotientGroup.congr _ _ (MulEquiv.subgroupCongr SUm_four_eq) (by
    rw [← center_statedSU_four_two]
    exact Subgroup.map_center_eq _)

theorem card_U2_four : Nat.card (Unitary.U2 4) = 25920 := by
  rw [Nat.card_congr u2FourEquiv.toEquiv]
  exact CFSG.ComponentClassification.UnbalancingLocal.card_psu_four_two Unitary.card_K

theorem card_statedSp_two_three : Nat.card (StatedSp 2 (ZMod 3)) = 51840 :=
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp_two_zmod_three

theorem card_PSp43_le : Nat.card PSp43 ≤ 25920 := by
  set Z := (StatedScalars (Fin 2 ⊕ Fin 2) (ZMod 3)).subgroupOf (StatedSp 2 (ZMod 3))
  have hc : Nat.card PSp43 * Nat.card Z = 51840 := by
    rw [← card_statedSp_two_three]
    exact (Subgroup.card_eq_card_quotient_mul_card_subgroup Z).symm
  have hZ : 2 ≤ Nat.card Z := by
    have hne : Z ≠ ⊥ := by
      intro hbot
      have hmem : (⟨-1, neg_one_mem_statedSp⟩ : StatedSp 2 (ZMod 3)) ∈ Z :=
        Subgroup.mem_subgroupOf.mpr neg_one_mem_statedScalars
      rw [hbot, Subgroup.mem_bot] at hmem
      have := congrArg (fun g : StatedSp 2 (ZMod 3) =>
        ((g : GL (Fin 2 ⊕ Fin 2) (ZMod 3)) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3))
          (.inl 0) (.inl 0)) hmem
      simp at this
      exact absurd this (by decide)
    exact (Subgroup.one_lt_card_iff_ne_bot Z).mpr hne
  have : Nat.card PSp43 * 2 ≤ Nat.card PSp43 * Nat.card Z := Nat.mul_le_mul_left _ hZ
  omega

theorem card_range_sigma43 : Nat.card sigma43.range = 25920 := by
  rw [range_sigma43_eq, ← Nat.card_congr (MonoidHom.ofInjective rho43_injective).toEquiv,
    card_U2_four]

theorem Y43_eq_top : Y43 = ⊤ := by
  apply Subgroup.eq_top_of_card_eq
  refine le_antisymm (Subgroup.card_le_card_group _) ?_
  calc Nat.card PSp43 ≤ 25920 := card_PSp43_le
    _ = Nat.card sigma43.range := card_range_sigma43.symm
    _ ≤ Nat.card Y43 := Nat.card_le_card_of_surjective _ sigma43.rangeRestrict_surjective

theorem sigma43_rangeRestrict_bijective : Function.Bijective sigma43.rangeRestrict := by
  refine sigma43.rangeRestrict_surjective.bijective_of_nat_card_le ?_
  rw [card_range_sigma43, Y43_eq_top, Subgroup.card_top]
  exact card_PSp43_le

@[expose] noncomputable def psp43EquivU2 : PSp43 ≃* Unitary.U2 4 :=
  ((((MulEquiv.subgroupCongr Y43_eq_top).trans Subgroup.topEquiv).symm.trans
    (MulEquiv.ofBijective sigma43.rangeRestrict sigma43_rangeRestrict_bijective)).trans
      (MulEquiv.subgroupCongr range_sigma43_eq)).trans
    (MonoidHom.ofInjective rho43_injective).symm

theorem statedClassicalModel_PSp_two_three_of_PSU_four_two {G : Type} [Group G]
    (h : StatedClassicalModel G .PSU 4 2 1) : StatedClassicalModel G .PSp 2 3 1 := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fintype K := Fintype.ofFinite K
  have : Fintype Blueprint.Fischer.K := Fintype.ofFinite _
  have hc : Fintype.card K = Fintype.card Blueprint.Fischer.K := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, Unitary.card_K]
  let e₁ := CFSG.Fischer.Classification.Recognition.statedProjSUEquiv
    (FiniteField.ringEquivOfCardEq hc) 4 (2 ^ 1)
  exact ⟨⟨Nat.prime_three, le_rfl, by norm_num, by decide⟩, ZMod 3, inferInstance, inferInstance,
    by simp, ⟨(e.trans e₁).trans (u2FourEquiv.symm.trans psp43EquivU2.symm)⟩⟩

theorem lieModel_PSp_two_three_of_lieModel_PSU_four_two {G : Type} [Group G]
    (h : Blueprint.LieModel G .PSU 4 2 1) : Blueprint.LieModel G .PSp 2 3 1 := by
  rcases h with ⟨-, h⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · exact Or.inl ⟨by decide, statedClassicalModel_PSp_two_three_of_PSU_four_two h⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

end CFSG.GH74.Exceptional
