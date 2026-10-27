module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8G2LeviCent

public section

namespace CFSG.ComponentClassification.RankTwoExceptional

open Subgroup CFSG.Blueprint.Chevalley CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.LieType.Chevalley (WeylGroup canonicalRep coxeterSystem simple torusGroup borelGroup)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

section SL2Inv

open Matrix Projectivization
open scoped LinearAlgebra.Projectivization

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_units_sq_eq (b : Kˣ) : ∃ μ : Kˣ, μ ^ 2 = b := by
  have hq1 : 1 < Nat.card K := Finite.one_lt_card
  obtain ⟨k, hk⟩ := odd_card_sub_one (K := K)
  have h2q : 2 ∣ Nat.card K := ⟨k + 1, by omega⟩
  refine ⟨b ^ (Nat.card K / 2), ?_⟩
  rw [← pow_mul, Nat.div_mul_cancel h2q]
  have h1 : b ^ (Nat.card K - 1) = 1 := by
    rw [← Nat.card_units]
    exact pow_card_eq_one'
  calc b ^ Nat.card K = b ^ (Nat.card K - 1 + 1) := by rw [Nat.sub_add_cancel hq1.le]
    _ = b := by rw [pow_succ, h1, one_mul]

omit [Finite K] [CharP K 2] in
theorem HSL_mul_uSL (μ : Kˣ) (b : K) :
    LieType.Chevalley.HSL μ * LieType.Chevalley.uSL b =
      LieType.Chevalley.uSL ((μ : K) ^ 2 * b) * LieType.Chevalley.HSL μ := by
  refine LieType.Chevalley.SL2_ext ?_ ?_ ?_ ?_ <;>
    simp [LieType.Chevalley.coe_uSL, LieType.Chevalley.coe_HSL, Matrix.mul_apply,
      Fin.sum_univ_two]
  field_simp

theorem exists_conj_eq_uSL_one {g : LieType.Chevalley.SL2 K} (hg2 : g * g = 1) (hg1 : g ≠ 1) :
    ∃ h : LieType.Chevalley.SL2 K, h * g * h⁻¹ = LieType.Chevalley.uSL 1 := by
  have e := congrArg (fun x : LieType.Chevalley.SL2 K => (x : Matrix (Fin 2) (Fin 2) K)) hg2
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at e
  have e00 := congrFun (congrFun e 0) 0
  have e01 := congrFun (congrFun e 0) 1
  have e10 := congrFun (congrFun e 1) 0
  have e11 := congrFun (congrFun e 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  have hdet := LieType.Chevalley.det_SL2 g
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have htr : (g : Matrix (Fin 2) (Fin 2) K) 0 0 + (g : Matrix (Fin 2) (Fin 2) K) 1 1 = 0 := by
    by_contra hτ
    have hb : (g : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by
      have : (g : Matrix (Fin 2) (Fin 2) K) 0 1 * ((g : Matrix (Fin 2) (Fin 2) K) 0 0 +
          (g : Matrix (Fin 2) (Fin 2) K) 1 1) = 0 := by linear_combination e01
      exact (mul_eq_zero.1 this).resolve_right hτ
    have ha : (g : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by
      have : ((g : Matrix (Fin 2) (Fin 2) K) 0 0 - 1) * ((g : Matrix (Fin 2) (Fin 2) K) 0 0 - 1) =
          0 := by linear_combination e00 - (g : Matrix (Fin 2) (Fin 2) K) 1 0 * hb -
            ((g : Matrix (Fin 2) (Fin 2) K) 0 0 - 1) * h2
      exact sub_eq_zero.1 (mul_self_eq_zero.1 this)
    have hd : (g : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by
      have : ((g : Matrix (Fin 2) (Fin 2) K) 1 1 - 1) * ((g : Matrix (Fin 2) (Fin 2) K) 1 1 - 1) =
          0 := by linear_combination e11 - (g : Matrix (Fin 2) (Fin 2) K) 1 0 * hb -
            ((g : Matrix (Fin 2) (Fin 2) K) 1 1 - 1) * h2
      exact sub_eq_zero.1 (mul_self_eq_zero.1 this)
    exact hτ (by rw [ha, hd]; exact h2.symm ▸ (one_add_one_eq_two))
  have hM : ((g : Matrix (Fin 2) (Fin 2) K) - 1).det = 0 := by
    rw [Matrix.det_fin_two]
    simp only [Matrix.sub_apply, Matrix.one_apply_eq,
      Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
      Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), sub_zero]
    linear_combination hdet - htr + h2
  obtain ⟨v, hv, hMv⟩ := CFSG.LinearGroups.exists_mulVec_eq_zero_of_det_eq_zero hM
  have hgv : (g : Matrix (Fin 2) (Fin 2) K) *ᵥ v = v := by
    rw [sub_mulVec, one_mulVec, sub_eq_zero] at hMv
    exact hMv
  have hP : g • mk K v hv = mk K v hv := by
    rw [smul_mk]
    exact (mk_eq_mk_iff' K _ _ _ _).2 ⟨1, by rw [one_smul]; exact hgv.symm⟩
  obtain ⟨g₀, hg₀⟩ := exists_smul_mk_e0 (mk K v hv)
  set g' := g₀⁻¹ * g * g₀ with hg'
  have hfix : g' • mk K ![(1 : K), 0] (by simp) = mk K ![(1 : K), 0] (by simp) := by
    rw [hg', mul_smul, mul_smul, hg₀, hP, ← hg₀, inv_smul_smul]
  have h10 := apply_one_zero_eq_zero_of_smul hfix
  have hg'2 : g' * g' = 1 := by
    rw [hg', show g₀⁻¹ * g * g₀ * (g₀⁻¹ * g * g₀) = g₀⁻¹ * (g * g) * g₀ by group, hg2]
    group
  have e' := congrArg (fun x : LieType.Chevalley.SL2 K => (x : Matrix (Fin 2) (Fin 2) K)) hg'2
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at e'
  have f00 := congrFun (congrFun e' 0) 0
  have f11 := congrFun (congrFun e' 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, h10] at f00 f11
  have ha : (g' : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by
    have : ((g' : Matrix (Fin 2) (Fin 2) K) 0 0 - 1) * ((g' : Matrix (Fin 2) (Fin 2) K) 0 0 - 1) =
        0 := by linear_combination f00 - ((g' : Matrix (Fin 2) (Fin 2) K) 0 0 - 1) * h2
    exact sub_eq_zero.1 (mul_self_eq_zero.1 this)
  have hd : (g' : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by
    have : ((g' : Matrix (Fin 2) (Fin 2) K) 1 1 - 1) * ((g' : Matrix (Fin 2) (Fin 2) K) 1 1 - 1) =
        0 := by linear_combination f11 - ((g' : Matrix (Fin 2) (Fin 2) K) 1 1 - 1) * h2
    exact sub_eq_zero.1 (mul_self_eq_zero.1 this)
  set b := (g' : Matrix (Fin 2) (Fin 2) K) 0 1 with hb
  have hgu : g' = LieType.Chevalley.uSL b :=
    LieType.Chevalley.SL2_ext (by simp [LieType.Chevalley.coe_uSL, ha])
      (by simp [LieType.Chevalley.coe_uSL, hb]) (by simp [LieType.Chevalley.coe_uSL, h10])
      (by simp [LieType.Chevalley.coe_uSL, hd])
  have hb0 : b ≠ 0 := by
    intro h0
    apply hg1
    have : g' = 1 := by
      rw [hgu, h0]
      exact LieType.Chevalley.SL2_ext (by simp [LieType.Chevalley.coe_uSL])
        (by simp [LieType.Chevalley.coe_uSL]) (by simp [LieType.Chevalley.coe_uSL])
        (by simp [LieType.Chevalley.coe_uSL])
    rw [hg'] at this
    calc g = g₀ * (g₀⁻¹ * g * g₀) * g₀⁻¹ := by group
      _ = 1 := by rw [this, mul_one, mul_inv_cancel]
  obtain ⟨μ, hμ⟩ := exists_units_sq_eq (Units.mk0 b hb0)⁻¹
  refine ⟨LieType.Chevalley.HSL μ * g₀⁻¹, ?_⟩
  have e1 : LieType.Chevalley.HSL μ * g₀⁻¹ * g * (LieType.Chevalley.HSL μ * g₀⁻¹)⁻¹ =
      LieType.Chevalley.HSL μ * g' * (LieType.Chevalley.HSL μ)⁻¹ := by rw [hg']; group
  rw [e1, hgu, HSL_mul_uSL, mul_inv_cancel_right]
  congr 1
  have hμ' : (μ : K) ^ 2 = b⁻¹ := by
    have := congrArg Units.val hμ
    simpa using this
  rw [hμ', inv_mul_cancel₀ hb0]

end SL2Inv

section LongC

variable {K : Type} [Field K] [CharP K 2]

theorem g2LongC_eq_map
    : g2LongC K = (g2RankOne K g2ia).map
    (MulAut.conj (weylElt .G2 K g2ia 1 * weylElt .G2 K g2ir 1)).toMonoidHom := by
  apply le_antisymm
  · refine (closure_le _).2 ?_
    rintro _ (⟨x, rfl⟩ | ⟨x, rfl⟩)
    · refine ⟨pinnedX .G2 K g2a x, ?_, ?_⟩
      · rw [g2RankOne_a_eq]
        exact subset_closure (Or.inl ⟨x, rfl⟩)
      · show weylElt .G2 K g2ia 1 * weylElt .G2 K g2ir 1 * pinnedX .G2 K g2a x *
          (weylElt .G2 K g2ia 1 * weylElt .G2 K g2ir 1)⁻¹ = pinnedX .G2 K g2c x
        rw [show weylElt .G2 K g2ia 1 * weylElt .G2 K g2ir 1 * pinnedX .G2 K g2a x *
          (weylElt .G2 K g2ia 1 * weylElt .G2 K g2ir 1)⁻¹ = weylElt .G2 K g2ia 1 *
            (weylElt .G2 K g2ir 1 * pinnedX .G2 K g2a x * (weylElt .G2 K g2ir 1)⁻¹) *
              (weylElt .G2 K g2ia 1)⁻¹ by group, weylElt_r_conj_a, weylElt_a_conj_b]
    · refine ⟨pinnedX .G2 K (-g2a) x, ?_, ?_⟩
      · rw [g2RankOne_a_eq, ← g2na_eq_neg]
        exact subset_closure (Or.inr ⟨x, rfl⟩)
      · show weylElt .G2 K g2ia 1 * weylElt .G2 K g2ir 1 * pinnedX .G2 K (-g2a) x *
          (weylElt .G2 K g2ia 1 * weylElt .G2 K g2ir 1)⁻¹ = pinnedX .G2 K (-g2c) x
        rw [show weylElt .G2 K g2ia 1 * weylElt .G2 K g2ir 1 * pinnedX .G2 K (-g2a) x *
          (weylElt .G2 K g2ia 1 * weylElt .G2 K g2ir 1)⁻¹ = weylElt .G2 K g2ia 1 *
            (weylElt .G2 K g2ir 1 * pinnedX .G2 K (-g2a) x * (weylElt .G2 K g2ir 1)⁻¹) *
              (weylElt .G2 K g2ia 1)⁻¹ by group, weylElt_r_conj_na, weylElt_a_conj_nb]
  · rintro _ ⟨y, hy, rfl⟩
    exact weylElt_ar_conj_mem_g2LongC hy

theorem exists_sl2_g2LongC
    : ∃ ρ : LieType.Chevalley.SL2 K →* ModGL .G2 K,
    Function.Injective ρ ∧ ρ.range = g2LongC K ∧
      ρ (LieType.Chevalley.uSL 1) = pinnedX .G2 K g2c 1 := by
  obtain ⟨ρ, hu, -, -, -, hrange, hinj, -⟩ := g2_rank_one (K := K) g2ia
  refine ⟨(MulAut.conj (weylElt .G2 K g2ia 1 * weylElt .G2 K g2ir 1)).toMonoidHom.comp ρ,
    (MulAut.conj _).injective.comp hinj, ?_, ?_⟩
  · rw [MonoidHom.range_comp, hrange, g2LongC_eq_map]
  · show weylElt .G2 K g2ia 1 * weylElt .G2 K g2ir 1 * ρ (LieType.Chevalley.uSL 1) *
      (weylElt .G2 K g2ia 1 * weylElt .G2 K g2ir 1)⁻¹ = pinnedX .G2 K g2c 1
    rw [hu, xUnit_g2ia, show weylElt .G2 K g2ia 1 * weylElt .G2 K g2ir 1 * pinnedX .G2 K g2a 1 *
      (weylElt .G2 K g2ia 1 * weylElt .G2 K g2ir 1)⁻¹ = weylElt .G2 K g2ia 1 *
        (weylElt .G2 K g2ir 1 * pinnedX .G2 K g2a 1 * (weylElt .G2 K g2ir 1)⁻¹) *
          (weylElt .G2 K g2ia 1)⁻¹ by group, weylElt_r_conj_a, weylElt_a_conj_b]

omit [CharP K 2] in
theorem g2LongC_le_adjointGroup
    : g2LongC K ≤ adjointGroup .G2 K :=
  g2LongC_le_g2LongA2.trans g2LongA2_le_adjointGroup

theorem g2LongC_commutator
    [Finite K] (hK4 : 4 ≤ Nat.card K) :
    ⁅g2LongC K, g2LongC K⁆ = g2LongC K := by
  rw [g2LongC_eq_map, ← map_commutator, g2RankOne_commutator hK4]

omit [CharP K 2] in
theorem g2LongC_le_centralizer :
    g2LongC K ≤ centralizer (g2TorusR K : Set (ModGL .G2 K)) := by
  refine (closure_le _).2 ?_
  rintro _ (⟨x, rfl⟩ | ⟨x, rfl⟩) <;> refine mem_centralizer_iff.2 ?_ <;> rintro _ ⟨t, rfl⟩
  · show torusElt .G2 K g2ir t * pinnedX .G2 K g2c x = pinnedX .G2 K g2c x * torusElt .G2 K g2ir t
    rw [← mul_inv_eq_iff_eq_mul, torus_r_c]
  · show torusElt .G2 K g2ir t * pinnedX .G2 K (-g2c) x =
      pinnedX .G2 K (-g2c) x * torusElt .G2 K g2ir t
    rw [← mul_inv_eq_iff_eq_mul, root_torus_conjugation g2ir
      (LieType.Chevalley.IsRoot.neg isRoot_g2c) t x,
      show ∑ j, Tag.G2.cartan g2ir j * (-g2c) j = 0 by decide, zpow_zero, Units.val_one, one_mul]

theorem center_g2LongC
    : center ↥(g2LongC K) = ⊥ := by
  obtain ⟨ρ, hinj, hrange, -⟩ := exists_sl2_g2LongC (K := K)
  let e : LieType.Chevalley.SL2 K ≃* ↥(g2LongC K) :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  rw [eq_bot_iff]
  intro z hz
  have hz' : e.symm z ∈ center (LieType.Chevalley.SL2 K) := mem_center_iff.2 fun y => by
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact mem_center_iff.1 hz (e y)
  rw [CFSG.Walter.sl2_center_eq_bot_of_charTwo, mem_bot] at hz'
  rw [mem_bot, ← e.apply_symm_apply z, hz', map_one]

variable [Finite K]

theorem statedClassicalModel_g2LongC
    {m : ℕ} (hK : Nat.card K = 2 ^ m) (hm : 2 ≤ m) :
    StatedClassicalModel (RankTwoStandard.rankTwoQuot (g2LongC K)) .PSL 2 2 m := by
  obtain ⟨ρ, hinj, hrange, -⟩ := exists_sl2_g2LongC (K := K)
  let e : LieType.Chevalley.SL2 K ≃* ↥(g2LongC K) :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  let e₁ : RankTwoStandard.rankTwoQuot (g2LongC K) ≃* ↥(g2LongC K) :=
    (QuotientGroup.quotientMulEquivOfEq center_g2LongC).trans QuotientGroup.quotientBot
  let e₂ : ↥(g2LongC K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
    e.symm.trans (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := K)).symm
  have h4 : 4 ≤ 2 ^ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  refine ⟨⟨Nat.prime_two, by omega, le_rfl, ?_, ?_⟩, K, inferInstance, inferInstance, hK,
    ⟨(e₁.trans e₂).trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K)⟩⟩
  · intro h
    simp only [Prod.mk.injEq, true_and] at h
    omega
  · intro h
    simp only [Prod.mk.injEq, true_and] at h
    omega

theorem odd_card_g2Centralizer_sup_g2LongC
    (hK8 : 8 ≤ Nat.card K) :
    Odd (Nat.card (g2Centralizer K ((g2TorusR K ⊔ g2LongC K : Subgroup (ModGL .G2 K)) :
      Set (ModGL .G2 K)))) := by
  have hle : g2Centralizer K ((g2TorusR K ⊔ g2LongC K : Subgroup (ModGL .G2 K)) :
      Set (ModGL .G2 K)) ≤ g2TorusR K := by
    intro x hx
    obtain ⟨hxC, hxc⟩ := mem_inf.1 hx
    have hx' : x ∈ g2Centralizer K (g2TorusR K : Set (ModGL .G2 K)) :=
      mem_inf.2 ⟨hxC, centralizer_le (SetLike.coe_subset_coe.2 le_sup_left) hxc⟩
    obtain ⟨h, hh, hl⟩ := exists_mem_g2TorusR_mul_g2LongC hK8 hx'
    have hlZ : (⟨h⁻¹ * x, hl⟩ : ↥(g2LongC K)) ∈ center ↥(g2LongC K) := by
      refine mem_center_iff.2 fun y => Subtype.ext ?_
      have hxy : (y : ModGL .G2 K) * x = x * y :=
        mem_centralizer_iff.1 hxc y (mem_sup_right y.2)
      have hhy : (y : ModGL .G2 K) * h = h * y :=
        (mem_centralizer_iff.1 (g2LongC_le_centralizer y.2) h hh).symm
      show (y : ModGL .G2 K) * (h⁻¹ * x) = h⁻¹ * x * y
      calc (y : ModGL .G2 K) * (h⁻¹ * x) = h⁻¹ * (h * y * h⁻¹) * x := by group
        _ = h⁻¹ * (y * x) := by rw [← hhy, mul_inv_cancel_right, mul_assoc]
        _ = h⁻¹ * x * y := by rw [hxy, mul_assoc]
    rw [center_g2LongC, mem_bot] at hlZ
    have h1 : h⁻¹ * x = 1 := congrArg Subtype.val hlZ
    rw [show x = h * (h⁻¹ * x) by group, h1, mul_one]
    exact hh
  obtain ⟨k, hk⟩ := card_dvd_of_le hle
  rw [card_g2TorusR] at hk
  exact Nat.Odd.of_mul_left (hk ▸ odd_card_sub_one)

theorem exists_conj_eq_pinnedX_c_of_mem_g2LongC
    {x : ModGL .G2 K}
    (hx : x ∈ g2LongC K) (hx2 : x ^ 2 = 1) (hx1 : x ≠ 1) :
    ∃ h ∈ adjointGroup .G2 K, h * x * h⁻¹ = pinnedX .G2 K g2c 1 := by
  obtain ⟨ρ, hinj, hrange, hu⟩ := exists_sl2_g2LongC (K := K)
  have hx' : x ∈ ρ.range := by rw [hrange]; exact hx
  obtain ⟨g, rfl⟩ := hx'
  have hg2 : g * g = 1 := hinj (by rw [map_mul, ← sq, hx2, map_one])
  have hg1 : g ≠ 1 := fun h => hx1 (by rw [h, map_one])
  obtain ⟨h, hh⟩ := exists_conj_eq_uSL_one hg2 hg1
  refine ⟨ρ h, g2LongC_le_adjointGroup (by rw [← hrange]; exact ⟨h, rfl⟩), ?_⟩
  rw [← map_inv, ← map_mul, ← map_mul, hh, hu]

theorem g2Levi187_of_three_le
    {m : ℕ} (hK : Nat.card K = 2 ^ m) (hm : 3 ≤ m) :
    ∃ L : Subgroup (ModGL .G2 K), L ≤ adjointGroup .G2 K ∧ rootSubgroup .G2 K g2c ≤ L ∧
      ⁅L, L⁆ = L ∧ L ≤ centralizer (g2TorusR K : Set (ModGL .G2 K)) ∧
      (∀ x ∈ g2Centralizer K (g2TorusR K : Set (ModGL .G2 K)), ∃ h ∈ g2TorusR K,
        h⁻¹ * x ∈ L) ∧
      Odd (Nat.card (center ↥L)) ∧
      (if m = 2 then StatedClassicalModel (RankTwoStandard.rankTwoQuot L) .PSL 3 2 2
        else StatedClassicalModel (RankTwoStandard.rankTwoQuot L) .PSL 2 2 m) ∧
      Odd (Nat.card (g2Centralizer K ((g2TorusR K ⊔ L : Subgroup (ModGL .G2 K)) :
        Set (ModGL .G2 K)))) ∧
      (∀ x ∈ L, x ^ 2 = 1 → x ≠ 1 →
        ∃ h ∈ adjointGroup .G2 K, h * x * h⁻¹ = pinnedX .G2 K g2c 1) ∧
      (m = 2 → (center ↥L).map L.subtype = g2TorusR K) := by
  have h8 : 8 ≤ Nat.card K := by
    rw [hK]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  refine ⟨g2LongC K, g2LongC_le_adjointGroup, (closure_le _).2 fun _ ⟨x, hx⟩ => hx ▸
    pinnedX_c_mem_g2LongC x, g2LongC_commutator (by omega), g2LongC_le_centralizer,
    fun x hx => exists_mem_g2TorusR_mul_g2LongC h8 hx, ?_, ?_,
    odd_card_g2Centralizer_sup_g2LongC h8,
    fun x hx hx2 hx1 => exists_conj_eq_pinnedX_c_of_mem_g2LongC hx hx2 hx1, fun h => by omega⟩
  · rw [center_g2LongC, card_bot]
    exact odd_one
  · have hm2 : ¬ m = 2 := by omega
    simp only [hm2, ↓reduceIte]
    exact statedClassicalModel_g2LongC hK (by omega)

end LongC

end CFSG.ComponentClassification.RankTwoExceptional
