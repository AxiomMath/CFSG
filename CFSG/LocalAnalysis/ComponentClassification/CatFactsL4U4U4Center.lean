module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4U4Core
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4U4Cover
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4L4Center

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.LinearGroups

theorem orderOf_mk_eq_two {Y : Type*} [Group Y] {Z : Subgroup Y} [Z.Normal] {ℓ : Y}
    (hℓ : ℓ ∉ Z) (hℓ2 : ℓ ^ 2 ∈ Z) : orderOf (QuotientGroup.mk ℓ : Y ⧸ Z) = 2 := by
  apply orderOf_eq_prime
  · rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hℓ2
  · rw [Ne, QuotientGroup.eq_one_iff]
    exact hℓ

theorem orderOf_mk_eq_of_isPGroup {Y : Type*} [Group Y] {Z : Subgroup Y} [Z.Normal]
    (hZ2 : IsPGroup 2 Z) {y : Y} {s : ℕ} (hs : s.Prime) (hs2 : s ≠ 2) (hy : orderOf y = s) :
    orderOf (QuotientGroup.mk y : Y ⧸ Z) = s := by
  have := Fact.mk hs
  apply orderOf_eq_prime
  · rw [← QuotientGroup.mk_pow, ← hy, pow_orderOf_eq_one, QuotientGroup.mk_one]
  · rw [Ne, QuotientGroup.eq_one_iff]
    exact not_mem_of_isPGroup_two hZ2 hs hs2 hy

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
include h

theorem orderOf_toProjU_of_mk {Y : Type} [Group Y] {Z : Subgroup Y} [Z.Normal]
    (e : Y ⧸ Z ≃* StatedProj (StatedSU 4 (p ^ f) K)) {u : Y}
    {A : ClassicalGroups.UnitaryFlag.unitarySU p f K 4}
    (hA : (QuotientGroup.mk A : StatedProj (StatedSU 4 (p ^ f) K)) = e (QuotientGroup.mk u)) :
    orderOf (toProjU h 4 A) = orderOf (QuotientGroup.mk u : Y ⧸ Z) := by
  rw [show toProjU h 4 A = projSUToProjU h 4 (by norm_num) (QuotientGroup.mk A) from rfl,
    orderOf_injective _ (projSUToProjU_injective h 4 (by norm_num)), hA, MulEquiv.orderOf_eq]

theorem card_mod_four_of_inner_U4 {Y : Type} [Group Y] (hZ2 : IsPGroup 2 (Subgroup.center Y))
    (hp2 : p ≠ 2) (e : Y ⧸ Subgroup.center Y ≃* StatedProj (StatedSU 4 (p ^ f) K)) {ℓ y : Y}
    (hℓ : ℓ ∉ Subgroup.center Y) (hℓ2 : ℓ ^ 2 ∈ Subgroup.center Y) {s : ℕ} (hs : s.Prime)
    (hs2 : s ≠ 2) (hsq : s ∣ (p ^ f) ^ 2 + 1) (hy : orderOf y = s) (hyℓ : y * ℓ = ℓ * y) :
    p ^ f % 4 = 1 := by
  obtain ⟨A, hA⟩ := QuotientGroup.mk_surjective (e (QuotientGroup.mk ℓ))
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (e (QuotientGroup.mk y))
  have hcomm : toProjU h 4 g * toProjU h 4 A = toProjU h 4 A * toProjU h 4 g := by
    rw [show toProjU h 4 g = projSUToProjU h 4 (by norm_num) (QuotientGroup.mk g) from rfl,
      show toProjU h 4 A = projSUToProjU h 4 (by norm_num) (QuotientGroup.mk A) from rfl,
      ← map_mul, ← map_mul, hA, hg, ← map_mul, ← map_mul, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul, hyℓ]
  obtain ⟨-, -, -, -, -, hq, -⟩ := unitary_four_core h hp2 A g
    (by rw [orderOf_toProjU_of_mk h e hA, orderOf_mk_eq_two hℓ hℓ2]) hs hs2 hsq
    (by rw [orderOf_toProjU_of_mk h e hg, orderOf_mk_eq_of_isPGroup hZ2 hs hs2 hy]) hcomm
  exact hq

theorem neg_one_mem_statedSU_four : (-1 : GL (Fin 4) K) ∈ StatedSU 4 (p ^ f) K := by
  change (-1 : GL (Fin 4) K) ∈ ClassicalGroups.UnitaryFlag.unitarySU p f K 4
  rw [ClassicalGroups.UnitaryFlag.mem_unitarySU_iff h]
  refine ⟨?_, ?_⟩
  · rw [Units.val_neg, Units.val_one, Matrix.det_neg, Matrix.det_one, Fintype.card_fin]
    norm_num
  · rw [Units.val_neg, Units.val_one]
    ext i j
    simp [Matrix.map_apply, Matrix.neg_apply, Matrix.one_apply, Matrix.transpose_apply, eq_comm]

theorem center_eq_bot_of_inner_U4 {Y : Type} [Group Y] [Finite Y] [Group.IsPerfect Y]
    (hZ2 : IsPGroup 2 (Subgroup.center Y)) (hp2 : p ≠ 2)
    (e : Y ⧸ Subgroup.center Y ≃* StatedProj (StatedSU 4 (p ^ f) K))
    {ℓ : Y} (hℓ : ℓ ∉ Subgroup.center Y) (hℓ2 : ℓ ^ 2 ∈ Subgroup.center Y)
    {J : Subgroup Y} (hJ : J ≤ Subgroup.centralizer {ℓ}) (hJp : ⁅J, J⁆ = J)
    (hJc : (p ^ f) ^ 2 * ((p ^ f) ^ 4 - 1) ≤ 2 * Nat.card J)
    {s : ℕ} (hs : s.Prime) (hs2 : s ≠ 2) (hsq : s ∣ (p ^ f) ^ 2 + 1) (hsJ : s ∣ Nat.card J)
    (hnc : ∀ x ∈ J, (∀ w ∈ J, x * w = w * x) → x * x = 1 → x = 1) :
    Subgroup.center Y = ⊥ := by
  classical
  have := Fact.mk hs
  have : Finite K := h.finite
  let : Fintype K := Fintype.ofFinite K
  obtain ⟨y', hy'⟩ := exists_prime_orderOf_dvd_card' (G := J) s hsJ
  set y : Y := (y' : Y) with hydef
  have hy : orderOf y = s := by rw [hydef, Subgroup.orderOf_coe, hy']
  have hyℓ : y * ℓ = ℓ * y := Subgroup.mem_centralizer_singleton_iff.mp (hJ y'.2)
  have hq1 := card_mod_four_of_inner_U4 h hZ2 hp2 e hℓ hℓ2 hs hs2 hsq hy hyℓ
  by_contra hZ
  obtain ⟨ψ, hψ⟩ := exists_equiv_statedSU_four hZ2 hZ h hp2 hq1 e
  have hcomm : toProjU h 4 (ψ y) * toProjU h 4 (ψ ℓ) = toProjU h 4 (ψ ℓ) * toProjU h 4 (ψ y) := by
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, hyℓ]
  set Asq := toSesq h 4 (ψ ℓ) with hAsq
  obtain ⟨l, -, -, -, -, -, hdP, -, eC, heC⟩ := unitary_four_core h hp2 (ψ ℓ) (ψ y)
    (by rw [orderOf_toProjU_of_mk h e (hψ ℓ).symm, orderOf_mk_eq_two hℓ hℓ2]) hs hs2 hsq
    (by rw [orderOf_toProjU_of_mk h e (hψ y).symm, orderOf_mk_eq_of_isPGroup hZ2 hs hs2 hy])
    hcomm
  set φ : Y →* sesqUnitaryGroup (stdHermForm h 4) := (toSesq h 4).comp ψ.toMonoidHom with hφ
  have hφinj : Function.Injective φ := (toSesq_injective h 4).comp ψ.injective
  have hJC : J.map φ ≤ Subgroup.centralizer {Asq} := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    change φ x * φ ℓ = φ ℓ * φ x
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp (hJ hx)]
  set J₁ := (J.map φ).subgroupOf (Subgroup.centralizer {Asq}) with hJ₁
  have hJ₁p : ⁅J₁, J₁⁆ = J₁ := by
    apply Subgroup.map_injective (Subgroup.centralizer {Asq}).subtype_injective
    rw [Subgroup.map_commutator, hJ₁, Subgroup.map_subgroupOf_eq_of_le hJC,
      ← Subgroup.map_commutator, hJp]
  have hJ₁c : Nat.card J₁ = Nat.card J := by
    rw [hJ₁, ← Subgroup.card_map_of_injective (Subgroup.centralizer {Asq}).subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hJC, Subgroup.card_map_of_injective hφinj]
  let b := Module.finBasisOfFinrankEq K (eigenPlus l (unitaryOp Asq)) hdP
  set τ : LinearMap.GeneralLinearGroup K (eigenPlus l (unitaryOp Asq)) ≃* GL (Fin 2) K :=
    Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toMulEquiv with hτ
  set ρ : Subgroup.centralizer {Asq} →* GL (Fin 2) K :=
    τ.toMonoidHom.comp eC.toMonoidHom with hρ
  have hρinj : Function.Injective ρ := τ.injective.comp eC.injective
  set J₂ := J₁.map ρ with hJ₂
  set D := (GeneralLinearGroup.det : GL (Fin 2) K →* Kˣ).ker with hD
  have hJ₂D : J₂ ≤ D := by
    have hp : ⁅J₂, J₂⁆ = J₂ := by rw [hJ₂, ← Subgroup.map_commutator, hJ₁p]
    rw [← hp, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  have hJ₂card : Nat.card J₂ = Nat.card J₁ := Subgroup.card_map_of_injective hρinj
  have hcardK : Fintype.card K = (p ^ f) ^ 2 := by
    rw [Fintype.card_eq_nat_card, h.card, ← pow_mul, mul_comm]
  have hDcard : Nat.card D = (p ^ f) ^ 2 * ((p ^ f) ^ 4 - 1) := by
    rw [hD, card_ker_det_two, hcardK, ← pow_mul (p ^ f) 2 2]
  have hidx : (J₂.subgroupOf D).index ≤ 2 := by
    have h1 := Subgroup.card_mul_index (J₂.subgroupOf D)
    have h2 : Nat.card (J₂.subgroupOf D) = Nat.card J₂ := by
      rw [← Subgroup.card_map_of_injective D.subtype_injective, Subgroup.subgroupOf_map_subtype,
        inf_of_le_left hJ₂D]
    rw [h2, hJ₂card, hJ₁c, hDcard] at h1
    have hpos : 0 < Nat.card J := Nat.card_pos
    by_contra hlt
    have : 3 * Nat.card J ≤ Nat.card J * (J₂.subgroupOf D).index := by
      rw [mul_comm 3]
      exact Nat.mul_le_mul_left _ (by omega)
    omega
  let u : GL (Fin 2) K :=
    ⟨!![0, 1; -1, 0], !![0, -1; 1, 0],
      by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
      by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩
  have huD : u ∈ D := by
    rw [hD, MonoidHom.mem_ker]
    apply Units.ext
    simp [u, GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  have hu2 : u ^ 2 = -1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, pow_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [u, Matrix.mul_apply, Fin.sum_univ_two]
  have hneg : (-1 : GL (Fin 2) K) ∈ J₂ := by
    have h1 := sq_mem_of_index_le_two hidx ⟨u, huD⟩
    rw [Subgroup.mem_subgroupOf] at h1
    rw [← hu2]
    exact h1
  set m : StatedSU 4 (p ^ f) K := ⟨-1, neg_one_mem_statedSU_four h⟩ with hm
  have hmc : ∀ X : StatedSU 4 (p ^ f) K, m * X = X * m := by
    intro X
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hm, neg_one_mul, mul_neg_one]
  have hmC : toSesq h 4 m ∈ Subgroup.centralizer {Asq} := by
    rw [Subgroup.mem_centralizer_singleton_iff, hAsq, ← map_mul, ← map_mul, hmc]
  have heC1 : ((eC ⟨toSesq h 4 m, hmC⟩ : LinearMap.GeneralLinearGroup K
      (eigenPlus l (unitaryOp Asq))) : Module.End K (eigenPlus l (unitaryOp Asq))) = -1 := by
    refine LinearMap.ext fun v => Subtype.ext ?_
    have h1 := congrArg (fun F => F v) (heC ⟨toSesq h 4 m, hmC⟩)
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h1
    rw [h1, LinearMap.neg_apply, Module.End.one_apply, Submodule.coe_neg]
    show (((toSesq h 4 m : sesqUnitaryGroup (stdHermForm h 4)) :
      LinearMap.GeneralLinearGroup K (Fin 4 → K)) : (Fin 4 → K) →ₗ[K] Fin 4 → K)
        (v : Fin 4 → K) = _
    rw [toSesq_apply, hm, Units.val_neg, Units.val_one, Matrix.neg_mulVec, Matrix.one_mulVec]
  have hρm : ρ ⟨toSesq h 4 m, hmC⟩ = -1 := by
    apply Units.ext
    rw [hρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom, hτ,
      Units.coe_mapEquiv, Units.val_neg, Units.val_one]
    change (LinearMap.toMatrixAlgEquiv b) ((eC ⟨toSesq h 4 m, hmC⟩ :
      LinearMap.GeneralLinearGroup K (eigenPlus l (unitaryOp Asq))) :
        Module.End K (eigenPlus l (unitaryOp Asq))) = -1
    have h2 : (LinearMap.toMatrixAlgEquiv b)
        (-1 : Module.End K (eigenPlus l (unitaryOp Asq))) = -1 :=
      (map_neg (LinearMap.toMatrixAlgEquiv b) 1).trans (by rw [map_one])
    rw [heC1]
    exact h2
  rw [← hρm] at hneg
  have hmem := (Subgroup.mem_map_iff_mem hρinj).1 hneg
  rw [hJ₁, Subgroup.mem_subgroupOf] at hmem
  obtain ⟨x, hx, hxe⟩ := hmem
  have hψx : ψ x = m := toSesq_injective h 4 hxe
  apply hZ
  exfalso
  have h2K : (2 : K) ≠ 0 := two_ne_zero_of_odd h hp2
  have hx1 : x ≠ 1 := by
    intro h1
    rw [h1, map_one] at hψx
    have h2 := congrArg (fun X : StatedSU 4 (p ^ f) K =>
      ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 0 0) hψx
    simp only [hm, OneMemClass.coe_one, Units.val_one, Units.val_neg, Matrix.one_apply_eq,
      Matrix.neg_apply] at h2
    apply h2K
    linear_combination h2
  apply hx1
  refine hnc x hx (fun w _ => ψ.injective ?_) (ψ.injective ?_)
  · rw [map_mul, map_mul, hψx, hmc]
  · rw [map_mul, hψx, map_one]
    apply Subtype.ext
    rw [Subgroup.coe_mul, hm, neg_one_mul, neg_neg]
    rfl

end CFSG.ComponentClassification.CatFactsL4U4
