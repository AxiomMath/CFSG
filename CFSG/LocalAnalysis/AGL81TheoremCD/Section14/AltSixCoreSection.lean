module

public import Mathlib.Algebra.Module.ZMod
public import Mathlib.FieldTheory.Finite.GaloisField

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.A6Core

open Subgroup

open scoped commutatorElement

universe u

variable {K : Type u} [Group K] [Finite K]

private theorem normal_subgroupOf_of_commutator {A B : Subgroup K} (hBA : B ≤ A)
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, ⁅x, y⁆ ∈ B) :
    (B.subgroupOf A).Normal := by
  rw [Subgroup.normal_subgroupOf_iff hBA]
  intro h k hh hk
  have hk' : k * h * k⁻¹ = ⁅k, h⁆ * h := by group
  rw [hk']
  exact B.mul_mem (hcomm k hk h (hBA hh)) hh

private theorem quotient_mul_comm {A B : Subgroup K} (hBA : B ≤ A)
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, ⁅x, y⁆ ∈ B) [hN : (B.subgroupOf A).Normal] :
    ∀ q₁ q₂ : ↥A ⧸ B.subgroupOf A, q₁ * q₂ = q₂ * q₁ := by
  intro q₁ q₂
  induction q₁ using QuotientGroup.induction_on with
  | H x =>
    induction q₂ using QuotientGroup.induction_on with
    | H y =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
      change ((x : K) * y)⁻¹ * ((y : K) * x) ∈ B
      have hm : ((x : K) * y)⁻¹ * ((y : K) * x) = ⁅(y : K)⁻¹, (x : K)⁻¹⁆ := by
        group
      rw [hm]
      exact hcomm ((y : K)⁻¹) (A.inv_mem y.2) ((x : K)⁻¹) (A.inv_mem x.2)

@[instance_reducible]
private def quotientCommGroup {A B : Subgroup K} (hBA : B ≤ A)
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, ⁅x, y⁆ ∈ B) [hN : (B.subgroupOf A).Normal] :
    CommGroup (↥A ⧸ B.subgroupOf A) :=
  { (inferInstance : Group (↥A ⧸ B.subgroupOf A)) with
    mul_comm := quotient_mul_comm hBA hcomm }

private noncomputable def conjOnSubgroup {A Y : Subgroup K}
    (hYA : Y ≤ normalizer (A : Set K)) : ↥Y →* MulAut ↥A :=
  (Subgroup.normalizerMonoidHom A).comp (Subgroup.inclusion hYA)

private theorem conjOnSubgroup_apply {A Y : Subgroup K}
    (hYA : Y ≤ normalizer (A : Set K)) (y : ↥Y) (x : ↥A) :
    ((conjOnSubgroup hYA y) x : ↥A) =
      ⟨(y : K) * x * (y : K)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hYA y.2) (x : K)).mp x.2⟩ := rfl

private theorem conjOnSubgroup_symm_apply {A Y : Subgroup K}
    (hYA : Y ≤ normalizer (A : Set K)) (y : ↥Y) (x : ↥A) :
    (((conjOnSubgroup hYA y).symm x : ↥A)) =
      ⟨(y : K)⁻¹ * x * (y : K),
        by
          simpa only [inv_inv] using
            (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hYA y.2)) (x : K)).mp x.2⟩ := by
  rw [← MulAut.inv_apply, ← map_inv, conjOnSubgroup_apply]
  simp

private theorem map_conjOnSubgroup {A B Y : Subgroup K}
    (hYA : Y ≤ normalizer (A : Set K)) (hYB : Y ≤ normalizer (B : Set K)) (y : ↥Y) :
    (B.subgroupOf A).map (conjOnSubgroup hYA y : ↥A →* ↥A) = B.subgroupOf A := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz' : (z : K) ∈ B := Subgroup.mem_subgroupOf.mp hz
    have hval : (((conjOnSubgroup hYA y) z : ↥A) : K) =
        (y : K) * (z : K) * (y : K)⁻¹ := by
      rw [conjOnSubgroup_apply]
    rw [Subgroup.mem_subgroupOf]
    change (((conjOnSubgroup hYA y) z : ↥A) : K) ∈ B
    rw [hval]
    exact (Subgroup.mem_normalizer_iff.mp (hYB y.2) (z : K)).mp hz'
  · intro hx
    refine ⟨(conjOnSubgroup hYA y).symm x, ?_, by simp⟩
    have hx' : (↑((conjOnSubgroup hYA y).symm x) : K) ∈ B := by
      rw [conjOnSubgroup_symm_apply]
      simpa only [inv_inv] using
        (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hYB y.2)) (x : K)).mp
          (Subgroup.mem_subgroupOf.mp hx)
    exact hx'

private noncomputable def actionQ {A B Y : Subgroup K}
    (hYA : Y ≤ normalizer (A : Set K)) (hYB : Y ≤ normalizer (B : Set K))
    [hN : (B.subgroupOf A).Normal] :
    ↥Y →* MulAut (↥A ⧸ B.subgroupOf A) where
  toFun y := QuotientGroup.congr (B.subgroupOf A) (B.subgroupOf A)
    (conjOnSubgroup hYA y) (map_conjOnSubgroup hYA hYB y)
  map_one' := by
    ext v
    induction v using QuotientGroup.induction_on with
    | H x =>
      rw [QuotientGroup.congr_mk, MulAut.one_apply]
      congr 1
      exact Subtype.ext (by rw [conjOnSubgroup_apply]; simp)
  map_mul' y z := by
    ext v
    induction v using QuotientGroup.induction_on with
    | H x =>
      rw [MulAut.mul_apply, QuotientGroup.congr_mk, QuotientGroup.congr_mk, QuotientGroup.congr_mk]
      congr 1
      exact Subtype.ext (by
        simp only [conjOnSubgroup_apply, Subgroup.coe_mk, Subgroup.coe_mul, Subgroup.coe_inv]
        group)

private theorem actionQ_mk {A B Y : Subgroup K}
    (hYA : Y ≤ normalizer (A : Set K)) (hYB : Y ≤ normalizer (B : Set K))
    [hN : (B.subgroupOf A).Normal] (y : ↥Y) (x : ↥A) :
    actionQ hYA hYB y (x : ↥A ⧸ B.subgroupOf A) =
      ((⟨(y : K) * x * (y : K)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hYA y.2) (x : K)).mp x.2⟩ : ↥A) :
        ↥A ⧸ B.subgroupOf A) :=
  rfl

private noncomputable def mulAutToAddAut {Q : Type*} [Group Q] :
    MulAut Q →* Multiplicative (AddAut (Additive Q)) where
  toFun σ := Multiplicative.ofAdd ((AddAutAdditive Q).symm (Additive.ofMul σ))
  map_one' := by rfl
  map_mul' σ τ := by rfl

private noncomputable def addAutToLinearEquiv {Q : Type*} [CommGroup Q] {r : ℕ}
    [Module (ZMod r) (Additive Q)] :
    Multiplicative (AddAut (Additive Q)) →* (Additive Q ≃ₗ[ZMod r] Additive Q) where
  toFun e := (Multiplicative.toAdd e).toLinearEquiv (fun c x => ZMod.map_smul _ c x)
  map_one' := rfl
  map_mul' e₁ e₂ := rfl

private theorem quotient_smul_eq_zero {A B : Subgroup K} {r : ℕ}
    (hexp : ∀ x ∈ A, x ^ r ∈ B) [hN : (B.subgroupOf A).Normal] :
    ∀ v : Additive (↥A ⧸ B.subgroupOf A), r • v = 0 := by
  intro v
  apply (Additive.toMul (α := ↥A ⧸ B.subgroupOf A)).injective
  rw [toMul_nsmul]
  change Additive.toMul v ^ r = 1
  induction Additive.toMul v using QuotientGroup.induction_on with
  | H x =>
    rw [← QuotientGroup.mk_pow]
    change ((x ^ r : ↥A) : ↥A ⧸ B.subgroupOf A) = 1
    rw [QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr (by simpa using hexp (x : K) x.2)

private theorem finrank_quotient_le_four {A B : Subgroup K} {r : ℕ} [Fact r.Prime]
    (hBA : B ≤ A) (hcard : Nat.card A ≤ r ^ 4 * Nat.card B)
    [hN : (B.subgroupOf A).Normal] [hC : CommGroup (↥A ⧸ B.subgroupOf A)]
    [hM : Module (ZMod r) (Additive (↥A ⧸ B.subgroupOf A))] :
    Module.finrank (ZMod r) (Additive (↥A ⧸ B.subgroupOf A)) ≤ 4 := by
  have hcardV : Nat.card (Additive (↥A ⧸ B.subgroupOf A)) =
      r ^ Module.finrank (ZMod r) (Additive (↥A ⧸ B.subgroupOf A)) :=
    (FiniteField.pow_finrank_eq_natCard r (Additive (↥A ⧸ B.subgroupOf A))).symm
  have hBcard : Nat.card ↥(B.subgroupOf A) = Nat.card ↥B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBA).toEquiv
  have hA : Nat.card ↥A = Nat.card (↥A ⧸ B.subgroupOf A) * Nat.card ↥B := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (B.subgroupOf A), hBcard]
  have hBpos : 0 < Nat.card ↥B := by
    haveI : Nonempty ↥B := ⟨⟨1, B.one_mem⟩⟩
    haveI : Finite ↥B := Subtype.finite
    exact Nat.card_pos
  have hQle : Nat.card (↥A ⧸ B.subgroupOf A) ≤ r ^ 4 := by
    refine Nat.le_of_mul_le_mul_right (c := Nat.card ↥B) ?_ hBpos
    calc Nat.card (↥A ⧸ B.subgroupOf A) * Nat.card ↥B = Nat.card ↥A := hA.symm
      _ ≤ r ^ 4 * Nat.card B := hcard
  have hpow : r ^ Module.finrank (ZMod r) (Additive (↥A ⧸ B.subgroupOf A)) ≤ r ^ 4 := by
    calc r ^ Module.finrank (ZMod r) (Additive (↥A ⧸ B.subgroupOf A))
        = Nat.card (Additive (↥A ⧸ B.subgroupOf A)) := hcardV.symm
      _ = Nat.card (↥A ⧸ B.subgroupOf A) := Nat.card_congr Additive.toMul
      _ ≤ r ^ 4 := hQle
  exact (Nat.pow_le_pow_iff_right (Fact.out : r.Prime).one_lt).mp hpow

private theorem commutator_mem_of_action_eq_one {A B Y : Subgroup K} {r : ℕ}
    (hYA : Y ≤ normalizer (A : Set K)) (hYB : Y ≤ normalizer (B : Set K))
    [hN : (B.subgroupOf A).Normal] [hC : CommGroup (↥A ⧸ B.subgroupOf A)]
    [hM : Module (ZMod r) (Additive (↥A ⧸ B.subgroupOf A))]
    (ρ : ↥Y →* (Additive (↥A ⧸ B.subgroupOf A) ≃ₗ[ZMod r]
      Additive (↥A ⧸ B.subgroupOf A)))
    (hρ_apply : ∀ (y : ↥Y) (q : ↥A ⧸ B.subgroupOf A),
      (ρ y) (Additive.ofMul q) = Additive.ofMul (actionQ hYA hYB y q))
    {y : ↥Y} (hy : ρ y = 1) {x : K} (hx : x ∈ A) :
    ⁅x, (y : K)⁆ ∈ B := by
  have hv := DFunLike.congr_fun hy
    (Additive.ofMul (((⟨x, hx⟩ : ↥A) : ↥A ⧸ B.subgroupOf A)))
  rw [hρ_apply] at hv
  have hq : actionQ hYA hYB y (((⟨x, hx⟩ : ↥A) : ↥A ⧸ B.subgroupOf A)) =
      ((⟨x, hx⟩ : ↥A) : ↥A ⧸ B.subgroupOf A) := by
    simpa using hv
  have hq' : (((⟨(y : K) * x * (y : K)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hYA y.2) (x : K)).mp hx⟩ : ↥A) :
        ↥A ⧸ B.subgroupOf A) =
      ((⟨x, hx⟩ : ↥A) : ↥A ⧸ B.subgroupOf A)) := by
    rw [← actionQ_mk hYA hYB y ⟨x, hx⟩]
    exact hq
  have hdiv : ((⟨(y : K) * x * (y : K)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hYA y.2) (x : K)).mp hx⟩ : ↥A) /
      ⟨x, hx⟩ : ↥A) ∈ B.subgroupOf A :=
    QuotientGroup.eq_iff_div_mem.mp hq'
  have hcommy : ⁅(y : K), x⁆ ∈ B := by
    have h := Subgroup.mem_subgroupOf.mp hdiv
    simpa [div_eq_mul_inv, commutatorElement_def] using h
  simpa only [commutatorElement_inv] using B.inv_mem hcommy

theorem exists_linearAction_of_section {r : ℕ} [Fact r.Prime] {Y A B : Subgroup K}
    (hBA : B ≤ A) (hYA : Y ≤ normalizer (A : Set K))
    (hYB : Y ≤ normalizer (B : Set K)) (hexp : ∀ x ∈ A, x ^ r ∈ B)
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, ⁅x, y⁆ ∈ B)
    (hcard : Nat.card A ≤ r ^ 4 * Nat.card B) :
    ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module (ZMod r) V)
      (_ : FiniteDimensional (ZMod r) V) (ρ : ↥Y →* (V ≃ₗ[ZMod r] V)),
      Module.finrank (ZMod r) V ≤ 4 ∧
        ∀ y : ↥Y, ρ y = 1 → ∀ x ∈ A, ⁅x, (y : K)⁆ ∈ B := by
  letI hB'N : (B.subgroupOf A).Normal := normal_subgroupOf_of_commutator hBA hcomm
  letI hComm : CommGroup (↥A ⧸ B.subgroupOf A) := quotientCommGroup hBA hcomm
  letI hAddC : AddCommGroup (Additive (↥A ⧸ B.subgroupOf A)) := Additive.addCommGroup
  have hzero := quotient_smul_eq_zero hexp
  letI hM : Module (ZMod r) (Additive (↥A ⧸ B.subgroupOf A)) :=
    @AddCommGroup.zmodModule r (Additive (↥A ⧸ B.subgroupOf A))
      Additive.addCommGroup hzero
  letI hFin : FiniteDimensional (ZMod r) (Additive (↥A ⧸ B.subgroupOf A)) :=
    Module.Finite.of_finite
  let ρ : ↥Y →* (Additive (↥A ⧸ B.subgroupOf A) ≃ₗ[ZMod r]
      Additive (↥A ⧸ B.subgroupOf A)) :=
    (addAutToLinearEquiv (Q := ↥A ⧸ B.subgroupOf A) (r := r)).comp
      ((mulAutToAddAut (Q := ↥A ⧸ B.subgroupOf A)).comp (actionQ hYA hYB))
  have hρ_apply : ∀ (y : ↥Y) (q : ↥A ⧸ B.subgroupOf A),
      (ρ y) (Additive.ofMul q) = Additive.ofMul (actionQ hYA hYB y q) := by
    intro y q
    rfl
  refine ⟨Additive (↥A ⧸ B.subgroupOf A), Additive.addCommGroup, hM, hFin, ρ, ?_, ?_⟩
  · exact finrank_quotient_le_four hBA hcard
  · intro y hy x hx
    exact commutator_mem_of_action_eq_one hYA hYB ρ hρ_apply hy hx

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.A6Core
