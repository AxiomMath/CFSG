module

public import CFSG.Fischer.Classification.Basic.Heisenberg
public import Mathlib.LinearAlgebra.Eigenspace.Zero
public import Mathlib.Algebra.Module.ZMod
import CFSG.LieType.Steinberg.CentralExt.SUThreeFieldTwo

public section

namespace CFSG.AGLEmbedding

open CFSG.Fischer.Classification
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G] {x y : G}

theorem pow_three_mem_zpowers_of_cubeRel (hR : CubeRel x y) (hxy : x * y ≠ y * x) {t : G}
    (ht : t ^ 3 = 1)
    (htR : ∀ r ∈ Subgroup.closure ({x, y} : Set G),
      t * r * t⁻¹ ∈ Subgroup.closure ({x, y} : Set G))
    {r : G} (hr : r ∈ Subgroup.closure ({x, y} : Set G)) :
    (t * r) ^ 3 ∈ Subgroup.zpowers ⁅x, y⁆ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set R := Subgroup.closure ({x, y} : Set G) with hRdef
  set z := ⁅x, y⁆ with hz
  have hxR : x ∈ R := Subgroup.subset_closure (Set.mem_insert x {y})
  have hyR : y ∈ R := Subgroup.subset_closure (Set.mem_insert_of_mem x rfl)
  have hzR : z ∈ R := by
    rw [hz, commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hxR hyR) (inv_mem hxR)) (inv_mem hyR)
  have hzc : ∀ g ∈ R, Commute z g := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      rcases hg with rfl | rfl
      · exact hR.commute_commutator_left
      · exact hR.commute_commutator_right
    | one => exact Commute.one_right z
    | mul a b _ _ ha hb => exact ha.mul_right hb
    | inv a _ ha => exact ha.inv_right
  set C : Subgroup R := (Subgroup.zpowers z).subgroupOf R with hC
  have hCn : C.Normal := by
    refine ⟨fun c hc g => ?_⟩
    have hcz : (c : G) ∈ Subgroup.zpowers z := hc
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hcz
    have hcom : Commute (c : G) (g : G) := hm ▸ (hzc g g.2).zpow_left m
    have : g * c * g⁻¹ = c := Subtype.ext (by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hcom.symm.eq, mul_inv_cancel_right])
    rw [this]
    exact hc
  have hgen : ∀ q : R ⧸ C, q ∈ Subgroup.closure
      ((QuotientGroup.mk' C) '' (Subtype.val ⁻¹' ({x, y} : Set G))) := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective C q
    rw [← MonoidHom.map_closure, Subgroup.closure_closure_coe_preimage]
    exact ⟨g, Subgroup.mem_top g, rfl⟩
  have hpair : ((QuotientGroup.mk' C) '' (Subtype.val ⁻¹' ({x, y} : Set G))).Pairwise
      Commute := by
    have key : (QuotientGroup.mk' C ⟨x, hxR⟩) * (QuotientGroup.mk' C ⟨y, hyR⟩) =
        (QuotientGroup.mk' C ⟨y, hyR⟩) * (QuotientGroup.mk' C ⟨x, hxR⟩) := by
      rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq, hC, Subgroup.mem_subgroupOf]
      have e : ((((⟨x, hxR⟩ : R) * ⟨y, hyR⟩)⁻¹ * ((⟨y, hyR⟩ : R) * ⟨x, hxR⟩) : R) : G) =
          z⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [hR.mul_comm_eq, hz]
        group
      rw [e]
      exact inv_mem (Subgroup.mem_zpowers z)
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ -
    have ha' : (a : G) = x ∨ (a : G) = y := ha
    have hb' : (b : G) = x ∨ (b : G) = y := hb
    have hax : ∀ {w : R}, (w : G) = x → w = ⟨x, hxR⟩ := fun h => Subtype.ext h
    have hay : ∀ {w : R}, (w : G) = y → w = ⟨y, hyR⟩ := fun h => Subtype.ext h
    rcases ha' with h1 | h1 <;> rcases hb' with h2 | h2
    · rw [hax h1, hax h2]
    · rw [hax h1, hay h2]
      exact key
    · rw [hay h1, hax h2]
      exact key.symm
    · rw [hay h1, hay h2]
  have hQcomm : ∀ a b : R ⧸ C, a * b = b * a := by
    intro a b
    have h := (Subgroup.isMulCommutative_closure hpair).is_comm.comm ⟨a, hgen a⟩ ⟨b, hgen b⟩
    exact congrArg Subtype.val h
  let _ : CommGroup (R ⧸ C) := { (inferInstance : Group (R ⧸ C)) with mul_comm := hQcomm }
  have hQ3 : ∀ q : R ⧸ C, q ^ 3 = 1 := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective C q
    rw [← map_pow]
    have : g ^ 3 = 1 := Subtype.ext (by simpa using hR.pow_three_eq_one g.2)
    rw [this, map_one]
  have hz1 : z ≠ 1 := by
    intro h1
    apply hxy
    have := hR.mul_comm_eq
    have h1' : ⁅x, y⁆ = 1 := h1
    rw [h1', inv_one, mul_one] at this
    exact this.symm
  have hzo : orderOf z = 3 := orderOf_eq_prime hR.commutator_pow_three hz1
  have hCcard : Nat.card C = 3 := by
    rw [hC, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      ((Subgroup.zpowers_le).2 hzR)).toEquiv, Nat.card_zpowers, hzo]
  have hQcard : Nat.card (R ⧸ C) = 9 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup C
    rw [CFSG.LieType.Steinberg.CentralExt.SUThreeFieldTwo.card_closure_eq_of_cubeRel hR hxy,
      hCcard] at h1
    omega
  let φ : R →* R :=
    { toFun := fun g => ⟨t * g * t⁻¹, htR g g.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hφ : ∀ g : R, (φ g : G) = t * g * t⁻¹ := fun g => rfl
  have hφC : C ≤ C.comap φ := by
    intro c hc
    rw [Subgroup.mem_comap, ← QuotientGroup.eq_one_iff (N := C)]
    change QuotientGroup.mk' C (φ c) = 1
    have hcz : (c : G) ∈ Subgroup.zpowers z := hc
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hcz
    have hcm : c = (⟨z, hzR⟩ : R) ^ m := Subtype.ext (by rw [Subgroup.coe_zpow]; exact hm.symm)
    rw [hcm, map_zpow, map_zpow]
    have hφz : φ ⟨z, hzR⟩ = φ ⟨x, hxR⟩ * φ ⟨y, hyR⟩ * (φ ⟨x, hxR⟩)⁻¹ * (φ ⟨y, hyR⟩)⁻¹ := by
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      congr 1
    rw [hφz, map_mul, map_mul, map_mul, map_inv, map_inv, hQcomm (QuotientGroup.mk' C _)
      (QuotientGroup.mk' C (φ ⟨y, hyR⟩))]
    group
  let ψ : R ⧸ C →* R ⧸ C := QuotientGroup.map C C φ hφC
  have hψ : ∀ g : R, ψ (QuotientGroup.mk' C g) = QuotientGroup.mk' C (φ g) := fun g => rfl
  have hψ3 : ∀ q, ψ (ψ (ψ q)) = q := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective C q
    rw [hψ, hψ, hψ]
    congr 1
    refine Subtype.ext ?_
    simp only [hφ]
    have h3 : t * t * t = 1 := by rw [← ht, pow_three, mul_assoc]
    calc t * (t * (t * (g : G) * t⁻¹) * t⁻¹) * t⁻¹ = (t * t * t) * g * (t * t * t)⁻¹ := by
          group
      _ = g := by rw [h3]; group
  have hV3 : ∀ v : Additive (R ⧸ C), (3 : ℕ) • v = 0 := fun v => by
    change Additive.ofMul ((Additive.toMul v) ^ 3) = Additive.ofMul 1
    rw [hQ3]
  let _ : Module (ZMod 3) (Additive (R ⧸ C)) := AddCommGroup.zmodModule hV3
  let f : Additive (R ⧸ C) →ₗ[ZMod 3] Additive (R ⧸ C) :=
    (MonoidHom.toAdditive ψ).toZModLinearMap 3
  have hf : ∀ v, f v = Additive.ofMul (ψ (Additive.toMul v)) := fun v => rfl
  have hf3 : f ^ 3 = 1 := LinearMap.ext fun v => by
    rw [pow_three, Module.End.mul_apply, Module.End.mul_apply, Module.End.one_apply, hf, hf, hf]
    simp only [toMul_ofMul]
    rw [hψ3]
    rfl
  have h3E : (3 : Module.End (ZMod 3) (Additive (R ⧸ C))) = 0 := LinearMap.ext fun v => by
    rw [LinearMap.zero_apply, show (3 : Module.End (ZMod 3) (Additive (R ⧸ C))) =
      (3 : ZMod 3) • 1 by rw [ofNat_smul_eq_nsmul, nsmul_one]; rfl]
    rw [LinearMap.smul_apply, show (3 : ZMod 3) = 0 from rfl, zero_smul]
  have hnil : IsNilpotent (f - 1) := ⟨3, by
    have e : (f - 1) ^ 3 = f ^ 3 - 1 - 3 * (f ^ 2 - f) := by noncomm_ring
    rw [e, hf3, h3E, zero_mul, sub_self, sub_zero]⟩
  have : Fintype (Additive (R ⧸ C)) := Fintype.ofFinite _
  have hfr : Module.finrank (ZMod 3) (Additive (R ⧸ C)) = 2 := by
    have h1 := Module.card_eq_pow_finrank (K := ZMod 3) (V := Additive (R ⧸ C))
    rw [ZMod.card, ← Nat.card_eq_fintype_card, Nat.card_congr Additive.toMul, hQcard,
      show (9 : ℕ) = 3 ^ 2 by norm_num] at h1
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) h1).symm
  have hsq : (f - 1) ^ 2 = 0 := by
    have h := LinearMap.aeval_self_charpoly (f - 1)
    rwa [hnil.charpoly_eq_X_pow_finrank, hfr, map_pow, Polynomial.aeval_X] at h
  have hnorm : f ^ 2 + f + 1 = 0 := by
    have e : f ^ 2 + f + 1 = (f - 1) ^ 2 + 3 * f := by noncomm_ring
    rw [e, hsq, h3E, zero_mul, add_zero]
  set g : R := ⟨r, hr⟩ with hg
  have hq : QuotientGroup.mk' C (φ g * φ (φ g) * g) = 1 := by
    have h := LinearMap.congr_fun hnorm (Additive.ofMul (QuotientGroup.mk' C g))
    rw [LinearMap.add_apply, LinearMap.add_apply, pow_two, Module.End.mul_apply, hf, hf,
      Module.End.one_apply, LinearMap.zero_apply] at h
    simp only [toMul_ofMul] at h
    change ψ (ψ (QuotientGroup.mk' C g)) * ψ (QuotientGroup.mk' C g) *
      QuotientGroup.mk' C g = 1 at h
    rw [map_mul, map_mul, ← hψ, ← hψ, hQcomm (ψ (QuotientGroup.mk' C g))]
    exact h
  have hmem : ((φ g * φ (φ g) * g : R) : G) ∈ Subgroup.zpowers z := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hC, Subgroup.mem_subgroupOf] at hq
    exact hq
  have h2 : t⁻¹ * t⁻¹ = t := by
    have h3 : t * t * t = 1 := by rw [← ht, pow_three, mul_assoc]
    calc t⁻¹ * t⁻¹ = t⁻¹ * t⁻¹ * (t * t * t) := by rw [h3, mul_one]
      _ = t := by group
  have e : ((φ g * φ (φ g) * g : R) : G) = (t * r) ^ 3 := by
    simp only [Subgroup.coe_mul, hφ, hg]
    calc t * r * t⁻¹ * (t * (t * r * t⁻¹) * t⁻¹) * r = t * r * t * r * (t⁻¹ * t⁻¹) * r := by
          group
      _ = (t * r) ^ 3 := by rw [h2, pow_three]; group
  rwa [e] at hmem

end CFSG.AGLEmbedding
