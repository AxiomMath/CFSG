module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Ree
public import CFSG.LieType.Ree.LargeReeInvolutionFusion

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LieType.ChevTwo.Semi CFSG.LieType.Ree.LargeReeInvolution

set_option linter.unusedSectionVars false

open scoped Pointwise

section TitsV2


variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}

theorem rankOne_eq_one_of_commute_centralAOne (hK : Nat.card K = 2 ^ (2 * a + 1))
    {r : ModGL ReeTag.F4.tag K} (hr : r ∈ rankOneGroupOne K a)
    (hodd : Nat.Coprime (orderOf r) 2) (hc : r * centralAOne = centralAOne * r) : r = 1 := by
  have h2 : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  obtain ⟨g, hg⟩ : ∃ g : SL2 K, largeReeA1Hom K a g = r := by
    obtain ⟨g, hg⟩ := (rankOneEquivSL K a hK).surjective ⟨r, hr⟩
    exact ⟨g, congrArg Subtype.val hg⟩
  have hu : (centralAOne : ModGL ReeTag.F4.tag K) = largeReeA1Hom K a (uSL 1) := by
    rw [largeReeA1Hom_uSL (K := K) a (1 : K), one_pow]
  subst hg
  rw [hu, ← map_mul, ← map_mul] at hc
  have hgu : g * uSL 1 = uSL 1 * g := largeReeA1Hom_injective hc
  have hm := congrArg (fun h : SL2 K => (h : Matrix (Fin 2) (Fin 2) K)) hgu
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_uSL] at hm
  have h00 := congrFun (congrFun hm 0) 0
  have h01 := congrFun (congrFun hm 0) 1
  have h10 := congrFun (congrFun hm 1) 0
  have h11 := congrFun (congrFun hm 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
  have hpp : (g : Matrix (Fin 2) (Fin 2) K) 0 0 = (g : Matrix (Fin 2) (Fin 2) K) 1 1 := by
    have h := h01
    rw [add_comm ((g : Matrix (Fin 2) (Fin 2) K) 0 1)] at h
    exact add_right_cancel h
  have hdet := det_SL2 g
  rw [h00, mul_zero, sub_zero, ← hpp] at hdet
  have hg2 : g * g = 1 := by
    refine SL2_ext ?_ ?_ ?_ ?_
    · simp [Matrix.mul_apply, Fin.sum_univ_two, h00, hdet]
    · simp [Matrix.mul_apply, Fin.sum_univ_two, ← hpp, mul_comm, CharTwo.add_self_eq_zero]
    · simp [Matrix.mul_apply, Fin.sum_univ_two, h00]
    · simp [Matrix.mul_apply, Fin.sum_univ_two, h00, ← hpp, hdet]
  have hr2 : (largeReeA1Hom K a g) ^ 2 = 1 := by
    rw [pow_two, ← map_mul, hg2, map_one]
  have hdvd : orderOf (largeReeA1Hom K a g) ∣ 2 := orderOf_dvd_of_pow_eq_one hr2
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hodd hdvd)

theorem centralAOne_mem_rankOneGroupOne (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    (centralAOne : ModGL ReeTag.F4.tag K) ∈ rankOneGroupOne K a := by
  have h : (centralAOne : ModGL ReeTag.F4.tag K) ∈
      (ReeTag.F4.reeFixedOrbitUnipotent K a ⟨0, by decide⟩ : Set (ModGL ReeTag.F4.tag K)) := by
    rw [coe_reeFixedOrbitUnipotent_zero hK]
    exact ⟨1, by simp [centralAOne]⟩
  exact Subgroup.subset_closure (.inl (.inl h))

theorem rankOne_conj_mem_tKernel (hK : Nat.card K = 2 ^ (2 * a + 1)) {g y : ModGL ReeTag.F4.tag K}
    (hg : g ∈ rankOneGroupOne K a) (hy : y ∈ tKernel K a) : g * y * g⁻¹ ∈ tKernel K a :=
  (Subgroup.mem_normalizer_iff.1 (rankOneGroupOne_le_normalizer_tKernel hK hg) y).1 hy

theorem tOne_decomp (hK : Nat.card K = 2 ^ (2 * a + 1)) {x : ↥(ReeTag.F4.reeGamma K a)}
    (hxo : Nat.Coprime (orderOf x) 2)
    (hxt : (x : ModGL ReeTag.F4.tag K) * sylowL a K 1 = sylowL a K 1 * x) :
    ∃ q ∈ tKernel K a, ∃ r ∈ rankOneGroupOne K a,
      q * r = (x : ModGL ReeTag.F4.tag K) ∧ Nat.Coprime (orderOf r) 2 := by
  haveI : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  have hxC : (x : ModGL ReeTag.F4.tag K) ∈ centralizerT K a := by
    rw [← reeGamma_inf_centralizer_tOne_eq hK]
    refine Subgroup.mem_inf.2 ⟨x.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    rw [hg]
    exact hxt.symm
  obtain ⟨q, hq, r, hr, hqr⟩ : ∃ q ∈ tKernel K a, ∃ r ∈ rankOneGroupOne K a,
      q * r = (x : ModGL ReeTag.F4.tag K) := by
    have hset : ((centralizerT K a : Subgroup (ModGL ReeTag.F4.tag K)) :
        Set (ModGL ReeTag.F4.tag K)) =
        (tKernel K a : Set (ModGL ReeTag.F4.tag K)) *
          (rankOneGroupOne K a : Set (ModGL ReeTag.F4.tag K)) :=
      Subgroup.coe_mul_of_right_le_normalizer_left _ _ (rankOneGroupOne_le_normalizer_tKernel hK)
    have h : (x : ModGL ReeTag.F4.tag K) ∈ ((centralizerT K a : Subgroup (ModGL ReeTag.F4.tag K)) :
        Set (ModGL ReeTag.F4.tag K)) := hxC
    rw [hset] at h
    obtain ⟨q, hq, r, hr, e⟩ := h
    exact ⟨q, hq, r, hr, e⟩
  have hbotK := tKernel_inf_rankOneGroupOne (K := K) (a := a) hK
  have hpow : ∀ n : ℕ, ∃ q' ∈ tKernel K a,
      (x : ModGL ReeTag.F4.tag K) ^ n = q' * r ^ n := by
    intro n
    induction n with
    | zero => exact ⟨1, one_mem _, by simp⟩
    | succ n ih =>
      obtain ⟨q', hq', e⟩ := ih
      refine ⟨q * (r * q' * r⁻¹), mul_mem hq (rankOne_conj_mem_tKernel hK hr hq'), ?_⟩
      rw [pow_succ', e, ← hqr, pow_succ']
      group
  have hrm : r ^ orderOf (x : ModGL ReeTag.F4.tag K) = 1 := by
    obtain ⟨q', hq', e⟩ := hpow (orderOf (x : ModGL ReeTag.F4.tag K))
    rw [pow_orderOf_eq_one] at e
    have h1 : r ^ orderOf (x : ModGL ReeTag.F4.tag K) = q'⁻¹ :=
      eq_inv_of_mul_eq_one_right e.symm
    have hb : r ^ orderOf (x : ModGL ReeTag.F4.tag K) ∈ tKernel K a ⊓ rankOneGroupOne K a :=
      Subgroup.mem_inf.2 ⟨h1 ▸ inv_mem hq', pow_mem hr _⟩
    rw [hbotK, Subgroup.mem_bot] at hb
    exact hb
  refine ⟨q, hq, r, hr, hqr, ?_⟩
  refine Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hrm) ?_
  rwa [Subgroup.orderOf_coe]

theorem reeLIOddAt_one (hK : Nat.card K = 2 ^ (2 * a + 1)) : ReeLIOddAt K a ⟨1, by decide⟩ := by
  haveI : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  intro x hxo hx
  have hV : sylowL a K 1 ∈ ReeTag.F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩ :=
    (blocks_mem hK 0 0 0 0 0 0 1).2.2.2.2.2.2.2
  have hΓt : sylowL a K 1 ∈ ReeTag.F4.reeGamma K a := (Subgroup.mem_inf.1 hV).2
  have hQJt : (⟨sylowL a K 1, hΓt⟩ : ↥(ReeTag.F4.reeGamma K a)) ∈
      reeQJ ReeTag.F4 K a (some ⟨1, by decide⟩) := by
    rw [reeQJ_some]
    exact Subgroup.mem_subgroupOf.2 hV
  have hxt : (x : ModGL ReeTag.F4.tag K) * sylowL a K 1 = sylowL a K 1 * x := by
    have h1 := congrArg (fun y : ↥(ReeTag.F4.reeGamma K a) => (y : ModGL ReeTag.F4.tag K))
      (hx _ hQJt)
    simp only [Subgroup.coe_mul] at h1
    exact h1
  obtain ⟨q, hq, r, hr, hqr, hrodd⟩ := tOne_decomp hK hxo hxt
  have hbotK := tKernel_inf_rankOneGroupOne (K := K) (a := a) hK
  have hA := centralAOne_mem_rankOneGroupOne (K := K) (a := a) hK
  have hAV : (centralAOne : ModGL ReeTag.F4.tag K) ∈
      ReeTag.F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩ := centralAOne_mem_complement hK
  have hAΓ : (centralAOne : ModGL ReeTag.F4.tag K) ∈ ReeTag.F4.reeGamma K a :=
    (Subgroup.mem_inf.1 hAV).2
  have hAQJ : (⟨centralAOne, hAΓ⟩ : ↥(ReeTag.F4.reeGamma K a)) ∈
      reeQJ ReeTag.F4 K a (some ⟨1, by decide⟩) := by
    rw [reeQJ_some]
    exact Subgroup.mem_subgroupOf.2 hAV
  have hxu : (x : ModGL ReeTag.F4.tag K) * (centralAOne : ModGL ReeTag.F4.tag K) =
      (centralAOne : ModGL ReeTag.F4.tag K) * (x : ModGL ReeTag.F4.tag K) := by
    have h1 := congrArg (fun y : ↥(ReeTag.F4.reeGamma K a) => (y : ModGL ReeTag.F4.tag K))
      (hx _ hAQJ)
    simp only [Subgroup.coe_mul] at h1
    exact h1
  have hcomm : r * centralAOne = centralAOne * r := by
    have h1 : q * r * centralAOne = centralAOne * (q * r) := by rw [hqr]; exact hxu
    have e : r * centralAOne * r⁻¹ * centralAOne⁻¹ = q⁻¹ * (centralAOne * q * centralAOne⁻¹) := by
      calc r * centralAOne * r⁻¹ * centralAOne⁻¹
          = q⁻¹ * (q * r * centralAOne) * r⁻¹ * centralAOne⁻¹ := by group
        _ = q⁻¹ * (centralAOne * (q * r)) * r⁻¹ * centralAOne⁻¹ := by rw [h1]
        _ = q⁻¹ * (centralAOne * q * centralAOne⁻¹) := by group
    have hc2 : r * centralAOne * r⁻¹ * centralAOne⁻¹ ∈ tKernel K a := by
      rw [e]
      exact mul_mem (inv_mem hq) (rankOne_conj_mem_tKernel hK hA hq)
    have hc1 : r * centralAOne * r⁻¹ * centralAOne⁻¹ ∈ rankOneGroupOne K a :=
      mul_mem (mul_mem (mul_mem hr hA) (inv_mem hr)) (inv_mem hA)
    have hb : r * centralAOne * r⁻¹ * centralAOne⁻¹ ∈ tKernel K a ⊓ rankOneGroupOne K a :=
      Subgroup.mem_inf.2 ⟨hc2, hc1⟩
    rw [hbotK, Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hb
    exact hb
  have hr1 : r = 1 := rankOne_eq_one_of_commute_centralAOne hK hr hrodd hcomm
  rw [hr1, mul_one] at hqr
  have hqV : (x : ModGL ReeTag.F4.tag K) ∈
      ReeTag.F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩ := by
    rw [← hqr]
    exact (Subgroup.mem_inf.1 hq).1
  have hxQJ : x ∈ reeQJ ReeTag.F4 K a (some ⟨0, by decide⟩) := by
    rw [reeQJ_some]
    exact Subgroup.mem_subgroupOf.2 hqV
  exact eq_one_of_mem_pGroup_of_coprime (q := 2) (ree_QJ_pgroup (t := ReeTag.F4) _) hxQJ hxo

end TitsV2

end CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ
