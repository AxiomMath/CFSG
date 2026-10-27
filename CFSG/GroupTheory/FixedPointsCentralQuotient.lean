module

public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.GroupTheory.PCore.SubgroupCore
public import CFSG.GroupTheory.PCore.FixedSubgroupCore

public section

namespace CFSG

open CFSG.Open
open CFSG.HardMathSupport.Solomon.Coordinator

variable {K Q : Type*} [Group K] [Group Q]

noncomputable def fixSubgroupCocycle (π : K →* Q) (hker : π.ker ≤ Subgroup.center K)
    (α : MulAut K) (β : MulAut Q) (hαβ : ∀ k, π (α k) = β (π k)) :
    ↥((fixSubgroup β).comap π) →* ↥π.ker where
  toFun k :=
    ⟨(k : K)⁻¹ * α (k : K), by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hαβ]
      rw [show β (π (k : K)) = π (k : K) from k.2, inv_mul_cancel]⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' k l := by
    obtain ⟨z, hz, hαk⟩ := alpha_eq_mul_central π hker α β hαβ k.2
    have hzk : (k : K)⁻¹ * α (k : K) = z := by rw [hαk]; group
    have hc : ∀ x : K, x * ((k : K)⁻¹ * α (k : K)) = ((k : K)⁻¹ * α (k : K)) * x := by
      intro x
      rw [hzk]
      exact Subgroup.mem_center_iff.1 hz x
    have h1 : (l : K)⁻¹ * ((k : K)⁻¹ * α (k : K)) * (l : K) = (k : K)⁻¹ * α (k : K) := by
      calc (l : K)⁻¹ * ((k : K)⁻¹ * α (k : K)) * (l : K)
          = (l : K)⁻¹ * (((k : K)⁻¹ * α (k : K)) * (l : K)) := by rw [mul_assoc]
        _ = (l : K)⁻¹ * ((l : K) * ((k : K)⁻¹ * α (k : K))) := by rw [← hc (l : K)]
        _ = (k : K)⁻¹ * α (k : K) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
    apply Subtype.ext
    show ((k : K) * (l : K))⁻¹ * α ((k : K) * (l : K)) =
      ((k : K)⁻¹ * α (k : K)) * ((l : K)⁻¹ * α (l : K))
    conv_lhs => rw [map_mul, mul_inv_rev,
      show α (k : K) = (k : K) * ((k : K)⁻¹ * α (k : K)) from by group,
      show α (l : K) = (l : K) * ((l : K)⁻¹ * α (l : K)) from by group]
    conv_lhs => rw [show (l : K)⁻¹ * (k : K)⁻¹ *
        (((k : K) * ((k : K)⁻¹ * α (k : K))) * ((l : K) * ((l : K)⁻¹ * α (l : K)))) =
      (l : K)⁻¹ * ((k : K)⁻¹ * α (k : K)) * (l : K) * ((l : K)⁻¹ * α (l : K)) from by group, h1]

theorem fixSubgroupCocycle_ker (π : K →* Q) (hker : π.ker ≤ Subgroup.center K)
    (α : MulAut K) (β : MulAut Q) (hαβ : ∀ k, π (α k) = β (π k)) :
    (fixSubgroupCocycle π hker α β hαβ).ker =
      (fixSubgroup α).subgroupOf ((fixSubgroup β).comap π) := by
  ext k
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_fixSubgroup, ← mem_fixSubgroup (α := α)]
  constructor
  · intro h
    have h' := congrArg (fun z : ↥π.ker => (z : K)) h
    simp only [fixSubgroupCocycle, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_one,
      Subtype.coe_mk] at h'
    calc α (k : K) = (k : K) * ((k : K)⁻¹ * α (k : K)) := by group
      _ = (k : K) * 1 := by rw [h']
      _ = (k : K) := mul_one _
  · intro h
    rw [mem_fixSubgroup] at h
    apply Subtype.ext
    simp only [fixSubgroupCocycle, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_one,
      Subtype.coe_mk]
    rw [h, inv_mul_cancel]

theorem relIndex_fixSubgroup_comap_dvd_card_ker (π : K →* Q)
    (hker : π.ker ≤ Subgroup.center K) (α : MulAut K) (β : MulAut Q)
    (hαβ : ∀ k, π (α k) = β (π k)) :
    (fixSubgroup α).relIndex ((fixSubgroup β).comap π) ∣ Nat.card π.ker := by
  have hidx : (fixSubgroup α).relIndex ((fixSubgroup β).comap π) =
      Nat.card (fixSubgroupCocycle π hker α β hαβ).range := by
    rw [Subgroup.relIndex, ← fixSubgroupCocycle_ker π hker α β hαβ, Subgroup.index_ker]
  rw [hidx]
  calc Nat.card (fixSubgroupCocycle π hker α β hαβ).range
      ∣ Nat.card ↥(⊤ : Subgroup ↥π.ker) := Subgroup.card_dvd_of_le le_top
    _ = Nat.card π.ker := Subgroup.card_top

theorem pPrimeCore_eq_bot_of_fixSubgroup [Finite K] [Finite Q] {p : ℕ} (hp : p.Prime)
    (π : K →* Q) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center K)
    (hpker : IsPGroup p π.ker) (α : MulAut K) (β : MulAut Q)
    (hαβ : ∀ k, π (α k) = β (π k))
    (hK : pPrimeCore p ↥(fixSubgroup α) = ⊥) : pPrimeCore p ↥(fixSubgroup β) = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  set B : Subgroup K := (fixSubgroup β).comap π with hB
  set A : Subgroup K := fixSubgroup α with hA
  have hAB : A ≤ B := fun a ha =>
    map_fixSubgroup_le π hker α β hαβ (Subgroup.mem_map_of_mem π ha)
  have hkerB : π.ker ≤ B := fun z hz => by
    show π z ∈ fixSubgroup β
    rw [MonoidHom.mem_ker.1 hz]
    exact (fixSubgroup β).one_mem
  have hAn : (A.subgroupOf B).Normal := by
    rw [← fixSubgroupCocycle_ker π hker α β hαβ]
    infer_instance
  have hdvd : A.relIndex B ∣ Nat.card π.ker := relIndex_fixSubgroup_comap_dvd_card_ker π hker α β hαβ
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hpker
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 (hn ▸ hdvd :
    A.relIndex B ∣ p ^ n)
  have hBbot : GLAPPrimeCoreOf p B = ⊥ :=
    gLAPPrimeCoreOf_eq_bot_of_relIndex_eq_pow hp hAB hAn hj
      (gLAPPrimeCoreOf_eq_bot_iff_pPrimeCore.mpr hK)
  have hBcore : pPrimeCore p ↥B = ⊥ := gLAPPrimeCoreOf_eq_bot_iff_pPrimeCore.mp hBbot
  let f : ↥B →* ↥(fixSubgroup β) := (π.domRestrict B).codRestrict _ fun k => k.2
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨k, hk⟩ := hπ (y : Q)
    refine ⟨⟨k, ?_⟩, Subtype.ext hk⟩
    show π k ∈ fixSubgroup β
    rw [hk]
    exact y.2
  have hfker : f.ker = (π.ker).subgroupOf B := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    exact ⟨fun h => Subtype.ext_iff.1 h, fun h => Subtype.ext h⟩
  have hcentral : f.ker ≤ Subgroup.center ↥B := by
    intro x hx
    rw [hfker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_center_iff.1 (hker hx) (y : K)
  have hcard : Nat.card ↥f.ker = Nat.card π.ker := by
    rw [hfker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerB).toEquiv
  have hpker' : IsPGroup p f.ker := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hpker
    exact IsPGroup.iff_card.2 ⟨m, hcard.trans hm⟩
  have hD := central_p_kernel_prime_core_image f hf hcentral hpker'
  rw [hD, hBcore, Subgroup.map_bot]

end CFSG
