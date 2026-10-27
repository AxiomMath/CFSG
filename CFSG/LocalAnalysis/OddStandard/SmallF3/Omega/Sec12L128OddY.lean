module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L128OddM
public import CFSG.LocalAnalysis.ComponentClassification.OddCore
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.GroupTheory.PCore.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem sec128_tau_inverts_oddCore {Y : Type} [Group Y] [Finite Y] (tau : Y)
    (h2 : orderOf tau = 2)
    (hK : Nonempty (↥(centralizer ({tau} : Set Y)) ≃*
      (Multiplicative (ZMod 2) × ↥(alternatingGroup (Fin 5))))) :
    ∀ o ∈ oddCore Y, tau * o * tau⁻¹ = o⁻¹ := by
  obtain ⟨e⟩ := hK
  have htau2 : tau * tau = 1 := by
    have hpow := pow_orderOf_eq_one tau
    rw [h2] at hpow
    simpa [pow_two] using hpow
  have htau_inv : tau⁻¹ = tau := by
    rw [inv_eq_iff_mul_eq_one]
    exact htau2
  let O : Subgroup Y := oddCore Y
  let K : Subgroup Y := centralizer ({tau} : Set Y)
  let N : Subgroup ↥K := O.subgroupOf K
  have hOodd : Odd (Nat.card O) := CFSG.ComponentClassification.OddCore.odd_card Y
  have hNcard : Nat.card N = Nat.card (O ⊓ K : Subgroup Y) := by
    change Nat.card (O.subgroupOf K) = Nat.card (O ⊓ K : Subgroup Y)
    rw [← inf_subgroupOf_right O K]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hNodd : Odd (Nat.card N) := by
    rw [hNcard]
    exact hOodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  haveI : (N.map e.toMonoidHom).Normal :=
    (inferInstance : N.Normal).map e.toMonoidHom e.surjective
  have hmapbot : N.map e.toMonoidHom = ⊥ :=
    sec128_model_oddNormal_bot (N.map e.toMonoidHom) (by
      rw [Subgroup.card_map_of_injective e.injective]
      exact hNodd)
  have hNbot : N = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    have hx' : e x ∈ N.map e.toMonoidHom := Subgroup.mem_map_of_mem e.toMonoidHom hx
    rw [hmapbot] at hx'
    exact Subgroup.mem_bot.mpr (e.injective (by rw [Subgroup.mem_bot.mp hx', map_one]))
  have hfix : ∀ o ∈ O, tau * o * tau⁻¹ = o → o = 1 := by
    intro o ho hconjo
    have hcomm : tau * o = o * tau := by
      have hthis := congrArg (fun z => z * tau) hconjo
      have hL : (tau * o * tau⁻¹) * tau = tau * o := by
        rw [htau_inv, mul_assoc (tau * o) tau tau, htau2, mul_one]
      rw [hL] at hthis
      exact hthis
    have hoK : o ∈ K := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact hcomm
    have hoN : (⟨o, hoK⟩ : ↥K) ∈ N := ho
    rw [hNbot] at hoN
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hoN)
  let φ : MulAut Y := MulAut.conj tau
  have hφ_apply : ∀ x : Y, φ x = tau * x * tau⁻¹ := fun x => MulAut.conj_apply tau x
  have hφφ : φ * φ = 1 := by
    change MulAut.conj tau * MulAut.conj tau = 1
    rw [← map_mul (MulAut.conj : Y →* MulAut Y) tau tau, htau2]
    exact map_one _
  have hφφa : ∀ x : Y, φ (φ x) = x := by
    intro x
    rw [← MulAut.mul_apply, hφφ, MulAut.one_apply]
  have hconj : ∀ x : Y, φ (x⁻¹ * φ x) = (x⁻¹ * φ x)⁻¹ := by
    intro x
    rw [map_mul, map_inv, hφφa x, mul_inv_rev, inv_inv]
  let f : ↥O → ↥O := fun a => ⟨(a : Y)⁻¹ * φ (a : Y), by
    refine O.mul_mem (O.inv_mem a.2) ?_
    rw [hφ_apply]
    exact (inferInstance : O.Normal).conj_mem (a : Y) a.2 tau⟩
  have hfinj : Function.Injective f := by
    intro a b hab
    have habv : (a : Y)⁻¹ * φ (a : Y) = (b : Y)⁻¹ * φ (b : Y) :=
      congrArg Subtype.val hab
    have hmem : (b : Y) * (a : Y)⁻¹ ∈ O := O.mul_mem b.2 (O.inv_mem a.2)
    have hfixed : φ ((b : Y) * (a : Y)⁻¹) = (b : Y) * (a : Y)⁻¹ := by
      rw [map_mul, map_inv]
      have hcalc : (b : Y) * (a : Y)⁻¹ = φ (b : Y) * (φ (a : Y))⁻¹ := by
        calc (b : Y) * (a : Y)⁻¹
            = (b : Y) * ((a : Y)⁻¹ * φ (a : Y)) * (φ (a : Y))⁻¹ := by group
          _ = (b : Y) * ((b : Y)⁻¹ * φ (b : Y)) * (φ (a : Y))⁻¹ := by rw [habv]
          _ = φ (b : Y) * (φ (a : Y))⁻¹ := by group
      exact hcalc.symm
    have hone : (b : Y) * (a : Y)⁻¹ = 1 :=
      hfix ((b : Y) * (a : Y)⁻¹) hmem (by rw [← hφ_apply]; exact hfixed)
    exact Subtype.ext (eq_of_mul_inv_eq_one hone).symm
  have hfsurj : Function.Surjective f := (Finite.injective_iff_surjective).mp hfinj
  intro o ho
  obtain ⟨a, ha⟩ := hfsurj ⟨o, ho⟩
  have hval : (a : Y)⁻¹ * φ (a : Y) = o := congrArg Subtype.val ha
  rw [← hval, ← hφ_apply]
  exact hconj (a : Y)

end CFSG.OddStandard.SmallF3.Omega
