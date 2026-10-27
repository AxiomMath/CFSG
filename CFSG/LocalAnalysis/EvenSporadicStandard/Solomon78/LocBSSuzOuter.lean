module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSSuzFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSSuzModel
public import Certificates.Certificate26681

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four

section Outer


theorem mem_invE_zero {g : Equiv.Perm (Fin 1782)} :
    g ∈ invE 0 ↔ g ∈ suzM ∧ g * suzInv 0 = suzInv 0 * g := by
  rw [invE_eq_centM (by norm_num : 0 < 4), centM, Subgroup.mem_inf, and_comm,
    Subgroup.mem_centralizer_singleton_iff]

@[expose] noncomputable def suzV0 : Equiv.Perm (Fin 1782) := suzWord suzWordM0 * suzV

theorem suzOuter_data :
    lettersOK 2 suzWordM0 = true ∧
      eqA 1782 (compA 1782 suzArrV0 (tArr 0)) (compA 1782 (tArr 0) suzArrV0) = true ∧
      suzCentCheck = true ∧ suzCosetCheck = true := by
  have h := Certificates.certificate26681
  simp only [suzOuterCheck, suzOuterRelOK, Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem rep_suzArrV0 : Rep 1782 suzArrV0 suzV0 := by
  have h := (suzOuter_data).1
  unfold suzArrV0 suzArrM0 suzV0
  exact rep_compA (rep_suzArr (lettersOK_mono (by norm_num) h)) rep_v

theorem suzV0_mem : suzV0 ∈ suzT :=
  suzT.mul_mem (suzM_le_suzT (suzWord_mem (suzOuter_data).1)) suzV_mem_suzT

theorem suzV0_not_mem : suzV0 ∉ suzM := by
  intro h
  have hm : suzWord suzWordM0 ∈ suzM := suzWord_mem (suzOuter_data).1
  apply suzV_not_mem
  have := suzM.mul_mem (suzM.inv_mem hm) h
  simpa [suzV0] using this

theorem suzV0_comm : suzV0 * suzInv 0 = suzInv 0 * suzV0 :=
  (eqA_iff (rep_compA rep_suzArrV0 (rep_suzInv (by norm_num)))
    (rep_compA (rep_suzInv (by norm_num)) rep_suzArrV0)).1 (suzOuter_data).2.1

theorem suz_cent_range {g : Equiv.Perm (Fin 42)} (hg : g ∈ rho0.range)
    (hc : ∀ j < 5, g * dperm j = dperm j * g) : g = 1 := by
  refine eq_one_of_centralOK (T := suzRangeTabs) (gs := dGens) rho0_enumerates
    (suzOuter_data).2.2.1 hg fun i hi => ?_
  rw [dGens_size] at hi
  exact ⟨dperm i, tabRep_dperm hi, hc i hi⟩

theorem suz_coset_ne {σ : Equiv.Perm (Fin 42)} (hσ : TabRep suzTabV0 σ) {g : Equiv.Perm (Fin 42)}
    (hg : g ∈ rho0.range) : ¬ ∀ j < 5, σ * g * dperm j = dperm j * (σ * g) := by
  intro hc
  obtain ⟨t, ht, hrep⟩ := rho0_enumerates.complete g hg
  obtain ⟨k, hk, rfl⟩ := exists_getElem!_of_mem ht
  have h := (suzOuter_data).2.2.2
  simp only [suzCosetCheck, allBelow_eq_true] at h
  have hk' := h k hk
  simp only [Bool.not_eq_true'] at hk'
  have hall : allBelow dGens.size (fun j =>
      comp 42 (comp 42 suzTabV0 suzRangeTabs[k]!) dGens[j]! ==
        comp 42 dGens[j]! (comp 42 suzTabV0 suzRangeTabs[k]!)) = true := by
    rw [allBelow_eq_true]
    intro j hj
    rw [dGens_size] at hj
    have hd := tabRep_dperm hj
    exact (((hσ.comp hrep).comp hd).beq_iff (hd.comp (hσ.comp hrep))).2 (hc j hj)
  rw [hall] at hk'
  exact Bool.noConfusion hk'

theorem suz_inner_ker {x : Equiv.Perm (Fin 1782)} (hx : x ∈ invE 0)
    {K : Subgroup (Equiv.Perm (Fin 1782))} (hK : K ≤ invE 0) (hperf : Group.IsPerfect K)
    (hcard : Nat.card K = 20160) (hc : ∀ k ∈ K, x * k = k * x) :
    (⟨x, hx⟩ : invE 0) ∈ rho0.ker := by
  have hK' : Group.IsPerfect (K.subgroupOf (invE 0)) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hK).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hK).symm.surjective
  have hcard' : Nat.card (K.subgroupOf (invE 0)) = Nat.card suzD := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK).toEquiv, hcard, card_suzD]
  refine suz_quot2Data.mem_ker_of_centralizes hK' hcard' (fun y hy hyd => ?_)
    (fun k hk => Subtype.ext (hc k hk))
  exact suz_cent_range hy fun j hj => hyd _ (Subgroup.subset_closure ⟨j, hj, rfl⟩)

theorem suz_subgroupOf_data {K : Subgroup (Equiv.Perm (Fin 1782))} (hK : K ≤ invE 0)
    (hperf : Group.IsPerfect K) (hcard : Nat.card K = 20160) :
    Group.IsPerfect (K.subgroupOf (invE 0)) ∧
      Nat.card (K.subgroupOf (invE 0)) = Nat.card suzD := by
  refine ⟨Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hK).symm.toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe hK).symm.surjective, ?_⟩
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK).toEquiv, hcard, card_suzD]

theorem suzHat_preserves : ∀ g ∈ suzT ⊓ Subgroup.centralizer
      ({suzInv 0} : Set (Equiv.Perm (Fin 1782))),
    ∀ x : Fin 1782, (x : ℕ) ∈ fixList 0 → (g x : ℕ) ∈ fixList 0 := by
  intro g hg x hx
  rw [mem_fixList (by norm_num : 0 < 4)] at hx ⊢
  have hc := Subgroup.mem_centralizer_singleton_iff.1 hg.2
  have := congrArg (fun σ : Equiv.Perm (Fin 1782) => σ x) hc
  simp only [Equiv.Perm.mul_apply, hx] at this
  exact this.symm

@[expose] noncomputable def rhoHat : (suzT ⊓ Subgroup.centralizer
      ({suzInv 0} : Set (Equiv.Perm (Fin 1782))) : Subgroup (Equiv.Perm (Fin 1782))) →*
    Equiv.Perm (Fin 42) :=
  (fixList_points hm0).restrHom _ suzHat_preserves

theorem suz_no_outer {x : Equiv.Perm (Fin 1782)} (hx : x ∈ suzT) (hxM : x ∉ suzM)
    (hxt : x * suzInv 0 = suzInv 0 * x) {K : Subgroup (Equiv.Perm (Fin 1782))}
    (hK : K ≤ invE 0) (hperf : Group.IsPerfect K) (hcard : Nat.card K = 20160)
    (hc : ∀ k ∈ K, x * k = k * x) : False := by
  set Ê : Subgroup (Equiv.Perm (Fin 1782)) :=
    suzT ⊓ Subgroup.centralizer ({suzInv 0} : Set (Equiv.Perm (Fin 1782))) with hÊdef
  have hv0Ê : suzV0 ∈ Ê := ⟨suzV0_mem, Subgroup.mem_centralizer_singleton_iff.2 suzV0_comm⟩
  have hxÊ : x ∈ Ê := ⟨hx, Subgroup.mem_centralizer_singleton_iff.2 hxt⟩
  have ha : (⟨suzV0⁻¹, suzT.inv_mem suzV0_mem⟩ : suzT) ∉ suzM.subgroupOf suzT := by
    rw [Subgroup.mem_subgroupOf]
    intro h
    exact suzV0_not_mem (by simpa using suzM.inv_mem h)
  have hb : (⟨x, hx⟩ : suzT) ∉ suzM.subgroupOf suzT := by
    rw [Subgroup.mem_subgroupOf]
    exact hxM
  have he : suzV0⁻¹ * x ∈ suzM := by
    have h3 := (Subgroup.mul_mem_iff_of_index_two suzM_index_T).2 (iff_of_false ha hb)
    rw [Subgroup.mem_subgroupOf] at h3
    exact h3
  have h1 : suzV0⁻¹ * suzInv 0 = suzInv 0 * suzV0⁻¹ := by
    calc suzV0⁻¹ * suzInv 0 = suzV0⁻¹ * (suzInv 0 * suzV0) * suzV0⁻¹ := by group
      _ = suzV0⁻¹ * (suzV0 * suzInv 0) * suzV0⁻¹ := by rw [suzV0_comm]
      _ = suzInv 0 * suzV0⁻¹ := by group
  have heC : suzV0⁻¹ * x * suzInv 0 = suzInv 0 * (suzV0⁻¹ * x) := by
    calc suzV0⁻¹ * x * suzInv 0 = suzV0⁻¹ * (x * suzInv 0) := by group
      _ = suzV0⁻¹ * (suzInv 0 * x) := by rw [hxt]
      _ = (suzV0⁻¹ * suzInv 0) * x := by group
      _ = (suzInv 0 * suzV0⁻¹) * x := by rw [h1]
      _ = suzInv 0 * (suzV0⁻¹ * x) := by group
  have heE : suzV0⁻¹ * x ∈ invE 0 := mem_invE_zero.2 ⟨he, heC⟩
  have heÊ : suzV0⁻¹ * x ∈ Ê :=
    ⟨suzM_le_suzT he, Subgroup.mem_centralizer_singleton_iff.2 heC⟩
  have hprod : (⟨x, hxÊ⟩ : Ê) = ⟨suzV0, hv0Ê⟩ * ⟨suzV0⁻¹ * x, heÊ⟩ :=
    Subtype.ext (by simp)
  have hσ : TabRep suzTabV0 (rhoHat ⟨suzV0, hv0Ê⟩) := by
    unfold suzTabV0
    exact (fixList_points hm0).tabRep_restrHom _ suzHat_preserves ⟨suzV0, hv0Ê⟩ rep_suzArrV0
  obtain ⟨hK', hcard'⟩ := suz_subgroupOf_data hK hperf hcard
  have hmap := suz_quot2Data.map_eq hK' hcard'
  have hcomm : ∀ j < 5, rhoHat ⟨x, hxÊ⟩ * dperm j = dperm j * rhoHat ⟨x, hxÊ⟩ := by
    intro j hj
    have hd : dperm j ∈ suzD := Subgroup.subset_closure ⟨j, hj, rfl⟩
    rw [← hmap] at hd
    obtain ⟨k, hk, hkd⟩ := hd
    have hkK : (k : Equiv.Perm (Fin 1782)) ∈ K := hk
    have hkE := mem_invE_zero.1 k.2
    have hkÊ : (k : Equiv.Perm (Fin 1782)) ∈ Ê :=
      ⟨suzM_le_suzT hkE.1, Subgroup.mem_centralizer_singleton_iff.2 hkE.2⟩
    have hρk : rhoHat ⟨k, hkÊ⟩ = rho0 k := rfl
    rw [← hkd, ← hρk, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hc k hkK)
  have hy : rhoHat ⟨x, hxÊ⟩ = rhoHat ⟨suzV0, hv0Ê⟩ * rho0 ⟨suzV0⁻¹ * x, heE⟩ := by
    rw [hprod, map_mul]
    rfl
  exact suz_coset_ne hσ (rho0.mem_range.2 ⟨_, rfl⟩) (by rw [← hy]; exact hcomm)

end Outer

end CFSG.EvenSporadicStandard.Solomon78
