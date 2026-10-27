module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSSuzOuter
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSSuzEquiv
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Sporadic.SuzOddCore

section Aut


theorem suz_card_le_two_of_inf_bot {S : Subgroup (Equiv.Perm (Fin 1782))} (hS : S ≤ suzT)
    (h : S ⊓ suzM = ⊥) : Nat.card S ≤ 2 := by
  classical
  have hone : ∀ a ∈ S, ∀ b ∈ S, a ≠ 1 → b ≠ 1 → a = b := by
    intro a ha b hb ha1 hb1
    have haM : a ∉ suzM := fun hM => ha1 (by
      have : a ∈ S ⊓ suzM := ⟨ha, hM⟩
      rw [h, Subgroup.mem_bot] at this
      exact this)
    have hbM : b ∉ suzM := fun hM => hb1 (by
      have : b ∈ S ⊓ suzM := ⟨hb, hM⟩
      rw [h, Subgroup.mem_bot] at this
      exact this)
    have ha' : (⟨a⁻¹, suzT.inv_mem (hS ha)⟩ : suzT) ∉ suzM.subgroupOf suzT := by
      rw [Subgroup.mem_subgroupOf]
      intro hM
      exact haM (by simpa using suzM.inv_mem hM)
    have hb' : (⟨b, hS hb⟩ : suzT) ∉ suzM.subgroupOf suzT := by
      rw [Subgroup.mem_subgroupOf]
      exact hbM
    have h3 := (Subgroup.mul_mem_iff_of_index_two suzM_index_T).2 (iff_of_false ha' hb')
    rw [Subgroup.mem_subgroupOf] at h3
    have h4 : a⁻¹ * b ∈ S ⊓ suzM := ⟨S.mul_mem (S.inv_mem ha) hb, h3⟩
    rw [h, Subgroup.mem_bot] at h4
    exact inv_mul_eq_one.1 h4
  have hinj : Function.Injective (fun g : S => decide (g = 1)) := by
    intro g g' hgg
    by_cases hg : g = 1
    · have hg' : g' = 1 := by
        by_contra hg'
        simp [hg, hg'] at hgg
      rw [hg, hg']
    · have hg' : g' ≠ 1 := by
        intro hg'
        simp [hg, hg'] at hgg
      refine Subtype.ext (hone g g.2 g' g'.2 (fun h1 => hg (Subtype.ext h1))
        (fun h1 => hg' (Subtype.ext h1)))
  calc Nat.card S ≤ Nat.card Bool := Nat.card_le_card_of_injective _ hinj
    _ = 2 := by simp

theorem suz_two_subgroup_le {K : Subgroup (Equiv.Perm (Fin 1782))} (hK : K ≤ invE 0)
    (hperf : Group.IsPerfect K) (hcard : Nat.card K = 20160)
    {S : Subgroup (Equiv.Perm (Fin 1782))}
    (hSY : S ≤ suzT ⊓ Subgroup.centralizer (K : Set (Equiv.Perm (Fin 1782))))
    (hS : IsPGroup 2 S) : Nat.card S ≤ 4 := by
  have hST : S ≤ suzT := fun s hs => (hSY hs).1
  have hSK : ∀ s ∈ S, ∀ k ∈ K, s * k = k * s := fun s hs k hk =>
    (Subgroup.mem_centralizer_iff.1 (hSY hs).2 k hk).symm
  have hKM : K ≤ suzM := fun k hk => ((mem_invE_zero.1 (hK hk)).1)
  by_cases hS0 : S ⊓ suzM = ⊥
  · have := suz_card_le_two_of_inf_bot hST hS0
    omega
  have hnil : Group.IsNilpotent ↥S := hS.isNilpotent
  let N₀ : Subgroup ↥S := (S ⊓ suzM).subgroupOf S
  have hN₀ : N₀.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    refine ⟨S.mul_mem (S.mul_mem g.2 hn.1) (S.inv_mem g.2), ?_⟩
    exact suzT_conj_mem_suzM (hST g.2) hn.2
  have hN₀ne : N₀ ≠ ⊥ := by
    intro h
    apply hS0
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hx.1⟩ : ↥S) ∈ N₀ := Subgroup.mem_subgroupOf.2 hx
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
  have hP := Group.IsNilpotent.inf_center_ne_bot_of_normal (H := N₀) hN₀ne
  set P₀ : Subgroup ↥S := N₀ ⊓ Subgroup.center ↥S with hP₀
  have hP2 : IsPGroup 2 ↥P₀ := hS.to_subgroup P₀
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hP2
  have hn1 : n ≠ 0 := by
    rintro rfl
    exact hP (Subgroup.eq_bot_of_card_eq P₀ (by simpa using hn))
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t', ht'⟩ := exists_prime_orderOf_dvd_card' (G := ↥P₀) 2 (by
    rw [hn]
    exact dvd_pow_self 2 hn1)
  set t : Equiv.Perm (Fin 1782) := (((t' : ↥P₀) : ↥S) : Equiv.Perm (Fin 1782)) with htdef
  have ht2 : orderOf t = 2 := by
    rw [htdef, Subgroup.orderOf_coe, Subgroup.orderOf_coe, ht']
  have htN : (((t' : ↥P₀) : ↥S) : Equiv.Perm (Fin 1782)) ∈ S ⊓ suzM :=
    Subgroup.mem_subgroupOf.1 t'.2.1
  have htM : t ∈ suzM := htN.2
  have htc : ∀ s ∈ S, s * t = t * s := by
    intro s hs
    have := Subgroup.mem_center_iff.1 t'.2.2 ⟨s, hs⟩
    exact congrArg Subtype.val this
  have htS : t ∈ S := htN.1
  have hdvd : 20160 ∣ Nat.card (Subgroup.centralizer
      ({(⟨t, htM⟩ : ↥suzM)} : Set ↥suzM)) := by
    have hle : K.subgroupOf suzM ≤ Subgroup.centralizer ({(⟨t, htM⟩ : ↥suzM)} : Set ↥suzM) := by
      intro k hk
      rw [Subgroup.mem_centralizer_singleton_iff]
      refine Subtype.ext ?_
      exact (hSK t htS k (Subgroup.mem_subgroupOf.1 hk)).symm
    have := Subgroup.card_dvd_of_le hle
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv, hcard] at this
  obtain ⟨c, hcT, hct⟩ := suz_conj_zero (MulEquiv.refl ↥suzM) ⟨t, htM⟩
    (by rw [Subgroup.orderOf_mk, ht2]) hdvd
  have hct' : c * suzInv 0 * c⁻¹ = t := hct
  have ht0 : suzInv 0 = c⁻¹ * t * c := by
    rw [← hct']
    group
  have hcM : ∀ m ∈ suzM, c⁻¹ * m * c ∈ suzM := fun m hm => by
    have := suzT_conj_mem_suzM (suzT.inv_mem hcT) hm
    simpa using this
  have hcM' : ∀ m ∈ suzM, c * m * c⁻¹ ∈ suzM := fun m hm => suzT_conj_mem_suzM hcT hm
  set cj : Equiv.Perm (Fin 1782) →* Equiv.Perm (Fin 1782) :=
    (MulAut.conj c⁻¹).toMonoidHom with hcj
  have hcj : ∀ y, cj y = c⁻¹ * y * c := fun y => by
    simp [hcj]
  set K' : Subgroup (Equiv.Perm (Fin 1782)) := K.map cj with hK'def
  have hK'E : K' ≤ invE 0 := by
    rintro _ ⟨k, hk, rfl⟩
    have hkE := mem_invE_zero.1 (hK hk)
    refine mem_invE_zero.2 ⟨by rw [hcj]; exact hcM k hkE.1, ?_⟩
    rw [hcj, ht0]
    calc c⁻¹ * k * c * (c⁻¹ * t * c) = c⁻¹ * (k * t) * c := by group
      _ = c⁻¹ * (t * k) * c := by rw [hSK t htS k hk |>.symm]
      _ = c⁻¹ * t * c * (c⁻¹ * k * c) := by group
  have hK'perf : Group.IsPerfect K' := by
    have := hperf
    exact Group.IsPerfect.map _
  have hK'card : Nat.card K' = 20160 := by
    rw [hK'def, Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective, hcard]
  have hSker : S.map cj ≤ (rho0.ker).map (invE 0).subtype := by
    rintro _ ⟨x, hx, rfl⟩
    have hxT := hST hx
    have hxt : x * t = t * x := htc x hx
    have hx't : cj x * suzInv 0 = suzInv 0 * cj x := by
      rw [hcj, ht0]
      calc c⁻¹ * x * c * (c⁻¹ * t * c) = c⁻¹ * (x * t) * c := by group
        _ = c⁻¹ * (t * x) * c := by rw [hxt]
        _ = c⁻¹ * t * c * (c⁻¹ * x * c) := by group
    have hx'T : cj x ∈ suzT := by
      rw [hcj]
      have := suzT.mul_mem (suzT.mul_mem (suzT.inv_mem hcT) hxT) hcT
      exact this
    have hcomm : ∀ k' ∈ K', cj x * k' = k' * cj x := by
      rintro _ ⟨k, hk, rfl⟩
      rw [← map_mul, ← map_mul, hSK x hx k hk]
    have hx'M : cj x ∈ suzM := by
      by_contra hxM
      exact suz_no_outer hx'T hxM hx't hK'E hK'perf hK'card hcomm
    have hx'E : cj x ∈ invE 0 := mem_invE_zero.2 ⟨hx'M, hx't⟩
    exact ⟨⟨cj x, hx'E⟩, suz_inner_ker hx'E hK'E hK'perf hK'card hcomm, rfl⟩
  have h1 : Nat.card (S.map cj) = Nat.card S :=
    Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective
  have h2 : Nat.card ((rho0.ker).map (invE 0).subtype) = 4 := by
    rw [Subgroup.card_map_of_injective (invE 0).subtype_injective, card_ker_rho0]
  calc Nat.card S = Nat.card (S.map cj) := h1.symm
    _ ≤ Nat.card ((rho0.ker).map (invE 0).subtype) := Subgroup.card_le_of_le hSker
    _ = 4 := h2

theorem suz_twoAdic_centralizer_T {K : Subgroup (Equiv.Perm (Fin 1782))} (hK : K ≤ invE 0)
    (hperf : Group.IsPerfect K) (hcard : Nat.card K = 20160) :
    twoAdic (suzT ⊓ Subgroup.centralizer (K : Set (Equiv.Perm (Fin 1782)))) ≤ 2 := by
  set Y : Subgroup (Equiv.Perm (Fin 1782)) :=
    suzT ⊓ Subgroup.centralizer (K : Set (Equiv.Perm (Fin 1782))) with hY
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥Y) := inferInstance
  set S : Subgroup (Equiv.Perm (Fin 1782)) := (P : Subgroup ↥Y).map Y.subtype with hS
  have hSY : S ≤ Y := Subgroup.map_subtype_le _
  have hSp : IsPGroup 2 S := P.isPGroup'.map Y.subtype
  have hcardS : Nat.card S = 2 ^ twoAdic Y := by
    rw [hS, Subgroup.card_map_of_injective Y.subtype_injective, P.card_eq_multiplicity]
    rfl
  have h4 := suz_two_subgroup_le hK hperf hcard hSY hSp
  rw [hcardS] at h4
  by_contra hlt
  push Not at hlt
  have h8 : 2 ^ 3 ≤ 2 ^ twoAdic Y := Nat.pow_le_pow_right (by norm_num) hlt
  omega

end Aut

end CFSG.EvenSporadicStandard.Solomon78
