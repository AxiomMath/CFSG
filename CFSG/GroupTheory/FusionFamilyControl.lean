module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Commutator.FocalSubgroup
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.GroupTheory

variable {G : Type*} [Group G]

@[expose] def FusionStep (F : Set (Subgroup G)) (P : Subgroup G) (x y : G) : Prop :=
  x ∈ P ∧ y ∈ P ∧ ∃ H ∈ F, ∃ h ∈ H, y = h * x * h⁻¹

@[expose] def FamilyControlsFusion (F : Set (Subgroup G)) (P : Subgroup G) : Prop :=
  ∀ x y : G, x ∈ P → y ∈ P → IsConj x y → Relation.EqvGen (FusionStep F P) x y

theorem FamilyControlsFusion.mul_inv_mem {F : Set (Subgroup G)} {P Q : Subgroup G}
    (hctrl : FamilyControlsFusion F P)
    (hstep : ∀ x y : G, FusionStep F P x y → x⁻¹ * y ∈ Q)
    {x y : G} (hx : x ∈ P) (hy : y ∈ P) (hconj : IsConj x y) : x⁻¹ * y ∈ Q := by
  refine Relation.EqvGen.rec (motive := fun a b _ => a⁻¹ * b ∈ Q) ?_ ?_ ?_ ?_
    (hctrl x y hx hy hconj)
  · intro a b hab
    exact hstep a b hab
  · intro a
    simpa using Q.one_mem
  · intro a b _ ih
    have h : b⁻¹ * a = (a⁻¹ * b)⁻¹ := by group
    rw [h]
    exact Q.inv_mem ih
  · intro a b c _ _ hab hbc
    have h : a⁻¹ * c = (a⁻¹ * b) * (b⁻¹ * c) := by group
    rw [h]
    exact Q.mul_mem hab hbc

theorem inf_commutator_le_of_familyControlsFusion [Finite G] {p : ℕ} [Fact p.Prime]
    {P : Sylow p G} {F : Set (Subgroup G)} {Q : Subgroup G}
    (hctrl : FamilyControlsFusion F (P : Subgroup G))
    (hstep : ∀ x y : G, FusionStep F (P : Subgroup G) x y → x⁻¹ * y ∈ Q) :
    (P : Subgroup G) ⊓ commutator G ≤ Q := by
  have hfocal := CFSG.sylow_inf_derivedSubgroup_eq_focalSubgroup p P
  rw [CFSG.derivedSubgroup, derivedSeries_one] at hfocal
  rw [hfocal, Subgroup.closure_le]
  rintro z ⟨x, hxP, y, hyP, hxy, rfl⟩
  exact hctrl.mul_inv_mem (Q := Q) hstep hxP hyP hxy

theorem no_fusion_in_cyclic_sylow_two_quotient [Finite G] {H K T : Subgroup G} (hKH : K ≤ H)
    [hKnormal : (K.subgroupOf H).Normal] (hT : CFSG.ABGLocalTools.IsSylowOf 2 T H)
    (hcyc : IsCyclic ((T.subgroupOf H).map (QuotientGroup.mk' (K.subgroupOf H))))
    {h x : G} (hh : h ∈ H) (hx : x ∈ T) (hconj : h * x * h⁻¹ ∈ T) :
    x⁻¹ * (h * x * h⁻¹) ∈ K := by
  classical
  let N : Subgroup H := K.subgroupOf H
  let π : H →* H ⧸ N := QuotientGroup.mk' N
  obtain ⟨TH, hTH⟩ := hT.exists_sylow_eq_subgroupOf
  let Tbar : Sylow 2 (H ⧸ N) := TH.mapSurjective (QuotientGroup.mk'_surjective N)
  have hTbar_coe : (Tbar : Subgroup (H ⧸ N)) = (T.subgroupOf H).map π := by
    rw [Sylow.coe_mapSurjective, hTH]
  have hcycTbar : IsCyclic (Tbar : Subgroup (H ⧸ N)) := by
    rw [hTbar_coe]
    exact hcyc
  let xH : H := ⟨x, hT.le hx⟩
  let hH : H := ⟨h, hh⟩
  let yH : H := ⟨h * x * h⁻¹, hT.le hconj⟩
  let xbar : H ⧸ N := π xH
  let ybar : H ⧸ N := π yH
  let hbar : H ⧸ N := π hH
  have hxTH : xH ∈ (TH : Subgroup H) := by
    rw [hTH, Subgroup.mem_subgroupOf]
    exact hx
  have hyTH : yH ∈ (TH : Subgroup H) := by
    rw [hTH, Subgroup.mem_subgroupOf]
    exact hconj
  have hxbar : xbar ∈ (Tbar : Subgroup (H ⧸ N)) := by
    rw [hTbar_coe]
    exact Subgroup.mem_map.mpr ⟨xH, by simpa [hTH] using hxTH, rfl⟩
  have hybar : ybar ∈ (Tbar : Subgroup (H ⧸ N)) := by
    rw [hTbar_coe]
    exact Subgroup.mem_map.mpr ⟨yH, by simpa [hTH] using hyTH, rfl⟩
  have hconjbar : ybar = hbar * xbar * hbar⁻¹ := by
    change π yH = π hH * π xH * (π hH)⁻¹
    rw [← map_mul, ← map_inv, ← map_mul]
    congr 1
  letI : IsCyclic (Tbar : Subgroup (H ⧸ N)) := hcycTbar
  have hcomm : IsMulCommutative (Tbar : Subgroup (H ⧸ N)) := IsCyclic.isMulCommutative
  have hxbarC : xbar ∈ Subgroup.centralizer ((Tbar : Subgroup (H ⧸ N)) : Set (H ⧸ N)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact congrArg Subtype.val (hcomm.is_comm.comm ⟨t, ht⟩ ⟨xbar, hxbar⟩)
  have hybarC : ybar ∈ Subgroup.centralizer ((Tbar : Subgroup (H ⧸ N)) : Set (H ⧸ N)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact congrArg Subtype.val (hcomm.is_comm.comm ⟨t, ht⟩ ⟨ybar, hybar⟩)
  by_cases heven : 2 ∣ Nat.card (H ⧸ N)
  · have hmin : (Nat.card (H ⧸ N)).minFac = 2 := (Nat.minFac_eq_two_iff _).mpr heven
    have hNC := IsCyclic.normalizer_le_centralizer (p := 2) hmin hcycTbar
    have hcent : (hbar⁻¹)⁻¹ * xbar * hbar⁻¹ ∈
        Subgroup.centralizer ((Tbar : Subgroup (H ⧸ N)) : Set (H ⧸ N)) := by
      have hcent_eq : (hbar⁻¹)⁻¹ * xbar * hbar⁻¹ = ybar := by
        rw [inv_inv]
        exact hconjbar.symm
      rw [hcent_eq]
      exact hybarC
    obtain ⟨n, hn, hnconj⟩ :=
      Sylow.conj_eq_normalizer_conj_of_mem_centralizer Tbar xbar hbar⁻¹ hxbarC hcent
    have hnC : n ∈ Subgroup.centralizer ((Tbar : Subgroup (H ⧸ N)) : Set (H ⧸ N)) := hNC hn
    have hnx : n⁻¹ * xbar * n = xbar := by
      have hcommn : xbar * n = n * xbar :=
        Subgroup.mem_centralizer_iff.mp hnC xbar hxbar
      calc n⁻¹ * xbar * n = n⁻¹ * (xbar * n) := by group
        _ = n⁻¹ * (n * xbar) := by rw [hcommn]
        _ = xbar := by group
    have hxybar : ybar = xbar := by
      calc ybar = hbar * xbar * hbar⁻¹ := hconjbar
        _ = (hbar⁻¹)⁻¹ * xbar * hbar⁻¹ := by rw [inv_inv]
        _ = n⁻¹ * xbar * n := hnconj
        _ = xbar := hnx
    have hpi : π xH = π yH := by
      change xbar = ybar
      exact hxybar.symm
    have hmemN : xH⁻¹ * yH ∈ N := (QuotientGroup.eq).mp hpi
    have hmemK : ((xH⁻¹ * yH : H) : G) ∈ K := Subgroup.mem_subgroupOf.mp hmemN
    simpa [xH, yH] using hmemK
  · have hTbar_bot : (Tbar : Subgroup (H ⧸ N)) = ⊥ := by
      obtain ⟨k, hk⟩ := Tbar.isPGroup'.exists_card_eq
      have hdvd : 2 ^ k ∣ Nat.card (H ⧸ N) := by
        rw [← hk]
        exact Subgroup.card_subgroup_dvd_card _
      have hk0 : k = 0 := by
        by_contra hne
        exact heven ((dvd_pow_self 2 hne).trans hdvd)
      rw [hk0, pow_zero] at hk
      exact Subgroup.eq_bot_of_card_eq _ hk
    have hxbar1 : xbar = 1 := by
      have : xbar ∈ (⊥ : Subgroup (H ⧸ N)) := by simpa [hTbar_bot] using hxbar
      exact Subgroup.mem_bot.mp this
    have hybar1 : ybar = 1 := by
      have : ybar ∈ (⊥ : Subgroup (H ⧸ N)) := by simpa [hTbar_bot] using hybar
      exact Subgroup.mem_bot.mp this
    have hxK : x ∈ K := by
      have hxN : xH ∈ N := (QuotientGroup.eq_one_iff xH).mp hxbar1
      exact Subgroup.mem_subgroupOf.mp hxN
    have hyK : h * x * h⁻¹ ∈ K := by
      have hyN : yH ∈ N := (QuotientGroup.eq_one_iff yH).mp hybar1
      exact Subgroup.mem_subgroupOf.mp hyN
    exact K.mul_mem (K.inv_mem hxK) hyK

theorem inf_commutator_le_of_familyControlsFusion_sylow [Finite G] {T : Sylow 2 G}
    {S : Subgroup G} {F : Set (Subgroup G)}
    (hctrl : FamilyControlsFusion F (T : Subgroup G))
    (hH : ∀ H ∈ F, (T : Subgroup G) ≤ H)
    (hK : ∀ H ∈ F, ∃ (K : Subgroup G) (hKn : (K.subgroupOf H).Normal), K ≤ H ∧
      (T : Subgroup G) ⊓ K ≤ S ∧
      IsCyclic ((T.subgroupOf H).map (@QuotientGroup.mk' H _ (K.subgroupOf H) hKn))) :
    (T : Subgroup G) ⊓ commutator G ≤ S := by
  apply inf_commutator_le_of_familyControlsFusion (p := 2) (P := T) (F := F) (Q := S) hctrl
  intro x y hstep
  rcases hstep with ⟨hxT, hyT, H, hHF, h', hh'H, hyeq⟩
  have hTleH : (T : Subgroup G) ≤ H := hH H hHF
  have hTsyl : CFSG.ABGLocalTools.IsSylowOf 2 (T : Subgroup G) H := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨hTleH, T.isPGroup', ?_⟩
    intro h2
    exact T.not_dvd_index (h2.trans (Subgroup.relIndex_dvd_index_of_le hTleH))
  obtain ⟨K, hKn, hKH, hTKS, hcycK⟩ := hK H hHF
  have hconjT : h' * x * h'⁻¹ ∈ (T : Subgroup G) := by
    rw [← hyeq]
    exact hyT
  have hmemK : x⁻¹ * (h' * x * h'⁻¹) ∈ K := by
    haveI : (K.subgroupOf H).Normal := hKn
    exact no_fusion_in_cyclic_sylow_two_quotient hKH hTsyl hcycK hh'H hxT hconjT
  have hmemT : x⁻¹ * (h' * x * h'⁻¹) ∈ (T : Subgroup G) :=
    T.mul_mem (T.inv_mem hxT) hconjT
  have hmemS : x⁻¹ * (h' * x * h'⁻¹) ∈ S := hTKS ⟨hmemT, hmemK⟩
  simpa [hyeq] using hmemS

theorem sylow_le_of_familyControlsFusion_of_perfect [Finite G] {T : Sylow 2 G}
    {S : Subgroup G} {F : Set (Subgroup G)}
    (hctrl : FamilyControlsFusion F (T : Subgroup G))
    (hH : ∀ H ∈ F, (T : Subgroup G) ≤ H)
    (hK : ∀ H ∈ F, ∃ (K : Subgroup G) (hKn : (K.subgroupOf H).Normal), K ≤ H ∧
      (T : Subgroup G) ⊓ K ≤ S ∧
      IsCyclic ((T.subgroupOf H).map (@QuotientGroup.mk' H _ (K.subgroupOf H) hKn)))
    (hperf : commutator G = ⊤) : (T : Subgroup G) ≤ S := by
  have h := inf_commutator_le_of_familyControlsFusion_sylow hctrl hH hK
  rwa [hperf, inf_top_eq] at h

end CFSG.GroupTheory

end
