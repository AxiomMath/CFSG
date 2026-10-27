module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdgeSecLift
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtxSecOddFree
public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.CentQuotCongr
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx

section Pullback

variable {H : Type} [Group H] [Finite H] {N : Subgroup H} [N.Normal]

theorem exists_classicalMember_of_oddQuot'' (hNodd : Odd (Nat.card ↥N)) {t : H}
    (ht2 : t * t = 1) {L : Subgroup (H ⧸ N)}
    (hL : IsClassicalMember3 L (QuotientGroup.mk' N t)) :
    ∃ K : Subgroup H, IsClassicalMember3 K t ∧ (∀ k ∈ K, QuotientGroup.mk' N k ∈ L) ∧
      (∀ l ∈ L, ∃ k ∈ K, QuotientGroup.mk' N k = l) := by
  classical
  set π : H →* H ⧸ N := QuotientGroup.mk' N with hπ
  set C : Subgroup H := Subgroup.centralizer ({t} : Set H) with hC
  set P : Subgroup H := L.comap π with hP
  set K : Subgroup H := P ⊓ C with hK
  have htP : t ∈ P := Subgroup.mem_comap.mpr hL.mem
  have htC : t ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have htK : t ∈ K := ⟨htP, htC⟩
  have hLC : L ≤ Subgroup.centralizer ({π t} : Set (H ⧸ N)) := isSubnormal_le' hL.subnormal
  have hCbar : Subgroup.centralizer ({π t} : Set (H ⧸ N)) = C.map π :=
    OddQ.centralizer_mk_eq hNodd ht2
  have hKL : ∀ k : K, π (k : H) ∈ L := fun k => Subgroup.mem_comap.mp k.2.1
  set f : ↥K →* ↥L := (π.comp K.subtype).codRestrict L hKL with hf
  have hfs : Function.Surjective f := by
    intro x
    have hx := hLC x.2
    rw [hCbar] at hx
    obtain ⟨c, hcC, hcx⟩ := hx
    have hcP : c ∈ P := Subgroup.mem_comap.mpr (by rw [hcx]; exact x.2)
    exact ⟨⟨c, hcP, hcC⟩, Subtype.ext hcx⟩
  have hfk : Odd (Nat.card f.ker) := by
    have hker : f.ker = N.subgroupOf K := by
      ext k
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      constructor
      · intro h1
        exact (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val h1)
      · intro h1
        exact Subtype.ext ((QuotientGroup.eq_one_iff _).mpr h1)
    rw [hker]
    have h1 : Nat.card (N.subgroupOf K) = Nat.card (N ⊓ K : Subgroup H) := by
      rw [← Subgroup.subgroupOf_map_subtype, Subgroup.card_map_of_injective K.subtype_injective]
    rw [h1]
    exact hNodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have ht2' : orderOf t = 2 := by
    refine orderOf_eq_prime (by rw [pow_two]; exact ht2) ?_
    intro h1
    have := hL.orderOf_eq_two
    rw [hπ, QuotientGroup.mk'_apply, h1, QuotientGroup.mk_one, orderOf_one] at this
    omega
  refine ⟨K, ⟨ht2', htK, ?_, ?_⟩, fun k hk => Subgroup.mem_comap.mp hk.1, ?_⟩
  · have h1 := isSubnormal_comap' π hL.subnormal
    rw [hCbar] at h1
    have h2 := isSubnormal_inf h1 C
    have h3 : (C.map π).comap π ⊓ C = C := by
      rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
      exact inf_eq_right.mpr le_sup_left
    rw [h3] at h2
    exact h2
  · obtain ⟨e⟩ := hL.nonempty_equiv
    exact ⟨(CFSG.ComponentClassification.OddKernel.coreQuotientEquiv f hfs hfk).trans e⟩
  · intro l hl
    obtain ⟨k, hk⟩ := hfs ⟨l, hl⟩
    exact ⟨k, k.2, congrArg Subtype.val hk⟩

end Pullback

section Section

variable {Y : Type} [Group Y] [Finite Y] {C : Subgroup Y}

theorem exists_sectionMember_of_lift {H : Subgroup ↥C} (hH : IsSubnormal H ⊤) {t : ↥C}
    (ht : t ∈ H) (ht2 : t * t = 1) {L : Subgroup (↥H ⧸ classicalInvolutionOddCore ↥H)}
    (hL : IsClassicalMember3 L (QuotientGroup.mk' (classicalInvolutionOddCore ↥H) ⟨t, ht⟩)) :
    ∃ K : Subgroup Y, Q3NL.IsSectionMember3 C K (t : Y) ∧
      (∀ k ∈ K, ∃ h : ↥H, (((h : ↥C)) : Y) = k ∧
        QuotientGroup.mk' (classicalInvolutionOddCore ↥H) h ∈ L) ∧
      (∀ l ∈ L, ∃ h : ↥H, (((h : ↥C)) : Y) ∈ K ∧
        QuotientGroup.mk' (classicalInvolutionOddCore ↥H) h = l) := by
  obtain ⟨K, hK, hKL, hLK⟩ := exists_classicalMember_of_oddQuot''
    (CFSG.ComponentClassification.OddCore.odd_card ↥H) (t := (⟨t, ht⟩ : H))
    (Subtype.ext ht2) hL
  have hKC := isClassicalMember3_map_subnormal hH hK
  refine ⟨_, TL4.isSectionMember3_map hKC, ?_, ?_⟩
  · rintro k ⟨_, ⟨h, hh, rfl⟩, rfl⟩
    exact ⟨h, rfl, hKL h hh⟩
  · intro l hl
    obtain ⟨k, hk, hkl⟩ := hLK l hl
    exact ⟨k, ⟨_, ⟨k, hk, rfl⟩, rfl⟩, hkl⟩

end Section

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
