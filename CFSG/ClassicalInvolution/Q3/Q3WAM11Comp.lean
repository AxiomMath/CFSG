module

public import CFSG.ClassicalInvolution.Q3.Q3WAComp

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

section M11

theorem nonempty_equiv_sl2_of_mem_m11Class {J : Subgroup ↥CFSG.Blueprint.NativeSporadic.M11}
    (hJ : J ∈ M11ClassicalClass) : Nonempty (J ≃* SL(2, ZMod 3)) := by
  obtain ⟨w, hw⟩ := hJ
  have hcard : Nat.card J = 24 :=
    hw.card_eq_of_mulEquiv_m11 (MulEquiv.refl ↥CFSG.Blueprint.NativeSporadic.M11)
  obtain ⟨e'⟩ := hw.nonempty_equiv
  have hq : Nat.card (J ⧸ classicalInvolutionOddCore J) = 24 := by
    rw [Nat.card_congr e'.toEquiv, natCard_sl2Three]
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup (classicalInvolutionOddCore J)
  rw [hq, hcard] at hmul
  have h1 : Nat.card (classicalInvolutionOddCore J) = 1 := by omega
  have hO : classicalInvolutionOddCore J = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
  exact hw.nonempty_equiv_sl2 hO

theorem not_commutes_of_mem_m11Class {J J' : Subgroup ↥CFSG.Blueprint.NativeSporadic.M11}
    (hJ : J ∈ M11ClassicalClass) (hJ' : J' ∈ M11ClassicalClass) : ¬ Commutes J J' := by
  intro hc
  obtain ⟨e⟩ := nonempty_equiv_sl2_of_mem_m11Class hJ
  obtain ⟨w, hw⟩ := hJ
  obtain ⟨w', hw'⟩ := hJ'
  have hcard : Nat.card J = 24 :=
    hw.card_eq_of_mulEquiv_m11 (MulEquiv.refl ↥CFSG.Blueprint.NativeSporadic.M11)
  have hcard' : Nat.card J' = 24 :=
    hw'.card_eq_of_mulEquiv_m11 (MulEquiv.refl ↥CFSG.Blueprint.NativeSporadic.M11)
  set C : Subgroup ↥CFSG.Blueprint.NativeSporadic.M11 :=
    Subgroup.centralizer ({w} : Set ↥CFSG.Blueprint.NativeSporadic.M11) with hCdef
  have hC : Nat.card C ≤ 48 := card_centralizer_le_of_orderOf_eq_two hw.orderOf_eq_two
  have hJC : J ≤ C := isSubnormal_le hw.subnormal
  have hJ'C : J' ≤ C := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hc w hw.mem a ha).symm
  have hidx : ∀ H : Subgroup ↥CFSG.Blueprint.NativeSporadic.M11, H ≤ C → Nat.card H = 24 →
      (H.subgroupOf C).index ≤ 2 := by
    intro H hH h24
    have h1 := Subgroup.card_mul_index (H.subgroupOf C)
    have h2 : Nat.card (H.subgroupOf C) = 24 := by
      rw [← h24]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH).toEquiv
    rw [h2] at h1
    omega
  have hi1 := hidx J hJC hcard
  have hi2 := hidx J' hJ'C hcard'
  have hinf : (J.subgroupOf C ⊓ J'.subgroupOf C).index ≤
      (J.subgroupOf C).index * (J'.subgroupOf C).index := Subgroup.index_inf_le
  have hmul := Subgroup.card_mul_index (J.subgroupOf C ⊓ J'.subgroupOf C)
  have hC24 : 24 ≤ Nat.card C := by
    rw [← hcard]
    exact Subgroup.card_le_of_le hJC
  have hmem : ∀ a : ↥(J.subgroupOf C ⊓ J'.subgroupOf C),
      e ⟨((a.1 : C) : ↥CFSG.Blueprint.NativeSporadic.M11), Subgroup.mem_subgroupOf.mp a.2.1⟩ ∈
        ({1, -1} : Set SL(2, ZMod 3)) := by
    intro a
    have ha' : ((a.1 : C) : ↥CFSG.Blueprint.NativeSporadic.M11) ∈ J' :=
      Subgroup.mem_subgroupOf.mp a.2.2
    have hcen : e ⟨((a.1 : C) : ↥CFSG.Blueprint.NativeSporadic.M11),
        Subgroup.mem_subgroupOf.mp a.2.1⟩ ∈ Subgroup.center SL(2, ZMod 3) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨j, rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hc _ j.2 _ ha')
    rcases (CFSG.ClassicalInvolution.mem_center_sl2_iff _).mp hcen with h | h <;> simp [h]
  have hZ : Nat.card ↥(J.subgroupOf C ⊓ J'.subgroupOf C) ≤ 2 := by
    refine (Nat.card_le_card_of_injective
      (fun a => (⟨e ⟨((a.1 : C) : ↥CFSG.Blueprint.NativeSporadic.M11),
        Subgroup.mem_subgroupOf.mp a.2.1⟩, hmem a⟩ : ↥({1, -1} : Set SL(2, ZMod 3)))) ?_).trans ?_
    · intro a b hab
      have h1 := congrArg Subtype.val hab
      have h2 := e.injective h1
      have h3 := Subtype.ext_iff.mp h2
      exact Subtype.ext (Subtype.ext h3)
    · rw [Nat.card_coe_set_eq]
      exact (Set.ncard_insert_le _ _).trans (by simp)
  have hmul22 : (J.subgroupOf C).index * (J'.subgroupOf C).index ≤ 2 * 2 :=
    Nat.mul_le_mul hi1 hi2
  have hind4 : (J.subgroupOf C ⊓ J'.subgroupOf C).index ≤ 4 := hinf.trans (by omega)
  have : Nat.card C ≤ 2 * 4 := by
    rw [← hmul]
    exact Nat.mul_le_mul hZ hind4
  omega

end M11

section Comp


variable {G : Type} [Group G] [Finite G] {ι : Type} {Ω : Set (Subgroup G)} {x : G}

theorem not_commutes_of_m11_comp3 (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    (hP1 : LocalOddCentral Ω {x}) (hO3 : LocalOddThreeFree3 Ω x)
    {D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x)} {i : ι}
    (hk : D.kind i = CompData.m11) {N N' : Subgroup G} (hN : N ∈ compMembers3 Ω x D i)
    (hN' : N' ∈ compMembers3 Ω x D i) : ¬ Commutes N N' := by
  intro hc
  obtain ⟨R, hR⟩ := exists_corr_left3 hΩ hex hP1 hO3 D hN
  obtain ⟨R', hR'⟩ := exists_corr_left3 hΩ hex hP1 hO3 D hN'
  have hpc : PowCop3 (D.kind i) := hk ▸ powCop3_m11
  have hRR' := (corr_commutes3 hΩ hex hP1 hO3 hpc hR hR').mp hc
  have key : ∀ c : CompData, c = CompData.m11 → ∀ R R' : Subgroup c.G, R ∈ c.fund →
      R' ∈ c.fund → ¬ Commutes R R' := by
    rintro c rfl R R' hR hR'
    exact not_commutes_of_mem_m11Class hR hR'
  exact key _ hk R R' hR.2.1 hR'.2.1 hRR'

end Comp

end CFSG.ClassicalInvolution.Q3.Q3W
