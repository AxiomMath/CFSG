module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G6Odd
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFAutBound
public import CFSG.LieType.ChevTwo.OppCl.SmallGlue

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom)

variable {G : Type} [Group G]

private noncomputable def sec8t84g6o_act (K : Subgroup G) {T : Type} [Group T]
    (θ : ↥K ⧸ center ↥K ≃* T) : normalizer (K : Set G) →* MulAut T :=
  (MulAut.congr θ).toMonoidHom.comp ((centerQuotientHom ↥K).comp K.normalizerMonoidHom)

private theorem sec8t84g6o_act_eq_one_iff (K : Subgroup G) [Group.IsPerfect ↥K] {T : Type} [Group T]
    (θ : ↥K ⧸ center ↥K ≃* T) (g : normalizer (K : Set G)) :
    sec8t84g6o_act K θ g = 1 ↔ (g : G) ∈ centralizer (K : Set G) := by
  have hker : g ∈ K.normalizerMonoidHom.ker ↔ (g : G) ∈ centralizer (K : Set G) := by
    rw [normalizerMonoidHom_ker, mem_subgroupOf]
  rw [← hker, MonoidHom.mem_ker]
  constructor
  · intro h
    apply CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_eq_one_imp
    apply (MulAut.congr θ).injective
    rw [map_one]
    exact h
  · intro h
    change (MulAut.congr θ) (centerQuotientHom ↥K (K.normalizerMonoidHom g)) = 1
    rw [h, map_one, map_one]

private theorem sec8t84g6o_act_apply_of_mem (K : Subgroup G) {T : Type} [Group T]
    (θ : ↥K ⧸ center ↥K ≃* T) {k : G} (hk : k ∈ K) :
    sec8t84g6o_act K θ ⟨k, Subgroup.le_normalizer hk⟩ =
      MulAut.conj (θ (QuotientGroup.mk (⟨k, hk⟩ : ↥K))) := by
  have h1 : K.normalizerMonoidHom ⟨k, Subgroup.le_normalizer hk⟩ =
      MulAut.conj (⟨k, hk⟩ : ↥K) := by
    ext a
    simp
  have h2 : centerQuotientHom ↥K (MulAut.conj (⟨k, hk⟩ : ↥K)) =
      MulAut.conj (QuotientGroup.mk (⟨k, hk⟩ : ↥K) : ↥K ⧸ center ↥K) := by
    ext u
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective u
    change CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient _
      (QuotientGroup.mk' (center ↥K) a) = _
    rw [CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk]
    rfl
  change MulAut.congr θ (centerQuotientHom ↥K (K.normalizerMonoidHom _)) = _
  rw [h1, h2, CFSG.ComponentClassification.OuterAutomorphisms.congr_conj]

theorem sec8t84g6o_mem_sup_of_odd {K : Subgroup G} [Group.IsPerfect ↥K] {T : Type} [Group T]
    [Finite T] (θ : ↥K ⧸ center ↥K ≃* T) (hO : Nat.card (Outer T) ∣ 2) {x : G}
    (hx : x ∈ normalizer (K : Set G)) (hodd : Odd (orderOf x)) :
    x ∈ K ⊔ centralizer (K : Set G) := by
  obtain ⟨g, hg⟩ : ∃ g : normalizer (K : Set G), g = ⟨x, hx⟩ := ⟨_, rfl⟩
  have hgx : (g : G) = x := by rw [hg]
  have hord : Odd (orderOf (sec8t84g6o_act K θ g)) := by
    have h1 : orderOf (sec8t84g6o_act K θ g) ∣ orderOf g := orderOf_map_dvd _ _
    have h2 : orderOf g = orderOf x := by rw [← hgx, Subgroup.orderOf_coe]
    rw [h2] at h1
    exact hodd.of_dvd_nat h1
  have hin : sec8t84g6o_act K θ g ∈ inner T :=
    CFSG.LieType.ChevTwo.OppCl.mem_inner_of_odd_orderOf_of_card_outer_dvd_two hO hord
  obtain ⟨t, ht⟩ := hin
  obtain ⟨s, hs⟩ : ∃ s : ↥K, θ (QuotientGroup.mk s) = t := by
    obtain ⟨u, rfl⟩ := θ.surjective t
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective u
    exact ⟨s, rfl⟩
  have hsN : (s : G) ∈ normalizer (K : Set G) := Subgroup.le_normalizer s.2
  have h3 : sec8t84g6o_act K θ ⟨(s : G), hsN⟩ = sec8t84g6o_act K θ g := by
    rw [sec8t84g6o_act_apply_of_mem K θ s.2, ← ht]
    simp [hs]
  have h5 : sec8t84g6o_act K θ ((⟨(s : G), hsN⟩ : normalizer (K : Set G))⁻¹ * g) = 1 := by
    rw [map_mul, map_inv, h3, inv_mul_cancel]
  have h6 := (sec8t84g6o_act_eq_one_iff K θ _).mp h5
  have h7 : (((⟨(s : G), hsN⟩ : normalizer (K : Set G))⁻¹ * g : normalizer (K : Set G)) : G) =
      (s : G)⁻¹ * x := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hgx]
  rw [h7] at h6
  have hx' : x = (s : G) * ((s : G)⁻¹ * x) := by group
  rw [hx']
  exact Subgroup.mul_mem_sup s.2 h6

theorem sec8t84g_om5Out : Sec8T84FactOm5Out := by
  intro G _ _ K hK x hx hodd
  have hsimple : IsSimpleGroup (↥K ⧸ CFSG.oddCore ↥K) :=
    sec8t84g6_simple_of_shape (Or.inl hK.2)
  haveI : Group.IsPerfect ↥K := hK.1.1
  have hcen : center ↥K = CFSG.oddCore ↥K := center_eq_oddCore_of_simple hK.1 hsimple
  have hle : Nat.card (Outer (↥K ⧸ CFSG.oddCore ↥K)) ≤ 2 :=
    ff_card_outer_le_two_of_lieModel_psp hK.2
  have hpos : 0 < Nat.card (Outer (↥K ⧸ CFSG.oddCore ↥K)) := Nat.card_pos
  have hO : Nat.card (Outer (↥K ⧸ CFSG.oddCore ↥K)) ∣ 2 := by
    rcases (by omega : Nat.card (Outer (↥K ⧸ CFSG.oddCore ↥K)) = 1 ∨
        Nat.card (Outer (↥K ⧸ CFSG.oddCore ↥K)) = 2) with h | h
    · rw [h]; exact one_dvd _
    · rw [h]
  exact sec8t84g6o_mem_sup_of_odd (QuotientGroup.quotientMulEquivOfEq hcen) hO hx hodd

end CFSG.OddStandard.SmallF3.Omega
