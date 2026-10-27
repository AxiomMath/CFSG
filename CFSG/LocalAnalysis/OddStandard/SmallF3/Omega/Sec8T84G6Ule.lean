module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G6Cor
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G6Ex
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G6Rk

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec8t84g_U_le_K (F : Sec8T84Base) (hGi : Sec8T84FactGamInner)
    (hO5 : Sec8T84FactOm5Out) {G : Type} [Group G] [Finite G] {t : G}
    {L S : Subgroup G} {z g : G} {B : Subgroup G} (hctx : Sec8Ctx G t L S z g B) {γ : G}
    (hγS : γ ∈ S) (hγ2 : orderOf γ = 2) (hout : InducesOutsideGStar L 6 (-1) γ)
    {K U : Subgroup G} (hK : IsComponentIn K (centralizer ({γ} : Set G))) (hKF : InFStar K)
    (hK0 : layerCent L γ ≤ K) (hKN : (K.subgroupOf (centralizer ({γ} : Set G))).Normal)
    (hU : IsElemAb2 U 4) (hUγ : U ≤ centralizer ({γ} : Set G))
    (htU : t ∈ normalizer (U : Set G)) (hUt : U ⊓ centralizer ({t} : Set G) ≤ L)
    {y : G} (hy : Odd (orderOf y)) (hyγ : y ∈ centralizer ({γ} : Set G))
    (hyU : y ∈ normalizer (U : Set G)) (hyfix : ∀ u ∈ U, y * u = u * y → u = 1) :
    U ≤ K := by
  have hγ2' : γ * γ = 1 := by
    have h := pow_orderOf_eq_one γ
    rw [hγ2, pow_two] at h
    exact h
  have hγ1 : γ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hγ2
    exact absurd hγ2 (by norm_num)
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [hctx.involution, pow_two] at h
    exact h
  have htC : t ∈ centralizer ({γ} : Set G) :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp (hctx.sylow.1 hγS)).symm
  have hLM : IsOm6M L := ⟨hctx.component.isQuasisimple, hctx.omega6m⟩
  have hKq : IsQuasisimple ↥K := hK.isQuasisimple
  have hKC : K ≤ centralizer ({γ} : Set G) := hK.le
  have hCN : centralizer ({γ} : Set G) ≤ normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKC).mp hKN
  have hno := sec8t84g6_not_extra F.hAutF hGi hLM hγ2' hout hKq hCN hK0 hU hUγ htC ht2 htU hUt
  have hKF' : InF K := by
    unfold InFStar IsFStarGroup at hKF
    rcases hKF with hF | ⟨-, hQ⟩
    · exact hF
    · exfalso
      apply hno
      unfold SmallF3StarQuotient at hQ
      rcases hQ with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
  have hno' : ¬ (IsU33 K ∨ IsL29 K) := fun h => hno (by
    rcases h with h | h
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inl h)
  have hSet : Sec3SettingLB G γ K := sec3SettingLB_of_component hctx.toSec3SettingLB hγ2 hK hKF'
  have h56 : IsOm5Q K ∨ IsOm6M K := by
    rcases F.hShapes G γ K hSet with h5 | h6p | h6m
    · exact Or.inl ⟨hKq, h5⟩
    · exact (F.h6p G γ K hSet h6p).elim
    · exact Or.inr ⟨hKq, h6m⟩
  have hsimple : IsSimpleGroup (↥K ⧸ CFSG.oddCore ↥K) := by
    refine sec8t84g6_simple_of_shape ?_
    rcases h56 with h | h
    · exact Or.inl h.2
    · exact Or.inr (Or.inl h.2)
  have hZ := sec8t84g6_center_odd hKq hsimple
  have hyN : y ∈ normalizer (K : Set G) := hCN hyγ
  have hyInner : InnerOn K y := by
    rcases h56 with h | h
    · exact hO5 G K h y hyN hy
    · exact F.hM.out_two G K h y hyN hy
  have hyK : ∃ k ∈ K, ∃ c ∈ centralizer (K : Set G), y = k * c := by
    have hle : centralizer (K : Set G) ≤ normalizer (K : Set G) := fun x hx =>
      Subgroup.centralizer_le_normalizer _ hx
    have hmem : y ∈ K ⊔ centralizer (K : Set G) := hyInner
    rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left K _ hle] at hmem
    obtain ⟨k, hk, c, hc, hkc⟩ := Set.mem_mul.mp hmem
    exact ⟨k, hk, c, hc, hkc.symm⟩
  have hrank := sec8t84g6_rank F.h64 hSet (F.hH62 G γ K hSet) ⟨γ, hγ2, hK⟩ hKF hno'
  have hyU' : ∀ u ∈ U, y * u * y⁻¹ ∈ U := fun u hu =>
    (Subgroup.mem_normalizer_iff.mp hyU u).mp hu
  exact sec8t84g6_core hKC hCN hZ hU.1 hUγ hγ2' hγ1 hy hyγ hyU' hyfix hyK hrank

end CFSG.OddStandard.SmallF3.Omega
