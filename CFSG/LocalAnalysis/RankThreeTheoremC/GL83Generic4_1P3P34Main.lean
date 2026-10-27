module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3P34Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1P34b
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3M11Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

theorem isGenericPoint_of_abelian (hS : Setting G) (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G}
    {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M) (hPab : IsMulCommutative (P : Subgroup G))
    {u : G} (huP : u ∈ (P : Subgroup G)) (hu1 : u ≠ 1) (hu3 : u ^ 3 = 1)
    (hCu : ¬ centralizer ({u} : Set G) ≤ M) : IsGenericPoint 3 P M u := by
  have hprime : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hprime⟩
  obtain ⟨hPM, hP3⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  have hPC : (P : Subgroup G) ≤ centralizer ({u} : Set G) := fun g hg =>
    mem_centralizer_singleton_iff.mpr (p34_comm_of_isMulCommutative hPab hg huP)
  have hinf : (P : Subgroup G) ⊓ centralizer ({u} : Set G) = (P : Subgroup G) :=
    inf_eq_left.mpr hPC
  have hsyl : IsSylowOf 3 (P : Subgroup G) (centralizer ({u} : Set G)) :=
    ⟨P.subtype hPC, by rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hPC]⟩
  refine ⟨huP, ⟨hPM huP, hu1, hu3, ?_, hCu⟩, ?_, ?_⟩
  · exact hP3.ge.trans (pRank_mono 3 hprime.one_lt hPC)
  · rw [hinf]
    exact hsyl
  · rw [hinf]
    exact hP3

theorem lemma42_of_fusion_abelian (hS : Setting G) (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G}
    {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M) {x : G} (hxP : x ∈ (P : Subgroup G))
    (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1) (hPab : IsMulCommutative (P : Subgroup G))
    (hwc : LineWeaklyClosed x (P : Subgroup G))
    (hfus : ∀ u : G, IsGenericPoint 3 P M u →
      LinesNotWeaklyClosed 3 u ((P : Subgroup G) ⊓ centralizer ({u} : Set G))) :
    M11Lemma42 3 P M x := by
  intro U hUP hU hUc hxU u huU hux
  by_contra hCu
  have huP : u ∈ (P : Subgroup G) := hUP huU
  have hu1 : u ≠ 1 := fun h => hux (h ▸ one_mem _)
  have hu3 : u ^ 3 = 1 := hU.2 u huU
  have hgen := isGenericPoint_of_abelian hS hp hM hPab huP hu1 hu3 hCu
  have hPC : (P : Subgroup G) ≤ centralizer ({u} : Set G) := fun g hg =>
    mem_centralizer_singleton_iff.mpr (p34_comm_of_isMulCommutative hPab hg huP)
  have hinf : (P : Subgroup G) ⊓ centralizer ({u} : Set G) = (P : Subgroup G) :=
    inf_eq_left.mpr hPC
  have hxQ : x ∈ (P : Subgroup G) ⊓ centralizer ({u} : Set G) := ⟨hxP, hPC hxP⟩
  have hne : zpowers x ≠ zpowers u := fun h => hux (h ▸ mem_zpowers u)
  have hcomm : ⁅Subgroup.closure {z : G | z ∈ (P : Subgroup G) ⊓ centralizer ({u} : Set G) ∧
      z ^ 3 = 1}, Subgroup.closure {z : G | z ∈ (P : Subgroup G) ⊓ centralizer ({u} : Set G) ∧
      z ^ 3 = 1}⁆ = ⊥ := by
    have hle : Subgroup.closure {z : G | z ∈ (P : Subgroup G) ⊓ centralizer ({u} : Set G) ∧
        z ^ 3 = 1} ≤ (P : Subgroup G) := by
      rw [Subgroup.closure_le]
      intro z hz
      exact hz.1.1
    refine eq_bot_iff.mpr (Subgroup.commutator_le.mpr fun a ha b hb => ?_)
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact p34_comm_of_isMulCommutative hPab (hle ha) (hle hb)
  have hne' : zpowers x ≠ ⁅Subgroup.closure {z : G | z ∈ (P : Subgroup G) ⊓
      centralizer ({u} : Set G) ∧ z ^ 3 = 1}, Subgroup.closure {z : G | z ∈ (P : Subgroup G) ⊓
      centralizer ({u} : Set G) ∧ z ^ 3 = 1}⁆ := by
    rw [hcomm]
    exact fun h => hx1 (Subgroup.zpowers_eq_bot.mp h)
  exact hfus u hgen x hxQ hx1 hx3 hne hne' (by rw [hinf]; exact hwc)

end CFSG.LocalAnalysis.RankThreeTheoremC
