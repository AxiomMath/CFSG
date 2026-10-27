module

public import CFSG.GH74.Generic.S1.SymNbhd
public import CFSG.GH74.Generic.S45.LLift
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.L5U5 CFSG.ABGLocalTools CFSG.Blueprint CFSG.GH74.GLS Subgroup
open scoped commutatorElement

theorem b_S45_liftCentral_of_core
    (h : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) → Gen4 G → KGH G →
      ∀ (x : G), orderOf x = 2 → ∀ (K : Subgroup (CentralizerBar x)), IsComponent K → IsJ1OrRee ↥K →
        xbar x ∉ K → 3 ≤ pRank 2 G → (∀ S : Sylow 2 G, ¬ IsMulCommutative (S : Subgroup G)) →
        IsJMax x K → ¬ HasTwoThinConfiguration G →
        ∀ n ∈ S1.liftL x K, proj x n = 1 → ∀ l ∈ S1.liftL x K, n * l = l * n) :
    B_S45_liftCentral := by
  intro G _ _ hs hn hgen hKGH x hx K hKc hj hnot T hT P hPK hPperf _ z hzP hz1 g hgP
  have hPC : P ≤ centralizer ({x} : Set G) := fun p hp => (hPK hp).1
  set P' : Subgroup ↥(centralizer ({x} : Set G)) := P.subgroupOf (centralizer ({x} : Set G)) with hP'
  have hP'K : P' ≤ K.comap (proj x) := by
    intro p hp
    have hp' : (p : G) ∈ P := hp
    have h1 := (hPK hp').2
    rw [piC_of_mem x p.2] at h1
    exact h1
  have hP'perf : ⁅P', P'⁆ = P' := by
    apply Subgroup.map_injective (centralizer ({x} : Set G)).subtype_injective
    rw [Subgroup.map_commutator]
    have h2 : P'.map (centralizer ({x} : Set G)).subtype = P := by
      rw [hP', Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hPC]
    rw [h2, hPperf]
  have hP'L : P' ≤ S1.liftL x K := S1.perfect_le_liftL hP'K hP'perf
  have hzC := hPC hzP
  have hgC := hPC hgP
  have hz' : (⟨z, hzC⟩ : ↥(centralizer ({x} : Set G))) ∈ S1.liftL x K := hP'L hzP
  have hg' : (⟨g, hgC⟩ : ↥(centralizer ({x} : Set G))) ∈ S1.liftL x K := hP'L hgP
  have hz1' : proj x ⟨z, hzC⟩ = 1 := by rw [← piC_of_mem x hzC]; exact hz1
  exact congrArg Subtype.val
    (h G hs hn hgen hKGH x hx K hKc hj hnot hT.rank hT.nonabSylow hT.jmax hT.nothin _ hz' hz1' _ hg')

end CFSG.GH74.Generic.S45
