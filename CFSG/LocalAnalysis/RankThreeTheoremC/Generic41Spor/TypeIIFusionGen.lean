module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TypeIICommon
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TypeIIStruct
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Fusion
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Lemma42Torus
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3S u3T u3ZT u3U0 U3LineWC KFactWeakClosureHeis
  GenericComponentClass u3_endgame TypeSE TypeTorusLift TypeTorusOnCenter FusionStruct
  fusion_core_gen u3_torus_lift_gen)

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}
  {J : Subgroup G} {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop}
  {Shape : ∀ {X : Type} [Group X], Subgroup X → Subgroup X → Subgroup X → Prop}

theorem typeSE_mcl : TypeSE IsMcLType 5 := by
  intro K _ _ hK
  exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hK.1, Or.inr (Or.inl hK.2)⟩)))),
    TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.McL, hK.2⟩

theorem typeSE_j4 : TypeSE IsJ4Type 11 := by
  intro K _ _ hK
  exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hK.1, hK.2⟩)))),
    TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.J4, hK.2⟩

theorem typeTorusOnCenter_of_transCenter (hp : p.Prime) (hX : ExtraFacts Typ p Shape) :
    TypeTorusOnCenter Typ p := by
  intro K _ _ hK T c hcT hcZ hc1 k hk
  haveI : Fact p.Prime := ⟨hp⟩
  have hcp : c ^ p = 1 := (hX.sylow K hK T).2.2 c hcT
  have hco : orderOf c = p := orderOf_eq_prime hcp hc1
  have hZin : ∀ z ∈ (T : Subgroup K), z ∈ Subgroup.centralizer ((T : Subgroup K) : Set K) →
      z ∈ Zin (T : Subgroup K) := by
    intro z hzT hzZ
    refine ⟨⟨z, hzT⟩, ?_, rfl⟩
    show (⟨z, hzT⟩ : ↥(T : Subgroup K)) ∈ Subgroup.center ↥(T : Subgroup K)
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hzZ g g.2)
  have hck : c ^ k ∈ (T : Subgroup K) := zpow_mem hcT k
  have hckZ : c ^ k ∈ Subgroup.centralizer ((T : Subgroup K) : Set K) :=
    Subgroup.zpow_mem _ hcZ k
  have hck1 : c ^ k ≠ 1 := by
    intro h
    have := orderOf_dvd_iff_zpow_eq_one.mpr h
    rw [hco] at this
    exact hk this
  obtain ⟨n, hn, hnc⟩ := hX.transCenter K hK T c (hZin c hcT hcZ) hc1 (c ^ k) (hZin _ hck hckZ) hck1
  exact ⟨n, hn, hnc⟩

theorem typeII_fusion_core_of_se (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G)
    (hK : TypeIIKFacts) (hX : ExtraFacts Typ p Shape) (hSE : TypeSE Typ p)
    (hc : PointConfig Typ G p P M x J) :
    (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G) ∧ U3LineWC x (P : Subgroup G) := by
  haveI : Fact p.Prime := ⟨hc.prime⟩
  have hA : FusionStruct p P x J := ⟨typeII_T_structure hX hc, typeII_S_decomp hX hc, typeII_U0_facts hX hc⟩
  have hTorQ : TypeTorusOnCenter Typ p := typeTorusOnCenter_of_transCenter hc.prime hX
  have hTor : TypeTorusLift p P x J := fun c hcT hcZ hc1 k hk => by
    obtain ⟨h, hhJ, -, hh⟩ := u3_torus_lift_gen hTorQ hc hcT hcZ hc1 k hk
    exact ⟨h, hhJ, hh⟩
  exact fusion_core_gen hS hD1 hK.sig hc hSE hA hTor

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
