module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.OrdinaryProofs.SylowTransport
public import CFSG.Monster.Generated.FiniteSimple
import CFSG.Sporadic.Bridge.Y322Central
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentSporDefs

public section

namespace CFSG.AGLEmbedding.Norton.OrdinaryProofs

open CFSG.Open
open CFSG.Monster.Generated

theorem GLBCore_anti {p k k' : ℕ} {G : Type*} [Group G] [Finite G] (h : k ≤ k')
    (P : Subgroup G) : GLBCore p k' P ≤ GLBCore p k P := by
  unfold GLBCore
  refine sSup_le_sSup ?_
  rintro N ⟨Q, hQ, hk, rfl⟩
  exact ⟨Q, hQ, le_trans h hk, rfl⟩

theorem sporGammaOneAt_M_thirteen_of_core_two
    (e : CFSG.Blueprint.NativeSporadic.Carrier .M ≃* Gmat)
    (c13 : ∀ S : Sylow 13 Gmat,
      @GLBCore Gmat _ generated_rational_group_finite_simple.2.2 13 2 (S : Subgroup Gmat) = ⊤) :
    CFSG.AGLEmbedding.SporGammaOneAt .M 13 := by
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have : Finite Gmat := generated_rational_group_finite_simple.2.2
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Y443.nonempty_mulEquiv
  intro K _ _ ⟨φ⟩ T
  have h2 : GLBCore 13 2 (T : Subgroup K) = ⊤ :=
    GLBCore_top_forall_sylow_map (φ.trans (b.symm.trans e)).symm c13 T
  have hanti := GLBCore_anti (p := 13) (k := 1) (k' := 2) (by norm_num) (T : Subgroup K)
  rw [h2] at hanti
  exact top_le_iff.mp hanti

end CFSG.AGLEmbedding.Norton.OrdinaryProofs

end
