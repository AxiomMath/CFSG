module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.G23Facts
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.ModelDef

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec1Proof

open CFSG.OddStandard.HigherRank.G2Three.Sec1 Subgroup
open scoped Pointwise

theorem conj_smul_eq_map {G : Type} [Group G] (g : G) (H : Subgroup G) :
    MulAut.conj g • H = H.map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [mem_smul_pointwise_iff_exists, Subgroup.mem_map]
  rfl

theorem g23Facts_of_inputs
    (hM : ∀ (Q : Type) [Group Q] [Finite Q], HRG23 Q →
      ∃ m : G23Model (MulAut Q), m.L = innerAut Q)
    (hF : ∀ (G : Type) [Group G] [Finite G] (m : G23Model G), (frameOf m).Facts m.L) :
    G23Facts := by
  intro Q _ _ hQ P
  obtain ⟨m, hL⟩ := hM Q hQ
  have hsyl : IsSylowIn 2 ⊤ (frameOf m).Sσ := (hF (MulAut Q) m).1.2.2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hp, hidx⟩ := hsyl
  rw [relIndex_top_right] at hidx
  let P₀ : Sylow 2 (MulAut Q) := hp.toSylow hidx
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (MulAut Q) P₀ P
  refine ⟨frameOf (twist g m), ?_, ?_⟩
  · rw [frameOf_twist, frameMap_Sσ, ← conj_smul_eq_map]
    have h1 : ((g • P₀ : Sylow 2 (MulAut Q)) : Subgroup (MulAut Q)) =
        MulAut.conj g • (frameOf m).Sσ := rfl
    rw [← h1, hg]
  · have := hF (MulAut Q) (twist g m)
    rwa [show (twist g m).L = innerAut Q from hL] at this

end CFSG.OddStandard.HigherRank.G2Three.Sec1Proof
