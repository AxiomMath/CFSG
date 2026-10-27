module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs
public import CFSG.LieType.BorelTits.Basic
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.Tab

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab

open CFSG.OddStandard.HigherRank.G2Three.Sec1 Subgroup
open scoped commutatorElement

variable {Γ : Type} [Group Γ] {D : TabData} {elt : ℕ → Γ}

theorem pCoreOf_eq_of_sylow {p : ℕ} [Fact p.Prime] [Finite Γ] {H N : Subgroup Γ}
    (hS : IsSylowIn p H N) (hN : (N.subgroupOf H).Normal) : CFSG.Open.pCoreOf p H = N := by
  obtain ⟨hNH, hNp, hNindex⟩ := hS
  apply le_antisymm
  · have hNindex' : ¬ p ∣ (N.subgroupOf H).index := by
      simpa only [Subgroup.relIndex] using hNindex
    let NS : Sylow p ↥H := (hNp.comap_subtype (K := H)).toSylow hNindex'
    have hcore_le : CFSG.pCore p ↥H ≤ N.subgroupOf H :=
      IsPGroup.le_sylow_of_normal (CFSG.pCore_isPGroup (p := p) (G := ↥H)) NS
    have hmap := Subgroup.map_mono (f := H.subtype) hcore_le
    rw [Subgroup.map_subgroupOf_eq_of_le hNH] at hmap
    simpa [CFSG.Open.pCoreOf] using hmap
  · exact CFSG.LieType.BorelTits.le_pCoreOf p hNH hN hNp

end CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab