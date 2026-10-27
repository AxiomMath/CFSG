module

public import CFSG.CGT.Foote81L6.OddQuot
public import CFSG.CGT.Foote81L6.TheoremOne

public section

namespace CFSG.CGT.Foote81L6

open Subgroup

@[expose] def FooteLemma11 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Sylow 2 G) (n : ℕ) (D : FooteData G T 2 n),
    ¬ StronglyInvolutionClosed D.A T → ¬ StronglyInvolutionClosed D.Astar T →
      ∀ g : G, g * D.a * g⁻¹ ∈ (T : Subgroup G) → g * D.a * g⁻¹ = D.a

@[expose] def FooteFinal : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Sylow 2 G) (n : ℕ) (D : FooteCore G T 2 n),
    D.a ∈ center G → StronglyInvolutionClosed D.A T ∨ StronglyInvolutionClosed D.Astar T

theorem footeCaseFour_of (hL11 : FooteLemma11) (hFin : FooteFinal) : FooteCaseFour := by
  intro G _ _ T n D
  by_contra hneither
  push Not at hneither
  obtain ⟨hnA, hnAs⟩ := hneither
  have hiso := hL11 G T n D hnA hnAs
  have hzZ : (⟨D.a, D.a_mem_T⟩ : (T : Subgroup G)) ∈ Subgroup.center (T : Subgroup G) :=
    Subgroup.mem_center_iff.2 fun y => Subtype.ext (D.a_comm_T y.2)
  have hz : orderOf (⟨D.a, D.a_mem_T⟩ : (T : Subgroup G)) = 2 := by
    rw [Subgroup.orderOf_mk, D.a_order]
  have hwc : ∀ g : G, g⁻¹ * D.a * g ∈ (T : Subgroup G) → g⁻¹ * D.a * g = D.a := by
    intro g hg
    have := hiso g⁻¹ (by rwa [inv_inv])
    rwa [inv_inv] at this
  obtain ⟨-, hcen⟩ := CFSG.Adapters.glauberman_zStar T ⟨D.a, D.a_mem_T⟩ hzZ hz hwc
  have hO : Odd (Nat.card (CFSG.oddCore G)) := CFSG.Holt.StarLemma26.odd_card_oddCore G
  let Tbar : Sylow 2 (G ⧸ CFSG.oddCore G) :=
    T.mapSurjective (QuotientGroup.mk'_surjective (CFSG.oddCore G))
  have hinj := D.mk_eq_one_of_odd hO
  rcases hFin (G ⧸ CFSG.oddCore G) Tbar n (D.oddQuot hO).toFooteCore hcen with h | h
  · exact hnA (stronglyInvolutionClosed_of_map_of_injOn _ hinj D.A_le_T h)
  · have h' : StronglyInvolutionClosed (D.Astar.map (QuotientGroup.mk' (CFSG.oddCore G)))
        ((T : Subgroup G).map (QuotientGroup.mk' (CFSG.oddCore G))) := by
      rw [← D.Astar_oddQuot hO]
      exact h
    exact hnAs (stronglyInvolutionClosed_of_map_of_injOn _ hinj D.Astar_le_T h')

end CFSG.CGT.Foote81L6
