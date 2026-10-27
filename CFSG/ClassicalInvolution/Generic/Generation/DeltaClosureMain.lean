module

public import CFSG.ClassicalInvolution.Balance.Delta
public import CFSG.ClassicalInvolution.Generic.Generation.DeltaClosureStep

public section

namespace CFSG.ClassicalInvolution.Generic.DeltaClosure

open CFSG.Open

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {A : Subgroup G} {S : Set (Subgroup G)}

theorem mem_omegaStar_of_omegaConnected (hΩ : InClass p f Ω) (hF : FrameSide p f Ω A S)
    (hconn : OmegaConnected Ω) {L : Subgroup G} (hLΩ : L ∈ Ω) : L ∈ omegaStar p f Ω A S := by
  obtain ⟨K₀, hK₀⟩ := hF.nonempty
  obtain ⟨z, hzA, hz⟩ := hF.involution K₀ hK₀
  have hK₀s : K₀ ∈ omegaStar p f Ω A S :=
    ⟨hF.subset hK₀, 1, one_mem _, K₀, hK₀, z, hzA, hz, by simpa using hz⟩
  have key : ∀ L', Relation.ReflTransGen (fun M N : Subgroup G => N ∈ Ω ∧ Commutes M N) K₀ L' →
      L' ∈ omegaStar p f Ω A S := by
    intro L' hpath
    induction hpath with
    | refl => exact hK₀s
    | tail _ hbc ih => exact mem_omegaStar_of_commutes hΩ hF ih hbc.1 hbc.2
  exact key L (hconn K₀ (hF.subset hK₀) L hLΩ)

theorem rankThreeSpan_eq_top (hΩ : InClass p f Ω) (hF : FrameSide p f Ω A S)
    (hconn : OmegaConnected Ω) : rankThreeSpan A = ⊤ := by
  refine top_unique ?_
  rw [← hΩ.generated]
  exact iSup₂_le fun _ hLΩ => le_rankThreeSpan_of_mem_omegaStar hΩ hF
    (mem_omegaStar_of_omegaConnected hΩ hF hconn hLΩ)

theorem fusionGenerated_of_deltaClosure (hΩ : InClass p f Ω) (hF : FrameSide p f Ω A S)
    (hconn : OmegaConnected Ω) : CFSG.ClassicalInvolution.Balance.FusionGenerated A :=
  CFSG.ClassicalInvolution.Balance.fusionGenerated_of_centralizer_generated
    (rankThreeSpan_eq_top hΩ hF hconn)

end CFSG.ClassicalInvolution.Generic.DeltaClosure
