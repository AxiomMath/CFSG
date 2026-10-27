module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinIdentKind
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscData
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpWz
public import CFSG.ClassicalInvolution.Q3.Q3NLCtx

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG
open CFSG.Open hiding StatedLieTag
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.RouteD.Exotic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Q3.Disc3
  CFSG.ClassicalInvolution.Q3.Q3T7 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinIdent



section Orth

theorem orthTag_of_oneComp {X : Type} [Group X] [Finite X] {Λ : Set (Subgroup X)}
    (D : OmegaLieU 3 1 Λ) (hΛ : HypOmegaModU (.sl2 3 1) Λ) (hgen : omegaGen Λ = ⊤)
    (htrans : ∀ K ∈ Λ, ∀ L ∈ Λ, ∃ g : X, conjSub g K = L)
    (hK : ∃ K ∈ Λ, ∃ K' ∈ twinSet Λ K, K' ≠ K) (hcard : D.card = 1) (i : Fin D.card) :
    ∃ (tag : CFSG.Assembly.LowTwoRank.StatedLieTag) (k d : ℕ) (ε : Bool), 5 ≤ d ∧
      IsOrthTag d ε tag k ∧ CompIs 3 1 (D.kind i) tag k := by
  obtain ⟨K, hKΛ, K', hK'Λ, hne'⟩ := hK
  have hne : Λ.Nonempty := ⟨K, hKΛ⟩
  rcases D.valid i with ⟨t, k, e, ht, hadm, he, hc⟩ | ⟨h3, hc | hc⟩
  · have hcis : CompIs 3 1 (D.kind i) t k := ⟨e, he, ht, hadm, hc⟩
    have he1 : e = 1 := by
      rcases he with he | ⟨-, he⟩
      · exact he
      · omega
    subst he1
    let M := toIh8ModelSect D hΛ hgen hcard i ht hadm (Or.inl rfl) hc
    by_cases hG2d4 : t = .G2 ∨ t = .trialityD4
    · exact absurd (noTwins_of_g2d4_datum M htrans hG2d4 K hKΛ K' hK'Λ) hne'
    have hG2 : t ≠ .G2 := fun h => hG2d4 (Or.inl h)
    have hD4 : t ≠ .trialityD4 := fun h => hG2d4 (Or.inr h)
    obtain ⟨d, ε, hd, hdε⟩ := twinIdent_shape hΛ M hG2 hD4 ⟨K, hKΛ, K', hK'Λ, hne'⟩
    exact ⟨t, k, d, ε, hd, hdε, hcis⟩
  · exact absurd (top_mem_of_sl23_component_sect D hne hgen hcard i hc)
      (top_notMem_of_transitive3 htrans hKΛ hK'Λ.1 hne')
  · obtain ⟨e⟩ := exists_mulEquiv_m11_sect D hgen hcard i hc
    exact absurd (noTwins_of_mulEquiv_m11 e hΛ K hKΛ K' hK'Λ) hne'

end Orth

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
