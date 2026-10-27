module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115AltSix

public section

namespace CFSG.QuasithinUnique.Ch1

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.QuasithinUnique

@[expose] def OddAutInner : Prop :=
  ∀ (K : Type) [Group K] [Finite K], OddList K → ¬ Nonempty (K ≃* alternatingGroup (Fin 6)) →
    ∀ β : K ≃* K, (∀ x, β (β x) = x) → (∃ P : Sylow 2 K, ∀ t ∈ (P : Subgroup K), β t = t) →
      CharTwo (fixedSubgroup β) → IsInnerAut β

@[expose] def OddInvolutionCentralizers : Prop :=
  ∀ (K : Type) [Group K] [Finite K], OddList K → ¬ Nonempty (K ≃* alternatingGroup (Fin 6)) →
    ∀ t : K, t ≠ 1 → t * t = 1 → CharTwo (Subgroup.centralizer ({t} : Set K)) →
      StatedClassicalModel K .PSL 3 3 1 ∨ StatedClassicalModel K .PSU 3 3 1 ∨
        ∃ p : ℕ, IsFermatOrMersennePrime p ∧ StatedClassicalModel K .PSL 2 p 1

theorem simpleInspection_oddList
    (hA : OddAutInner) (hC : OddInvolutionCentralizers) :
    SimpleInspection OddList := by
  intro K _ _ β h hz hK
  by_cases h6 : Nonempty (K ≃* alternatingGroup (Fin 6))
  · exact simpleInspection_altSix K β h hz h6
  · obtain ⟨l, hl⟩ := hA K hK h6 β h.involutory h.sylow h.charTwo
    obtain ⟨hl1, hll⟩ := h.involution_of_inner hz hl
    have hc : CharTwo (Subgroup.centralizer ({l} : Set K)) := by
      rw [← fixedSubgroup_eq_centralizer hl]
      exact h.charTwo
    rcases hC K hK h6 l hl1 hll hc with h3 | hu | ⟨p, hp, hm⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inl h3, l, hl⟩))))
    · exact Or.inl ⟨h.isSimpleGroup hz, Or.inr (Or.inr hu), l, hl⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inr ⟨p, hp, hm⟩, l, hl⟩))))

end CFSG.QuasithinUnique.Ch1
