module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ComponentOrder
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.FS79Thm13Guarded

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus

open scoped commutatorElement
open Subgroup Relation CFSG.Blueprint CFSG.Blueprint.NativeSporadic
  CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Solomon78

variable {G : Type} [Group G]

theorem commutator_conj_eq_bot_of_ne [Finite G] {L : Subgroup G} {s t : G} (hst : s * t = t * s)
    (hL : IsCompIn L (centralizer ({t} : Set G)))
    (hLe : L.map (MulAut.conj s).toMonoidHom ≠ L) :
    ⁅L, L.map (MulAut.conj s).toMonoidHom⁆ = ⊥ := by
  rw [commutator_eq_bot_iff_le_centralizer]
  intro b hb
  rw [mem_centralizer_iff]
  intro a ha
  exact (commute_conj_of_ne hst hL hLe b hb a ha).symm

theorem maximalF_of_links [Finite G] (h13 : FS79Thm13UseSec G)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G) {N : Subgroup G}
    (hN : FStarSimple N) (hperf : ∀ P : Subgroup G, ⁅P, P⁆ = P → P ≤ N) {M : Subgroup G}
    (hM : InLF M) (hMq : IsSporadic (↥M ⧸ center ↥M) .HS)
    (hlink : ∀ K L : Subgroup G, ∀ s t : G, orderOf s = 2 → orderOf t = 2 → s * t = t * s →
      IsCompIn K (centralizer ({s} : Set G)) → IsCompIn L (centralizer ({t} : Set G)) →
      K ≤ L ⊔ L.map (MulAut.conj s).toMonoidHom → IsSporadic (↥K ⧸ center ↥K) .HS →
      K = L ∨ (L.map (MulAut.conj s).toMonoidHom ≠ L ∧ IsSporadic (↥L ⧸ center ↥L) .HS))
    (hrk : ∀ K : Subgroup G, IsSporadic (↥K ⧸ center ↥K) .HS → CFSG.pRank 2 ↥K ≠ 1) :
    MaximalF M := by
  obtain ⟨M', hM', hmax', -⟩ := exists_maximalF_above hM
  rcases hM' with rfl | hchain
  · exact hmax'
  have key : ∀ K : Subgroup G, TransGen LtF M K → IsSporadic (↥K ⧸ center ↥K) .HS ∧
      (K = M ∨ ∃ g : G, K.map (MulAut.conj g).toMonoidHom ≠ K ∧
        ⁅K, K.map (MulAut.conj g).toMonoidHom⁆ = ⊥) := by
    intro K hK
    induction hK with
    | single h =>
      obtain ⟨s, t, hs, ht, hst, hK₀, hL, hKL⟩ := h
      rcases hlink _ _ s t hs ht hst hK₀ hL hKL hMq with heq | ⟨hne, hq⟩
      · subst heq
        exact ⟨hMq, Or.inl rfl⟩
      · exact ⟨hq, Or.inr ⟨s, hne, commutator_conj_eq_bot_of_ne hst hL hne⟩⟩
    | tail _ h ih =>
      obtain ⟨hq, hor⟩ := ih
      obtain ⟨s, t, hs, ht, hst, hK₀, hL, hKL⟩ := h
      rcases hlink _ _ s t hs ht hst hK₀ hL hKL hq with heq | ⟨hne, hq'⟩
      · subst heq
        exact ⟨hq, hor⟩
      · exact ⟨hq', Or.inr ⟨s, hne, commutator_conj_eq_bot_of_ne hst hL hne⟩⟩
  obtain ⟨hq', hor'⟩ := key M' hchain
  have hstd : StdBare M' := h13.at hkp N hN hperf M' hmax' (hrk M' hq')
  rcases hor' with rfl | ⟨g, -, hcomm⟩
  · exact hmax'
  · exact absurd hcomm (hstd.1 g)

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus
