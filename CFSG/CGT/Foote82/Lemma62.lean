module

public import CFSG.CGT.Foote82.Lemma62Faithful
public import CFSG.CGT.Foote82.Lemma62Endgame

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11

theorem lemma62_aux (n : ℕ) :
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
      (G S L K : Subgroup (GLV V)), Conf62 G S L K → Nat.card K = n → ⁅K, L⁆ = ⊥ := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro V _ _ _ G S L K hc hn
  by_contra hne
  have hmin : Min62 S L K := by
    intro K' hK' hSK' hLK'
    refine IH (Nat.card K') ?_ V G S L K' ⟨hc.setup, hK'.le.trans hc.K_le, ?_, hSK', hLK'⟩ rfl
    · rw [← hn]
      exact Subgroup.card_lt_of_lt hK'
    · exact Odd.of_dvd_nat hc.odd (Subgroup.card_dvd_of_le hK'.le)
  obtain ⟨V₀, _, _, _, G₀, S₀, L₀, K₀, hc₀, -, hne₀, hcard₀, hfix₀⟩ := hc.reduce hmin hne
  obtain ⟨G', s, p, hcore⟩ := exists_core hc₀
    (fun G' S' L' K' hc' hlt => IH (Nat.card K') (by omega) V₀ G' S' L' K' hc' rfl) hne₀ hfix₀
  exact hcore.false

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem lemma62 {G S L K : Subgroup (GLV V)} (h : Setup6 G S L) (hKG : K ≤ G)
    (hK : Odd (Nat.card K)) (hSK : S ≤ Subgroup.normalizer (K : Set (GLV V)))
    (hLK : L ≤ Subgroup.normalizer (K : Set (GLV V))) : ⁅K, L⁆ = ⊥ :=
  lemma62_aux _ V G S L K ⟨h, hKG, hK, hSK, hLK⟩ rfl

end CFSG.CGT.Foote82
