module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParTwoPar

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar

open CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.Open
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen

variable {S S' : Type} [Group S] [Group S']

theorem TwoPar.map (e : S ≃* S') {T P₁ P₂ : Subgroup S} (h : TwoPar S T P₁ P₂) :
    TwoPar S' (T.map e.toMonoidHom) (P₁.map e.toMonoidHom) (P₂.map e.toMonoidHom) := by
  set φ : Subgroup S ≃o Subgroup S' := e.mapSubgroup with hφ
  have hφa : ∀ X : Subgroup S, φ X = X.map e.toMonoidHom := fun X => rfl
  have hN : Subgroup.normalizer ((φ T : Subgroup S') : Set S') =
      φ (Subgroup.normalizer (T : Set S)) := (Subgroup.map_equiv_normalizer_eq T e).symm
  have hpe : ∀ P : Subgroup S, pElementSubgroup 2 (φ P) = φ (pElementSubgroup 2 P) :=
    fun P => pElementSubgroup_map_equiv e P
  show TwoPar S' (φ T) (φ P₁) (φ P₂)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try rw [hN]
  · rw [hφa]; exact isSylowTwoOf_top_map_equiv e h.sylow
  · exact φ.lt_iff_lt.2 h.lt₁
  · exact φ.lt_iff_lt.2 h.lt₂
  · intro Q' hQ1 hQ2
    obtain ⟨Q, rfl⟩ := φ.surjective Q'
    rcases h.atom₁ Q (φ.le_iff_le.1 hQ1) (φ.le_iff_le.1 hQ2) with e1 | e1
    · exact Or.inl (by rw [e1])
    · exact Or.inr (by rw [e1])
  · intro Q' hQ1 hQ2
    obtain ⟨Q, rfl⟩ := φ.surjective Q'
    rcases h.atom₂ Q (φ.le_iff_le.1 hQ1) (φ.le_iff_le.1 hQ2) with e1 | e1
    · exact Or.inl (by rw [e1])
    · exact Or.inr (by rw [e1])
  · exact fun e1 => h.ne (φ.injective e1)
  · exact fun e1 => h.top₁ (φ.injective (by rw [e1]; exact (φ.map_top).symm))
  · exact fun e1 => h.top₂ (φ.injective (by rw [e1]; exact (φ.map_top).symm))
  · intro Y' hY
    obtain ⟨Y, rfl⟩ := φ.surjective Y'
    rcases h.hover Y (φ.le_iff_le.1 hY) with e1 | e1 | e1 | e1
    · exact Or.inl (by rw [e1])
    · exact Or.inr (Or.inl (by rw [e1]))
    · exact Or.inr (Or.inr (Or.inl (by rw [e1])))
    · exact Or.inr (Or.inr (Or.inr (by rw [e1]; exact φ.map_top)))
  · intro X' hX hX'
    obtain ⟨X, rfl⟩ := φ.surjective X'
    have hXt : X ≠ ⊤ := fun e1 => hX' (by rw [e1]; exact φ.map_top)
    rcases h.cover X (φ.le_iff_le.1 hX) hXt with e1 | e1
    · exact Or.inl (φ.le_iff_le.2 e1)
    · exact Or.inr (φ.le_iff_le.2 e1)
  · intro X' hX hXP hXn
    obtain ⟨X, rfl⟩ := φ.surjective X'
    rw [hpe]
    exact φ.le_iff_le.2 (h.ov₁ X (φ.le_iff_le.1 hX) (φ.le_iff_le.1 hXP)
      (fun e1 => hXn (φ.le_iff_le.2 e1)))
  · intro X' hX hXP hXn
    obtain ⟨X, rfl⟩ := φ.surjective X'
    rw [hpe]
    exact φ.le_iff_le.2 (h.ov₂ X (φ.le_iff_le.1 hX) (φ.le_iff_le.1 hXP)
      (fun e1 => hXn (φ.le_iff_le.2 e1)))
  · rw [hpe, ← OrderIso.map_sup]
    exact φ.le_iff_le.2 h.gen₁
  · rw [hpe, ← OrderIso.map_sup]
    exact φ.le_iff_le.2 h.gen₂
  · exact Ch1.charTwo_map_mulEquiv e h.ct₁
  · exact Ch1.charTwo_map_mulEquiv e h.ct₂

theorem TwoPar.exists_of_equiv [Finite S'] (e : S ≃* S') {T P₁ P₂ : Subgroup S}
    (h : TwoPar S T P₁ P₂) {T' : Subgroup S'} (hT' : IsSylowTwoOf T' ⊤) :
    ∃ P₁' P₂' : Subgroup S', TwoPar S' T' P₁' P₂' := by
  have h1 := h.map e
  obtain ⟨g, hg⟩ := exists_conj_of_sylowTwo h1.sylow hT'
  rw [← hg]
  have h2 := h1.map (MulAut.conj g)
  exact ⟨_, _, h2⟩

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar
