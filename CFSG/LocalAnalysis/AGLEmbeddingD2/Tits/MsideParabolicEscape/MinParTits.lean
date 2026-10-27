module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113LieTits
public import CFSG.Quasithin.Recognition.CertTitsOvergroup
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParS
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParTwo

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar

open CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.Open
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen

section

variable {S : Type} [Group S]

theorem le_pElementSubgroup_of_atom {T P : Subgroup S} (hT2 : IsPGroup 2 T)
    (hN : Subgroup.normalizer (T : Set S) = T) (hTP : T < P)
    (hatom : ∀ Q : Subgroup S, T ≤ Q → Q ≤ P → Q = T ∨ Q = P) : P ≤ pElementSubgroup 2 P := by
  have h1 : T ≤ pElementSubgroup 2 P := le_pElementSubgroup_of_isPGroup hTP.le hT2
  rcases hatom _ h1 (pElementSubgroup_le P) with e | e
  · exfalso
    have : P ≤ Subgroup.normalizer (pElementSubgroup 2 P : Set S) :=
      Subgroup.le_normalizer.trans (CFSG.AGLEmbeddingD2.GN.normalizer_le_normalizer_pElementSubgroup 2 P)
    rw [e, hN] at this
    exact hTP.not_ge this
  · exact e.ge

theorem TwoParLat.of_atoms {T P₁ P₂ : Subgroup S} (sylow : IsSylowTwoOf T ⊤)
    (normT : Subgroup.normalizer (T : Set S) = T) (lt₁ : T < P₁) (lt₂ : T < P₂)
    (atom₁ : ∀ Q : Subgroup S, T ≤ Q → Q ≤ P₁ → Q = T ∨ Q = P₁)
    (atom₂ : ∀ Q : Subgroup S, T ≤ Q → Q ≤ P₂ → Q = T ∨ Q = P₂) (ne : P₁ ≠ P₂)
    (top₁ : P₁ ≠ ⊤) (top₂ : P₂ ≠ ⊤)
    (hover : ∀ Y : Subgroup S, T ≤ Y → Y = T ∨ Y = P₁ ∨ Y = P₂ ∨ Y = ⊤)
    (ct₁ : CharTwo P₁) (ct₂ : CharTwo P₂) : TwoParLat S T P₁ P₂ :=
  ⟨sylow, normT, lt₁, lt₂, atom₁, atom₂, ne, top₁, top₂, hover,
    le_pElementSubgroup_of_atom sylow.2.1 normT lt₁ atom₁,
    le_pElementSubgroup_of_atom sylow.2.1 normT lt₂ atom₂, ct₁, ct₂⟩

end

section Tits

open CFSG.Sporadic.Schreier.Tits CFSG.QuasithinUnique.Setup.X6 CFSG.QuasithinUnique.Setup.X6.TitsLat

theorem twoParLat_tits :
    TwoParLat ↥titsD titsFlagStab titsPointStab titsLineStab := by
  have pd := CFSG.QuasithinUnique.B113Lie.Tits.parabolicData
  have hP1 : titsPointStab ≠ ⊤ := (pd.le _ (by simp)).2
  have hP2 : titsLineStab ≠ ⊤ := (pd.le _ (by simp)).2
  have hcF := card_titsFlagStab
  have hcP := card_titsPointStab
  have hcN := card_titsLineStab
  have hF1 : titsFlagStab < titsPointStab :=
    lt_of_le_of_ne titsFlagStab_le_point fun e => by rw [e, hcP] at hcF; omega
  have hF2 : titsFlagStab < titsLineStab :=
    lt_of_le_of_ne titsFlagStab_le_line fun e => by rw [e, hcN] at hcF; omega
  have hne : titsPointStab ≠ titsLineStab := fun e => by rw [e, hcN] at hcP; omega
  have hnoPN : ¬ titsLineStab ≤ titsPointStab := fun h => by
    have := Subgroup.card_dvd_of_le h
    rw [hcN, hcP] at this
    omega
  have hnoNP : ¬ titsPointStab ≤ titsLineStab := fun h => by
    have := Subgroup.card_dvd_of_le h
    rw [hcN, hcP] at this
    omega
  refine TwoParLat.of_atoms isSylowTwoOf_flagStab ?_ hF1 hF2 ?_ ?_ hne hP1 hP2
    tits_overgroups (pd.charTwo _ (by simp)) (pd.charTwo _ (by simp))
  · refine le_antisymm ?_ Subgroup.le_normalizer
    have := CFSG.Quasithin.titsSD_normalizer_le
    rw [CFSG.Quasithin.titsSD_eq_flagStab] at this
    exact this
  · intro Q hQ1 hQ2
    rcases tits_overgroups Q hQ1 with e | e | e | e
    · exact Or.inl e
    · exact Or.inr e
    · exact absurd (e ▸ hQ2) hnoPN
    · exact absurd (top_le_iff.1 (e ▸ hQ2)) hP1
  · intro Q hQ1 hQ2
    rcases tits_overgroups Q hQ1 with e | e | e | e
    · exact Or.inl e
    · exact absurd (e ▸ hQ2) hnoNP
    · exact Or.inr e
    · exact absurd (top_le_iff.1 (e ▸ hQ2)) hP2

end Tits

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar
