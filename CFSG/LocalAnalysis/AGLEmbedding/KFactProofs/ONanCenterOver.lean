module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideDefsAux
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieZZK0ShapeFacts
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCenterOverLin
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCenterOverUnitary

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

@[expose] def KFactReeCenterOver : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (d : TauCeti.ValidLieTypeIndex), IsReeGTwoIndex 3 d →
    Nonempty (L ≃* CatGroup d) → ∀ T₁ : Sylow 3 L, ∀ Y : Subgroup L,
      (T₁ : Subgroup L) ⊓ Subgroup.centralizer ((T₁ : Subgroup L) : Set L) ≤ Y →
      ¬ Group.IsSolvable Y → Y = ⊤

theorem centerOver_unitary {K L : Type} [Group K] [Finite K] [IsSimpleGroup K] [Group L]
    [Finite L] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hKnc : ∃ a b : K, a * b ≠ b * a)
    (T : Sylow p K) {d : TauCeti.ValidLieTypeIndex} (hd : IsUnitaryIndex p d)
    (hL : Nonempty (L ≃* CatGroup d)) (T₁ : Sylow p L) (Y : Subgroup L) (φ : Y →* K)
    (hφ : Function.Surjective φ) (hcop : p.Coprime (Nat.card φ.ker))
    (hZY : (T₁ : Subgroup L) ⊓ Subgroup.centralizer ((T₁ : Subgroup L) : Set L) ≤ Y) :
    Y = ⊤ ∨ Nat.card ((T₁ : Subgroup L) ⊓ Subgroup.centralizer ((T₁ : Subgroup L) : Set L) :
      Subgroup L) = Nat.card (T : Subgroup K) := by
  obtain ⟨-, hf, hq, K', _, _, J, hJ, hK', hfix, ⟨e⟩⟩ :=
    UnitaryModel.exists_equiv_psu (UnitaryModel.statedClassicalModel hd hL)
  obtain ⟨S, hS⟩ := UnitaryModel.exists_sylow_eq_rootGroup J hJ hK' hfix hf
  obtain ⟨e', he'⟩ := UnitaryModel.exists_equiv_map_eq e T₁ S
  exact CenterOver.eq_top_or_card_eq_psu J hJ hK' hfix hp2 hf hq hKnc e' T₁ (he'.trans hS) T Y φ
    hφ hcop hZY

theorem kFactOneLieCenterOver_of_ident (hId : KFactOneLieIdent)
    (hRee : KFactReeCenterOver) : KFactOneLieCenterOver := by
  intro K _ _ hKs hKnc _ p hp hp2 T _ _ _ L _ _ hLs hLnc hLcat T₁ hT₁nc hT₁glb hT₁rk Y φ hφ hcop hZY
  have : Fact p.Prime := ⟨hp⟩
  have : IsSimpleGroup K := hKs
  obtain ⟨d, hd, ⟨e⟩⟩ := hId L hLs hLnc hLcat p hp hp2 T₁ hT₁nc hT₁glb hT₁rk
  rcases hd with ⟨n, hn3, hlin⟩ | ⟨hu, -⟩ | hree
  · obtain ⟨e₂⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hlin
    exact Or.inl (CenterOver.eq_top_of_equiv_psl2GF hp2 (by omega) hKnc (e.trans e₂) T₁ Y φ hφ
      hZY)
  · rcases centerOver_unitary hp2 hKnc T hu ⟨e⟩ T₁ Y φ hφ hcop hZY with h | h
    · exact Or.inl h
    · exact Or.inr ⟨⟨d, hu, ⟨e⟩⟩, h⟩
  · obtain ⟨rfl, -⟩ := id hree
    exact Or.inl (hRee L d hree ⟨e⟩ T₁ Y hZY (CenterOver.not_isSolvable_of_surjective hKnc φ hφ))

end CFSG.AGLEmbedding
