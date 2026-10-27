module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.EngineOver
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.ParabolicFacts
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.BlockExclusion
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.Escape
public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenGlue

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.GN
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.Quasithin.B2F CFSG.Quasithin.E2

namespace CFSG.AGLEmbeddingD2.Tits.GN516

public section

variable {X : Type} [Group X] [Finite X] {T : Subgroup X}

theorem parabolic_of_concl_over (hK : KFactChevMinParabolic) (hX : GNSetting X T)
    {C₁ C₂ : Subgroup X} {L : Subgroup (X ⧸ gnC T)} (hL : Open.IsComponentOf L ⊤)
    (hch : IsChevTwo (↥L ⧸ Subgroup.center ↥L)) {P : Subgroup (X ⧸ gnC T)}
    (hPb : IsMinOverBorel L (gnImg T T ⊓ L) P)
    (hconcl : ∀ K M : Subgroup X, gnStab T (Subgroup.normalizer (L : Set (X ⧸ gnC T)) ⊓ Subgroup.normalizer (P : Set (X ⧸ gnC T))) ≤ K →
      K.map (QuotientGroup.mk' (gnC T)) = pElementSubgroup 2 P ⊔ (gnImg T T ⊓
        (Subgroup.normalizer (L : Set (X ⧸ gnC T)) ⊓ Subgroup.normalizer (P : Set (X ⧸ gnC T)))) →
      MinParabolic K (gnStab T (Subgroup.normalizer (L : Set (X ⧸ gnC T)) ⊓ Subgroup.normalizer (P : Set (X ⧸ gnC T)))) M → CharTwo K →
      (C₁ ≤ centerOf K ∨ K ≤ Subgroup.normalizer (C₂ : Set X) ∨
          BlocksGen K (gnStab T (Subgroup.normalizer (L : Set (X ⧸ gnC T)) ⊓ Subgroup.normalizer (P : Set (X ⧸ gnC T))))) ∨
        (pElementSubgroup 2 P ≤ gnImg T (Subgroup.centralizer (C₁ : Set X)) ∨
          pElementSubgroup 2 P ≤ gnImg T (Subgroup.normalizer (C₂ : Set X)))) :
    pElementSubgroup 2 P ≤ gnImg T (Subgroup.centralizer (C₁ : Set X)) ∨
      pElementSubgroup 2 P ≤ gnImg T (Subgroup.normalizer (C₂ : Set X)) := by
  set N : Subgroup (X ⧸ gnC T) :=
    Subgroup.normalizer (L : Set (X ⧸ gnC T)) ⊓ Subgroup.normalizer (P : Set (X ⧸ gnC T)) with hNdef
  have hNL : N ≤ Subgroup.normalizer (L : Set (X ⧸ gnC T)) := inf_le_left
  have hLN : gnImg T T ⊓ L ≤ N :=
    le_inf (inf_le_right.trans Subgroup.le_normalizer)
      ((le_of_isMinOverBorel hPb inf_le_right).trans Subgroup.le_normalizer)
  have hRP : gnImg T T ⊓ N ≤ Subgroup.normalizer (P : Set (X ⧸ gnC T)) :=
    inf_le_right.trans inf_le_right
  obtain ⟨K, M₁, hSK, hmap, hmin, hF⟩ :=
    exists_minParabolic_over_gnStab hK hX hL hch hPb hNL hLN
  have hmap' : K.map (QuotientGroup.mk' (gnC T)) = pElementSubgroup 2 P ⊔ (gnImg T T ⊓ N) := by
    rw [hmap, conjClosure_eq_self_of_le_normalizer hRP]
  have hPW : pElementSubgroup 2 P ≤ gnImg T K := by
    show pElementSubgroup 2 P ≤ K.map (QuotientGroup.mk' (gnC T))
    rw [hmap']
    exact le_sup_left
  have hout := escape_of_le_gnImg (C₁ := C₁) (C₂ := C₂) hPW
  have hQH : pCoreOf 2 (⊤ : Subgroup X) ≤ K := (pCoreOf_le_gnStab hX N).trans hSK
  have hR2 : IsPGroup 2 ↥(gnImg T T ⊓ N) := (hX.sylow.2.1.map _).to_le inf_le_left
  have hRW : gnImg T T ⊓ N ≤ Subgroup.normalizer (pElementSubgroup 2 P : Set (X ⧸ gnC T)) :=
    hRP.trans (normalizer_le_normalizer_pElementSubgroup 2 P)
  have hblock : BlocksGen K (gnStab T N) → False := by
    rintro ⟨r, Kb, -, hKb, hKK, hres, -, -⟩
    have hK' : ∀ i, IsChiBlockGN K (Kb i) := fun i => ⟨(hKb i).1.1, (hKb i).1.2⟩
    by_cases hPL : P = L
    · have hWL : pElementSubgroup 2 P ≤ L := (pElementSubgroup_le _).trans hPb.1
      have hLW : L ≤ Subgroup.normalizer (pElementSubgroup 2 P : Set (X ⧸ gnC T)) := by
        rw [hPL]
        exact Subgroup.le_normalizer.trans (normalizer_le_normalizer_pElementSubgroup 2 L)
      exact false_of_blocks_of_normal_q hX hL hWL hLW (isSylowTwoOf_pElementSubgroup hX hL hPb)
        (not_le_normalizer_of_isMinOverBorel hPb) hR2 hRW hQH hmap' hK' hres
    · exact false_of_blocks_of_ne_q hX hR2 hRW (commutator_ne_bot_of_ne hK hX hL hch hPb hPL)
        hQH hmap' hK' hKK hres
  rcases hconcl K M₁ hSK hmap' hmin hF with (h1 | h2 | h3) | h
  · exact hout (Or.inl h1)
  · exact hout (Or.inr h2)
  · exact (hblock h3).elim
  · exact h

end

end CFSG.AGLEmbeddingD2.Tits.GN516
