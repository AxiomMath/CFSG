module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.Engine
public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenDefs
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.BlockOver
import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenNatCase
import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenCases
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.BlockLiftQ
public import CFSG.Quasithin.Background.C118WeakPair

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.GN
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.Quasithin.B2F CFSG.Quasithin.E2

variable {X : Type} [Group X] [Finite X] {T : Subgroup X}

@[expose] def GNHardCase (H T : Subgroup X) : Prop :=
  ¬ thompsonJ T ≤ Subgroup.centralizer (VZ T H : Set X) ∧
    ∃ hV : IsElemAbelian 2 (VZ T H),
      (NatCaseGen H T (VZ T H) hV ∧ ∀ I, E23FamGen H T (VZ T H) hV I →
          (∀ L ∈ I, ∃ n : ℕ, 2 ≤ n ∧ IsL2Natural L (fixV (autI hV (twoResidual H))) n) →
            2 ≤ I.card) ∨
        SymCaseGen H T (VZ T H) hV

theorem parabolic_or_hardCase (hE : E23NonsolvGen) (hK : KFactChevMinParabolic)
    (hX : GNSetting X T) {C₁ C₂ : Subgroup X} (hP : IsC118Pair T C₁ C₂)
    {L : Subgroup (X ⧸ gnC T)} (hL : Open.IsComponentOf L ⊤)
    (hch : IsChevTwo (↥L ⧸ Subgroup.center ↥L)) {P : Subgroup (X ⧸ gnC T)}
    (hPb : IsMinOverBorel L (gnImg T T ⊓ L) P) :
    (pElementSubgroup 2 P ≤ gnImg T (Subgroup.centralizer (C₁ : Set X)) ∨
        pElementSubgroup 2 P ≤ gnImg T (Subgroup.normalizer (C₂ : Set X))) ∨
      ∃ H₁ M₁ : Subgroup X, T ≤ H₁ ∧
        gnImg T H₁ = conjClosure (pElementSubgroup 2 (conjClosure P
          (gnImg T T ⊓ Subgroup.normalizer (L : Set (X ⧸ gnC T))))) (gnImg T T) ⊔ gnImg T T ∧
        MinParabolic H₁ T M₁ ∧ CharTwo H₁ ∧ GNHardCase H₁ T := by
  obtain ⟨H₁, M₁, hTH₁, hmap, hmin, hF⟩ := exists_minParabolic_of_gnSetting hK hX hL hch hPb
  have hmap' : gnImg T H₁ = conjClosure (pElementSubgroup 2 (conjClosure P
      (gnImg T T ⊓ Subgroup.normalizer (L : Set (X ⧸ gnC T))))) (gnImg T T) ⊔ gnImg T T := hmap
  have hconcl := escape_over_of_concl1Gen (C₁ := C₁) (C₂ := C₂) hK hX hL hch hPb le_rfl
    inf_le_left ((B6.pCoreOf_two_le_of_isSylowTwoOf hX.sylow).trans hTH₁) hmap' hmin.isSylow hF
  refine cases_weak hE hP.toWeakSelf hmin hF (fun h => Or.inl (hconcl h))
    (fun hVel hred hJ hnat => ?_)
    fun hVel _ hJ hsym => Or.inr ⟨H₁, M₁, hTH₁, hmap', hmin, hF, hJ, hVel, Or.inr hsym⟩
  by_cases hone : ∃ I, E23FamGen H₁ T (VZ T H₁) hVel I ∧
      (∀ L ∈ I, ∃ n : ℕ, 2 ≤ n ∧ IsL2Natural L (fixV (autI hVel (twoResidual H₁))) n) ∧
        I.card < 2
  · exact Or.inl (hconcl
      (concl1Gen_of_natCase_single_weak hE hP.toWeakSelf hmin hF hred rfl hJ hnat hone))
  · refine Or.inr ⟨H₁, M₁, hTH₁, hmap', hmin, hF, hJ, hVel, Or.inl ⟨hnat, fun I hFam hn2 => ?_⟩⟩
    by_contra hlt
    exact hone ⟨I, hFam, hn2, by omega⟩

end CFSG.AGLEmbeddingD2.Tits.GN516
