module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.MinPar
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.WeakPair
public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenDefs
import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenNatCase
import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenCases
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.MinParLift
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.StabCore

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.B2F CFSG.Quasithin.E2
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbeddingD2.GN

variable {X : Type} [Group X] [Finite X] {T : Subgroup X}

omit [Finite X] in
theorem map_gnStab (N : Subgroup (X ⧸ gnC T)) :
    (gnStab T N).map (QuotientGroup.mk' (gnC T)) = gnImg T T ⊓ N :=
  gnImg_gnStab T N

theorem pCoreOf_le_gnStab' (hX : GNSetting X T) (N : Subgroup (X ⧸ gnC T)) :
    pCoreOf 2 (⊤ : Subgroup X) ≤ gnStab T N :=
  pCoreOf_le_gnStab hX N

theorem exists_minParabolic_over_gnStab (hK : KFactChevMinParabolic) (hX : GNSetting X T)
    {L P N : Subgroup (X ⧸ gnC T)} (hL : Open.IsComponentOf L ⊤)
    (hChev : IsChevTwo (↥L ⧸ Subgroup.center ↥L)) (hP : IsMinOverBorel L (gnImg T T ⊓ L) P)
    (hNL : N ≤ Subgroup.normalizer (L : Set (X ⧸ gnC T))) (hLN : gnImg T T ⊓ L ≤ N) :
    ∃ K M₁ : Subgroup X, gnStab T N ≤ K ∧
      K.map (QuotientGroup.mk' (gnC T)) =
        pElementSubgroup 2 (conjClosure P (gnImg T T ⊓ N)) ⊔ (gnImg T T ⊓ N) ∧
      MinParabolic K (gnStab T N) M₁ ∧ CharTwo K := by
  set π := QuotientGroup.mk' (gnC T)
  set T' : Subgroup (X ⧸ gnC T) := gnImg T T
  set R : Subgroup (X ⧸ gnC T) := T' ⊓ N with hRdef
  set W : Subgroup (X ⧸ gnC T) := pElementSubgroup 2 (conjClosure P R)
  set S : Subgroup X := gnStab T N with hSdef
  have hM : ∃ M, MinParabolic (W ⊔ R) R M :=
    (kFact_of_le hK hX hL hChev hP inf_le_left (inf_le_right.trans hNL)
      (le_inf inf_le_left hLN)).1
  obtain ⟨M₀, hM₀⟩ := hM
  have hmapS : S.map π = R := map_gnStab N
  have hCS : T ⊓ gnC T ≤ S := fun x hx => ⟨hx.1, by
    show π x ∈ N
    rw [show π x = 1 from (QuotientGroup.eq_one_iff x).2 hx.2]
    exact N.one_mem⟩
  obtain ⟨K, M₁, hmin, hF, hSK, hmapK⟩ := exists_minParabolic_lift_of_le hX (gnStab_le T N) hCS
    (pCoreOf_le_gnStab' hX N) (by rw [hmapS]; exact hM₀)
  exact ⟨K, M₁, hSK, hmapK, hmin, hF⟩

section Engine

variable {G : Type} [Group G] [Finite G]

export CFSG.AGLEmbeddingD2.GN (concl1Gen_of_natCase_core_weak concl1Gen_of_natCase_single_weak)

theorem cases_over_weak (hE : E23NonsolvGen) {C₁ C₂ K S T M : Subgroup G} {Q : Prop}
    (hP : IsC118Pair T C₁ C₂) (hT : IsPGroup 2 T) (hbS : baum T ≤ S) (hST : S ≤ T)
    (hmin : MinParabolic K S M) (hF : CharTwo K)
    (hcard : ∀ (V : Subgroup G) (hV : IsElemAbelian 2 V), V = VZ S K →
      ∀ I, E23FamGen K S V hV I →
        (∀ L ∈ I, ∃ n : ℕ, 2 ≤ n ∧ IsL2Natural L (fixV (autI hV (twoResidual K))) n) →
          twoResidual K ≤ thompsonJ K → I.card < 2)
    (hQ : Concl1Gen C₁ C₂ K S → Q)
    (hsym : ∀ hV : IsElemAbelian 2 (VZ S K),
      ¬ thompsonJ S ≤ Subgroup.centralizer (VZ S K : Set G) → SymCaseGen K S (VZ S K) hV → Q) :
    Q := by
  have hW := IsC118Pair.toWeak hP hT hbS hST
  refine cases_weak hE hW hmin hF hQ (fun hVel hred hJ hnat => hQ ?_)
    fun hVel _ hJ hsym' => hsym hVel hJ hsym'
  obtain ⟨-, I, hFam, hn2⟩ := id hnat
  exact concl1Gen_of_natCase_single_weak hE hW hmin hF hred rfl hJ hnat
    ⟨I, hFam, hn2, hcard _ hVel rfl I hFam hn2 hnat.1⟩

end Engine

end CFSG.AGLEmbeddingD2.Tits.GN516
