module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.SymDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.SymOverC3
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.SymOverMinPar
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.SymOverBlockRad
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.SymOverImage
import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenSym
public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenSolvC126

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.GN
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

variable {G : Type} [Group G] [Finite G]

theorem concl1Gen_of_symCase_all {C₁ C₂ K S T M : Subgroup G}
    (hP : IsC118Pair T C₁ C₂) (hT : IsPGroup 2 T) (hbS : baum T ≤ S) (hST : S ≤ T)
    (hmin : MinParabolic K S M) (hF : CharTwo K)
    (hJ : ¬ thompsonJ S ≤ Subgroup.centralizer (VZ S K : Set G))
    (hV : IsElemAbelian 2 (VZ S K)) (hSym : SymCaseGen K S (VZ S K) hV) :
    Concl1Gen C₁ C₂ K S := by
  obtain ⟨-, -, hred⟩ := conjClosure_isTwoReducedIn_of_charTwo hmin.isSylow hF (le_refl _)
  obtain ⟨C, Y₀, hY₀K, hC3, hY₀C, hY₀N, hgen⟩ :=
    exists_symOver_lift hV hmin hred hbS hST hJ hSym
  obtain ⟨Y', M', hY'K, hY'C, hY'N, hmp, hsolv, hFP, hgen'⟩ :=
    exists_solvable_minParabolic_sym hV hmin hF hred hbS hST hJ hY₀K hC3 hY₀C hY₀N hgen
  have hKN : K ≤ Subgroup.normalizer (VZ S K : Set G) := hred.2.1
  have hSK : S ≤ K := hmin.isSylow.1
  have hQS : pCoreOf 2 K ≤ S := B6.pCoreOf_two_le_of_isSylowTwoOf hmin.isSylow
  have hRS : R₁ K T ≤ S := sup_le hQS hbS
  have hRK : R₁ K T ≤ K := hRS.trans hSK
  have hR2 : IsPGroup 2 ↥(R₁ K T) := hmin.isSylow.2.1.to_le hRS
  have hPK : Y' ⊔ R₁ K T ≤ K := sup_le hY'K hRK
  have hWP : IsC118WeakPair (R₁ K T) C₁ C₂ := hP.toWeak hT (baum_le_R₁ K T) (hRS.trans hST)
  have hperf : perfectCore (Y' ⊔ R₁ K T) ≤
      Subgroup.centralizer (VZ (R₁ K T) (Y' ⊔ R₁ K T) : Set G) := by
    rw [(isSolvable_iff_perfectCore_eq_bot _).1 hsolv]
    exact bot_le
  obtain ⟨-, h1Z, -, -, h2B, h2char, -⟩ := id hP
  rcases concl1Gen_of_perfectCore_le_weak hWP hmp hFP hperf with h1 | h2 | hblk
  ·
    left
    refine le_inf (h1.trans (inf_le_left.trans hPK)) ?_
    rw [Subgroup.le_centralizer_iff]
    rw [← hgen']
    refine sup_le (fun y hy c hc => ?_) (fun s hs c hc => ?_)
    · exact (Subgroup.mem_centralizer_iff.1 (h1 hc).2 y ((le_sup_left : Y' ≤ Y' ⊔ R₁ K T) hy)).symm
    · have hcT : c ∈ centerOf T := C1GN.omegaOneCenterOf_le_centerOf T (h1Z hc)
      exact (Subgroup.mem_centralizer_iff.1 hcT.2 s (hST hs)).symm
  ·
    right; left
    have hTS : T ≤ Subgroup.normalizer (baum T : Set G) :=
      Subgroup.le_normalizer.trans (normalizer_le_normalizer_baum T)
    have hTN2 : T ≤ Subgroup.normalizer (C₂ : Set G) :=
      hTS.trans (normalizer_le_normalizer_of_characteristic_subgroupOf h2B h2char)
    rw [← hgen']
    exact sup_le (le_sup_left.trans h2) (fun s hs => hTN2 (hST hs))
  ·
    obtain ⟨K', hK'blk, -, hPeq⟩ := hblk
    have hK'P : K' ≤ Y' ⊔ R₁ K T := hK'blk.1.2.1
    have hK'K : K' ≤ K := hK'P.trans hPK
    have hshort : IsShort2 K' := hK'blk.1.1
    have hQP : pCoreOf 2 K ≤ Y' ⊔ R₁ K T := (pCoreOf_le_R₁ K T).trans le_sup_right
    have hQN : pCoreOf 2 K ≤ Subgroup.normalizer (K' : Set G) :=
      le_normalizer_of_isSubnormal_of_pGroup hK'P hK'blk.1.2.2 (twoResidual_eq_of_isShort2 hshort)
        hQP (hPK.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
    have hK'V : ¬ K' ≤ Subgroup.centralizer (VZ S K : Set G) := by
      intro hc
      have hconj : conjClosure K' (R₁ K T) ≤ Subgroup.centralizer (VZ S K : Set G) :=
        conjClosure_le fun r hr z hz =>
          (Subgroup.mem_normalizer_iff.1 (B6.le_normalizer_centralizer hKN (hRK hr)) z).1 (hc hz)
      have hYle : Y' ≤ Subgroup.centralizer (VZ S K : Set G) ⊔ R₁ K T :=
        ((le_sup_left : Y' ≤ Y' ⊔ R₁ K T).trans hPeq.le).trans
          (sup_le le_sup_right (hconj.trans le_sup_left))
      exact not_le_centralizer_sup_pGroup hKN hRK hR2 hC3 hY'K hY'C hYle
    have hconjK : conjClosure K' (R₁ K T) ≤ conjClosure K' K :=
      conjClosure_le fun r hr z hz =>
        (Subgroup.mem_normalizer_iff.1 (le_normalizer_conjClosure K' K (hRK hr)) z).1
          (le_conjClosure K' K hz)
    have hgenK : K ≤ conjClosure K' K ⊔ S := by
      have hP' : Y' ⊔ R₁ K T ≤ conjClosure K' K ⊔ S :=
        hPeq.le.trans (sup_le (hRS.trans le_sup_right) (hconjK.trans le_sup_left))
      exact hgen'.symm.le.trans
        (sup_le ((le_sup_left : Y' ≤ Y' ⊔ R₁ K T).trans hP') le_sup_right)
    have hRad := radFree_of_shortBlock hmin.isSylow hF hred hK'K hshort hQN hK'V hgenK
    exact concl1Gen_of_symCase_of_radFree_weak (hP.toWeak hT hbS hST) hmin hF hred rfl hJ hSym
      (Or.inl hRad)

theorem agl81I516SymOver_of_kFact (hK : KFactChevMinParabolic) : AGL81I516SymOver := by
  intro X _ _ T hX C₁ C₂ hP L hL hch P hPb S hbS hST hQS hCS K M hSK hmap hmin hF hJ hV hsym
  have hLS : gnImg T T ⊓ L ≤ gnImg T S :=
    inf_le_gnImg_of_isSylowTwoOf hX hPb hST hmin.isSylow hmap
  exact escape_over_of_concl1Gen hK hX hL hch hPb hST hLS (hQS.trans hSK) hmap hmin.isSylow hF
    (concl1Gen_of_symCase_all hP hX.sylow.2.1 hbS hST hmin hF hJ hV hsym)

end CFSG.AGLEmbeddingD2.Tits.GN516
