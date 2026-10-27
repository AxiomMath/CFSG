module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Statements
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem9S331

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped commutatorElement IsMulCommutative

section Main

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}

omit [CFSG.GH74.QTGen4.Finite4 G] in

private theorem pCoreOf_subgroupOf_self (L : Subgroup G) :
    (pCoreOf 2 L).subgroupOf L = CFSG.pCore 2 ↥L := by
  rw [CFSG.pCore_eq_open (↥L) 2]
  exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective _

theorem stmt12_2_9_two_F4
    (h331 : Stmt3_3_1_F4) (h1222 : Stmt12_2_2_F4)
    (hC58 : TheoremC58) (h317 : AS317Sylow) (hH : Hyp1223 G T L V)
    (hCZ : Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤
      Subgroup.normalizer (L : Set G)) :
    L = ⁅L, thompsonJ T⁆ := by
  obtain ⟨⟨hmax, hle, huniq⟩, -, ⟨H₀, hH₀⟩, -, -⟩ :=
    (h331 G T hH.simple hH.nonabelian hH.qtke hH.sylow).2 L hH.maximal hH.quasisimple
  rw [hH.conjClosure_eq] at hmax hle huniq hH₀
  obtain ⟨-, -, hall⟩ := ((h1222 G T hH.simple hH.nonabelian hH.qtke hH.sylow).resolve_left
    hH.notAlt) L hH.maximal hH.faithful hH.quasisimple
  obtain ⟨⟨hVT, hTV, hred, -⟩, -, -, hab, -⟩ := hall V hH.irrPlus
  have hVLT : V ≤ L ⊔ T := hVT.trans le_sup_right
  have hV0 : conjClosure V T = V := conjClosure_eq_self_of_normalizes hTV
  have hQ : pCoreOf 2 (L ⊔ T) = T ⊓ Subgroup.centralizer (V : Set G) := by
    have := (stmt3_2_2_eight_proved G T L V hH.fsu).2.2
    rwa [hH.conjClosure_eq, hV0] at this
  have hperf : L = oTwoUpper L := (hH.faithful.2.1 _ (oTwoUpper_le L)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (oTwoUpper_le L)).mpr
      (le_normalizer_oTwoUpper L))
    fun _ hx => exists_pow_mem_oTwoUpper L hx).symm
  have h318 : Hyp318 T (Subgroup.normalizer (L : Set G)) L V :=
    { inM := ⟨hmax, hH.normalizes⟩
      nonempty := ⟨H₀, hH₀⟩
      perfect := hperf
      le_M := Subgroup.le_normalizer
      normal := le_rfl
      unique := ⟨⟨hmax, hle⟩, fun M' hM' => huniq M' hM'.1 hM'.2⟩
      reduced := isTwoReducedIn_iff_isPrimeReduced_subgroupOf.mpr ⟨hVLT, hred⟩
      centralizer := hQ }

  have hJ : ¬ thompsonJ T ≤ T ⊓ Subgroup.centralizer (V : Set G) := by
    rcases theorem318_three hC58 h317 hH.simple hH.nonabelian hH.qtke hH.sylow h318 with
      ⟨hJ, -⟩ | ⟨-, hZ, -⟩
    · exact hJ
    · exfalso
      apply hH₀.2.1
      exact (Subgroup.le_centralizer_iff.mp ((hZ H₀ hH₀).trans inf_le_right)).trans hCZ

  have hJT : thompsonJ T ≤ T := iSup₂_le fun A hA => hA.1
  have hJL : thompsonJ T ≤ Subgroup.normalizer (L : Set G) := hJT.trans hH.normalizes
  have hcc : L ∈ cComp (L ⊔ T) := hH.faithful.1.2.1
  by_contra hne
  rcases cComp_commutator_dichotomy_of_le hcc (hJT.trans le_sup_right) with ⟨-, hsolv⟩ | hconj
  · apply hJ
    refine le_inf hJT ?_
    have hLJL : ⁅L, thompsonJ T⁆ ≤ L := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.le_normalizer_iff_commutator_le_right.mp hJL
    have hq' : CFSG.IsQuasisimple (↥L ⧸ (pCoreOf 2 L).subgroupOf L) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv
        (QuotientGroup.quotientMulEquivOfEq (pCoreOf_subgroupOf_self L).symm) hH.quasisimple
    have hD := commutator_le_pCoreOf_of_solvable hq' hLJL
      (Subgroup.normalizer_commutator_ge_left L (thompsonJ T)) hsolv
    have hJQ : ⁅thompsonJ T, L⁆ ≤ pCoreOf 2 L :=
      commutator_le_of_commutator_commutator_le
        (hJL.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L) (perfect_of_mem_cComp hcc) hD
    have hO2 : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G) := by
      have := pCoreOf_le_pCoreOf_of_isSubnormal (subnormal_of_mem_cComp hcc)
      rw [hQ] at this
      exact this.trans inf_le_right
    have hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
      congrArg Subtype.val (mul_comm (⟨x, hx⟩ : ↥V) ⟨y, hy⟩)
    exact le_centralizer_of_commutator_le hVc (hH.sylow.1.to_le hVT) (hH.sylow.1.to_le hJT)
      hH.irrPlus.2.2.1 (hJT.trans hTV) hJL hH.irrPlus.2.2.2.1 hH.irrPlus.2.2.2.2.1
      hH.irrPlus.2.2.2.2.2.1 (hJQ.trans hO2)
  · exact hne (hconj.trans (conjClosure_eq_self_of_normalizes hJL)).symm

theorem stmt12_2_9_of_F4
    (h331 : Stmt3_3_1_F4) (h1222 : Stmt12_2_2_F4)
    (hC58 : TheoremC58) (h317 : AS317Sylow) : Stmt12_2_9_F4 := fun _ _ _ _ _ _ hH =>
  ⟨stmt12_2_9_one_F4 h331 hH, stmt12_2_9_two_F4 h331 h1222 hC58 h317 hH⟩

end Main

end CFSG.Quasithin.H13
