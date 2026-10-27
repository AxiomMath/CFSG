module

public import CFSG.Quasithin.H13.L32AL2Ik
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AL2Id
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AL2Ii
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem1434

public section

namespace CFSG.Quasithin.H13.L32A.L2

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open scoped IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace IData

variable {T L V TY : Subgroup G} {z z' : G} (D : IData T L V TY z z')
include D

theorem autOn_thompsonJ_ne_bot_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) :
    autOn (thompsonJ (iI T L V z z')) (vI T L V z z') ≠ ⊥ := by
  intro h
  apply D.not_thompsonJ_le_centralizer_vI_F4 h1222 h1332 h1334
  have hJT := thompsonJ_le_thompsonJ_of_isSylowTwoOf D.isSylowTwoOf_T
  intro g hg
  have hgI : g ∈ iI T L V z z' := (iSup₂_le fun _ hA => hA.1 : thompsonJ _ ≤ _) (hJT hg)
  have hgN := iI_le_normalizer_vI T L V z z' hgI
  have h1 := A1b.conjAct_mem_autOn hgN (hJT hg)
  rw [h, Subgroup.mem_bot] at h1
  exact A1b.conjAct_eq_one_iff.mp h1

theorem b53Hyp_J_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    [IsMulCommutative ↥(vI T L V z z')] :
    B53Hyp (autOn (thompsonJ (iI T L V z z')) (vI T L V z z')) := by
  obtain ⟨-, hWe, hred⟩ := D.vI_spec_F4 h1222 h1332 h1334
  have hUN := iI_le_normalizer_vI T L V z z'
  have hSQ := D.sqtk_iI_F4 h1222 h1332 h1334
  have hO2 := Setup.pCoreOf_autOn_eq_bot hred
  have hJI : thompsonJ (iI T L V z z') ≤ iI T L V z z' := iSup₂_le fun _ hA => hA.1
  have hJn := InternalSec.autOn_normal_of (U := vI T L V z z') (iI_le_normalizer_thompsonJ
    (T := T) (L := L) (V := V) (z := z) (z' := z'))
  have hJH := InternalSec.autOn_le_autOn_of_le (U := vI T L V z z') hJI
  have hJnorm : ((autOn (thompsonJ (iI T L V z z')) (vI T L V z z')).subgroupOf
      (autOn (iI T L V z z') (vI T L V z z'))).Normal :=
    (Subgroup.normal_subgroupOf_iff hJH).2 fun h k hh hk => hJn k hk h hh
  have hffJ : autOn (thompsonJ (iI T L V z z')) (vI T L V z z') =
      ffJ (autOn (thompsonJ (iI T L V z z')) (vI T L V z z')) :=
    le_antisymm (SzN17.autOn_thompsonJ_le_ffJ_self hWe hred.1 hUN) (B6.ffJ_le _)
  exact SzN17.b53Hyp_of_normal hUN hSQ hO2 hJH hJnorm hffJ

theorem false_of_cComp_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (h1434 : Lemma1434One_F4) (h37 : A37ForSQTK) (h38 : A38ForSQTK) {K : Subgroup G}
    (hK : K ∈ cComp (thompsonJ (iI T L V z z'))) (hne : autOn K (vI T L V z z') ≠ ⊥) :
    False := by
  obtain ⟨-, hWe, hred⟩ := D.vI_spec_F4 h1222 h1332 h1334
  have hIW := iI_le_normalizer_vI T L V z z'
  have hJI : thompsonJ (iI T L V z z') ≤ iI T L V z z' := iSup₂_le fun _ hA => hA.1
  have hKI : K ≤ iI T L V z z' := (le_of_mem_cComp hK).trans hJI
  have hKW : K ≤ Subgroup.normalizer (vI T L V z z' : Set G) := hKI.trans hIW

  have hJsub : IsSubnormal (thompsonJ (iI T L V z z')) (iI T L V z z') :=
    IsSubnormal.step hJI ((Subgroup.normal_subgroupOf_iff_le_normalizer hJI).mpr
      iI_le_normalizer_thompsonJ) (IsSubnormal.refl _)
  have hKc : K ∈ cComp (iI T L V z z') := cComp_mem_of_subnormal hJsub hK

  have hT := D.S.hyp.fsu.sylow
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomm : ⁅vI T L V z z', K⁆ ≠ ⊥ := by
    intro h
    apply hne
    rw [eq_bot_iff]
    intro φ hφ
    obtain ⟨⟨k, hkN⟩, hkK, rfl⟩ := Setup.mem_autOn_iff.mp hφ
    rw [Subgroup.mem_bot]
    refine A1b.conjAct_eq_one_iff.mpr (Subgroup.mem_centralizer_iff.mpr fun v hv => ?_)
    have h1 := Subgroup.commutator_mem_commutator hv hkK
    rw [h, Subgroup.mem_bot] at h1
    rw [commutatorElement_def] at h1
    calc v * k = (v * k * v⁻¹ * k⁻¹) * (k * v) := by group
      _ = k * v := by rw [h1, one_mul]
  have hLf : quasithinIsFaithfulLocal T K := by
    have h1 := isFaithfulLocal_of_commutator_ne_bot D.S.hyp.fsu.qtke.2.1 (hT.1.toSylow hT.2)
      (H := iI T L V z z') (by
        rw [IsPGroup.toSylow_coe]
        exact ⟨T_le_iI, D.pCoreOf_iI_ne_bot_F4 h1222 h1332 h1334⟩) hKc hred hcomm
    rwa [IsPGroup.toSylow_coe] at h1

  have hTK : T ≤ Subgroup.normalizer (K : Set G) := (h1332 G T L D.S.hyp.hyp.h13 K hLf).2.1.1
  have hKn : (K.subgroupOf (iI T L V z z')).Normal :=
    lemma_1_2_4_normal D.S.hyp.fsu.qtke D.S.hyp.fsu.simple D.S.hyp.fsu.nonabelian h37 h38
      (D.pCoreOf_iI_ne_bot_F4 h1222 h1332 h1334) D.isSylowTwoOf_T
      (cComp_subset_lFamily T_le_iI hKc) le_rfl hKc hTK
  have hIK : iI T L V z z' ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKI).mp hKn

  have hKpI : autOn K (vI T L V z z') ≤ autOn (iI T L V z z') (vI T L V z z') :=
    InternalSec.autOn_le_autOn_of_le hKI
  have hIKp : autOn (iI T L V z z') (vI T L V z z') ≤
      Subgroup.normalizer (autOn K (vI T L V z z') : Set (MulAut ↥(vI T L V z z'))) :=
    le_normalizer_of_conj (InternalSec.autOn_normal_of hIK)

  have hO2K : pCoreOf 2 K ≤ Subgroup.centralizer (vI T L V z z' : Set G) := by
    refine hred.2.2.2 _ ((pCoreOf_le 2 K).trans hKI)
      (hIK.trans (normalizer_le_normalizer_pCoreOf 2 K)) fun d hd => ?_
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 K ⟨d, hd⟩
    refine ⟨k, ?_⟩
    have : d ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    rw [this]
    exact one_mem _

  have hmodel := h1434 G T L D.S.hyp.hyp K hLf
  have hsimp : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) := by
    rcases hmodel with h5 | hlin
    · obtain ⟨e⟩ := h5
      exact (MulEquiv.isSimpleGroup_congr e).mpr inferInstance
    · obtain ⟨e⟩ := LieType.SteinbergBR.AltFiveGL3.nonempty_equiv_GL32 hlin
      exact (MulEquiv.isSimpleGroup_congr e).mpr
        LocalAnalysis.ComponentInitial.BinarySymplecticSix.FusionOrbits.isSimpleGroup_GL_three_two

  have hker : IsPGroup 2 ↥(K ⊓ Subgroup.centralizer (vI T L V z z' : Set G)) := by
    set M : Subgroup ↥K := (K ⊓ Subgroup.centralizer (vI T L V z z' : Set G)).subgroupOf K
      with hM
    have hMn : M.Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [hM, Subgroup.mem_subgroupOf] at hn ⊢
      refine Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem g.2 hn.1) (inv_mem g.2), ?_⟩
      exact (Subgroup.mem_normalizer_iff.mp (mem_normalizer_centralizer (hKW g.2)) _).mp hn.2
    have hMn' : (M.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))).Normal :=
      Subgroup.Normal.map hMn _ (QuotientGroup.mk'_surjective _)
    have hmap := hsimp.eq_bot_or_eq_top_of_normal (M.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)))
    rcases hmap with hbot | htop
    ·
      have hle : M ≤ CFSG.pCore 2 ↥K := by
        intro m hm
        have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥K) m = 1 := by
          rw [← Subgroup.mem_bot, ← hbot]
          exact ⟨m, hm, rfl⟩
        rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      intro x
      obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥K)) ⟨⟨(x : G), x.2.1⟩,
        hle (Subgroup.mem_subgroupOf.mpr x.2)⟩
      refine ⟨k, Subtype.ext ?_⟩
      have := congrArg (fun y : ↥(CFSG.pCore 2 ↥K) => ((y : ↥K) : G)) hk
      simpa using this
    ·
      exfalso
      apply hne
      rw [eq_bot_iff]
      intro φ hφ
      obtain ⟨⟨k, hkN⟩, hkK, rfl⟩ := Setup.mem_autOn_iff.mp hφ
      rw [Subgroup.mem_bot]
      refine A1b.conjAct_eq_one_iff.mpr ?_
      have hk1 : QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨k, hkK⟩ ∈
          M.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) := by
        rw [htop]
        exact Subgroup.mem_top _
      obtain ⟨m, hm, hmk⟩ := hk1
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hmk
      have hq : ((m⁻¹ * ⟨k, hkK⟩ : ↥K) : G) ∈ pCoreOf 2 K := by
        rw [pCoreOf, ← CFSG.pCore_eq_open]
        exact ⟨_, hmk, rfl⟩
      have e : k = (m : G) * ((m⁻¹ * ⟨k, hkK⟩ : ↥K) : G) := by simp
      show k ∈ Subgroup.centralizer (vI T L V z z' : Set G)
      rw [e]
      exact mul_mem (Subgroup.mem_subgroupOf.mp hm).2 (hO2K hq)

  have hO2 : pCoreOf 2 (autOn K (vI T L V z z')) = ⊥ := by
    have h1 : pCoreOf 2 (autOn K (vI T L V z z')) ≤
        pCoreOf 2 (autOn (iI T L V z z') (vI T L V z z')) :=
      le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans hKpI)
        (hIKp.trans (normalizer_le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)
    rw [Setup.pCoreOf_autOn_eq_bot hred] at h1
    exact le_bot_iff.mp h1
  obtain ⟨eK⟩ := autOn_equiv_quotient1527d hKW hO2 hker
  have hgood : GoodK (autOn K (vI T L V z z')) := by
    rcases hmodel with h5 | hlin
    · obtain ⟨e⟩ := h5
      exact GoodK.of_mulEquiv (eK.trans e) goodModel_alt_five
    · obtain ⟨e⟩ := LieType.SteinbergBR.AltFiveGL3.nonempty_equiv_GL32 hlin
      exact GoodK.of_mulEquiv (eK.trans e) goodModel_GL32
  exact D.false_of_goodK_F4 h1222 h1332 h1334 hgood hKpI (fun u hu _ => hIKp hu)
    (A4.isSylowTwoOf_inf_normal D.isSylowTwoOf_autOn_T hKpI hIKp)

end IData

end CFSG.Quasithin.H13.L32A.L2
