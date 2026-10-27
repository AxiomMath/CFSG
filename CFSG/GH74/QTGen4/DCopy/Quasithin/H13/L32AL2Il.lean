module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AL2Ik
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AL3S

public section

namespace CFSG.Quasithin.H13.L32A.L2

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open scoped IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace IData

variable {T L V TY : Subgroup G} {z z' : G} (D : IData T L V TY z z')
include D

theorem false_of_hyps_F4 (h56 : AsB56) (h39 : A39ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h1434 : Lemma1434One_F4) (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) : False := by
  obtain ⟨-, hWe, hred⟩ := D.vI_spec_F4 h1222 h1332 h1334
  have : IsMulCommutative ↥(vI T L V z z') := hWe.1
  have hIW := iI_le_normalizer_vI T L V z z'
  set Jp := autOn (thompsonJ (iI T L V z z')) (vI T L V z z') with hJp
  set Ip := autOn (iI T L V z z') (vI T L V z z') with hIp
  have hJI : Jp ≤ Ip := autOn_J_le
  have hIJ : Ip ≤ Subgroup.normalizer (Jp : Set (MulAut ↥(vI T L V z z'))) := autOn_le_normalizer_J
  have hSylT := D.isSylowTwoOf_autOn_T
  have hSylJ : IsSylowTwoOf (autOn T (vI T L V z z') ⊓ Jp) Jp :=
    A4.isSylowTwoOf_inf_normal hSylT hJI hIJ
  have hV : ∀ v : ↥(vI T L V z z'), v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hWe.2 v v.2)
  have hcases := h56 ↥(vI T L V z z') hV Jp (D.autOn_thompsonJ_ne_bot_F4 h1222 h1332 h1334)
    (D.b53Hyp_J_F4 h1222 h1332 h1334)
  rcases S153L.b56_components hcases with ⟨h6, hnc⟩ | ⟨G₁, G₂, hsup, hinf, hc, ⟨h1, hnc1⟩,
      ⟨h2, hnc2⟩⟩ | ⟨N₁, N₂, hne, hN₁J, hN₂J, -, -, hq₁, hq₂, -⟩
  ·
    obtain ⟨e⟩ := SBd.nonempty_mulEquiv_perm_three_of_card_six h6 hnc
    exact D.false_of_goodK_F4 h1222 h1332 h1334 (GoodK.of_mulEquiv e goodModel_perm_three) hJI
      (fun u hu _ => hIJ hu) hSylJ
  ·
    obtain ⟨e₁⟩ := SBd.nonempty_mulEquiv_perm_three_of_card_six h1 hnc1
    obtain ⟨e₂⟩ := SBd.nonempty_mulEquiv_perm_three_of_card_six h2 hnc2
    have hG₁J : G₁ ≤ Jp := hsup ▸ le_sup_left
    have hJG₁ : Jp ≤ Subgroup.normalizer (G₁ : Set (MulAut ↥(vI T L V z z'))) := by
      rw [← hsup]
      refine sup_le Subgroup.le_normalizer fun b hb => ?_
      exact Subgroup.centralizer_le_normalizer _
        (Subgroup.mem_centralizer_iff.mpr fun a ha => hc a ha b hb)
    have hSyl₁ : IsSylowTwoOf (autOn T (vI T L V z z') ⊓ G₁) G₁ := by
      have h := A4.isSylowTwoOf_inf_normal hSylJ hG₁J hJG₁
      rwa [inf_assoc, inf_eq_right.mpr hG₁J] at h
    refine D.false_of_goodK_F4 h1222 h1332 h1334 (GoodK.of_mulEquiv e₁ goodModel_perm_three)
      (hG₁J.trans hJI) (fun u hu hu3 => ?_) hSyl₁
    refine mem_normalizer_of_s3s3 hinf hc (S3Like.of_mulEquiv e₁) (S3Like.of_mulEquiv e₂) ?_ hu3
    rw [hsup]
    exact hIJ hu
  ·
    have hperf : perfectCore Jp ≠ ⊥ := by
      have key : ∀ N : Subgroup (MulAut ↥(vI T L V z z')), N ≤ Jp → N ≠ ⊥ →
          (N = ⊥ ∨ (CFSG.IsQuasisimple ↥N ∧ B56QuasisimpleList ↥N)) → perfectCore Jp ≠ ⊥ := by
        intro N hNJ hN hq h0
        rcases hq with h | ⟨hq, -⟩
        · exact hN h
        · apply hN
          have := le_perfectCore_of_perfect hNJ (S153L.comp_perfect_of_isQuasisimple hq)
          rw [h0] at this
          exact le_bot_iff.mp this
      rcases hne with h | h
      · exact key N₁ hN₁J h hq₁
      · exact key N₂ hN₂J h hq₂
    have hJI' : thompsonJ (iI T L V z z') ≤ iI T L V z z' := iSup₂_le fun _ hA => hA.1
    have hSQJ : SQTKGroup ↥(thompsonJ (iI T L V z z')) :=
      B5.sqtk_of_le (D.sqtk_iI_F4 h1222 h1332 h1334) hJI'
    have hspan : cCompSpan (thompsonJ (iI T L V z z')) = perfectCore (thompsonJ (iI T L V z z')) :=
      cCompSpan_eq_perfectCore_of_subgroup _
        (h39 _ (SQTKHyp.of_sqtkGroup ↥(thompsonJ (iI T L V z z')) hSQJ)).1
    by_contra hall
    apply hperf

    have hcomp : ∀ K ∈ cComp (thompsonJ (iI T L V z z')),
        K ≤ Subgroup.centralizer (vI T L V z z' : Set G) := by
      intro K hK
      by_contra hKC
      refine hall (D.false_of_cComp_F4 h1222 h1332 h1334 h1434 h37 h38 hK fun h => hKC ?_)
      intro k hk
      have hkN := hIW (hJI' (le_of_mem_cComp hK hk))
      have h1 := A1b.conjAct_mem_autOn hkN hk
      rw [h, Subgroup.mem_bot] at h1
      exact A1b.conjAct_eq_one_iff.mp h1
    have hspanle : perfectCore (thompsonJ (iI T L V z z')) ≤
        Subgroup.centralizer (vI T L V z z' : Set G) := by
      rw [← hspan]
      exact sSup_le fun K hK => hcomp K hK
    rw [eq_bot_iff]
    intro φ hφ
    have hmap : perfectCore Jp = (perfectCore ((thompsonJ (iI T L V z z')).subgroupOf
        (Subgroup.normalizer (vI T L V z z' : Set G)))).map (conjAct (vI T L V z z')) := by
      rw [hJp]
      unfold autOn
      exact (map_perfectCore (conjAct (vI T L V z z')) _).symm
    rw [hmap] at hφ
    obtain ⟨x, hx, rfl⟩ := hφ
    have hxJ : (x : G) ∈ perfectCore (thompsonJ (iI T L V z z')) := by
      have h1 := map_perfectCore (Subgroup.normalizer (vI T L V z z' : Set G)).subtype
        ((thompsonJ (iI T L V z z')).subgroupOf (Subgroup.normalizer (vI T L V z z' : Set G)))
      rw [Subgroup.map_subgroupOf_eq_of_le (hJI'.trans hIW)] at h1
      rw [← h1]
      exact ⟨x, hx, rfl⟩
    rw [Subgroup.mem_bot]
    exact A1b.conjAct_eq_one_iff.mpr (hspanle hxJ)

end IData

theorem lemma14_7_32_L2_I_of_F4 (h56 : AsB56) (h39 : A39ForSQTK) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h1434 : Lemma1434One_F4) (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) : Lemma14_7_32_L2_I_F4 := by
  intro G _ _ T L V TY z z' S hz hA hTY hLTY hTYV hO2Y0 hO2G1 hSyl hO2Y hW0 hVTY hL1 hx3 hVcl hCT
  exact IData.false_of_hyps_F4 ⟨S, hz, hA, hTY, hLTY, hTYV, hO2Y0, hO2G1, hSyl, hO2Y, hW0, hVTY,
    hL1, hx3, hVcl, hCT⟩ h56 h39 h37 h38 h1434 h1222 h1332 h1334

end CFSG.Quasithin.H13.L32A.L2
