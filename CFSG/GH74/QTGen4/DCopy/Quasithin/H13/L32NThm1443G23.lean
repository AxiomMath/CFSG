module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem1444f
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem1445a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem1445d
public import CFSG.GH74.QTGen4.Recog.G23.Consumer
public import CFSG.GH74.QTGen4.Recog.G23.Abstract
public import CFSG.Quasithin.H13.GoldschmidtQ8SqE9

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative
open scoped MatrixGroups

variable {G : Type} [Group G]

namespace Hyp14310One

variable [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}

theorem g23Ctx_F4 (h : Hyp14310One G T L V) (h13322 : Stmt13_3_2_two_F4) (hV : StmtL32NModule_F4)
    (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4) (h1284 : Lemma12_8_4_F4)
    (h14441 : Lemma1444One_F4) (h14442 : Lemma1444Two_F4) (h14444 : Lemma1444Four_F4)
    (h14447 : Lemma1444Seven_F4) (h14452 : Lemma1445Two_F4) (h14453 : Lemma1445Three_F4)
    (hdec : Q8SqE9Decomp) (hext : CFSG.IsExtraspecialPGroup 2 ↥(fsuU T V))
    (h32 : Nat.card ↥(fsuU T V) = 2 ^ 5) (hG2 : ¬ LieModel G .G2 0 3 1)
    (h14451 : Lemma1445One_F4) :
    ∃ H H₁ H₂ M : Subgroup G, CFSG.GH74.QTGen4.Recog.G23.G23Ctx G T H H₁ H₂ M := by
  have h1281 := h.hyp1281One_F4 h13322 hV
  obtain ⟨hVe, hV8, -, hV1, -⟩ := hV G T L V h.hyp h.fsu
  obtain ⟨hUQ, N, -, -, hN9, hN2⟩ := h14452 G T L V h hext h32 hG2
  obtain ⟨V₂, g, ⟨hV₂, hV₁₂⟩, hgP, hgH⟩ := h.exists_plane_and_g_F4 h13322 hV (exist1282g_F4 h1222)
  obtain ⟨⟨U₀, -, hU₀ext, hΦ, hU₀Z⟩, -⟩ :=
    lemma12_8_8_n3_F4 h1222 h12213 (h.setting1282One_F4 h13322 hV ⟨hV₂, hV₁₂⟩)
  have hV1Z := fsuV1_le_centerOf_of_decomp hU₀Z hU₀ext hΦ
  have hZ2 : Nat.card ↥(centerOf (fsuU T V)) = 2 := by
    rw [l32n_card_centerOf]
    exact hext.2.2.2
  have hZV1 : centerOf (fsuU T V) = fsuV1 T V :=
    (Subgroup.eq_of_le_of_card_ge hV1Z (by rw [hZ2, hV1])).symm
  have hk : IsQ8CentralPow 2 ↥(fsuU T V) := lemma1442Q8Four_of_inputs_F4 hV h hext h32
  have hQ8 : IsQ8Sq ↥(pCoreOf 2 (l32nH T V)) := hUQ ▸ isQ8Sq_of_isQ8CentralPow_two hk
  have hfaith : centralizerMod (centerOf (pCoreOf 2 (l32nH T V))) (l32nH T V)
      (pCoreOf 2 (l32nH T V)) = pCoreOf 2 (l32nH T V) := by
    rw [← hUQ, hZV1]
    exact (h1284 G T L V 3 h1281 (fsuV1 T V) (l32nH T V) (h.isTSub_fsuV1_F4 hV)
      (h.isHzOne_l32nH_F4 h13322 hV (lemma12_8_3_F4 h12213))).2.2.2.trans hUQ.symm
  obtain ⟨hK1, hK9⟩ := h14441 G T L V h hext h32 hG2
  obtain ⟨hQK, K₁, K₂, hsup, hinf, hcomm, he₁, he₂, hw⟩ :=
    hdec G (l32nH T V) hQ8 hK1 hK9 hfaith
  obtain ⟨-, -, hinv, -⟩ := h14442 G T L V h hext h32 hG2 V₂ g ⟨hV₂, hV₁₂⟩ hgP hgH
  have hT := h14453 G T L V h hext h32 hG2 V₂ g ⟨hV₂, hV₁₂⟩ hgP hgH
  have hHKT := (h14447 G T L V h hext h32 hG2).1
  have hgN : g ∈ Subgroup.normalizer (V₂ : Set G) :=
    (Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hgP.2 V₂) ⟨2, le_rfl, hV₂⟩)
  have hWgH := conjugate_le_l32nH (T := T) (V := V) ⟨hV₂, hV₁₂⟩ hgN
  have hwinv : ∀ w ∈ CFSG.conjugate (fsuU T V ⊓ Subgroup.centralizer (V₂ : Set G)) g,
      w ∉ pCoreOf 2 (l32nH T V) →
      ∀ x ∈ oTwoUpper (l32nH T V), w * x * w⁻¹ * x ∈ pCoreOf 2 (l32nH T V) := by
    intro w hwW hwQ x hx
    have hxH : x ∈ l32nH T V := oTwoUpper_le _ hx
    have hwH : w ∈ l32nH T V := hWgH hwW
    have hne : (QuotientGroup.mk ⟨w, hwH⟩ : OTwoQuot (l32nH T V)) ≠ 1 := by
      intro h1
      rw [QuotientGroup.eq_one_iff] at h1
      exact hwQ ⟨_, h1, rfl⟩
    have h1 := hinv (QuotientGroup.mk ⟨w, hwH⟩) ⟨⟨w, hwH⟩, hwW, rfl⟩ hne
      (QuotientGroup.mk ⟨x, hxH⟩) ⟨⟨x, hxH⟩, hx, rfl⟩
    have h2 : (QuotientGroup.mk (⟨w, hwH⟩ * ⟨x, hxH⟩ * ⟨w, hwH⟩⁻¹ * ⟨x, hxH⟩ :
        ↥(l32nH T V)) : OTwoQuot (l32nH T V)) = 1 := by
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [h1, inv_mul_cancel]
    rw [QuotientGroup.eq_one_iff] at h2
    exact ⟨_, h2, rfl⟩
  have hKN₁ : oTwoUpper (l32nH T V) ≤ Subgroup.normalizer (K₁ : Set G) := by
    rw [← hsup]
    exact sup_le Subgroup.le_normalizer
      ((Subgroup.le_centralizer_iff.mp hcomm).trans (Subgroup.centralizer_le_normalizer _))
  have hKN₂ : oTwoUpper (l32nH T V) ≤ Subgroup.normalizer (K₂ : Set G) := by
    rw [← hsup]
    exact sup_le (hcomm.trans (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer
  have hHN : ∀ i : Fin 2, l32nH T V ≤
      Subgroup.normalizer ((if i = 0 then K₁ else K₂ : Subgroup G) : Set G) := by
    intro i
    have hK : oTwoUpper (l32nH T V) ≤
        Subgroup.normalizer ((if i = 0 then K₁ else K₂ : Subgroup G) : Set G) := by
      fin_cases i
      · exact hKN₁
      · exact hKN₂
    have hW : CFSG.conjugate (fsuU T V ⊓ Subgroup.centralizer (V₂ : Set G)) g ≤
        Subgroup.normalizer ((if i = 0 then K₁ else K₂ : Subgroup G) : Set G) := by
      intro w hwW
      by_cases hwQ : w ∈ pCoreOf 2 (l32nH T V)
      · exact hK (hQK hwQ)
      have := hw w (hWgH hwW) (hwinv w hwW hwQ)
      fin_cases i
      · exact this.1
      · exact this.2
    calc l32nH T V = oTwoUpper (l32nH T V) ⊔ T := hHKT
      _ ≤ _ := sup_le hK (by
        rw [hT]
        exact sup_le ((hUQ.le.trans hQK).trans hK) hW)
  have hindex : (K₁ ⊔ K₂).relIndex (l32nH T V) = 2 := by
    rw [hsup, Subgroup.relIndex]
    have hker : (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥(l32nH T V))).ker ≤
        (oTwoUpper (l32nH T V)).subgroupOf (l32nH T V) := by
      intro x hx
      rw [QuotientGroup.ker_mk'] at hx
      exact hQK ⟨x, hx, rfl⟩
    rw [← Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective _) hker]
    have h18 : Nat.card (OTwoQuot (l32nH T V)) = 18 := by
      rw [← N.card_mul_index, hN9, hN2]
    have := (imageOTwoQuot (l32nH T V) (oTwoUpper (l32nH T V))).card_mul_index
    change Nat.card ↥(imageOTwoQuot (l32nH T V) (oTwoUpper (l32nH T V))) *
      (imageOTwoQuot (l32nH T V) (oTwoUpper (l32nH T V))).index = _ at this
    rw [hK9, h18] at this
    change (imageOTwoQuot (l32nH T V) (oTwoUpper (l32nH T V))).index = 2
    omega
  have hKQ : ∀ a ∈ oTwoUpper (l32nH T V), ∀ b ∈ oTwoUpper (l32nH T V),
      a⁻¹ * b⁻¹ * a * b ∈ pCoreOf 2 (l32nH T V) := by
    intro a ha b hb
    have haH : a ∈ l32nH T V := oTwoUpper_le _ ha
    have hbH : b ∈ l32nH T V := oTwoUpper_le _ hb
    have hA : (QuotientGroup.mk (⟨a, haH⟩ : ↥(l32nH T V)) : OTwoQuot (l32nH T V)) ∈
        imageOTwoQuot (l32nH T V) (oTwoUpper (l32nH T V)) :=
      Subgroup.mem_map.mpr ⟨⟨a, haH⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
    have hB : (QuotientGroup.mk (⟨b, hbH⟩ : ↥(l32nH T V)) : OTwoQuot (l32nH T V)) ∈
        imageOTwoQuot (l32nH T V) (oTwoUpper (l32nH T V)) :=
      Subgroup.mem_map.mpr ⟨⟨b, hbH⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩
    have hc : (QuotientGroup.mk (⟨a, haH⟩ : ↥(l32nH T V)) : OTwoQuot (l32nH T V)) *
        QuotientGroup.mk ⟨b, hbH⟩ = QuotientGroup.mk ⟨b, hbH⟩ * QuotientGroup.mk ⟨a, haH⟩ :=
      congrArg Subtype.val (hK1.1.is_comm.comm ⟨_, hA⟩ ⟨_, hB⟩)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul] at hc
    have key := QuotientGroup.eq.mp hc.symm
    refine Subgroup.mem_map.mpr ⟨(⟨b, hbH⟩ * ⟨a, haH⟩ : ↥(l32nH T V))⁻¹ *
      (⟨a, haH⟩ * ⟨b, hbH⟩), key, ?_⟩
    show (((⟨b, hbH⟩ * ⟨a, haH⟩ : ↥(l32nH T V))⁻¹ * (⟨a, haH⟩ * ⟨b, hbH⟩) :
        ↥(l32nH T V)) : G) = a⁻¹ * b⁻¹ * a * b
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hQn : l32nH T V ≤ Subgroup.normalizer (pCoreOf 2 (l32nH T V) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (l32nH T V)
  have hHNK : l32nH T V ≤ Subgroup.normalizer ((oTwoUpper (l32nH T V) : Subgroup G) : Set G) := by
    rw [← hsup]
    exact CFSG.GH74.QTGen4.Recog.G23.le_normalizer_sup_aux (hHN 0) (hHN 1)
  have hTK : T ≤ oTwoUpper (l32nH T V) ⊔
      CFSG.conjugate (fsuU T V ⊓ Subgroup.centralizer (V₂ : Set G)) g :=
    hT.le.trans (sup_le ((hUQ.le.trans hQK).trans le_sup_left) le_sup_right)
  have hHKB : l32nH T V ≤ oTwoUpper (l32nH T V) ⊔
      CFSG.conjugate (fsuU T V ⊓ Subgroup.centralizer (V₂ : Set G)) g :=
    hHKT.le.trans (sup_le le_sup_left hTK)
  have hone : G23Type.G23One (l32nH T V) K₁ K₂ := by
    have hK₁ : K₁ ≤ l32nH T V := (le_sup_left.trans hsup.le).trans (oTwoUpper_le _)
    have hK₂ : K₂ ≤ l32nH T V := (le_sup_right.trans hsup.le).trans (oTwoUpper_le _)
    refine ⟨hK₁, hK₂, hHN 0, hHN 1, he₁, he₂, hindex, ?_, ?_⟩
    · rw [hinf, ← hUQ, hZV1, hV1]
    · rw [hinf, ← hUQ, hZV1]
      exact normalizer_eq_centralizer_self_of_card_two hV1
  have htwo : G23Type.G23Two L := by
    have hFL : quasithinGenFitting L = pCoreOf 2 L := h.fsu.faithful.2.2.1
    have hVL := h14444 G T L V h hext h32 hG2
    refine ⟨?_, ?_, ?_⟩
    · rw [hFL, ← hVL]
      exact hVe
    · rw [hFL, ← hVL, hV8]
    · rw [hFL]
      exact exists_surj_SL32_of_lieModel h.hyp.linear
  refine ⟨l32nH T V, K₁, K₂, L, ?_⟩
  exact
    { simple := h.fsu.simple
      sylow := h.fsu.sylow
      tH := le_sup_right.trans hHKT.symm.le
      tM := (h13322 G T L h.hyp.h13 L h.hyp.h13.faithful).1.trans (h14451 G T L V h hext h32 hG2).le
      one := hone
      two := htwo
      inv := by
        rw [hsup]
        exact CFSG.GH74.QTGen4.Recog.G23.inv_of_decomp (oTwoUpper_le _) hQK hHNK hQn hWgH hHKB
          hKQ hwinv }

end Hyp14310One

theorem thm1443One_of_core_G23_F4
    (hG23 : ∀ (G : Type) [Group G] [Finite G] (T H H₁ H₂ M : Subgroup G),
      CFSG.GH74.QTGen4.Recog.G23.G23Ctx G T H H₁ H₂ M → LieModel G .G2 0 3 1)
    (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) (h1222 : Stmt12_2_2_F4)
    (h12213 : Stmt12_2_13_F4) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hRest : Lemma14323Rest_F4) (hCTL : Lemma1444CTL_F4) : Thm1443One_F4 := by
  have h14451 := lemma1445One_of_inputs_F4 h1332 h1334 h1222 h12213 h37 h38 h39 hRest hCTL
  have h14453 := lemma1445Three_of_inputs_F4 h1332 h1334 h1222 h12213 h37 h38 h39 hRest h14451
  intro G _ _ T L V h hext h32
  by_contra hG2
  obtain ⟨H, H₁, H₂, M, hctx⟩ := h.g23Ctx_F4 (stmt13_3_2_two_of_stmt13_3_2_F4 h1332)
    (stmtL32NModule_of_inputs_F4 h1332 h1334) h1222 h12213 (lemma12_8_4_F4 h1222 h37 h38 h39)
    (lemma1444One_of_inputs_F4 h1332 h1334 h1222 h12213 h37 h38 h39 hRest)
    (lemma1444Two_of_inputs_F4 h1332 h1334 h1222 h12213 h37 h38 h39 hRest
      (lemma1444Six_of_inputs_F4 h1332 h1334 h1222 h12213 h37 h38 h39 hRest hCTL))
    (lemma1444Four_of_inputs_F4 h1332 h1334 h1222 h12213)
    (lemma1444Seven_of_inputs_F4 h1332 h1334 h1222 h12213 h37 h38 h39 hRest)
    (lemma1445Two_of_inputs_F4 h1332 h1334 h1222 h12213 h37 h38 h39 hRest hCTL h14453)
    h14453 q8SqE9Decomp_holds hext h32 hG2 h14451
  exact hG2 (hG23 G T H H₁ H₂ M hctx)

end CFSG.Quasithin.H13
