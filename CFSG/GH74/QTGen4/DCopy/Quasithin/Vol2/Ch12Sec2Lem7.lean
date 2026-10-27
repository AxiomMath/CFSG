module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem7
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL3
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem6
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem7One
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem7Stmts
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2OrbitStmts

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace Lem7

theorem card_of_altSeven_F4 (hA7 : AltNaturalCoverSeven_F4) (h1222 : Stmt12_2_2_F4)
    {T Y VY : Subgroup G} (hHy : Hyp1223 G T Y VY)
    (e7 : (↥Y ⧸ CFSG.pCore 2 ↥Y) ⧸ Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y) ≃*
      alternatingGroup (Fin 7)) :
    Nat.card VY = 2 ^ 4 ∨ Nat.card VY = 2 ^ 6 := by
  obtain ⟨-, -, hall⟩ := ((h1222 G T hHy.simple hHy.nonabelian hHy.qtke hHy.sylow).resolve_left
    hHy.notAlt) Y hHy.maximal hHy.faithful hHy.quasisimple
  obtain ⟨⟨hVT, -, hred, -⟩, -, -, hcomm, hmod⟩ := hall VY hHy.irrPlus
  have hq := hHy.quasisimple
  obtain ⟨-, -, ⟨z, hz⟩⟩ := SteinbergBM.five_core_quotient_center_odd hq
  have h7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
    rw [Lem8.card_alternatingGroup_fin (by norm_num)]
    decide
  have hQ : Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) = 2520 * (2 * z + 1) := by
    rw [(Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y)).card_eq_card_quotient_mul_card_subgroup,
      Nat.card_congr e7.toEquiv, h7, hz]
  have hKV : Y ≤ Subgroup.normalizer (VY : Set G) := hHy.irrPlus.2.2.1
  have hc : ⁅VY, Y⁆ = VY := hHy.irrPlus.2.2.2.1
  have hVLT : VY ≤ Y ⊔ T := hVT.trans le_sup_right
  have hsq : ∀ v : ↥VY, v ^ 2 = 1 := by
    intro v
    have := hred.isElementaryAbelian
    have h2 := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := VY.subgroupOf (Y ⊔ T))
      (⟨v, hVLT v.2⟩ : ↥(Y ⊔ T)) (Subgroup.mem_subgroupOf.mpr v.2)
    exact Subtype.ext (by simpa using congrArg Subtype.val h2)
  have hcomm' := commV_autOn_eq_top hKV hc
  have hfix := fixV_autOn_eq hKV
  rcases hmod with ⟨n, hn, ⟨e⟩, -⟩ | ⟨⟨e⟩, -, -⟩ | ⟨⟨e⟩, -, -⟩ |
      ⟨n, hn5, hn8, ⟨φ, hφ, -⟩, halt⟩ | ⟨hcard, -⟩ | ⟨hU, -⟩ | ⟨-, -, ⟨e6⟩, -⟩
  · exfalso
    rw [Nat.card_congr e.toEquiv] at hQ
    rcases card_sl_three_four_five hn with h | h | h <;> rw [h] at hQ <;> omega
  · exfalso
    rw [Nat.card_congr e.toEquiv] at hQ
    rcases card_sl_three_four_five (Or.inl rfl) with h | h | h <;> rw [h] at hQ <;> omega
  · exfalso
    rw [Nat.card_congr e.toEquiv, Lem8.card_sl_five_zmod_two] at hQ
    omega
  · have hle := pCore_le_ker_of_surjective_alternating hn5 φ hφ
    have : IsSimpleGroup (alternatingGroup (Fin n)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; exact hn5)
    obtain ⟨-, en, -⟩ := SteinbergBM.five_quasisimple_centerless_image hq
      (alternatingGroup_nonabelian (by omega)) (QuotientGroup.lift (CFSG.pCore 2 ↥Y) φ hle)
      (QuotientGroup.lift_surjective_of_surjective _ φ hφ hle)
    have hn7 : n = 7 := by
      have h1 := Nat.card_congr (en.symm.trans e7).toEquiv
      rw [h7, Lem8.card_alternatingGroup_fin (by omega)] at h1
      interval_cases n <;> first | rfl | exact absurd h1 (by decide)
    subst hn7
    have hZ := hA7 ↥VY hsq (autOn Y VY) _ hfix.symm.le hcomm' halt
    rw [hZ] at halt
    obtain ⟨π, hπ⟩ := halt
    have hcard := G64.RealizesVia.card_eq hπ
    have hsec := Explicit.card_dn_sec (n := 7) (by norm_num) .alternating
    right
    rw [Subgroup.card_top, Subgroup.card_bot, mul_one] at hcard
    split_ifs at hsec with he
    · exact absurd he (by decide)
    · exact hcard.trans hsec
  · exact Or.inl hcard
  · exfalso
    rw [card_of_lieModel_psu_three_three hU] at hQ
    omega
  · exfalso
    have h1 := Nat.card_congr (e6.symm.trans e7).toEquiv
    rw [h7, Lem8.card_alternatingGroup_fin (by norm_num)] at h1
    exact absurd h1 (by decide)

end Lem7

open Lem7

theorem stmt12_2_7_nonsolvable_F4 (h331 : Stmt3_3_1_F4) (h1222 : Stmt12_2_2_F4)
    (h6220 : Stmt6_2_20_F4) (hE22 : E2.E22StatementNoN) (h36 : A36ForSQTK) (h37 : A37ForSQTK)
    (h128 : Lemma128One)
    (hA7 : AltNaturalCoverSeven_F4) (hEq : Lem1227ListEqNoN) (hLt : Lem1227ListLtNoN)
    (hNQ : Lem1227NotQuasisimple_F4) {T L V H : Subgroup G} (hH : Hyp1223 G T L V)
    (hCZ : Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤
      Subgroup.normalizer (L : Set G))
    (hHs : IsHStar T (Subgroup.normalizer (L : Set G)) H) (hns : ¬ Group.IsSolvable ↥H) :
    LieModel (↥(oTwoUpper H) ⧸ CFSG.pCore 2 ↥(oTwoUpper H)) .PSL 2 2 2 ∧
      ∃ Y : Subgroup G, oTwoUpper H ≤ Y ∧ quasithinIsMaximalLocal T Y ∧
        quasithinIsFaithfulLocal T Y ∧
        ((Y = oTwoUpper H ∧ IsA5ModuleSum (oTwoUpper H) ⁅VZ T H, oTwoUpper H⁆) ∨
          (Nonempty ((↥Y ⧸ CFSG.pCore 2 ↥Y) ⧸ Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y) ≃*
              alternatingGroup (Fin 7)) ∧
            CFSG.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y) ∧
            T ≤ Subgroup.normalizer (Y : Set G) ∧
            ∀ VY : Subgroup G, IsIrrPlusIn Y (reducedAggregate (Y ⊔ T)) T VY →
              T ≤ Subgroup.normalizer (VY : Set G) ∧
                (Nat.card VY = 2 ^ 4 ∨ Nat.card VY = 2 ^ 6))) := by
  obtain ⟨S, rfl⟩ := exists_sylow_coe_eq hH.sylow
  set M := Subgroup.normalizer (L : Set G) with hMdef
  have hmin := minParabolic_F4 h331 hH hHs
  have hU := isTwoReducedIn_VZ hH hHs
  have hsqtk : SQTKGroup ↥H :=
    sqtkGroup_of_pCoreOf_ne_bot hH.qtke hH.simple hH.nonabelian hHs.1.2

  obtain ⟨⟨X, hXc, hHX, hXq0, hE⟩, -⟩ := hE22 G H (S : Subgroup G) (H ⊓ M) hmin hsqtk hns
  have hXq : CFSG.IsQuasisimple (↥X ⧸ CFSG.pCore 2 ↥X) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open ↥X 2).symm)
      (A3.isQuasisimple_iff_open.mpr hXq0)

  have hXV : ⁅VZ (S : Subgroup G) H, X⁆ ≠ ⊥ := by
    intro h
    have hXC : X ≤ Subgroup.centralizer (VZ (S : Subgroup G) H : Set G) :=
      Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h)
    apply hHs.2.1
    rw [hHX]
    exact sup_le (hXC.trans ((centralizer_VZ_le _ H).trans hCZ)) hH.normalizes
  have hXf : quasithinIsFaithfulLocal (S : Subgroup G) X :=
    have h2 : ∃ W : Subgroup G, IsTwoReducedIn H W ∧ ⁅W, X⁆ ≠ ⊥ := ⟨_, hU, hXV⟩
    ((lemma_1_2_10_of_a36 hH.qtke hH.simple hH.nonabelian h36 S hHs.1
      hXc).out 1 2).mpr h2

  obtain ⟨Y, hXY, hYmax⟩ := exists_maximalLocal_ge hXf.1
  have hYf := (lemma_1_2_9_one hH.qtke hH.simple hH.nonabelian h37 h128 hH.sylow hXf hYmax.1
    hXY).2
  have hYq := hNQ G S L V H X Y hH hCZ hHs hns hXc hHX hXq hXY hYmax hYf

  obtain ⟨hTY, ⟨VY, hVY⟩, hallY⟩ := ((h1222 G S hH.simple hH.nonabelian hH.qtke
    hH.sylow).resolve_left hH.notAlt) Y hYmax hYf hYq
  have hHy : Hyp1223 G S Y VY :=
    ⟨hH.simple, hH.nonabelian, hH.qtke, hH.sylow, hH.notAlt, hYmax, hYf, hYq, hTY, hVY⟩
  obtain ⟨⟨-, hTVY, -, -⟩, -, -, hcommY, hmodY⟩ := hallY VY hVY

  have hTX : (S : Subgroup G) ≤ Subgroup.normalizer (X : Set G) := by
    have heq := lemma_1_2_8_one hH.qtke hH.simple hH.nonabelian h37 h128 hXf.1 hYmax.1 hXY
    intro t ht
    have ht' : t ∈ (S : Subgroup G) ⊓ Subgroup.normalizer (Y : Set G) := ⟨ht, hTY ht⟩
    rw [← heq] at ht'
    exact ht'.2
  have hK : oTwoUpper H = X := oTwoUpper_eq hH.sylow.1 hXc hHX hTX
  rw [hK]
  rcases eq_or_lt_of_le hXY with hXYe | hXYl
  ·
    subst hXYe
    have hLie := hEq G S X VY H (H ⊓ M) hHy hTVY ⟨hcommY, hmodY⟩ hHX hmin hE
    refine ⟨hLie, X, le_rfl, hYmax, hYf, Or.inl ⟨rfl, ?_⟩⟩
    have hNX : quasithinIsMaxTwoLocal (Subgroup.normalizer (X : Set G)) := by
      obtain ⟨⟨hmax2, -, -⟩, -⟩ :=
        (h331 G S hH.simple hH.nonabelian hH.qtke hH.sylow).2 X hYmax hYq
      rwa [conjClosure_eq_self_of_normalizes hTY] at hmax2
    have hVH : VZ (S : Subgroup G) H ≤ X ⊔ S := hHX ▸ hU.1
    have hred : IsPrimeReduced 2 ((VZ (S : Subgroup G) H).subgroupOf (X ⊔ S)) :=
      hHX ▸ (isTwoReducedIn_iff_isPrimeReduced_subgroupOf.mp hU).2
    rcases h6220 G S (Subgroup.normalizer (X : Set G)) X (VZ (S : Subgroup G) H) 2 hH.simple
        hH.nonabelian hH.qtke hH.sylow hNX hTY hYmax hYf Subgroup.le_normalizer le_rfl le_rfl
        hLie hVH hred hXV with ⟨-, hA5, -⟩ | hLie' | hM22 | hM23
    · exact hA5
    · exfalso
      rcases hLie' with h | h
      · exact hH.notAlt (Or.inl h)
      · exact hH.notAlt (Or.inr (Or.inl h))
    · exact absurd (Or.inr (Or.inr (Or.inl hM22))) hH.notAlt
    · exact absurd (Or.inr (Or.inr (Or.inr (Or.inl hM23)))) hH.notAlt
  ·
    obtain ⟨hLie, ⟨e7⟩⟩ :=
      hLt G S X Y VY H (H ⊓ M) hHy hTVY ⟨hcommY, hmodY⟩ hXf.1 hXYl hTX hXq hHX hmin hE
    refine ⟨hLie, Y, hXY, hYmax, hYf, Or.inr ⟨⟨e7⟩, hYq, hTY, fun VY' hVY' => ?_⟩⟩
    obtain ⟨⟨-, hTVY', -, -⟩, -⟩ := hallY VY' hVY'
    have hHy' : Hyp1223 G S Y VY' :=
      ⟨hH.simple, hH.nonabelian, hH.qtke, hH.sylow, hH.notAlt, hYmax, hYf, hYq, hTY, hVY'⟩
    exact ⟨hTVY', card_of_altSeven_F4 hA7 h1222 hHy' e7⟩

theorem stmt12_2_7_of_inputs_F4 (h331 : Stmt3_3_1_F4) (h1222 : Stmt12_2_2_F4) (h323 : Stmt3_2_3)
    (h6220 : Stmt6_2_20_F4) (hE22 : E2.E22StatementNoN) (h36 : A36ForSQTK) (h37 : A37ForSQTK)
    (h128 : Lemma128One)
    (hA7 : AltNaturalCoverSeven_F4) (hEq : Lem1227ListEqNoN) (hLt : Lem1227ListLtNoN)
    (hNQ : Lem1227NotQuasisimple_F4) : Stmt12_2_7_F4 := by
  intro G _ _ T L V H hH hCZ hHs
  have h1226 := stmt12_2_6_of_F4 h1222 h323
  exact ⟨stmt12_2_7_one_F4 h331 h1222 h1226 hH hCZ hHs, fun hns =>
    stmt12_2_7_nonsolvable_F4 h331 h1222 h6220 hE22 h36 h37 h128 hA7 hEq hLt hNQ hH hCZ hHs hns⟩

theorem stmt12_2_7_of_F4
    (h331 : Stmt3_3_1_F4) (h1222 : Stmt12_2_2_F4) (h323 : Stmt3_2_3)
    (h6220 : Stmt6_2_20_F4) (hE22 : E2.E22StatementNoN) (h37 : A37ForSQTK) (h128 : Lemma128One)
    (hEq : Lem1227ListEqNoN) (hLt : Lem1227ListLtNoN) (hNQ : Lem1227NotQuasisimple_F4) :
    Stmt12_2_7_F4 :=
  stmt12_2_7_of_inputs_F4 h331 h1222 h323 h6220 hE22 VolI.a36ForSQTK_holds h37 h128
    (fun V _ _ => VolI.altNaturalCoverSeven_holds V) hEq hLt hNQ

end CFSG.Quasithin.H13
