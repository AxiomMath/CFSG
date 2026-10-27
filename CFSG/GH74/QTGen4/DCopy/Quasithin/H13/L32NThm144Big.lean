module

public import CFSG.Quasithin.H13.L32NThm144Big
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NInputs
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NItems144
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NModule
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NStatements
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneFlag
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneLemma3
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneLemma4Four

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint HSType
open scoped IsMulCommutative

namespace Hyp14310One

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}

theorem isSylowTwoOf_l32nH_F4 (h : Hyp14310One G T L V) (hV : StmtL32NModule_F4) :
    QuasithinUnique.IsSylowTwoOf T (l32nH T V) := by
  obtain ⟨S, hS⟩ := exists_sylow_of_quasithinIsSylowTwo h.fsu.sylow
  have := isSylowTwoOf_of_sylow S (hS ▸ h.le_l32nH_F4 hV)
  rwa [hS] at this

theorem isHzOne_l32nH_F4 (h : Hyp14310One G T L V) (h13322 : Stmt13_3_2_two_F4)
    (hV : StmtL32NModule_F4) (h1283 : Lemma12_8_3_F4) : IsHzOne T L (fsuV1 T V) (l32nH T V) := by
  refine ⟨⟨sup_le ((oTwoUpper_le _).trans inf_le_right) (h.le_l32nH_F4 hV), ?_⟩, le_rfl,
    (h1283 G T L V 3 (h.hyp1281One_F4 h13322 hV)).2.2.2 _ (h.isTSub_fsuV1_F4 hV)⟩
  intro hb
  have hV1 := (hV G T L V h.hyp h.fsu).2.2.2.1
  have hle := h.fsuV1_le_pCoreOf
  rw [hb, le_bot_iff] at hle
  rw [hle, Subgroup.card_bot] at hV1
  omega

theorem fsuU_le_l32nH_F4 (h : Hyp14310One G T L V) (hV : StmtL32NModule_F4) :
    fsuU T V ≤ l32nH T V := by
  have hab := (hV G T L V h.hyp h.fsu).1.1
  have hVN : V ≤ l32nH T V := by
    intro v hv
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun w hw => ?_)
    exact congrArg Subtype.val (hab.is_comm.comm ⟨w, hw.1⟩ ⟨v, hv⟩)
  exact conjClosure_le fun x hx v hv =>
    (l32nH T V).mul_mem ((l32nH T V).mul_mem hx (hVN hv)) ((l32nH T V).inv_mem hx)

theorem fsuU_le_pCoreOf_F4 (h : Hyp14310One G T L V) (h13322 : Stmt13_3_2_two_F4)
    (hV : StmtL32NModule_F4) (h1283 : Lemma12_8_3_F4) (h1284 : Lemma12_8_4_F4) :
    fsuU T V ≤ pCoreOf 2 (l32nH T V) := by
  have h2 := (h1284 G T L V 3 (h.hyp1281One_F4 h13322 hV) (fsuV1 T V) (l32nH T V)
    (h.isTSub_fsuV1_F4 hV) (h.isHzOne_l32nH_F4 h13322 hV h1283)).2.1.1
  exact le_of_tildeOf_le (h.fsuU_le_l32nH_F4 hV) h.fsuV1_le_pCoreOf
    (h2.trans ((Subgroup.closure_le _).mpr fun _ hx => hx.1.1))

theorem fsuU_le_F4 (h : Hyp14310One G T L V) (h13322 : Stmt13_3_2_two_F4) (hV : StmtL32NModule_F4)
    (h1283 : Lemma12_8_3_F4) (h1284 : Lemma12_8_4_F4) : fsuU T V ≤ T :=
  (h.fsuU_le_pCoreOf_F4 h13322 hV h1283 h1284).trans
    (pCoreOf_two_le_of_isSylowTwoOf (h.isSylowTwoOf_l32nH_F4 hV))

end Hyp14310One

theorem thm144Big_of_inputs_F4 (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) (h1222 : Stmt12_2_2_F4)
    (h12213 : Stmt12_2_13_F4) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h14323 : Lemma14323Ge_F4) (h14413 : Lemma14413Big_F4) : Thm144Big_F4 := by
  intro G _ _ T L V h hext
  by_contra hne
  have h13322 := stmt13_3_2_two_of_stmt13_3_2_F4 h1332
  have hV := stmtL32NModule_of_inputs_F4 h1332 h1334
  have h1283 := lemma12_8_3_F4 h12213
  have h1284 := lemma12_8_4_F4 h1222 h37 h38 h39
  obtain ⟨V₂, g, hV₂, hgP, hgH⟩ := h.exists_plane_and_g_F4 h13322 hV (exist1282g_F4 h1222)
  obtain ⟨X, -, -, -, -, -, -, -, ⟨e⟩⟩ :=
    h14413 G T L V h hext hne V₂ g hV₂ hgP hgH
  have hTG₀ : T ≤ L ⊔ T ⊔ (lOne L (fsuV1 T V) ⊔ X ⊔ T) ⊔ (lOne L V₂ ⊔ X ⊔ T) :=
    le_sup_right.trans (le_sup_left.trans le_sup_left)
  have hTcard : Nat.card T ≤ 64 := by
    have hdvd := Subgroup.card_dvd_of_le hTG₀
    rw [Nat.card_congr e.toEquiv, card_SL_four_two] at hdvd
    exact card_le_of_isPGroup_two_of_dvd h.fsu.sylow.1 hdvd
  have hUle : Nat.card ↥(fsuU T V) ≤ Nat.card T :=
    Subgroup.card_le_of_le (h.fsuU_le_F4 h13322 hV h1283 h1284)
  have hU16 : 16 ≤ Nat.card ↥(fsuU T V) := by
    have h16 := h14323 G T L V h
    have hpos : 0 < Nat.card ↥(centerOf (fsuU T V)) := Nat.card_pos
    omega
  obtain ⟨k, hk⟩ := Q8Pow.card_eq_of_extraspecial hext
  rw [hk] at hU16 hUle hne
  have hk3 : k ≤ 2 := by
    by_contra hk3
    have : 2 ^ 7 ≤ 2 ^ (2 * k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases k <;> simp_all

end CFSG.Quasithin.H13
