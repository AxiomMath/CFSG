module

public import CFSG.Quasithin.H13.L32NLem14323b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14323a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14332a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14332h
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NThm144Big
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneTwelve

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin

namespace L14323

variable {G : Type} [Group G]

theorem exists_ctx_F4 [CFSG.GH74.QTGen4.Finite4 G] (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4) (h1288 : Lemma12_8_8_two_F4)
    (h12811 : Lemma12_8_11_F4) (h12811h : Lemma12_8_11_hat_F4) (h12813 : Lemma12_8_13_F4)
    (hG112 : G11.TheoremG112Fix) {T L V : Subgroup G} (h : Hyp14310One G T L V)
    {V₂ : Subgroup G} {g : G} (hV₂ : IsL32NPlane T V V₂) (hgP : g ∈ p128 T L V)
    (hgN : g ∉ l32nH T V) (D : HatModelU (fsuU T V)) (hd : Module.finrank (ZMod 2) D.V = 4) :
    ∃ a c : G, Ctx G T L V V₂ g a c D := by
  have h13322 := stmt13_3_2_two_of_stmt13_3_2_F4 h1332
  have hV := stmtL32NModule_of_inputs_F4 h1332 h1334
  have hs := h.setting1282One_F4 h13322 hV hV₂
  obtain ⟨hVe, hV8, hLTV, hV1, -⟩ := hV G T L V h.hyp h.fsu
  obtain ⟨⟨hVE, hV4⟩, ⟨hrel, hfix⟩, hlt⟩ := lemma14323Parts_of_inputs_F4 h1332 h1334 h1222 h12213
    h12811 h12811h h12813 G T L V h V₂ g hV₂ hgP hgN D hd

  have hV₂4 : Nat.card V₂ = 4 := hV₂.1.2.1
  have hlt12 : fsuV1 T V < V₂ := lt_of_le_of_ne hV₂.2 fun he => by
    rw [he] at hV1; omega
  obtain ⟨a, haV₂, ha1⟩ := IsConcreteLE.exists_of_lt hlt12
  have hlt2 : V₂ < V := lt_of_le_of_ne hV₂.1.1 fun he => by
    rw [he] at hV₂4; omega
  obtain ⟨c, hcV, hc2⟩ := IsConcreteLE.exists_of_lt hlt2
  have hVU : V ≤ fsuU T V := le_conjClosure V _
  have hVcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hVe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hVsq : ∀ x ∈ V, x * x = 1 := fun x hx => by rw [← pow_two]; exact hVe.2 x hx

  have hTH : T ≤ l32nH T V := h.le_l32nH_F4 hV
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := le_sup_right.trans hLTV
  have hTL : T ≤ Subgroup.normalizer (L : Set G) :=
    (h1332 G T L h.hyp.h13 L h.hyp.h13.faithful).2.1.1
  have hTodd : Odd ((D.img T).relIndex (D.img (l32nH T V))) := by
    have hdvd := L14332.relIndex_img_dvd D hTH (L14332.l32nH_le_normalizer_fsuU T V)
    have hsyl := (h.isSylowTwoOf_l32nH_F4 hV).2.2
    have hodd : Odd (T.relIndex (l32nH T V)) := Nat.odd_iff.mpr (by
      rcases Nat.even_or_odd (T.relIndex (l32nH T V)) with he | ho
      · exact absurd (even_iff_two_dvd.mp he) hsyl
      · exact Nat.odd_iff.mp ho)
    exact Odd.of_dvd_nat hodd hdvd
  have hgN₂ : g ∈ Subgroup.normalizer (V₂ : Set G) :=
    Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hgP.2 V₂) ⟨2, le_rfl, hV₂.1⟩
  have hWg : CFSG.conjugate (l32nW T V V₂) g ≤ l32nH T V :=
    (L14332.conj_le_centralizer_of_le inf_le_right hV₂.2 hgN₂).trans
      (Subgroup.centralizer_le_normalizer _)
  have hzUg := L14332.conj_zU_le_F4 h12813 hs hgP hgN
  obtain ⟨hg101, -, hg112⟩ := lemma12_8_12_hat_of_F4 h1222 h12213 hG112 G T L V 3 (fsuV1 T V) V₂ hs
    g hgP hgN a haV₂ ha1 D

  have hrot : ∃ l ∈ L, l ^ 3 = 1 ∧ l ∈ l32nH T V ∧ l * a * l⁻¹ = c := by
    obtain ⟨_, S⟩ := L14332.exists_setting_F4 h1332 h1334 h1222 h hV₂
    obtain ⟨z, -, -, hz, hz1, -⟩ := S.exists_basis_F4
    have haV : a ∈ V := hV₂.1.1 haV₂
    have hzV₂ : z ∈ V₂ := hV₂.2 hz
    obtain ⟨l, hlL, hl3, hlz, hla, -⟩ := S.exists_rot_F4 (Subgroup.mem_inf.mp hz).1 haV hcV
      (fun he => ha1 (by rw [he]; exact one_mem _)) (fun he => hc2 (by rw [he]; exact one_mem _))
      (fun he => ha1 (by rw [he]; exact hz)) (fun he => hc2 (by rw [he]; exact hzV₂))
      (fun he => hc2 (by rw [← he]; exact haV₂))
      (fun he => hc2 (by rw [he]; exact V₂.mul_mem hzV₂ haV₂))
    exact ⟨l, hlL, hl3, S.mem_g1_F4 hz hz1 hlz, hla⟩

  have hzU : fsuV1 T V < centerOf (fsuU T V) →
      D.img (CFSG.conjugate (centerOf (fsuU T V)) g) ≠ ⊥ := by
    intro hlt' hbot
    obtain ⟨-, -, h3, -⟩ := h12813 G T L V 3 (fsuV1 T V) V₂ hs g hgP hgN
    apply h3 hlt'
    intro ζ hζ
    have hζH : ζ ∈ l32nH T V := hzUg hζ
    have hζN := L14332.l32nH_le_normalizer_fsuU T V hζH
    have h1 : D.ρ ⟨ζ, hζN⟩ = 1 := by
      have hmem := L128A.HatU.rho_mem_img D hζ hζN
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hmem
    exact (L14332.rho_eq_one_iff_mem hζH hζN).mp h1

  have hquad : centerOf (fsuU T V) = fsuV1 T V → ∃ q : D.V → ZMod 2,
      (∀ u ∈ fsuU T V, q (D.π u) = 0 ↔ u ^ 2 = 1) ∧
        (∀ v w, q (v + w) = q v + q w + D.B v w) ∧
        ∀ γ ∈ D.img (l32nH T V), ∀ v, q (γ v) = q v := by
    intro hZ
    obtain ⟨-, -, -, hq⟩ := h1288 G T L V 3 (fsuV1 T V) V₂ hs D
    refine hq (L14332.frattiniOf_eq_bot_of_sq (L14332.zU_comm _) fun y hy => ?_)
    have hy' : y ∈ centerOf (fsuU T V) := hy
    rw [hZ] at hy'
    exact hVsq y (Subgroup.mem_inf.mp hy').1
  exact ⟨a, c,
    { hyp := h, plane := hV₂, setting := hs, gP := hgP, gN := hgN, d4 := hd, aV₂ := haV₂,
      a1 := ha1, cV := hcV, c2 := hc2, V_U := hVU, V_comm := hVcomm, V_sq := hVsq,
      card_V1 := hV1, VZ := lemma12_8_8_three_F4 h1222 h12213 hs, hatV := hVE,
      card_hatV := hV4, relIdx := hrel, zU_fix := hfix, lt_H := hlt, TH := hTH, TV := hTV,
      TL := hTL, LV := le_sup_left.trans hLTV, T2 := h.fsu.sylow.1, Todd := hTodd,
      zUg_le := hzUg,
      Wg_le := hWg, rot := hrot, g101 := hg101, g112 := hg112, zU_ne := hzU,
      quad := hquad }⟩

end L14323

end CFSG.Quasithin.H13
