module

public import CFSG.Quasithin.H13.L32NLem14332b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NItems143b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14332a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NThm144Big
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneModel

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped commutatorElement

namespace L14332

variable {G : Type} [Group G]

theorem exists_ctx14332_F4 [CFSG.GH74.QTGen4.Finite4 G] (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (h12810 : Lemma12_8_10_F4) (h12813 : Lemma12_8_13_F4)
    (h14331 : Lemma14331One_F4) {T L V : Subgroup G} (h : Hyp14310One G T L V)
    (hlt : fsuV1 T V < centerOf (fsuU T V)) :
    ∃ (V₂ : Subgroup G) (g a : G) (D : HatModelU (fsuU T V)), Ctx14332 G T L V V₂ g a D := by
  have h13322 := stmt13_3_2_two_of_stmt13_3_2_F4 h1332
  have hV := stmtL32NModule_of_inputs_F4 h1332 h1334
  have h1283 := lemma12_8_3_F4 h12213
  have h1284 := lemma12_8_4_F4 h1222 h37 h38 h39
  obtain ⟨V₂, g, hV₂, hgP, hgN⟩ := h.exists_plane_and_g_F4 h13322 hV (exist1282g_F4 h1222)
  have hs := h.setting1282One_F4 h13322 hV hV₂
  obtain ⟨D⟩ := hs.exists_hatModelU_F4 h1222 h12213
  obtain ⟨hVe, -, -, hV1, -⟩ := hV G T L V h.hyp h.fsu

  have hV₂4 : Nat.card V₂ = 4 := hV₂.1.2.1
  have hlt12 : fsuV1 T V < V₂ := lt_of_le_of_ne hV₂.2 fun he => by
    rw [he] at hV1; omega
  obtain ⟨a, haV₂, ha1⟩ := IsConcreteLE.exists_of_lt hlt12
  have hVU : V ≤ fsuU T V := le_conjClosure V _
  have hV₂U : V₂ ≤ fsuU T V := hV₂.1.1.trans hVU
  have haU : a ∈ fsuU T V := hV₂U haV₂
  have hidx : (fsuV1 T V).relIndex V₂ = 2 := by
    have := Subgroup.relIndex_mul_card (H := fsuV1 T V) (K := V₂)
    rw [inf_eq_left.mpr hV₂.2, hV1, hV₂4] at this
    omega
  have hV₂c : ∀ x ∈ V₂, x ∈ fsuV1 T V ∨ ∃ c ∈ fsuV1 T V, x = a * c := by
    intro x hx
    by_cases hx1 : x ∈ fsuV1 T V
    · exact Or.inl hx1
    right
    have hm := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨a⁻¹, V₂.inv_mem haV₂⟩)
      (b := ⟨x, hx⟩)).mpr (iff_of_false (fun hm => ha1 (by
        have := (fsuV1 T V).inv_mem (Subgroup.mem_subgroupOf.mp hm)
        rwa [inv_inv] at this)) (fun hm => hx1 (Subgroup.mem_subgroupOf.mp hm)))
    exact ⟨a⁻¹ * x, Subgroup.mem_subgroupOf.mp hm, by group⟩

  have hHV1 : ∀ h ∈ l32nH T V, ∀ c ∈ fsuV1 T V, h * c * h⁻¹ = c := by
    intro x hx c hc
    have := Subgroup.mem_centralizer_iff.mp (le_centralizer_normalizer_of_card_eq_two hV1 hc) x hx
    calc x * c * x⁻¹ = c * x * x⁻¹ := by rw [this]
      _ = c := by group

  have hU2 : IsPGroup 2 ↥(fsuU T V) :=
    (h.fsu.sylow.1).to_le (h.fsuU_le_F4 h13322 hV h1283 h1284)
  have hΦ : frattiniOf (fsuU T V) ≤ fsuV1 T V :=
    (display12_8_frattini_F4 h1222 h12213 G T L V 3 (fsuV1 T V) V₂ hs).le
  obtain ⟨hsq, hcomm⟩ := sq_mem_and_comm_mem hU2 hΦ

  have hTH : T ≤ l32nH T V := h.le_l32nH_F4 hV
  have hTV₂ : T ≤ Subgroup.normalizer (V₂ : Set G) := hV₂.1.2.2
  have hTodd : Odd ((D.img T).relIndex (D.img (l32nH T V))) := by
    have hdvd := relIndex_img_dvd D hTH (l32nH_le_normalizer_fsuU T V)
    have hsyl := (h.isSylowTwoOf_l32nH_F4 hV).2.2
    have hodd : Odd (T.relIndex (l32nH T V)) := Nat.odd_iff.mpr (by
      rcases Nat.even_or_odd (T.relIndex (l32nH T V)) with he | ho
      · exact absurd (even_iff_two_dvd.mp he) hsyl
      · exact Nat.odd_iff.mp ho)
    exact Odd.of_dvd_nat hodd hdvd

  have hZ := card_img_conj_zU_F4 h12810 h12813 hs hgP hgN (h14331 G T L V h hlt) hlt.le hV1 D

  have hVZ := lemma12_8_8_three_F4 h1222 h12213 hs
  have hpi : D.π a ≠ 0 := by
    intro h0
    have haZ := (L128A.HatU.π_eq_zero_iff D haU).mp h0
    apply ha1
    rw [← hVZ]
    exact Subgroup.mem_inf.mpr ⟨hV₂.1.1 haV₂, haZ⟩
  have hgN₂ : g ∈ Subgroup.normalizer (V₂ : Set G) :=
    Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hgP.2 V₂) ⟨2, le_rfl, hV₂.1⟩
  have hWg : CFSG.conjugate (l32nW T V V₂) g ≤ l32nH T V :=
    (conj_le_centralizer_of_le inf_le_right hV₂.2 hgN₂).trans
      (Subgroup.centralizer_le_normalizer _)
  exact ⟨V₂, g, a, D, ⟨h, hlt, hV₂, hs, hgP, hgN, haV₂, ha1, haU, hV₂c, hHV1, hU2, hV1, hsq,
    hcomm, le_inf hTH hTV₂, h.fsu.sylow.1, hTodd, hZ, hpi, conj_zU_le_F4 h12813 hs hgP hgN, hWg,
    h.fsuU_le_l32nH_F4 hV, hVU, fun x hx y hy =>
      congrArg Subtype.val (hVe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩),
    (h1284 G T L V 3 (h.hyp1281One_F4 h13322 hV) (fsuV1 T V) (l32nH T V) (h.isTSub_fsuV1_F4 hV)
      (h.isHzOne_l32nH_F4 h13322 hV h1283)).2.2.2⟩⟩

end L14332

end CFSG.Quasithin.H13
