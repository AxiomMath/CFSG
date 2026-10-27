module

public import CFSG.Quasithin.H13.L32NLem14325b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14332a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14332h
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem1434
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NThm14326
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NThm144Big
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneModel

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

namespace L14325

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem exists_ctx14325_F4 (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) (h1222 : Stmt12_2_2_F4)
    (h12213 : Stmt12_2_13_F4) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h12813 : Lemma12_8_13_F4) {T L V : Subgroup G} (h : Hyp14310One G T L V)
    (hne : centerOf (L ⊔ T) ⊓ fsuU T V ≠ ⊥) :
    ∃ (V₂ : Subgroup G) (g : G) (D : HatModelU (fsuU T V)), Ctx14325 G T L V V₂ g D := by
  have h13322 := stmt13_3_2_two_of_stmt13_3_2_F4 h1332
  have hV := stmtL32NModule_of_inputs_F4 h1332 h1334
  have h1283 := lemma12_8_3_F4 h12213
  have h1284 := lemma12_8_4_F4 h1222 h37 h38 h39
  obtain ⟨V₂, g, hV₂, hgP, hgN⟩ := h.exists_plane_and_g_F4 h13322 hV (exist1282g_F4 h1222)
  have hs := h.setting1282One_F4 h13322 hV hV₂
  obtain ⟨D⟩ := hs.exists_hatModelU_F4 h1222 h12213
  obtain ⟨-, hV8, -, hV1, -⟩ := hV G T L V h.hyp h.fsu
  have hUT := h.fsuU_le_F4 h13322 hV h1283 h1284
  have hT2 : IsPGroup 2 ↥T := h.fsu.sylow.1
  have hU2 : IsPGroup 2 ↥(fsuU T V) := hT2.to_le hUT
  have hZne := zL_ne_bot hUT hT2 hne
  have hZzU := zL_le_zU (L := L) hUT
  have hVU : V ≤ fsuU T V := le_conjClosure V _
  have hVZ := lemma12_8_8_three_F4 h1222 h12213 hs
  have hV1Z : fsuV1 T V ≤ centerOf (fsuU T V) := hVZ ▸ inf_le_right

  have hlt : fsuV1 T V < centerOf (fsuU T V) := by
    refine lt_of_le_of_ne hV1Z fun heq => hZne ?_
    obtain ⟨_, S⟩ := L14332.exists_setting_F4 h1332 h1334 h1222 h hV₂
    rw [eq_bot_iff, ← S.hZV]
    intro z hz
    have hzV1 : z ∈ fsuV1 T V := by rw [heq]; exact hZzU hz
    refine ⟨(inf_le_left : fsuV1 T V ≤ V) hzV1, ?_⟩
    exact Subgroup.centralizer_le (le_sup_left : L ≤ L ⊔ T) hz.1.1.2

  obtain ⟨S, hS⟩ := exists_sylow_of_quasithinIsSylowTwo h.fsu.sylow
  have hTH : T ≤ l32nH T V := h.le_l32nH_F4 hV
  have hred : IsTwoReducedIn (l32nH T V) (vH T L V) :=
    isTwoReducedIn_conjClosure (l32nH T V) S (hS ▸ hTH) (h.charTwo_l32nH_F4 hV)
      (hS ▸ inf_le_right)
  have hvH : vH T L V ≤ centerOf (fsuU T V) :=
    conjClosure_le fun x hx z hz =>
      (Subgroup.mem_normalizer_iff.mp (L14332.l32nH_le_normalizer_zU hx) z).mp (hZzU hz)

  have hcent : Subgroup.centralizer (vH T L V : Set G) ≤ Subgroup.normalizer (L : Set G) := by
    have hZ2 : IsPGroup 2 ↥(zL T L V) := hU2.to_le (inf_le_left.trans inf_le_right)
    obtain ⟨M', hM', hNM'⟩ := exists_maxTwoLocal_ge
      (L := Subgroup.normalizer (zL T L V : Set G)) ⟨zL T L V, hZne, hZ2, rfl⟩
    have hLTN : L ⊔ T ≤ Subgroup.normalizer (zL T L V : Set G) := by
      intro x hx
      refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
      intro z hz
      exact (Subgroup.mem_centralizer_iff.mp hz.1.1.2 x hx).symm
    have hM'eq := (h13322 G T L h.hyp.h13 L h.hyp.h13.faithful).2.2.2 M' hM' (hLTN.trans hNM')
    refine le_trans ?_ (hM'eq ▸ hNM')
    exact (Subgroup.centralizer_le (le_conjClosure _ _)).trans
      (Subgroup.centralizer_le_normalizer _)

  have hV1ne : fsuV1 T V ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hV1
    omega
  have hHM := lemma1433Six_of_inputs_F4 h1332 h1334 h1222 G T L V h.hyp h.fsu (fsuV1 T V)
    (l32nH T V) inf_le_left hV1ne le_rfl

  have hzUg : D.img (CFSG.conjugate (centerOf (fsuU T V)) g) ≠ ⊥ := by
    intro hb
    apply (h12813 G T L V 3 (fsuV1 T V) V₂ hs g hgP hgN).2.2.1 hlt
    intro x hx
    have hxH := L14332.conj_zU_le_F4 h12813 hs hgP hgN hx
    have hρ : D.ρ ⟨x, L14332.l32nH_le_normalizer_fsuU T V hxH⟩ = 1 := by
      have := L128A.HatU.rho_mem_img D hx (L14332.l32nH_le_normalizer_fsuU T V hxH)
      rw [hb, Subgroup.mem_bot] at this
      exact this
    exact (L14332.rho_eq_one_iff_mem hxH _).mp hρ

  have hhatV : Nat.card ↥(D.hat V) = 4 := by
    rw [L128A.HatU.card_hat D hVU]
    change (V ⊓ zU128 V (fsuV1 T V)).relIndex V = 4
    rw [hVZ]
    have := Subgroup.relIndex_mul_card (H := fsuV1 T V) (K := V)
    rw [inf_eq_left.mpr inf_le_left, hV1, hV8] at this
    omega
  exact ⟨V₂, g, D, ⟨h, hlt, hV₂, hs, hgP, hgN, hU2, hV1, hTH, h.fsuU_le_l32nH_F4 hV, hVU,
    L14332.conj_zU_le_F4 h12813 hs hgP hgN, hzUg,
    (h1284 G T L V 3 (h.hyp1281One_F4 h13322 hV) (fsuV1 T V) (l32nH T V) (h.isTSub_fsuV1_F4 hV)
      (h.isHzOne_l32nH_F4 h13322 hV h1283)).2.2.2, hhatV, hZne, hred, hvH, hcent, hHM⟩⟩

end L14325

end CFSG.Quasithin.H13
