module

public import CFSG.Quasithin.H13.L32NLem1444a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NItems143b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NThm144Big
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneModel

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped commutatorElement

namespace L1444

variable {G : Type} [Group G]

variable [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}

theorem zU_eq_F4 (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) (h1222 : Stmt12_2_2_F4)
    (h12213 : Stmt12_2_13_F4) (h : Hyp14310One G T L V)
    (hext : CFSG.IsExtraspecialPGroup 2 ↥(fsuU T V)) : centerOf (fsuU T V) = fsuV1 T V := by
  have h13322 := stmt13_3_2_two_of_stmt13_3_2_F4 h1332
  have hV := stmtL32NModule_of_inputs_F4 h1332 h1334
  obtain ⟨-, -, -, hV1, -⟩ := hV G T L V h.hyp h.fsu
  obtain ⟨V₂, hV₂⟩ := h.exists_plane_F4 hV
  obtain ⟨⟨U₀, -, hU₀ext, hΦ, hU₀Z⟩, -⟩ :=
    lemma12_8_8_n3_F4 h1222 h12213 (h.setting1282One_F4 h13322 hV hV₂)
  have hV1Z := fsuV1_le_centerOf_of_decomp hU₀Z hU₀ext hΦ
  have hZ2 : Nat.card ↥(centerOf (fsuU T V)) = 2 := by
    rw [l32n_card_centerOf]
    exact hext.2.2.2
  exact (Subgroup.eq_of_le_of_card_ge hV1Z (by rw [hZ2, hV1])).symm

theorem cHat_eq_F4 (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) (h1222 : Stmt12_2_2_F4)
    (h12213 : Stmt12_2_13_F4) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h : Hyp14310One G T L V) (hext : CFSG.IsExtraspecialPGroup 2 ↥(fsuU T V)) :
    l32nCHat T V = pCoreOf 2 (l32nH T V) := by
  have h13322 := stmt13_3_2_two_of_stmt13_3_2_F4 h1332
  have hV := stmtL32NModule_of_inputs_F4 h1332 h1334
  have h1281 := h.hyp1281One_F4 h13322 hV
  have hZ := zU_eq_F4 h1332 h1334 h1222 h12213 h hext
  show centralizerMod (centerOf (fsuU T V)) (l32nH T V) (fsuU T V) = _
  rw [hZ]
  exact (lemma12_8_4_F4 h1222 h37 h38 h39 G T L V 3 h1281 (fsuV1 T V) (l32nH T V)
    (h.isTSub_fsuV1_F4 hV) (h.isHzOne_l32nH_F4 h13322 hV (lemma12_8_3_F4 h12213))).2.2.2

end L1444

open L1444 in

theorem lemma1444One_of_inputs_F4 (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (hRest : Lemma14323Rest_F4) : Lemma1444One_F4 := by
  intro G _ _ T L V h hext h32 _
  classical
  have h13322 := stmt13_3_2_two_of_stmt13_3_2_F4 h1332
  have hV := stmtL32NModule_of_inputs_F4 h1332 h1334
  obtain ⟨-, -, -, hV1, -⟩ := hV G T L V h.hyp h.fsu
  obtain ⟨V₂, g, hV₂, hgP, hgH⟩ := h.exists_plane_and_g_F4 h13322 hV (exist1282g_F4 h1222)
  have hs := h.setting1282One_F4 h13322 hV hV₂
  obtain ⟨D⟩ := hs.exists_hatModelU_F4 h1222 h12213
  have hZ := zU_eq_F4 h1332 h1334 h1222 h12213 h hext
  have hC := cHat_eq_F4 h1332 h1334 h1222 h12213 h37 h38 h39 h hext

  have hd : Module.finrank (ZMod 2) D.V = 4 := by
    have hcard := D.card_U
    rw [hZ, hV1, h32] at hcard
    have h16 : Nat.card D.V = 2 ^ 4 := by omega
    have hpow := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := D.V)
    rw [h16, Nat.card_zmod] at hpow
    exact (Nat.pow_right_injective (le_refl 2) hpow).symm
  obtain ⟨-, hcases, -, -⟩ := hRest G T L V h V₂ g hV₂ hgP hgH D hd

  have hgN : g ∈ Subgroup.normalizer (V₂ : Set G) :=
    Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hgP.2 V₂) ⟨2, le_rfl, hV₂.1⟩
  have hZgU : CFSG.conjugate (centerOf (fsuU T V)) g ≤ fsuU T V := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hZ] at hx
    have hxV₂ : x ∈ V₂ := hV₂.2 hx
    have h1 := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hgN) x).mp hxV₂
    have hV₂V : V₂ ≤ V := hV₂.1.1
    exact le_conjClosure V _ (hV₂V (by simpa using h1))
  have hZg : D.img (CFSG.conjugate (centerOf (fsuU T V)) g) = ⊥ :=
    img_eq_bot_of_le D (comm_mem_centerOf hext) hZgU

  set e := mulEquivKStar D hC
  rcases hcases with hi | hii | hiii | hiv
  · obtain ⟨e₁⟩ := hi.iso
    have e₂ : ↥(oTwoUpper (⊤ : Subgroup ↥(D.img (l32nH T V)))) ≃* ↥s33Three :=
      (Subgroup.equivMapOfInjective _ e₁.toMonoidHom e₁.injective).trans
        (MulEquiv.subgroupCongr (by
          rw [← oTwoUpper_top_s33]
          exact oTwoUpper_top_map _ e₁.surjective))
    exact ⟨isElemAbelian_of_mulEquiv (e.trans e₂) isElemAbelian_s33Three,
      by rw [Nat.card_congr (e.trans e₂).toEquiv, card_s33Three]⟩
  · exfalso
    have h2 := hii.card_zU
    rw [hZg, Subgroup.card_bot] at h2
    exact absurd h2 (by norm_num)
  · exfalso
    have h2 := hiii.card_zU
    rw [hZg, Subgroup.card_bot] at h2
    omega
  · obtain ⟨N, -, hNe, hN9, hN2⟩ := hiv.e9
    have hNeq : oTwoUpper (⊤ : Subgroup ↥(D.img (l32nH T V))) = N :=
      oTwoUpper_top_eq_of_index_two hN2 hNe.2
    have e₂ : ↥(oTwoUpper (⊤ : Subgroup ↥(D.img (l32nH T V)))) ≃* ↥N :=
      MulEquiv.subgroupCongr hNeq
    exact ⟨isElemAbelian_of_mulEquiv (e.trans e₂) hNe,
      by rw [Nat.card_congr (e.trans e₂).toEquiv, hN9]⟩

end CFSG.Quasithin.H13
