module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NItems14331
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14331e
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NThm144Big
public import CFSG.Quasithin.H13.L32NKGConj

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

theorem lemma14331One_of_inputs_F4 (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (h12810 : Lemma12_8_10_F4) (h12813 : Lemma12_8_13_F4)
    (h14324 : Lemma14324One_F4) (h14325 : Lemma14325One_F4) (hKG : KGCert.KGG22Closure)
    (hI : Lemma14331CaseI_F4) : Lemma14331One_F4 := by
  intro G _ _ T L V h hlt
  obtain ⟨hc, V₂, g, z, b, l, C⟩ := L14328.exists_ctx_F4 h1332 h1334 h1222 h12213 h12810 h hlt
  by_contra hne
  obtain ⟨e, he, he1, he2⟩ := C.exists_e_F4 h14325 h1222 h12213 h12810 h12813 hne
  obtain ⟨D⟩ := C.setting.exists_hatModelU_F4 h1222 h12213
  have h13322 := stmt13_3_2_two_of_stmt13_3_2_F4 h1332
  have hV := stmtL32NModule_of_inputs_F4 h1332 h1334
  have h1283 := lemma12_8_3_F4 h12213
  have h1284 := lemma12_8_4_F4 h1222 h37 h38 h39
  have hQ : centralizerMod (fsuV1 T V) (l32nH T V) (fsuU T V) = pCoreOf 2 (l32nH T V) :=
    (h1284 G T L V 3 (h.hyp1281One_F4 h13322 hV) (fsuV1 T V) (l32nH T V) (h.isTSub_fsuV1_F4 hV)
      (h.isHzOne_l32nH_F4 h13322 hV h1283)).2.2.2
  have hO2 : pCoreOf 2 (l32nH T V) ≠ ⊥ := by
    intro hb
    have hle := h.fsuV1_le_pCoreOf
    rw [hb, le_bot_iff] at hle
    have := C.S.card_V1_F4
    rw [hle, Subgroup.card_bot] at this
    omega
  have hm3 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥(l32nH T V)) ≤ 2 := by
    have := h.fsu.simple
    have hsq := (QuasithinUnique.qtkeCore_of_cat h.fsu.nonabelian h.fsu.qtke).1 _ hO2
    exact CFSG.SectionRank.isStronglyQuasithin_iff.mp hsq.1 3 Nat.prime_three (by norm_num)
  rcases h14324 G T L V h hlt V₂ g C.plane C.gP C.gN D with h6 | ⟨hd, hi | hii | hiii⟩
  ·
    have := L14332.finite_linearEquiv D
    refine C.false_of_closure_F4 D h14325 h1222 h12813 hQ hm3 he he1 fun hN => ?_
    obtain ⟨hmem, hρ1⟩ := C.rho_a_mem_F4 D h14325 h1222 h12213 h12810 h12813 he he1 hN
    have hρ2 : D.ρ ⟨l⁻¹ * e * l, hN⟩ * D.ρ ⟨l⁻¹ * e * l, hN⟩ = 1 := by
      rw [← map_mul]
      have : (⟨l⁻¹ * e * l, hN⟩ : ↥(Subgroup.normalizer (fsuU T V : Set G))) *
          ⟨l⁻¹ * e * l, hN⟩ = 1 := Subtype.ext (by
        show l⁻¹ * e * l * (l⁻¹ * e * l) = 1
        rw [show l⁻¹ * e * l * (l⁻¹ * e * l) = l⁻¹ * (e * e) * l by group, he2]
        group)
      rw [this, map_one]
    have hB : ∀ γ ∈ D.img (l32nH T V), ∀ v w, D.B (γ v) (γ w) = D.B v w := by
      intro γ hγ v w
      obtain ⟨x, -, hxN, rfl⟩ := (L128A.HatU.mem_img D).mp hγ
      exact L128A.HatU.B_rho D ⟨x, hxN⟩ v w
    exact fun N hNΓ hΓN htN => hKG D.V D.B (L128A.HatU.B_isAlt D)
      (L128A.HatU.B_nondegenerate D) h6.1 (D.img (l32nH T V)) hB h6.2 _ hmem hρ2 hρ1 N hNΓ hΓN
      htN
  ·
    exact hne (hI G T L V h hlt V₂ g C.plane C.gP C.gN D hd hi)
  · exact C.false_of_case_ii_F4 D h14325 h1222 h12213 h12810 h12813 he he1 hii
  · exact C.false_of_case_iii_F4 D h14325 h1222 h12213 h12810 h12813 hQ hm3 he he1 hiii

end CFSG.Quasithin.H13
