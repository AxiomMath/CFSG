module

public import CFSG.Quasithin.H13.L32NLem14323c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14323b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem1442

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin

namespace L14323

variable {G : Type} [Group G]

namespace Ctx

variable [CFSG.GH74.QTGen4.Finite4 G] {T L V V₂ : Subgroup G} {g a c : G} {D : HatModelU (fsuU T V)}
variable (C : Ctx G T L V V₂ g a c D)
include C

theorem case_iv_F4 (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) (h14312 : Lemma14312One_F4)
    (h18 : Nat.card ↥(D.img (l32nH T V)) = 18) (hE : Sp4Cert.HasE9 (D.img (l32nH T V))) :
    Case14323iv T L V D := by
  have := L14332.finite_linearEquiv D
  obtain ⟨P, hPΓ, hP9, hnorm, hPc, hP3, hP⟩ := hE
  have hT2 : Nat.card ↥(D.img T) = 2 := by
    have := C.card_T_of (e := 1) h18 (by norm_num) (by norm_num)
    simpa using this
  refine ⟨⟨P.subgroupOf (D.img (l32nH T V)), ?_, ⟨?_, ?_⟩, ?_, ?_⟩,
    C.l1_normal_of hPΓ hP9 hPc hP (by rw [h18]; norm_num) (by rw [h18, hT2]), ?_⟩
  · exact ⟨fun n hn k => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact (Subgroup.mem_normalizer_iff.mp (hnorm k.2) n).mp hn⟩
  · exact ⟨⟨fun x y => Subtype.ext (Subtype.ext (hPc _ x.2 _ y.2))⟩⟩
  · intro x hx
    exact Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hP3 _ (Subgroup.mem_subgroupOf.mp hx))
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPΓ).toEquiv, hP9]
  · have h1 := (P.subgroupOf (D.img (l32nH T V))).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPΓ).toEquiv, hP9, h18] at h1
    omega
  ·
    have hle : Nat.card ↥(D.img (CFSG.conjugate (l32nW T V V₂) g)) ≤
        2 ^ (Module.finrank (ZMod 2) D.V / 2 - 1) := by
      rw [C.d4]
      exact (C.card_X_le_two h18).trans (by norm_num)
    obtain ⟨-, -, ⟨hZ, hext, -⟩, -⟩ := h14312 G T L V C.hyp V₂ g C.plane C.gP C.gN D hle
    have h32 : Nat.card ↥(fsuU T V) = 2 ^ 5 := by
      rw [D.card_U, hZ, C.card_V1, C.card_V]
      norm_num
    exact isQ8Sq_of_isQ8CentralPow_two
      (lemma1442Q8Four_of_inputs_F4 (stmtL32NModule_of_inputs_F4 h1332 h1334) C.hyp hext h32)

end Ctx

end L14323

theorem lemma14323Two_of_inputs_F4 (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4)
    (h1288 : Lemma12_8_8_two_F4) (h12811 : Lemma12_8_11_F4) (h12811h : Lemma12_8_11_hat_F4)
    (h12813 : Lemma12_8_13_F4) (h14312 : Lemma14312One_F4) (hG112 : G11.TheoremG112Fix) :
    Lemma14323Two_F4 := by
  intro G _ _ T L V h V₂ g hV₂ hgP hgN D hd
  obtain ⟨a, c, C⟩ := L14323.exists_ctx_F4 h1332 h1334 h1222 h12213 h1288 h12811 h12811h h12813
    hG112 h hV₂ hgP hgN D hd
  rcases Sp4Cert.sp4_classify (L128A.HatU.B_isAlt D) D.nondegenerate C.d4
      (L14323.img_le_sp D _) C.dvd_card C.hatV_eq C.pi_a_mem C.pi_c_mem C.pi_a_ne C.pi_c_ne
      C.pi_a_ne_c C.B_ac C.hT C.h3 C.hne C.h2 with
    ⟨h18, hE⟩ | ⟨hiso, hE, hF2, X, hXΓ, hX6, hXnc, hXn, hFX, hXy⟩ |
      ⟨hiso, hnat, hlay, hcen, hq⟩ | ⟨hiii, hq⟩
  · exact Or.inr (Or.inr (Or.inr (C.case_iv_F4 h1332 h1334 h14312 h18 hE)))
  · exact Or.inl (C.case_i hiso hE hF2 hXΓ hX6 hXnc hXn hFX hXy)
  · exact Or.inr (Or.inl (C.case_ii hiso hnat hlay hcen hq))
  · exact Or.inr (Or.inr (Or.inl (C.case_iii hiii hq)))

theorem lemma14323Rest_of_inputs_F4 (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4)
    (h1288 : Lemma12_8_8_two_F4) (h12811 : Lemma12_8_11_F4) (h12811h : Lemma12_8_11_hat_F4)
    (h12813 : Lemma12_8_13_F4) (h14312 : Lemma14312One_F4) (hG112 : G11.TheoremG112Fix) :
    Lemma14323Rest_F4 :=
  lemma14323Rest_of_two_F4 h1332 h1334 h1222 h12213 h12811 h12811h h12813
    (lemma14323Two_of_inputs_F4 h1332 h1334 h1222 h12213 h1288 h12811 h12811h h12813 h14312 hG112)

theorem lemma14324One_of_inputs_F4 (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4)
    (h1288 : Lemma12_8_8_two_F4) (h12811 : Lemma12_8_11_F4) (h12811h : Lemma12_8_11_hat_F4)
    (h12813 : Lemma12_8_13_F4) (h14312 : Lemma14312One_F4) (hG112 : G11.TheoremG112Fix)
    (hBig : Lemma14324Big_F4) : Lemma14324One_F4 :=
  lemma14324One_of_big_F4 h1332 h1334 h1222 h12213 h12811 h12813
    (lemma14323Two_of_inputs_F4 h1332 h1334 h1222 h12213 h1288 h12811 h12811h h12813 h14312 hG112)
    hBig

end CFSG.Quasithin.H13
