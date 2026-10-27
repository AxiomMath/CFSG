module

public import CFSG.Quasithin.H13.L32NLem14323
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NInputs
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NModule
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneFlag
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneModel

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem lemma14323Ge_of_inputs_F4 (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4) (h12811 : Lemma12_8_11_F4)
    (h12813 : Lemma12_8_13_F4) : Lemma14323Ge_F4 := by
  intro G _ _ T L V h
  have h13322 := stmt13_3_2_two_of_stmt13_3_2_F4 h1332
  have hV := stmtL32NModule_of_inputs_F4 h1332 h1334
  obtain ⟨V₂, g, hV₂, hgP, hgN⟩ := h.exists_plane_and_g_F4 h13322 hV (exist1282g_F4 h1222)
  have hs := h.setting1282One_F4 h13322 hV hV₂
  obtain ⟨D⟩ := hs.exists_hatModelU_F4 h1222 h12213
  obtain ⟨-, hE, -⟩ := h12811 G T L V 3 (fsuV1 T V) V₂ hs g hgP hgN
  obtain ⟨hVE, -⟩ := h12813 G T L V 3 (fsuV1 T V) V₂ hs g hgP hgN
  have hVZ := lemma12_8_8_three_F4 h1222 h12213 hs
  set E := w128 V (fsuV1 T V) V₂ ⊓ CFSG.conjugate (w128 V (fsuV1 T V) V₂) g with hEdef
  have hEU : E ≤ u128 V (fsuV1 T V) := inf_le_left.trans inf_le_left
  have hVU : V ≤ u128 V (fsuV1 T V) := hVE.trans hEU
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

  obtain ⟨-, hV8, -, hV1, -⟩ := hV G T L V h.hyp h.fsu
  have hVhat : Nat.card (D.homOn hVU).range = 4 := by
    have h1 := D.card_eq_mul_range hVU
    rw [hVZ, hV8, hV1] at h1
    omega

  have hiso := card_sq_le_of_isotropic D.nondegenerate (D.isotropic_hat hEU hEc)
  have h4 : 4 ≤ Nat.card (D.hat E) := hVhat ▸ D.card_range_le_hat hVU hVE
  have h16 : 16 ≤ Nat.card D.V := by nlinarith
  have hcard := D.card_U
  show 2 ^ 4 * Nat.card ↥(centerOf (u128 V (fsuV1 T V))) ≤ Nat.card ↥(u128 V (fsuV1 T V))
  rw [hcard]
  nlinarith

end CFSG.Quasithin.H13
