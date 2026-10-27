module

public import CFSG.LocalAnalysis.EvenBN.Tits.Model.ParrottCert

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.Star

open Subgroup CFSG.Sporadic.Schreier.Tits CFSG.LocalAnalysis.EvenBN.Tits.Model
  Certificates.TitsAschbacherParrott

section Abstract

variable {P : Type*} [Group P]

theorem conj_eq_of_mul_eq {a y y' : P} (h : a * y = y' * a) : a * y * a⁻¹ = y' := by
  rw [h, mul_inv_cancel_right]

theorem kap_sq {x2 x4 x6 x7 x8 x10 x11 x12 : P}
    (s2 : x2 * x2 = 1) (s4 : x4 * x4 = x8) (s6 : x6 * x6 = x11) (s11 : x11 * x11 = 1)
    (s12 : x12 * x12 = 1)
    (c42 : x4 * x2 = x2 * x4 * (x7 * (x11 * x12))) (c62 : x6 * x2 = x2 * x6)
    (c64 : x6 * x4 = x4 * x6) (c74 : x7 * x4 = x4 * x7 * (x10 * (x11 * x12)))
    (c76 : x7 * x6 = x6 * x7) (c114 : x11 * x4 = x4 * x11) (c116 : x11 * x6 = x6 * x11)
    (c106 : x10 * x6 = x6 * x10) (c87 : x8 * x7 = x7 * x8 * x12) (c1110 : x11 * x10 = x10 * x11)
    (c117 : x11 * x7 = x7 * x11) (z4 : x12 * x4 = x4 * x12) (z6 : x12 * x6 = x6 * x12)
    (z10 : x12 * x10 = x10 * x12) (z11 : x12 * x11 = x11 * x12) :
    x2 * x4 * x6 * (x2 * x4 * x6) = x7 * (x8 * x10 * x11 * x12) := by
  have hc6 : x7 * (x11 * x12) * x6 = x6 * (x7 * (x11 * x12)) := by
    calc x7 * (x11 * x12) * x6 = x7 * (x11 * (x12 * x6)) := by group
      _ = x7 * (x11 * (x6 * x12)) := by rw [z6]
      _ = x7 * (x11 * x6) * x12 := by group
      _ = x7 * (x6 * x11) * x12 := by rw [c116]
      _ = (x7 * x6) * x11 * x12 := by group
      _ = (x6 * x7) * x11 * x12 := by rw [c76]
      _ = x6 * (x7 * (x11 * x12)) := by group
  have hc4 : x7 * (x11 * x12) * x4 = x4 * (x7 * x10) := by
    calc x7 * (x11 * x12) * x4 = x7 * (x11 * (x12 * x4)) := by group
      _ = x7 * (x11 * (x4 * x12)) := by rw [z4]
      _ = x7 * (x11 * x4) * x12 := by group
      _ = x7 * (x4 * x11) * x12 := by rw [c114]
      _ = (x7 * x4) * x11 * x12 := by group
      _ = x4 * x7 * (x10 * (x11 * x12)) * x11 * x12 := by rw [c74]
      _ = x4 * x7 * x10 * (x11 * (x12 * x11)) * x12 := by group
      _ = x4 * x7 * x10 * (x11 * (x11 * x12)) * x12 := by rw [z11]
      _ = x4 * x7 * x10 * (x11 * x11) * (x12 * x12) := by group
      _ = x4 * (x7 * x10) := by rw [s11, s12]; group
  have h2 : x2 * x4 * x2 = x4 * (x7 * (x11 * x12)) := by
    calc x2 * x4 * x2 = x2 * (x4 * x2) := by group
      _ = x2 * (x2 * x4 * (x7 * (x11 * x12))) := by rw [c42]
      _ = (x2 * x2) * x4 * (x7 * (x11 * x12)) := by group
      _ = x4 * (x7 * (x11 * x12)) := by rw [s2]; group
  have h6 : x2 * x6 * x2 = x6 := by
    calc x2 * x6 * x2 = x2 * (x6 * x2) := by group
      _ = x2 * (x2 * x6) := by rw [c62]
      _ = (x2 * x2) * x6 := by group
      _ = x6 := by rw [s2]; group
  have h76 : x7 * x10 * x6 = x6 * (x7 * x10) := by
    calc x7 * x10 * x6 = x7 * (x10 * x6) := by group
      _ = x7 * (x6 * x10) := by rw [c106]
      _ = (x7 * x6) * x10 := by group
      _ = (x6 * x7) * x10 := by rw [c76]
      _ = x6 * (x7 * x10) := by group
  calc x2 * x4 * x6 * (x2 * x4 * x6)
      = (x2 * x4 * x2) * (x2 * x6 * x2) * x4 * x6 := by
        calc x2 * x4 * x6 * (x2 * x4 * x6) = x2 * x4 * 1 * x6 * x2 * x4 * x6 := by group
          _ = x2 * x4 * (x2 * x2) * x6 * x2 * x4 * x6 := by rw [s2]
          _ = (x2 * x4 * x2) * (x2 * x6 * x2) * x4 * x6 := by group
    _ = x4 * (x7 * (x11 * x12)) * x6 * x4 * x6 := by rw [h2, h6]
    _ = x4 * (x7 * (x11 * x12) * x6) * x4 * x6 := by group
    _ = x4 * (x6 * (x7 * (x11 * x12))) * x4 * x6 := by rw [hc6]
    _ = x4 * x6 * (x7 * (x11 * x12) * x4) * x6 := by group
    _ = x4 * x6 * (x4 * (x7 * x10)) * x6 := by rw [hc4]
    _ = x4 * (x6 * x4) * (x7 * x10 * x6) := by group
    _ = x4 * (x4 * x6) * (x6 * (x7 * x10)) := by rw [c64, h76]
    _ = (x4 * x4) * (x6 * x6) * x7 * x10 := by group
    _ = x8 * x11 * x7 * x10 := by rw [s4, s6]
    _ = x8 * (x11 * x7) * x10 := by group
    _ = x8 * (x7 * x11) * x10 := by rw [c117]
    _ = (x8 * x7) * x11 * x10 := by group
    _ = x7 * x8 * x12 * x11 * x10 := by rw [c87]
    _ = x7 * x8 * (x12 * x11) * x10 := by group
    _ = x7 * x8 * (x11 * x12) * x10 := by rw [z11]
    _ = x7 * x8 * x11 * (x12 * x10) := by group
    _ = x7 * x8 * x11 * (x10 * x12) := by rw [z10]
    _ = x7 * x8 * (x11 * x10) * x12 := by group
    _ = x7 * x8 * (x10 * x11) * x12 := by rw [c1110]
    _ = x7 * (x8 * x10 * x11 * x12) := by group

theorem kap_conj {x2 x4 x6 x8 x9 x10 x11 x12 : P}
    (s2 : x2 * x2 = 1) (s12 : x12 * x12 = 1)
    (z2 : x12 * x2 = x2 * x12) (z4 : x12 * x4 = x4 * x12) (z6 : x12 * x6 = x6 * x12)
    (c112 : x11 * x2 = x2 * x11) (c114 : x11 * x4 = x4 * x11) (c116 : x11 * x6 = x6 * x11)
    (c102 : x10 * x2 = x2 * x10) (c104 : x10 * x4 = x4 * x10 * x12)
    (c106 : x10 * x6 = x6 * x10)
    (c92 : x9 * x2 = x2 * x9 * x11) (c94 : x9 * x4 = x4 * x9) (c96 : x9 * x6 = x6 * x9 * x12)
    (c82 : x8 * x2 = x2 * x8 * (x10 * (x11 * x12))) (c84 : x8 * x4 = x4 * x8)
    (c86 : x8 * x6 = x6 * x8) :
    x2 * x4 * x6 * x12 * (x2 * x4 * x6)⁻¹ = x12 ∧
      x2 * x4 * x6 * x11 * (x2 * x4 * x6)⁻¹ = x11 ∧
      x2 * x4 * x6 * x10 * (x2 * x4 * x6)⁻¹ = x10 * x12 ∧
      x2 * x4 * x6 * x9 * (x2 * x4 * x6)⁻¹ = x9 * x11 * x12 ∧
      x2 * x4 * x6 * x8 * (x2 * x4 * x6)⁻¹ = x8 * x10 * x11 * x12 := by
  have conj3 : ∀ y : P, x2 * x4 * x6 * y * (x2 * x4 * x6)⁻¹ =
      x2 * (x4 * (x6 * y * x6⁻¹) * x4⁻¹) * x2⁻¹ := fun y => by group
  have i2 : x2⁻¹ = x2 := inv_eq_of_mul_eq_one_right s2
  have inv2 : ∀ {y y' : P}, y * x2 = x2 * y' → x2 * y * x2⁻¹ = y' := fun {y y'} h => by
    rw [i2]
    calc x2 * y * x2 = x2 * (y * x2) := by group
      _ = x2 * (x2 * y') := by rw [h]
      _ = (x2 * x2) * y' := by group
      _ = y' := by rw [s2]; group
  have inv12 : ∀ {a y : P}, x12 * a = a * x12 → y * a = a * y * x12 → a * y * a⁻¹ = y * x12 :=
    fun {a y} hz h => conj_eq_of_mul_eq (by
      calc a * y = a * y * (x12 * x12) := by rw [s12, mul_one]
        _ = a * y * x12 * x12 := by group
        _ = y * a * x12 := by rw [← h]
        _ = y * (a * x12) := by group
        _ = y * (x12 * a) := by rw [hz]
        _ = y * x12 * a := by group)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [conj3, conj_eq_of_mul_eq z6.symm, conj_eq_of_mul_eq z4.symm, conj_eq_of_mul_eq z2.symm]
  · rw [conj3, conj_eq_of_mul_eq c116.symm, conj_eq_of_mul_eq c114.symm,
      conj_eq_of_mul_eq c112.symm]
  · rw [conj3, conj_eq_of_mul_eq c106.symm, inv12 z4 c104]
    refine conj_eq_of_mul_eq ?_
    calc x2 * (x10 * x12) = (x2 * x10) * x12 := by group
      _ = (x10 * x2) * x12 := by rw [c102]
      _ = x10 * (x2 * x12) := by group
      _ = x10 * (x12 * x2) := by rw [z2]
      _ = x10 * x12 * x2 := by group
  · rw [conj3, inv12 z6 c96]
    have h4 : x4 * (x9 * x12) * x4⁻¹ = x9 * x12 := by
      refine conj_eq_of_mul_eq ?_
      calc x4 * (x9 * x12) = (x4 * x9) * x12 := by group
        _ = (x9 * x4) * x12 := by rw [c94]
        _ = x9 * (x4 * x12) := by group
        _ = x9 * (x12 * x4) := by rw [z4]
        _ = x9 * x12 * x4 := by group
    rw [h4]
    refine inv2 ?_
    calc x9 * x12 * x2 = x9 * (x12 * x2) := by group
      _ = x9 * (x2 * x12) := by rw [z2]
      _ = (x9 * x2) * x12 := by group
      _ = x2 * x9 * x11 * x12 := by rw [c92]
      _ = x2 * (x9 * x11 * x12) := by group
  · rw [conj3, conj_eq_of_mul_eq c86.symm, conj_eq_of_mul_eq c84.symm]
    refine inv2 ?_
    rw [c82]
    group

end Abstract

section Model


@[expose] noncomputable def kapG : Equiv.Perm (Fin 1755) := parrottV 2 * parrottV 4 * parrottV 6

theorem pv_rel {i j : ℕ} {l : List ℕ} (h : (i, j, l) ∈ parrottComm) :
    parrottV i * parrottV j = parrottV j * parrottV i * (l.map parrottV).prod :=
  parrottV_comm h

theorem kapG_mul_self :
    kapG * kapG = parrottV 7 * (parrottV 8 * parrottV 10 * parrottV 11 * parrottV 12) := by
  obtain ⟨-, s4, -, s6, s⟩ := parrott_squares
  have c42 := pv_rel (i := 4) (j := 2) (l := [7, 11, 12]) (by decide)
  have c74 := pv_rel (i := 7) (j := 4) (l := [10, 11, 12]) (by decide)
  have c87 := pv_rel (i := 8) (j := 7) (l := [12]) (by decide)
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at c42 c74 c87
  have z : ∀ j, 1 ≤ j → j ≤ 12 → parrottV 12 * parrottV j = parrottV j * parrottV 12 :=
    fun j h1 h2 => parrottV_twelve_comm h1 h2
  exact kap_sq (s 2 (by norm_num) (by norm_num) (by decide)) s4 s6
    (s 11 (by norm_num) (by norm_num) (by decide)) (s 12 (by norm_num) (by norm_num) (by decide))
    c42 (parrottV_commute (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)
      (by decide))
    (parrottV_commute (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)
      (by decide)) c74
    (parrottV_commute (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)
      (by decide))
    (parrottV_commute (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)
      (by decide))
    (parrottV_commute (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)
      (by decide))
    (parrottV_commute (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)
      (by decide)) c87
    (parrottV_commute (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)
      (by decide))
    (parrottV_commute (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)
      (by decide))
    (z 4 (by norm_num) (by norm_num)) (z 6 (by norm_num) (by norm_num))
    (z 10 (by norm_num) (by norm_num)) (z 11 (by norm_num) (by norm_num))

theorem kapG_conj :
    kapG * parrottV 12 * kapG⁻¹ = parrottV 12 ∧ kapG * parrottV 11 * kapG⁻¹ = parrottV 11 ∧
      kapG * parrottV 10 * kapG⁻¹ = parrottV 10 * parrottV 12 ∧
      kapG * parrottV 9 * kapG⁻¹ = parrottV 9 * parrottV 11 * parrottV 12 ∧
      kapG * parrottV 8 * kapG⁻¹ = parrottV 8 * parrottV 10 * parrottV 11 * parrottV 12 := by
  obtain ⟨-, -, -, -, s⟩ := parrott_squares
  have c104 := pv_rel (i := 10) (j := 4) (l := [12]) (by decide)
  have c92 := pv_rel (i := 9) (j := 2) (l := [11]) (by decide)
  have c96 := pv_rel (i := 9) (j := 6) (l := [12]) (by decide)
  have c82 := pv_rel (i := 8) (j := 2) (l := [10, 11, 12]) (by decide)
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one] at c104 c92 c96 c82
  have z : ∀ j, 1 ≤ j → j ≤ 12 → parrottV 12 * parrottV j = parrottV j * parrottV 12 :=
    fun j h1 h2 => parrottV_twelve_comm h1 h2
  exact kap_conj (s 2 (by norm_num) (by norm_num) (by decide))
    (s 12 (by norm_num) (by norm_num) (by decide))
    (z 2 (by norm_num) (by norm_num)) (z 4 (by norm_num) (by norm_num))
    (z 6 (by norm_num) (by norm_num))
    (parrottV_commute (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)
      (by decide))
    (parrottV_commute (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)
      (by decide))
    (parrottV_commute (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)
      (by decide))
    (parrottV_commute (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)
      (by decide)) c104
    (parrottV_commute (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)
      (by decide)) c92
    (parrottV_commute (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)
      (by decide)) c96 c82
    (parrottV_commute (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)
      (by decide))
    (parrottV_commute (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)
      (by decide))

theorem kapG_mem_parrottU : kapG ∈ parrottU 1 :=
  mul_mem (mul_mem (subset_closure ⟨2, ⟨by norm_num, by norm_num⟩, rfl⟩)
    (subset_closure ⟨4, ⟨by norm_num, by norm_num⟩, rfl⟩))
    (subset_closure ⟨6, ⟨by norm_num, by norm_num⟩, rfl⟩)

end Model

theorem kapG_mem_titsD :
    kapG ∈ titsD := by
  have h2 : parrottV 2 ∈ titsD := (parrottV_mem_titsD_iff (by norm_num)).2 (by decide)
  have h46 : parrottV 4 * parrottV 6 ∈ titsD :=
    titsS_le_titsD (parrottBlocks_subset (Or.inr ⟨4, by decide, 6, by decide, rfl⟩))
  rw [kapG, mul_assoc]
  exact mul_mem h2 h46

end CFSG.LocalAnalysis.EvenBN.Tits.N.Star
