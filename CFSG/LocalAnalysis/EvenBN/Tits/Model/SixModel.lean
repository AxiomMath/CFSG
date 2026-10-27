module

public import CFSG.LocalAnalysis.EvenBN.Tits.Model.NLocal

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.Model

open Subgroup CFSG.Sporadic.Schreier.Tits Certificates.TitsAschbacherParrott
  Certificates.TitsAschbacherE32
open CFSG.Quasithin (twoF4P)

theorem parrottV_seven_sq : parrottV 7 * parrottV 7 = 1 :=
  parrott_squares.2.2.2.2 7 (by norm_num) (by norm_num) (by decide)

theorem parrottV_eight_mem_hatE : parrottV 8 ∈ hatE := by
  apply parrottU_eight_le_hatE
  exact subset_closure ⟨8, ⟨le_rfl, by norm_num⟩, rfl⟩

theorem parrottV_eleven_mem_hatE : parrottV 11 ∈ hatE := by
  apply parrottU_eight_le_hatE
  exact subset_closure ⟨11, ⟨by norm_num, by norm_num⟩, rfl⟩

theorem titsZ_sq : titsZ * titsZ = 1 := by
  rw [← parrottV_twelve]
  exact parrott_squares.2.2.2.2 12 (by norm_num) (by norm_num) (by decide)

theorem parrottV_seven_comm_z : parrottV 7 * titsZ = titsZ * parrottV 7 := by
  rw [← parrottV_twelve]
  exact (parrottV_twelve_comm (by norm_num) (by norm_num)).symm

theorem parrottV_seven_conj_eight :
    parrottV 7 * parrottV 8 * (parrottV 7)⁻¹ = parrottV 8 * titsZ := by
  have hc := parrottV_comm (r := (8, 7, [12])) (by decide)
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hc
  rw [parrottV_twelve] at hc
  have hzi : titsZ⁻¹ = titsZ := inv_eq_of_mul_eq_one_right titsZ_sq
  have h1 : parrottV 7 * parrottV 8 = parrottV 8 * parrottV 7 * titsZ⁻¹ := by
    rw [hc, mul_assoc, mul_assoc, mul_inv_cancel, mul_one]
  have h2 : parrottV 7 * titsZ⁻¹ = titsZ⁻¹ * parrottV 7 := by
    rw [hzi]
    exact parrottV_seven_comm_z
  calc parrottV 7 * parrottV 8 * (parrottV 7)⁻¹
      = parrottV 8 * (parrottV 7 * titsZ⁻¹) * (parrottV 7)⁻¹ := by rw [h1]; group
    _ = parrottV 8 * titsZ := by rw [h2, hzi]; group

theorem parrottV_seven_noncomm_eight : parrottV 7 * parrottV 8 ≠ parrottV 8 * parrottV 7 := by
  intro h
  have h1 := parrottV_seven_conj_eight
  rw [h, mul_assoc, mul_inv_cancel, mul_one] at h1
  have : titsZ = 1 := by
    have := mul_left_cancel (a := parrottV 8) (b := titsZ) (c := 1) (by rw [mul_one]; exact h1.symm)
    exact this
  exact titsZ_ne_one this

theorem parrottV_seven_comm_iff {e : Equiv.Perm (Fin 1755)} (he : e ∈ hatE) :
    parrottV 7 * e = e * parrottV 7 ↔ e ∈ parrottF := by
  have hv7F : parrottV 7 ∈ parrottF := parrottV_mem_parrottF (by simp)
  constructor
  · intro hc
    classical
    set Cn : Subgroup (Equiv.Perm (Fin 1755)) := hatE ⊓ centralizer ({parrottV 7} : Set _)
      with hCn
    set F0 : Subgroup (Equiv.Perm (Fin 1755)) := hatE ⊓ parrottF with hF0
    have hF0C : F0 ≤ Cn := by
      intro a ha
      refine mem_inf.2 ⟨(mem_inf.1 ha).1, mem_centralizer_singleton_iff.2 ?_⟩
      exact (parrottF_elemAbelian.1 a (mem_inf.1 ha).2 _ hv7F)
    have hF0card : 16 ≤ Nat.card F0 := by
      have hbits : ∀ k < 16, ∀ i ∈ u8Bits (2 * k), 9 ≤ i ∧ i ≤ 12 := by decide
      let f : Fin 16 → F0 := fun k => ⟨eElt (2 * k), mem_inf.2 ⟨eElt_mem (by omega), by
        refine list_prod_map_mem fun i hi => subset_closure ⟨i, ?_, rfl⟩
        have := hbits k k.2 i hi
        have h' : i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 := by omega
        rcases h' with rfl | rfl | rfl | rfl <;> simp⟩⟩
      have hf : Function.Injective f := fun a b hab => by
        have := eElt_injOn (a := 2 * a) (b := 2 * b) (by omega) (by omega)
          (congrArg Subtype.val hab)
        exact Fin.ext (by omega)
      simpa using Nat.card_le_card_of_injective f hf
    have hCle : Nat.card Cn ≤ 16 := by
      have hdvd : Nat.card Cn ∣ Nat.card hatE := Subgroup.card_dvd_of_le (inf_le_left : Cn ≤ hatE)
      rw [card_hatE.2.2.2] at hdvd
      have hne : Nat.card Cn ≠ 32 := by
        intro h32
        have heq := Subgroup.eq_of_le_of_card_ge (inf_le_left : Cn ≤ hatE)
          (by rw [h32, card_hatE.2.2.2])
        have h8 : parrottV 8 ∈ hatE ⊓ centralizer ({parrottV 7} : Set (Equiv.Perm (Fin 1755))) := by
          rw [heq]
          exact parrottV_eight_mem_hatE
        exact parrottV_seven_noncomm_eight (mem_centralizer_singleton_iff.1 (mem_inf.1 h8).2).symm
      have hpos : 0 < Nat.card Cn := Nat.card_pos
      have hle32 : Nat.card Cn ≤ 32 := Nat.le_of_dvd (by norm_num) hdvd
      generalize Nat.card Cn = n at hdvd hne hpos hle32 ⊢
      interval_cases n <;> first | omega | (exfalso; revert hdvd; decide)
    have hEq : F0 = Cn := Subgroup.eq_of_le_of_card_ge hF0C (by omega)
    have heC : e ∈ Cn := mem_inf.2 ⟨he, mem_centralizer_singleton_iff.2 hc.symm⟩
    rw [← hEq] at heC
    exact (mem_inf.1 heC).2
  · intro hF
    exact (parrottF_elemAbelian.1 _ hv7F _ hF)

theorem parrottV_eleven_mem_parrottF : parrottV 11 ∈ parrottF :=
  parrottV_mem_parrottF (by simp)

theorem parrottV_eleven_not_mem_zpowers : parrottV 11 ∉ zpowers titsZ := by
  intro h
  obtain ⟨h1, -, h3, -⟩ := parrottV_ne
  rw [mem_zpowers_of_orderOf_two orderOf_titsZ] at h
  rcases h with h | h
  · exact h1 h
  · exact h3 (h.trans parrottV_twelve.symm)

theorem parrottV_five_conj_seven :
    parrottV 5 * parrottV 7 * (parrottV 5)⁻¹ = parrottV 7 * parrottV 11 := by
  have hc := parrottV_comm (r := (5, 7, [11])) (by decide)
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hc
  have h511 : parrottV 5 * parrottV 11 = parrottV 11 * parrottV 5 :=
    parrottV_commute (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)
      (by decide)
  calc parrottV 5 * parrottV 7 * (parrottV 5)⁻¹
      = parrottV 7 * parrottV 5 * parrottV 11 * (parrottV 5)⁻¹ := by rw [hc]
    _ = parrottV 7 * (parrottV 5 * parrottV 11) * (parrottV 5)⁻¹ := by group
    _ = parrottV 7 * parrottV 11 := by rw [h511]; group

theorem parrottF_cases {f : Equiv.Perm (Fin 1755)} (hf : f ∈ parrottF) :
    f ∈ hatE ∨ parrottV 7 * f ∈ hatE := by
  obtain ⟨m, hm, rfl⟩ := mem_parrottF_iff.1 hf
  have hev : ∀ m < 32, m % 2 = 0 → ∀ i ∈ fBits m, 9 ≤ i ∧ i ≤ 12 := by decide
  have hodd : ∀ m < 32, m % 2 = 1 → fBits m = 7 :: fBits (m - 1) := by decide
  have hE : ∀ l : List ℕ, (∀ i ∈ l, 9 ≤ i ∧ i ≤ 12) → (l.map parrottV).prod ∈ hatE := by
    intro l hl
    refine list_prod_map_mem fun i hi => ?_
    obtain ⟨h1, h2⟩ := hl i hi
    rw [hatE_eq_parrottU_eight]
    exact subset_closure ⟨i, ⟨by omega, h2⟩, rfl⟩
  rcases Nat.mod_two_eq_zero_or_one m with h0 | h1
  · left
    exact hE _ (hev m hm h0)
  · right
    have h := hodd m hm h1
    have hm1 : m - 1 < 32 := by omega
    have hm0 : (m - 1) % 2 = 0 := by omega
    have hr := hE _ (hev (m - 1) hm1 hm0)
    have e : fElt m = parrottV 7 * fElt (m - 1) := by
      rw [fElt, fElt, h]
      simp
    rw [e, ← mul_assoc, parrottV_seven_sq, one_mul]
    exact hr

end CFSG.LocalAnalysis.EvenBN.Tits.Model
