module

public import CFSG.LocalAnalysis.AGL81I.Section3.SL2Cyclic
public import CFSG.Dihedral.Glauberman.DicksonMaxStructure
public import CFSG.LocalAnalysis.AGL81I.Section3.PSL2BorelMaximal
public import CFSG.CharacterTheory.PSL2Table.Basic
public import CFSG.CharacterTheory.PSL2Table.Tori

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open Matrix
open scoped MatrixGroups

variable {F : Type} [Field F] [Finite F]

theorem weyl_not_mem_borelSL : CFSG.PSL2Table.weyl (F := F) ∉ CFSG.PSL2Table.borelSL F := by
  rw [CFSG.PSL2Table.mem_borelSL_iff]
  simp [CFSG.PSL2Table.coe_weyl]

theorem not_normalizer_le_borel {d : ℕ} (hd : d.Prime) (hd2 : d ≠ 2)
    (hdp : d ≠ ringChar F) (D : Subgroup (SL(2, F))) (hDnontriv : 1 < Nat.card D)
    (hD : IsPGroup d D) :
    ¬ Subgroup.normalizer (D : Set (SL(2, F))) ≤ CFSG.PSL2Table.borelSL F := by
  classical
  haveI : Fact d.Prime := ⟨hd⟩
  intro hnorm
  by_cases hDB : D ≤ CFSG.PSL2Table.borelSL F
  ·
    let χ : D →* Fˣ :=
      { toFun := fun A =>
          Units.mk0 ((A.1 : SL(2, F)) 0 0) (by
            have h10 : ((A.1 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 :=
              (CFSG.PSL2Table.mem_borelSL_iff (A.1 : SL(2, F))).mp (hDB A.2)
            have hdet := CFSG.PSL2Table.det_entries (A.1 : SL(2, F))
            rw [h10, mul_zero, sub_zero] at hdet
            exact left_ne_zero_of_mul_eq_one hdet)
        map_one' := by
          ext
          simp
        map_mul' := by
          intro A B
          ext
          simp only [Subgroup.coe_mul, Units.val_mul, Units.val_mk0]
          rw [CFSG.PSL2Table.mul_apply_SL]
          have h10 : ((B.1 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 :=
            (CFSG.PSL2Table.mem_borelSL_iff (B.1 : SL(2, F))).mp (hDB B.2)
          simp [h10] }
    have hχinj : Function.Injective χ := by
      have hker : ∀ A : D, χ A = 1 → A = 1 := by
        intro A hA1
        have h00 : ((A.1 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
          have h := congrArg (fun u : Fˣ => (u : F)) hA1
          simpa [χ] using h
        have h10 : ((A.1 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 :=
          (CFSG.PSL2Table.mem_borelSL_iff (A.1 : SL(2, F))).mp (hDB A.2)
        have h11 : ((A.1 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
          have hdet := CFSG.PSL2Table.det_entries (A.1 : SL(2, F))
          rw [h10, mul_zero, sub_zero, h00, one_mul] at hdet
          exact hdet
        have hAunip : (A.1 : SL(2, F)) =
            CFSG.PSL2Table.unip ((A.1 : SL(2, F)) 0 1) := by
          apply CFSG.PSL2Table.SL_ext <;> simp [h00, h11, h10]
        have hunip_pow : ∀ (t : F) (n : ℕ),
            CFSG.PSL2Table.unip t ^ n = CFSG.PSL2Table.unip ((n : F) * t) := by
          intro t n
          induction n with
          | zero => simp [CFSG.PSL2Table.unip_zero]
          | succ n ih =>
              rw [pow_succ, ih, ← CFSG.PSL2Table.unip_add]
              push_cast
              ring_nf
        have hpow : CFSG.PSL2Table.unip ((A.1 : SL(2, F)) 0 1) ^ ringChar F = 1 := by
          rw [hunip_pow, CharP.cast_eq_zero F (ringChar F), zero_mul,
            CFSG.PSL2Table.unip_zero]
        have hdvd_p : orderOf (A.1 : SL(2, F)) ∣ ringChar F := by
          rw [orderOf_dvd_iff_pow_eq_one, hAunip]
          exact hpow
        have hp : (ringChar F).Prime := CharP.char_is_prime F (ringChar F)
        by_contra hAne
        have hAneD : A ≠ 1 := hAne
        have hdvd_D : d ∣ orderOf A := hD.dvd_orderOf hAneD
        have hdvd : d ∣ orderOf (A.1 : SL(2, F)) := by
          simpa only [Subgroup.orderOf_coe] using hdvd_D
        have hAord_ne_one : orderOf (A.1 : SL(2, F)) ≠ 1 := by
          rw [Subgroup.orderOf_coe]
          exact fun h => hAne ((orderOf_eq_one_iff).mp h)
        have hAord : orderOf (A.1 : SL(2, F)) = ringChar F := by
          rcases (Nat.dvd_prime hp).mp hdvd_p with h1 | hp_eq
          · exact absurd h1 hAord_ne_one
          · exact hp_eq
        rw [hAord] at hdvd
        exact hdp ((Nat.prime_dvd_prime_iff_eq hd hp).mp hdvd)
      intro A B hAB
      have h1 : χ (A * B⁻¹) = 1 := by
        rw [map_mul, map_inv, hAB, mul_inv_cancel]
      have hAB1 : A * B⁻¹ = 1 := hker (A * B⁻¹) h1
      exact mul_inv_eq_one.mp hAB1
    have hcyc : IsCyclic D := isCyclic_of_injective χ hχinj
    letI : IsCyclic D := hcyc
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := D)
    have hgord : orderOf g = Nat.card D := orderOf_eq_card_of_forall_mem_zpowers hg
    let A : SL(2, F) := (g : SL(2, F))
    have hA10 : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 :=
      (CFSG.PSL2Table.mem_borelSL_iff A).mp (hDB g.2)
    have hdet := CFSG.PSL2Table.det_entries A
    rw [hA10, mul_zero, sub_zero] at hdet
    let a : Fˣ := χ g
    have ha_val : (a : F) = (A : Matrix (Fin 2) (Fin 2) F) 0 0 := rfl
    have hA11 : (A : Matrix (Fin 2) (Fin 2) F) 1 1 = (a : F)⁻¹ := by
      have h := hdet
      rw [← ha_val] at h
      exact eq_inv_of_mul_eq_one_right h
    have haord : orderOf a = Nat.card D := by
      rw [orderOf_injective χ hχinj g, hgord]
    have hDodd : Odd (Nat.card D) := by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := d)).mp hD
      rw [hk]
      exact (hd.odd_of_ne_two hd2).pow
    have ha2 : a ^ 2 ≠ 1 := by
      intro h2
      have hdvd : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one h2
      rw [haord] at hdvd
      obtain h1 | h2eq := (Nat.dvd_prime Nat.prime_two).mp hdvd
      · omega
      · have h2dvd : 2 ∣ Nat.card D := ⟨1, by omega⟩
        exact hDodd.not_two_dvd_nat h2dvd
    have ha_ne_inv : (a : F) ≠ (a : F)⁻¹ := by
      intro h
      apply ha2
      have h' : a = a⁻¹ := Units.ext h
      calc a ^ 2 = a * a := pow_two a
        _ = a * a⁻¹ := by nth_rewrite 2 [h']; rfl
        _ = 1 := mul_inv_cancel a
    let b : F := -((A : Matrix (Fin 2) (Fin 2) F) 0 1) / ((a : F) - (a : F)⁻¹)
    have hbden : (a : F) - (a : F)⁻¹ ≠ 0 := sub_ne_zero.mpr ha_ne_inv
    have hb : b * ((a : F) - (a : F)⁻¹) = -((A : Matrix (Fin 2) (Fin 2) F) 0 1) := by
      dsimp only [b]
      exact div_mul_cancel₀ _ hbden
    have hb'_aux : (a : F) * b + (A : Matrix (Fin 2) (Fin 2) F) 0 1 =
        b * (a : F)⁻¹ := by
      linear_combination hb
    have hb' : (A : Matrix (Fin 2) (Fin 2) F) 0 0 * b +
        (A : Matrix (Fin 2) (Fin 2) F) 0 1 =
        b * ((A : Matrix (Fin 2) (Fin 2) F) 0 0)⁻¹ := by
      simpa [ha_val] using hb'_aux
    have hAP : A * CFSG.PSL2Table.unip b =
        CFSG.PSL2Table.unip b * CFSG.PSL2Table.diag a := by
      apply CFSG.PSL2Table.SL_ext <;>
        simp [CFSG.PSL2Table.mul_apply_SL, CFSG.PSL2Table.coe_unip,
          CFSG.PSL2Table.coe_diag, ha_val, hA11, hA10, hb']
    let P : SL(2, F) := CFSG.PSL2Table.unip b
    let W : SL(2, F) := CFSG.PSL2Table.weyl
    let Q : SL(2, F) := P * W * P⁻¹
    have hPinvA : P⁻¹ * A * P = CFSG.PSL2Table.diag a := by
      calc P⁻¹ * A * P = P⁻¹ * (A * P) := by rw [mul_assoc]
        _ = P⁻¹ * (P * CFSG.PSL2Table.diag a) := by rw [hAP]
        _ = CFSG.PSL2Table.diag a := by rw [← mul_assoc, inv_mul_cancel, one_mul]
    have hA_eq : A = P * CFSG.PSL2Table.diag a * P⁻¹ := by
      calc A = A * P * P⁻¹ := by rw [mul_assoc, mul_inv_cancel, mul_one]
        _ = P * CFSG.PSL2Table.diag a * P⁻¹ := by rw [hAP]
    have hA_inv : A⁻¹ = P * (CFSG.PSL2Table.diag a)⁻¹ * P⁻¹ := by
      rw [hA_eq]
      simp only [_root_.mul_inv_rev, inv_inv, mul_assoc]
    have hQ : Q * A * Q⁻¹ = A⁻¹ := by
      calc Q * A * Q⁻¹
          = P * W * (P⁻¹ * A * P) * W⁻¹ * P⁻¹ := by
            simp only [Q, _root_.mul_inv_rev, inv_inv]
            group
        _ = P * W * CFSG.PSL2Table.diag a * W⁻¹ * P⁻¹ := by rw [hPinvA]
        _ = P * (W * CFSG.PSL2Table.diag a * W⁻¹) * P⁻¹ := by group
        _ = P * CFSG.PSL2Table.diag a⁻¹ * P⁻¹ := by
            rw [CFSG.PSL2Table.weyl_conj_diag]
        _ = P * (CFSG.PSL2Table.diag a)⁻¹ * P⁻¹ := by
            rw [CFSG.PSL2Table.diag_inv]
        _ = A⁻¹ := by rw [hA_inv]
    have hDgen : D = Subgroup.zpowers A := by
      apply le_antisymm
      · intro x hx
        have hxg : (⟨x, hx⟩ : D) ∈ Subgroup.zpowers g := hg ⟨x, hx⟩
        rw [Subgroup.mem_zpowers_iff] at hxg ⊢
        obtain ⟨k, hk⟩ := hxg
        exact ⟨k, by simpa [A] using congrArg Subtype.val hk⟩
      · rw [Subgroup.zpowers_le]
        exact g.2
    have hmap : D.map (MulAut.conj Q) = D := by
      rw [hDgen, MonoidHom.map_zpowers]
      simp [hQ]
    have hQmem : Q ∈ Subgroup.normalizer (D : Set (SL(2, F))) :=
      (Subgroup.mem_normalizer_iff_map_conj_eq).mpr hmap
    have hPmem : P ∈ CFSG.PSL2Table.borelSL F := by
      rw [CFSG.PSL2Table.mem_borelSL_iff]
      simp [P, CFSG.PSL2Table.coe_unip]
    have hWnot : W ∉ CFSG.PSL2Table.borelSL F := by
      simpa [W] using weyl_not_mem_borelSL (F := F)
    have hQnot : Q ∉ CFSG.PSL2Table.borelSL F := by
      intro hQb
      apply hWnot
      have hmem : P⁻¹ * Q * P ∈ CFSG.PSL2Table.borelSL F :=
        (CFSG.PSL2Table.borelSL F).mul_mem
          ((CFSG.PSL2Table.borelSL F).mul_mem
            ((CFSG.PSL2Table.borelSL F).inv_mem hPmem) hQb) hPmem
      have heq : P⁻¹ * Q * P = W := by
        simp only [Q, P, W]
        group
      rwa [heq] at hmem
    exact hQnot (hnorm hQmem)
  ·
    have hex : ∃ x, x ∈ D ∧ x ∉ CFSG.PSL2Table.borelSL F := by
      by_contra h
      apply hDB
      intro x hx
      by_contra hxB
      exact h ⟨x, hx, hxB⟩
    obtain ⟨x, hxD, hxB⟩ := hex
    exact hxB (hnorm (Subgroup.le_normalizer hxD))

theorem exists_normalizer_not_mem_borel {d : ℕ} (hd : d.Prime) (hd2 : d ≠ 2)
    (hdp : d ≠ ringChar F) (D : Subgroup (SL(2, F))) (hDnontriv : 1 < Nat.card D)
    (hD : IsPGroup d D) :
    ∃ w ∈ Subgroup.normalizer (D : Set (SL(2, F))), w ∉ CFSG.PSL2Table.borelSL F := by
  by_contra h
  apply not_normalizer_le_borel hd hd2 hdp D hDnontriv hD
  intro x hx
  by_contra hxB
  exact h ⟨x, hx, hxB⟩

theorem card_center_SL_le_two : Nat.card (Subgroup.center (SL(2, F))) ≤ 2 := by
  classical
  let f : Subgroup.center (SL(2, F)) → Fin 2 :=
    fun A => if A = 1 then 0 else 1
  have hf : Function.Injective f := by
    intro A B hAB
    by_cases hA : A = 1
    · have hfA : f A = 0 := by simp [f, hA]
      by_cases hB : B = 1
      · exact hA.trans hB.symm
      · have hfB : f B = 1 := by simp [f, hB]
        rw [hfA, hfB] at hAB
        exact absurd hAB (by decide)
    · have hA' : (A.1 : SL(2, F)) ≠ 1 := fun h => hA (Subtype.ext h)
      have hfA : f A = 1 := by simp [f, hA]
      by_cases hB : B = 1
      · have hfB : f B = 0 := by simp [f, hB]
        rw [hfA, hfB] at hAB
        exact absurd hAB (by decide)
      · have hB' : (B.1 : SL(2, F)) ≠ 1 := fun h => hB (Subtype.ext h)
        have hAm : (A.1 : SL(2, F)) = -1 :=
          ((CFSG.PSL2Table.mem_center_SL_iff A.1).mp A.2).resolve_left hA'
        have hBm : (B.1 : SL(2, F)) = -1 :=
          ((CFSG.PSL2Table.mem_center_SL_iff B.1).mp B.2).resolve_left hB'
        exact Subtype.ext (hAm.trans hBm.symm)
  have := Nat.card_le_card_of_injective f hf
  simpa using this

end CFSG.LocalAnalysis.AGL81I.Section3
