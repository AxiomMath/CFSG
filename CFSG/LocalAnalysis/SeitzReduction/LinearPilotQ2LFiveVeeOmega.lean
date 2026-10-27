module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveVeeCore
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star
public import Mathlib.RingTheory.PiTensorProduct

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix CFSG.Fischer
open scoped commutatorElement

variable {E : Type*} [AddCommGroup E] [Finite E]

omit [Finite E] in
theorem addMonoidEnd_pow_three_of_pow_three
    (ρ : SpecialLinearGroup (Fin 4) F4 →* AddMonoid.End E) {x : SpecialLinearGroup (Fin 4) F4}
    (hx : x ^ 3 = 1) : ρ x ^ 3 = 1 := by
  rw [← map_pow, hx, map_one]

theorem card_fixed_veeH1_eq_four (h2 : ∀ x : E, x + x = 0) (hE : Nat.card E = 2 ^ 8)
    (ρ : SpecialLinearGroup (Fin 4) F4 →* AddMonoid.End E)
    (hB : Nat.card {e : E // ρ veeB e = e} ≤ 16) (hC : ∀ e : E, ρ veeC e = e → e = 0) :
    Nat.card {e : E // ρ veeH1 e = e} = 4 ∧ Nat.card {e : E // ρ veeH2 e = e} = 4 ∧
      ∀ e : E, ρ veeZ e = e → e = 0 := by
  have hE' : Nat.card E = 256 := by rw [hE]; norm_num
  have hGG : ∀ e, ρ veeGG e = e → e = 0 := eq_zero_of_mul_eq ρ veeP4_mul_veeC hC
  have hZf : ∀ e, ρ veeZ e = e → e = 0 := eq_zero_of_mul_eq ρ veeP5_mul_veeGG hGG
  have hcG : Nat.card {e : E // ρ veeG e = e} ≤ 16 := by
    rw [card_fixed_eq_of_mul_eq ρ veeP1_mul_veeB]
    exact hB
  have hcG' := card_fixed_eq_of_mul_eq ρ veeP2_mul_veeG
  have hcZH := card_fixed_eq_of_mul_eq ρ veeP3_mul_veeG
  have hfixG : ∀ x : E, ρ veeG' ((ρ veeG - 1) x) = (ρ veeG - 1) x := by
    refine apply_eq_of_injective_mul_sub_one ?_
      (addMonoidEnd_pow_three_of_pow_three ρ veeG_pow_three)
      (addMonoidEnd_pow_three_of_pow_three ρ veeG'_pow_three) ?_ ?_
    · rw [← map_mul, ← map_mul, veeG_mul_veeG'_comm]
    · rw [← map_mul, veeG_mul_veeG']
      exact injective_sub_one_of_fixed _ hGG
    · rw [← map_mul, ← map_mul, veeG_mul_veeG'_mul_veeG']
      exact injective_sub_one_of_fixed _ hZf
  have hc2 : Nat.card {e : E // ρ veeG e = e} = 16 := by
    have hmul := card_fixed_mul_card_range_sub (ρ veeG)
    have hle : Nat.card (Set.range fun x => ρ veeG x - x) ≤
        Nat.card {e : E // ρ veeG' e = e} := by
      refine Nat.card_le_card_of_injective (fun y => ⟨y.1, ?_⟩) ?_
      · obtain ⟨x, hx⟩ := y.2
        rw [← hx]
        exact hfixG x
      · intro y z h
        have h' := congrArg Subtype.val h
        exact Subtype.ext h'
    rw [hcG'] at hle
    rw [hE'] at hmul
    interval_cases hc : Nat.card {e : E // ρ veeG e = e} <;> omega
  have hz2 : ρ veeZ * ρ veeZ + ρ veeZ + 1 = 0 :=
    mul_add_add_eq_zero_of_injective (addMonoidEnd_pow_three_of_pow_three ρ veeZ_pow_three)
      (injective_sub_one_of_fixed _ hZf)
  have hdec := card_eq_card_fixed_mul_card_fixed_mul_card_fixed h2 (z := ρ veeZ) (b := ρ veeH1)
    (by rw [← map_mul, ← map_mul, veeZ_mul_veeH1_comm]) hz2
    (addMonoidEnd_pow_three_of_pow_three ρ veeH1_pow_three)
  have e1 : ρ veeZ * ρ veeH1 = ρ veeZH := by rw [← map_mul, veeZ_mul_veeH1]
  have e2 : ρ veeZ * ρ veeZ * ρ veeH1 = ρ veeZZH := by
    rw [← map_mul, ← map_mul, veeZ_mul_veeZ_mul_veeH1]
  rw [e1, e2] at hdec
  have hZZH : Nat.card {e : E // ρ veeZZH e = e} = Nat.card {e : E // ρ veeH1 e = e} := by
    rw [card_fixed_eq_of_mul_eq ρ veeP6_mul_veeH1i, ← card_fixed_inv ρ veeH1,
      inv_eq_of_mul_eq_one_right veeH1_mul_veeH1i]
  rw [hcZH, hc2, hZZH, hE'] at hdec
  have hc1 : Nat.card {e : E // ρ veeH1 e = e} = 4 := by
    set c := Nat.card {e : E // ρ veeH1 e = e}
    have h4 : c ≤ 4 := by nlinarith
    have h4' : 4 ≤ c := by nlinarith
    omega
  refine ⟨hc1, ?_, hZf⟩
  rw [card_fixed_eq_of_mul_eq ρ veeP6_mul_veeH1, hc1]

theorem exists_omega_of_fixed (h2 : ∀ x : E, x + x = 0) (hE : Nat.card E = 2 ^ 8)
    (ρ : SpecialLinearGroup (Fin 4) F4 →* AddMonoid.End E)
    (hB : Nat.card {e : E // ρ veeB e = e} ≤ 16) (hC : ∀ e : E, ρ veeC e = e → e = 0) :
    ∃ ω : AddMonoid.End E, ω * ω + ω + 1 = 0 ∧ (∀ g, ω * ρ g = ρ g * ω) ∧
      ∀ τ : E →+ E, (∀ g e, τ (ρ g e) = ρ (veeFrob g) (τ e)) → ∀ e, τ (ω e) = ω (ω (τ e)) := by
  obtain ⟨hc1, hc2, hZf⟩ := card_fixed_veeH1_eq_four h2 hE ρ hB hC
  have hinv : ∀ g, ρ g * ρ g⁻¹ = 1 := fun g => by rw [← map_mul, mul_inv_cancel, map_one]
  have hinv' : ∀ g, ρ g⁻¹ * ρ g = 1 := fun g => by rw [← map_mul, inv_mul_cancel, map_one]
  set H1 := ρ veeH1 with hH1
  set H2 := ρ veeH2 with hH2
  have h12 : H1 * H2 = H2 * H1 := by rw [hH1, hH2, ← map_mul, ← map_mul, veeH1_mul_veeH2_comm]
  have hz2 : H1 * H2 * (H1 * H2) + H1 * H2 + 1 = 0 := by
    have h := mul_add_add_eq_zero_of_injective
      (addMonoidEnd_pow_three_of_pow_three ρ veeZ_pow_three) (injective_sub_one_of_fixed _ hZf)
    rwa [← veeH1_mul_veeH2, map_mul] at h
  obtain ⟨hω2, hωsym, hωfrob, hP1, hP2⟩ := omega_ring_identities h12
    (addMonoidEnd_pow_three_of_pow_three ρ veeH1_pow_three)
    (addMonoidEnd_pow_three_of_pow_three ρ veeH2_pow_three) hz2 (addMonoidEnd_two_eq_zero h2)
  set ω : AddMonoid.End E := 1 + H1 * H1 + H2 * (1 + H1 + H1 * H1) with hωdef
  have key : ∀ (A B : AddMonoid.End E) (q : SpecialLinearGroup (Fin 4) F4),
      A * B = B * A → A * (1 + A + A * A) = 1 + A + A * A →
      ω = 1 + A * A + B * (1 + A + A * A) → ρ q * A = A * ρ q →
      (∀ e, A e = e → ρ q e = e) → ω * ρ q = ρ q * ω := by
    intro A B q hAB hPA hω hqA htriv
    have hc : Commute A (ρ q) := hqA.symm
    have hA1 : (1 + A * A) * ρ q = ρ q * (1 + A * A) :=
      ((Commute.one_left _).add_left (hc.mul_left hc)).eq
    have hPc : (1 + A + A * A) * ρ q = ρ q * (1 + A + A * A) :=
      (((Commute.one_left _).add_left hc).add_left (hc.mul_left hc)).eq
    have hPfix : ∀ e, A ((1 + A + A * A) e) = (1 + A + A * A) e := fun e => by
      rw [← addMonoidEnd_mul_apply, hPA]
    have hBPfix : ∀ e, A (B ((1 + A + A * A) e)) = B ((1 + A + A * A) e) := fun e => by
      rw [← addMonoidEnd_mul_apply A B, hAB, addMonoidEnd_mul_apply, hPfix]
    have hB1 : B * (1 + A + A * A) * ρ q = B * (1 + A + A * A) := by
      ext e
      change B ((1 + A + A * A) (ρ q e)) = B ((1 + A + A * A) e)
      rw [← addMonoidEnd_mul_apply (1 + A + A * A), hPc, addMonoidEnd_mul_apply,
        htriv _ (hPfix e)]
    have hB2 : ρ q * (B * (1 + A + A * A)) = B * (1 + A + A * A) := by
      ext e
      change ρ q (B ((1 + A + A * A) e)) = B ((1 + A + A * A) e)
      exact htriv _ (hBPfix e)
    rw [hω]
    calc (1 + A * A + B * (1 + A + A * A)) * ρ q =
          (1 + A * A) * ρ q + B * (1 + A + A * A) * ρ q := add_mul _ _ _
      _ = ρ q * (1 + A * A) + ρ q * (B * (1 + A + A * A)) := by rw [hA1, hB1, hB2]
      _ = ρ q * (1 + A * A + B * (1 + A + A * A)) := (mul_add _ _ _).symm
  have hblock : ∀ (c : Fin 4) (A : AddMonoid.End E), Nat.card {e : E // A e = e} = 4 →
      (∀ q ∈ veeBlock c, ρ q * A = A * ρ q) →
      ∀ q ∈ veeBlock c, ∀ e, A e = e → ρ q e = e := by
    intro c A hcA hqA q hq e he
    have hcard : Nat.card (fixAddSubgroup A) ≤ 4 := by
      rw [← hcA]
      exact le_of_eq (Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl))
    refine apply_eq_of_isPerfect_of_card_le_four ρ (veeBlock_perfect c) (fixAddSubgroup A) hcard
      (fun q hq a ha => ?_) q hq e he
    change A (ρ q a) = ρ q a
    rw [← addMonoidEnd_mul_apply, ← hqA q hq, addMonoidEnd_mul_apply]
    exact congrArg (ρ q) ha
  have hq1 : ∀ q ∈ veeBlock 3, ρ q * H1 = H1 * ρ q := fun q hq => by
    rw [hH1, ← map_mul, ← map_mul, veeBlock_three_le q hq]
  have hq2 : ∀ q ∈ veeBlock 0, ρ q * H2 = H2 * ρ q := fun q hq => by
    rw [hH2, ← map_mul, ← map_mul, veeBlock_zero_le q hq]
  have hω1 : ∀ q ∈ veeBlock 3, ω * ρ q = ρ q * ω := fun q hq =>
    key H1 H2 q h12 hP1 hωdef (hq1 q hq) (hblock 3 H1 hc1 hq1 q hq)
  have hω2' : ∀ q ∈ veeBlock 0, ω * ρ q = ρ q * ω := fun q hq =>
    key H2 H1 q h12.symm hP2 hωsym (hq2 q hq) (hblock 0 H2 hc2 hq2 q hq)
  refine ⟨ω, hω2, ?_, ?_⟩
  ·
    let Sω : Subgroup (SpecialLinearGroup (Fin 4) F4) :=
      { carrier := {g | ω * ρ g = ρ g * ω}
        mul_mem' := fun {g h} hg hh => by
          have hg' : ω * ρ g = ρ g * ω := hg
          have hh' : ω * ρ h = ρ h * ω := hh
          change ω * ρ (g * h) = ρ (g * h) * ω
          rw [map_mul, ← mul_assoc, hg', mul_assoc, hh', ← mul_assoc]
        one_mem' := by
          change ω * ρ 1 = ρ 1 * ω
          rw [map_one, mul_one, one_mul]
        inv_mem' := fun {g} hg => by
          have hg' : ω * ρ g = ρ g * ω := hg
          change ω * ρ g⁻¹ = ρ g⁻¹ * ω
          calc ω * ρ g⁻¹ = ρ g⁻¹ * (ρ g * ω) * ρ g⁻¹ := by rw [← mul_assoc, hinv', one_mul]
            _ = ρ g⁻¹ * (ω * ρ g) * ρ g⁻¹ := by rw [hg']
            _ = ρ g⁻¹ * ω := by rw [mul_assoc, mul_assoc, hinv, mul_one] }
    have hmem : ∀ g, g ∈ Sω ↔ ω * ρ g = ρ g * ω := fun g => Iff.rfl
    have hdiag : ∀ (i j : Fin 4) (hij : i ≠ j) {c : F4} (hc : c ≠ 0),
        SpecialLinearGroup.diag2n hij c hc ∈ Sω := by
      intro i j hij c hc
      rw [hmem]
      obtain ⟨hd1, hd2⟩ := diag2n_mul_veeH hij hc
      have hc1' : Commute (ρ (SpecialLinearGroup.diag2n hij c hc)) H1 := by
        change _ * _ = _ * _
        rw [hH1, ← map_mul, ← map_mul, hd1]
      have hc2' : Commute (ρ (SpecialLinearGroup.diag2n hij c hc)) H2 := by
        change _ * _ = _ * _
        rw [hH2, ← map_mul, ← map_mul, hd2]
      exact (((Commute.one_right _).add_right (hc1'.mul_right hc1')).add_right
        (hc2'.mul_right (((Commute.one_right _).add_right hc1').add_right
          (hc1'.mul_right hc1')))).eq.symm
    have htrans : ∀ (i j : Fin 4) (hij : i ≠ j) (a : F4),
        SpecialLinearGroup.transvection hij a ∈ Sω := by
      intro i j hij a
      by_cases h3 : i ≠ 3 ∧ j ≠ 3
      · exact hω1 _ (transvection_mem_veeBlock hij a h3.1 h3.2)
      by_cases h0 : i ≠ 0 ∧ j ≠ 0
      · exact hω2' _ (transvection_mem_veeBlock hij a h0.1 h0.2)
      have hcases : (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) := by
        revert h3 h0 hij
        revert i j
        decide
      have hcomm : ∀ x y, x ∈ Sω → y ∈ Sω → ⁅x, y⁆ ∈ Sω := fun x y hx hy => by
        rw [commutatorElement_def]
        exact Sω.mul_mem (Sω.mul_mem (Sω.mul_mem hx hy) (Sω.inv_mem hx)) (Sω.inv_mem hy)
      rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have h := SpecialLinearGroup.commutatorElement_transvection
          (by decide : (0 : Fin 4) ≠ 1) (by decide : (1 : Fin 4) ≠ 3) hij a 1
        rw [mul_one] at h
        rw [← h]
        exact hcomm _ _
          (hω1 _ (transvection_mem_veeBlock (c := 3) (by decide : (0 : Fin 4) ≠ 1) a
            (by decide) (by decide)))
          (hω2' _ (transvection_mem_veeBlock (c := 0) (by decide : (1 : Fin 4) ≠ 3) 1
            (by decide) (by decide)))
      · have h := SpecialLinearGroup.commutatorElement_transvection
          (by decide : (3 : Fin 4) ≠ 1) (by decide : (1 : Fin 4) ≠ 0) hij a 1
        rw [mul_one] at h
        rw [← h]
        exact hcomm _ _
          (hω2' _ (transvection_mem_veeBlock (c := 0) (by decide : (3 : Fin 4) ≠ 1) a
            (by decide) (by decide)))
          (hω1 _ (transvection_mem_veeBlock (c := 3) (by decide : (1 : Fin 4) ≠ 0) 1
            (by decide) (by decide)))
    intro g
    exact (hmem g).1 (SpecialLinearGroup.diagonal_transvection_induction' (· ∈ Sω) g
      (fun i j hij c hc => hdiag i j hij hc) htrans (fun A B hA hB => Sω.mul_mem hA hB))
  ·
    intro τ hτ e
    set T : AddMonoid.End E := τ with hTdef
    have hT1 : T * H1 = H1 * H1 * T := by
      ext x
      change τ (ρ veeH1 x) = ρ veeH1 (ρ veeH1 (τ x))
      rw [hτ, veeFrob_veeH1, map_mul]
      rfl
    have hT2 : T * H2 = H2 * H2 * T := by
      ext x
      change τ (ρ veeH2 x) = ρ veeH2 (ρ veeH2 (τ x))
      rw [hτ, veeFrob_veeH2, map_mul]
      rfl
    have hT1' : ∀ X, T * (H1 * X) = H1 * (H1 * (T * X)) := fun X => by
      rw [← mul_assoc, hT1, mul_assoc, mul_assoc]
    have hT2' : ∀ X, T * (H2 * X) = H2 * (H2 * (T * X)) := fun X => by
      rw [← mul_assoc, hT2, mul_assoc, mul_assoc]
    have hT1'' : T * H1 = H1 * (H1 * T) := by rw [hT1, mul_assoc]
    have hT2'' : T * H2 = H2 * (H2 * T) := by rw [hT2, mul_assoc]
    have hTω : T * ω =
        (1 + H1 * H1 * (H1 * H1) + H2 * H2 * (1 + H1 * H1 + H1 * H1 * (H1 * H1))) * T := by
      rw [hωdef]
      simp only [mul_add, add_mul, mul_one, one_mul, mul_assoc, hT1', hT2', hT1'', hT2'']
    rw [hωfrob] at hTω
    exact congrArg (fun f : AddMonoid.End E => f e) hTω

end CFSG.SeitzReduction.LinearPilot
