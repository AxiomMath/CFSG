module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16RankFix
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16RankTv
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16RankD

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.ClassicalGroups.Unitary Matrix
open CFSG.LieType.Universal.Unitary (SUid)

section Root

variable {F : Type} [Field F] [Finite F] {σ : F ≃+* F}

theorem transvection_model (hσ : IsUnitaryInvolution σ) (h2 : (2 : F) = 0)
    {E : Subgroup (SUid σ 4)} (hE2 : ∀ a ∈ E, a * a = 1)
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = (2 ^ n) ^ 2) (hcard : Nat.card ↥E = 2 ^ (4 * n)) :
    ∃ B : Subgroup (SUid σ 4), B ≤ E ∧ Nat.card ↥B = 2 ^ n ∧
      ∀ a : SUid σ 4, a ∈ B ↔
        a ∈ E ∧ ∀ x : Fin 4 → F, (∀ b ∈ B, b • x = x) → a • x = x := by
  obtain ⟨hu, heq, hEP⟩ := eq_PW_of_card_eq hσ h2 hE2 hEc hn hF hcard
  obtain ⟨⟨w₀, hw₀W⟩, hw₀ne⟩ := Module.finrank_pos_iff_exists_ne_zero.mp
    (show 0 < Module.finrank F ↥(commSp E) by omega)
  have hw₀0 : w₀ ≠ 0 := fun h => hw₀ne (Subtype.ext h)
  have hti : ∀ w' ∈ commSp E, herm σ w₀ w' = 0 := by
    intro w' hw'
    have hh : w₀ ∈ horth σ (commSp E) := by
      rw [← fixSp_eq_horth hσ hE2, ← heq]; exact hw₀W
    rw [herm_conj σ hσ.invol w' w₀, mem_horth.mp hh w' hw', map_zero]
  have hww : herm σ w₀ w₀ = 0 := hti w₀ hw₀W
  have hc : ∀ c : F, σ c = c → c + σ c = 0 := fun c hc => by
    rw [hc, ← two_mul, h2, zero_mul]
  have htvE : ∀ (c : F) (hcc : c + σ c = 0), tv hσ.invol hww hcc ∈ E := by
    intro c hcc
    have hmem : tv hσ.invol hww hcc ∈ PW (commSp E) := by
      refine mem_PW.mpr ⟨fun v => ?_, fun w' hw' => ?_⟩
      · rw [tv_smul, add_sub_cancel_left]
        exact (commSp E).smul_mem _ hw₀W
      · rw [tv_smul, hti w' hw', mul_zero, zero_smul, add_zero]
    rwa [← hEP] at hmem
  let B : Subgroup (SUid σ 4) :=
    { carrier := {a | a ∈ E ∧ ∀ x, herm σ w₀ x = 0 → a • x = x}
      mul_mem' := fun {a b} ha hb => ⟨E.mul_mem ha.1 hb.1, fun x hx => by
        rw [mul_smul, hb.2 x hx, ha.2 x hx]⟩
      one_mem' := ⟨E.one_mem, fun x _ => one_smul _ _⟩
      inv_mem' := fun {a} ha => ⟨E.inv_mem ha.1, fun x hx => by
        rw [inv_smul_eq_iff]
        exact (ha.2 x hx).symm⟩ }
  have hBmem : ∀ a, a ∈ B ↔ a ∈ E ∧ ∀ x, herm σ w₀ x = 0 → a • x = x := fun a => Iff.rfl
  have hfixB : ∀ x : Fin 4 → F, (∀ b ∈ B, b • x = x) ↔ herm σ w₀ x = 0 := by
    intro x
    constructor
    · intro hx
      have hb : tv hσ.invol hww (hc 1 (map_one σ)) ∈ B :=
        ⟨htvE 1 (hc 1 (map_one σ)), fun y hy => by
          rw [tv_smul, hy, mul_zero, zero_smul, add_zero]⟩
      have := hx _ hb
      rw [tv_smul] at this
      have h3 : (1 * herm σ w₀ x) • w₀ = 0 := by
        have := add_eq_left.mp this
        exact this
      rcases smul_eq_zero.mp h3 with h | h
      · rwa [one_mul] at h
      · exact absurd h hw₀0
    · intro hx b hb
      exact hb.2 x hx
  refine ⟨B, fun a ha => ha.1, ?_, fun a => ?_⟩
  ·
    have hFix := card_fixedField_mul_self hσ h2
    have hq : Nat.card {c : F // σ c = c} = 2 ^ n := by
      rw [hF, ← sq] at hFix
      exact Nat.pow_left_injective (by norm_num) hFix
    rw [← hq]
    obtain ⟨x₀, hx₀⟩ := exists_herm_eq_one σ hw₀0
    refine (Nat.card_congr (Equiv.ofBijective
      (fun c : {c : F // σ c = c} =>
        (⟨tv hσ.invol hww (hc c.1 c.2), htvE c.1 (hc c.1 c.2), fun y hy => by
          rw [tv_smul, hy, mul_zero, zero_smul, add_zero]⟩ : ↥B)) ⟨?_, ?_⟩)).symm
    · intro c c' h
      have h1 : tv hσ.invol hww (hc c.1 c.2) = tv hσ.invol hww (hc c'.1 c'.2) :=
        congrArg Subtype.val h
      have h3 := congrArg (fun g : SUid σ 4 => g • x₀) h1
      simp only [tv_smul, hx₀, mul_one] at h3
      have h4 : (c.1 - c'.1) • w₀ = 0 := by
        rw [sub_smul]
        have := add_left_cancel h3
        rw [this, sub_self]
      rcases smul_eq_zero.mp h4 with h | h
      · exact Subtype.ext (sub_eq_zero.mp h)
      · exact absurd h hw₀0
    · rintro ⟨a, haE, haf⟩
      obtain ⟨c, hcc, hac⟩ := exists_tv_of_fix_perp hσ h2 (hE2 a haE) hw₀0 haf
      have hσc : σ c = c := by
        have : c + σ c = c + c := by rw [hcc, ← two_mul, h2, zero_mul]
        exact add_left_cancel this
      refine ⟨⟨c, hσc⟩, Subtype.ext ?_⟩
      show tv hσ.invol hww (hc c hσc) = a
      refine ext_smul σ fun x => ?_
      rw [tv_smul, hac x]
  · constructor
    · intro ha
      exact ⟨ha.1, fun x hx => ha.2 x ((hfixB x).mp hx)⟩
    · rintro ⟨haE, hax⟩
      exact ⟨haE, fun x hx => hax x ((hfixB x).mpr hx)⟩

end Root

end CFSG.LocalAnalysis.RankThreeUC
