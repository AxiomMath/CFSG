module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockInvThreeAltSevenSylow
import CFSG.LocalAnalysis.AGLEmbedding.BlockAltSevenPLAux

public section

namespace CFSG.AGLEmbedding.AltSevenInv

open Equiv Equiv.Perm

@[expose] def rFun (a b c : Fin 7) : Fin 7 → Fin 7 := ![a, b, r b, r (r b), r (r (r b)), c, r c]

theorem rFun_check : ∀ a b c : Fin 7, r a = a →
    (∀ i, rFun a b c (rFun a b c (rFun a b c i)) = i) → a = 0 ∧ b = 1 ∧ c = 5 := by
  decide +kernel

theorem comm_r_three (x : Perm (Fin 7)) (hc : x * r = r * x) (h3 : x * x * x = 1) : x = 1 := by
  have hcomm : ∀ i, x (r i) = r (x i) := fun i => by
    simpa [Perm.mul_apply] using congrArg (fun f : Perm (Fin 7) => f i) hc
  have h3' : ∀ i, x (x (x i)) = i := fun i => by
    simpa [Perm.mul_apply] using congrArg (fun f : Perm (Fin 7) => f i) h3
  have hr : r 0 = 0 ∧ r 1 = 2 ∧ r 2 = 3 ∧ r 3 = 4 ∧ r 5 = 6 := by decide +kernel
  obtain ⟨hr0, hr1, hr2, hr3, hr5⟩ := hr
  have hx2 : x 2 = r (x 1) := by rw [← hr1, hcomm]
  have hx3 : x 3 = r (r (x 1)) := by rw [← hr2, hcomm, hx2]
  have hx4 : x 4 = r (r (r (x 1))) := by
    rw [show (4 : Fin 7) = r 3 from hr3.symm, hcomm, hx3]
  have hx6 : x 6 = r (x 5) := by rw [← hr5, hcomm]
  have hfun : ∀ i, x i = rFun (x 0) (x 1) (x 5) i := by
    intro i
    fin_cases i
    · rfl
    · rfl
    · exact hx2
    · exact hx3
    · exact hx4
    · rfl
    · exact hx6
  have hfix : r (x 0) = x 0 := by rw [← hcomm, hr0]
  obtain ⟨h0, h1, h5⟩ := rFun_check (x 0) (x 1) (x 5) hfix fun i => by
    rw [← hfun, ← hfun, ← hfun]
    exact h3' i
  have hid : ∀ i, rFun 0 1 5 i = i := by decide +kernel
  ext i
  rw [hfun, h0, h1, h5, hid]
  rfl

variable {T : Subgroup (alternatingGroup (Fin 7))}

theorem isPGroup_normalizer_of_r (hTP : T ≤ P0) (hT2 : IsPGroup 2 T) (hT1 : T ≠ ⊥)
    (hr : inT T r ∨ inT T (r * r * r)) :
    IsPGroup 2 (Subgroup.normalizer (T : Set (alternatingGroup (Fin 7)))) := by
  set N := Subgroup.normalizer (T : Set (alternatingGroup (Fin 7)))
  have hA : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have key : ∀ q : ℕ, q.Prime → q ∣ Nat.card N → q = 2 := by
    intro q hq hqd
    have : Fact q.Prime := ⟨hq⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := N) q hqd
    rw [← Subgroup.orderOf_coe] at hx
    have hxN : (x : alternatingGroup (Fin 7)) ∈ N := x.2
    have hq2520 : q ∣ 2520 := by
      have := orderOf_dvd_natCard (x : alternatingGroup (Fin 7))
      rwa [hx, hA] at this
    have hq' : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 := by
      have hle := Nat.le_of_dvd (by norm_num) hq2520
      have h7 : q ≤ 7 ∨ 7 < q := le_or_gt q 7
      rcases h7 with h7 | h7
      · interval_cases q <;> first | omega | exact absurd hq (by norm_num)
      · exfalso
        have h2520 : (2520 : ℕ) = 2 ^ 3 * 3 ^ 2 * 5 * 7 := by norm_num
        rw [h2520] at hq2520
        rcases (Nat.Prime.dvd_mul hq).mp hq2520 with h | h
        · rcases (Nat.Prime.dvd_mul hq).mp h with h' | h'
          · rcases (Nat.Prime.dvd_mul hq).mp h' with h'' | h''
            · have := Nat.le_of_dvd (by norm_num) (hq.dvd_of_dvd_pow h''); omega
            · have := Nat.le_of_dvd (by norm_num) (hq.dvd_of_dvd_pow h''); omega
          · have := Nat.le_of_dvd (by norm_num) h'; omega
        · have := Nat.le_of_dvd (by norm_num) h; omega
    rcases hq' with h | h | h | h
    · exact h
    · exfalso
      subst h
      set y : Perm (Fin 7) := ((x : alternatingGroup (Fin 7)) : Perm (Fin 7))
      have hy3 : y * y * y = 1 := by
        have := pow_orderOf_eq_one (x : alternatingGroup (Fin 7))
        rw [hx] at this
        have := congrArg Subtype.val this
        simpa [y, pow_succ, mul_assoc] using this
      have hconj : ∀ σ, inT T σ → inT T (y * σ * y⁻¹) := by
        rintro σ ⟨hσ, hσT⟩
        have := (Subgroup.mem_normalizer_iff.mp hxN ⟨σ, hσ⟩).mp hσT
        exact ⟨((x : alternatingGroup (Fin 7)) * ⟨σ, hσ⟩ *
          (x : alternatingGroup (Fin 7))⁻¹).2, this⟩
      set ρ := y * r * y⁻¹ with hρ
      have hρ4 : ρ * ρ * ρ * ρ = 1 := by
        have h := r_pow.2.2
        calc ρ * ρ * ρ * ρ = y * (r * r * r * r) * y⁻¹ := by simp only [ρ]; group
          _ = 1 := by rw [h]; group
      have hρ3 : y * (r * r * r) * y⁻¹ = ρ * ρ * ρ := by simp only [ρ]; group
      have hρmem : ρ = r ∨ ρ = r * r * r := by
        rcases hr with h | h
        · have h1 := hconj _ h
          refine p0_four _ (mem_p0_of_inT hTP h1) fun h2 => r_pow.1 ?_
          calc r * r = y⁻¹ * (ρ * ρ) * y := by simp only [ρ]; group
            _ = 1 := by rw [h2]; group
        · have h1 := hconj _ h
          rw [hρ3] at h1
          have h3 : ρ * ρ * ρ * (ρ * ρ * ρ) ≠ 1 := by
            intro h2
            apply r_pow.2.1
            calc r * r * r * (r * r * r) = y⁻¹ * (ρ * ρ * ρ * (ρ * ρ * ρ)) * y := by
                  simp only [ρ]; group
              _ = 1 := by rw [h2]; group
          rcases p0_four _ (mem_p0_of_inT hTP h1) h3 with h4 | h4
          · right
            calc ρ = ρ * ρ * ρ * ρ * (ρ * ρ * ρ * ρ) * ρ := by rw [hρ4]; group
              _ = (ρ * ρ * ρ) * (ρ * ρ * ρ) * (ρ * ρ * ρ) := by group
              _ = r * r * r := by rw [h4]
          · left
            calc ρ = ρ * ρ * ρ * ρ * (ρ * ρ * ρ * ρ) * ρ := by rw [hρ4]; group
              _ = (ρ * ρ * ρ) * (ρ * ρ * ρ) * (ρ * ρ * ρ) := by group
              _ = (r * r * r) * (r * r * r) * (r * r * r) := by rw [h4]
              _ = r * r * r * r * (r * r * r * r) * r := by group
              _ = r := by rw [r_pow.2.2]; group
      have hρr : ρ = r := by
        rcases hρmem with h | h
        · exact h
        · exfalso
          have e1 : y * y * y * r * (y * y * y)⁻¹ = r * r * r := by
            calc y * y * y * r * (y * y * y)⁻¹ = y * (y * (y * r * y⁻¹) * y⁻¹) * y⁻¹ := by
                  group
              _ = y * (y * (r * r * r) * y⁻¹) * y⁻¹ := by rw [← hρ, h]
              _ = y * (ρ * ρ * ρ) * y⁻¹ := by rw [hρ3]
              _ = y * ((r * r * r) * (r * r * r) * (r * r * r)) * y⁻¹ := by rw [h]
              _ = y * (r * r * r * r * (r * r * r * r) * r) * y⁻¹ := by group
              _ = y * r * y⁻¹ := by rw [r_pow.2.2]; group
              _ = r * r * r := h
          rw [hy3] at e1
          simp only [one_mul, inv_one, mul_one] at e1
          apply r_pow.1
          have e2 : r * r * r * r = r * r := by rw [← e1]
          rw [← e2, r_pow.2.2]
      have hcomm : y * r = r * y := by
        calc y * r = (y * r * y⁻¹) * y := by group
          _ = r * y := by rw [← hρ, hρr]
      have hy1 := comm_r_three y hcomm hy3
      have hx1 : (x : alternatingGroup (Fin 7)) = 1 := Subtype.ext hy1
      rw [hx1, orderOf_one] at hx
      omega
    · exfalso
      exact hT1 (CFSG.AGLEmbedding.BlockAltSevenPL.eq_bot_of_orderOf_eq_five hT2 (h ▸ hx) hxN)
    · exfalso
      exact hT1 (CFSG.AGLEmbedding.BlockAltSevenPL.eq_bot_of_orderOf_eq_seven hT2 (h ▸ hx) hxN)
  have hcard := Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne'
    (fun {d} hd hdd => key d hd hdd)
  exact IsPGroup.of_card hcard

end CFSG.AGLEmbedding.AltSevenInv
