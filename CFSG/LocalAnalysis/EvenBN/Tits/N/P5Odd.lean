module

public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.EvenBN.Tits.Prelim.FourCount

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P5

open Subgroup CFSG.Open

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem inverts_of_hall {Hs O : Subgroup Γ} {t x : Γ} {a : ℕ}
    (hO : Odd (Nat.card O)) (hOHs : O ≤ Hs) (hOn : ∀ h ∈ Hs, ∀ o ∈ O, h * o * h⁻¹ ∈ O)
    (htHs : t ∈ Hs) (ht2 : t * t = 1) (ht1 : t ≠ 1)
    (hC : Nat.card ↥(centralizer ({t} : Set Γ) ⊓ Hs) ∣ 2 ^ a * 5)
    (hx5 : x ^ 5 = 1) (hx1 : x ≠ 1) (hxC : x ∈ centralizer ({t} : Set Γ) ⊓ Hs)
    (hnoX : ¬ zpowers x ≤ O) :
    ∀ o ∈ O, t * o * t⁻¹ = o⁻¹ := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set C := centralizer ({t} : Set Γ) ⊓ Hs
  set P := O ⊓ centralizer ({t} : Set Γ)
  have hPC : P ≤ C := fun p hp => mem_inf.2 ⟨(mem_inf.1 hp).2, hOHs (mem_inf.1 hp).1⟩
  have hP5 : Nat.card P ∣ 5 := by
    have hodd : Odd (Nat.card P) := hO.of_dvd_nat (card_dvd_of_le inf_le_left)
    exact (Nat.Coprime.pow_right a (Nat.coprime_two_right.2 hodd)).dvd_of_dvd_mul_left
      ((card_dvd_of_le hPC).trans hC)
  have hPbot : P = ⊥ := by
    rcases (Nat.dvd_prime Nat.prime_five).1 hP5 with h | h
    · exact card_eq_one.1 h
    · exfalso
      have hnorm : (P.subgroupOf C).Normal := by
        rw [normal_subgroupOf_iff hPC]
        intro p c hp hc
        exact mem_inf.2 ⟨hOn c (mem_inf.1 hc).2 p (mem_inf.1 hp).1,
          mul_mem (mul_mem (mem_inf.1 hc).1 (mem_inf.1 hp).2) (Subgroup.inv_mem _ (mem_inf.1 hc).1)⟩
      have hidx : P.relIndex C * 5 = Nat.card C := by
        have := relIndex_mul_card (H := P) (K := C)
        rwa [inf_eq_left.2 hPC, h] at this
      have hdvd : P.relIndex C ∣ 2 ^ a :=
        Nat.dvd_of_mul_dvd_mul_right (show 0 < 5 by norm_num) (by rw [hidx]; exact hC)
      have hcop : (P.relIndex C).Coprime (orderOf x) := by
        rw [orderOf_eq_prime hx5 hx1]
        exact Nat.Coprime.coprime_dvd_left hdvd (Nat.Coprime.pow_left a (by norm_num))
      have hxP : x ^ P.relIndex C ∈ P := by
        have := pow_index_mem (P.subgroupOf C) ⟨x, hxC⟩
        rwa [mem_subgroupOf, SubgroupClass.coe_pow] at this
      obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
      exact hnoX (zpowers_le.2 (hm ▸ (mem_inf.1 (pow_mem hxP m)).1))
  have horder : orderOf t = 2 := orderOf_eq_prime (by rw [sq]; exact ht2) ht1
  have htN : t ∈ normalizer (O : Set Γ) := by
    rw [mem_normalizer_iff]
    intro k
    refine ⟨hOn t htHs k, fun hk => ?_⟩
    have := hOn t⁻¹ (Subgroup.inv_mem _ htHs) _ hk
    rwa [inv_inv, show t⁻¹ * (t * k * t⁻¹) * t = k by group] at this
  intro o ho
  refine inv_of_forall_comm_eq_one hO horder htN (fun k hk hkt => ?_) ho
  have hkP : k ∈ P := mem_inf.2 ⟨hk, mem_centralizer_singleton_iff.2 hkt.symm⟩
  rw [hPbot] at hkP
  exact mem_bot.1 hkP

theorem centralizes_of_inverted {Hs O : Subgroup Γ} {t g x : Γ}
    (hOn : ∀ h ∈ Hs, ∀ o ∈ O, h * o * h⁻¹ ∈ O) (htHs : t ∈ Hs)
    (hinv : ∀ o ∈ O, t * o * t⁻¹ = o⁻¹) (hg : ∃ h ∈ Hs, g = h * t * h⁻¹)
    (hgx : g * x * g⁻¹ = x⁻¹) (hxHs : x ∈ Hs) (hx5 : x ^ 5 = 1) :
    ∀ o ∈ O, x * o = o * x := by
  have hconj : ∀ k ∈ Hs, ∀ o ∈ O, (k * t * k⁻¹) * o * (k * t * k⁻¹)⁻¹ = o⁻¹ := by
    intro k hk o ho
    have h1 := hinv _ (hOn k⁻¹ (Subgroup.inv_mem _ hk) o ho)
    calc (k * t * k⁻¹) * o * (k * t * k⁻¹)⁻¹ = k * (t * (k⁻¹ * o * k⁻¹⁻¹) * t⁻¹) * k⁻¹ := by group
      _ = o⁻¹ := by rw [h1]; group
  obtain ⟨h, hh, hgh⟩ := hg
  have hgHs : g ∈ Hs := hgh ▸ mul_mem (mul_mem hh htHs) (Subgroup.inv_mem _ hh)
  have hg1 : ∀ o ∈ O, g * o * g⁻¹ = o⁻¹ := hgh ▸ hconj h hh
  have hg2 : ∀ o ∈ O, g⁻¹ * o * g = o⁻¹ := by
    intro o ho
    have e := hg1 _ (hOn g⁻¹ (Subgroup.inv_mem _ hgHs) o ho)
    rw [inv_inv, show g * (g⁻¹ * o * g) * g⁻¹ = o by group] at e
    exact (inv_eq_iff_eq_inv.2 e).symm
  have hy : ∀ o ∈ O, (x * g * x⁻¹) * o * (x * g * x⁻¹)⁻¹ = o⁻¹ := by
    have := hconj (x * h) (mul_mem hxHs hh)
    rwa [show x * h * t * (x * h)⁻¹ = x * g * x⁻¹ by rw [hgh]; group] at this
  have hxx : x * x = (x * g * x⁻¹) * g⁻¹ := by
    have e : g * x⁻¹ * g⁻¹ = x := by
      calc g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
        _ = x := by rw [hgx, inv_inv]
    calc x * x = x * (g * x⁻¹ * g⁻¹) := by rw [e]
      _ = (x * g * x⁻¹) * g⁻¹ := by group
  have hsq : ∀ o ∈ O, Commute (x * x) o := by
    intro o ho
    show x * x * o = o * (x * x)
    calc x * x * o = (x * g * x⁻¹) * (g⁻¹ * o * g) * (x * g * x⁻¹)⁻¹ * (x * x) := by
          rw [hxx]; group
      _ = o * (x * x) := by rw [hg2 o ho, hy _ (Subgroup.inv_mem _ ho), inv_inv]
  intro o ho
  have h6 : (x * x) ^ 3 = x := by
    rw [← sq, ← pow_mul, show 2 * 3 = 5 + 1 by norm_num, pow_succ, hx5, one_mul]
  have hc := (hsq o ho).pow_left 3
  rw [h6] at hc
  exact hc

theorem normalizes_of_sup_odd {Hs W O : Subgroup Γ} (hWab : IsElemAbelian 2 W) (hO : Odd (Nat.card O))
    (hWc : ∀ w ∈ W, ∀ o ∈ O, w * o = o * w) (hN : ∀ h ∈ Hs, ∀ y ∈ W ⊔ O, h * y * h⁻¹ ∈ W ⊔ O) :
    ∀ h ∈ Hs, ∀ w ∈ W, h * w * h⁻¹ ∈ W := by
  intro h hh w hw
  have hWN : W ≤ normalizer (O : Set Γ) := by
    intro v hv
    rw [mem_normalizer_iff]
    intro o
    have hvo : ∀ o ∈ O, v * o * v⁻¹ = o := fun o ho => by rw [hWc v hv o ho, mul_inv_cancel_right]
    refine ⟨fun ho => by rw [hvo o ho]; exact ho, fun ho => ?_⟩
    have e := hWc v⁻¹ (Subgroup.inv_mem _ hv) _ ho
    have e' : o * v⁻¹ = v * o * v⁻¹ * v⁻¹ := by
      calc o * v⁻¹ = v⁻¹ * (v * o * v⁻¹) := by group
        _ = v * o * v⁻¹ * v⁻¹ := e
    rw [mul_right_cancel e']
    exact ho
  have hy : h * w * h⁻¹ ∈ ((W ⊔ O : Subgroup Γ) : Set Γ) := hN h hh w (mem_sup_left hw)
  rw [coe_mul_of_left_le_normalizer_right W O hWN] at hy
  obtain ⟨w', hw', o, ho, hwo⟩ := Set.mem_mul.1 hy
  have hoo : o ^ 2 = 1 ^ 2 := by
    have h1 : (h * w * h⁻¹) * (h * w * h⁻¹) = 1 := by
      rw [show (h * w * h⁻¹) * (h * w * h⁻¹) = h * (w * w) * h⁻¹ by group,
        hWab.mul_self_eq_one hw, mul_one, mul_inv_cancel]
    rw [← hwo] at h1
    have h2 : w' * o * (w' * o) = (w' * w') * (o * o) := by
      calc w' * o * (w' * o) = w' * (o * w') * o := by group
        _ = w' * (w' * o) * o := by rw [hWc w' hw' o ho]
        _ = (w' * w') * (o * o) := by group
    rw [h2, hWab.mul_self_eq_one hw', one_mul] at h1
    rw [one_pow, sq]
    exact h1
  have ho1 : o = 1 := CFSG.OddInversion.sq_injOn hO ho (one_mem O) hoo
  rw [← hwo, ho1, mul_one]
  exact hw'

end CFSG.LocalAnalysis.EvenBN.Tits.N.P5
