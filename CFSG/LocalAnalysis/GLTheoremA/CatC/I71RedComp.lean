module

public import CFSG.LocalAnalysis.GLTheoremA.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open

section CommComplement

variable {A : Type} [CommGroup A] [Finite A]

theorem comm_exists_complement {p : ℕ} (hp : p.Prime) (hexp : ∀ a : A, a ^ p = 1) (H : Subgroup A) :
    ∃ C : Subgroup A, C ⊓ H = ⊥ ∧ C ⊔ H = ⊤ := by
  obtain ⟨C, hC, hmax⟩ := (wellFounded_gt (α := Subgroup A)).has_min
    {C : Subgroup A | C ⊓ H = ⊥} ⟨⊥, by simp⟩
  refine ⟨C, hC, ?_⟩
  by_contra hne
  obtain ⟨x, hx⟩ : ∃ x : A, x ∉ C ⊔ H := by
    by_contra h
    push_neg at h
    exact hne (eq_top_iff.2 fun x _ => h x)
  have hC'H : (C ⊔ Subgroup.zpowers x) ⊓ H = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyC', hyH⟩
    obtain ⟨c, hc, z, hz, rfl⟩ := Subgroup.mem_sup.1 hyC'
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    by_cases hpi : (p : ℤ) ∣ i
    · obtain ⟨m, rfl⟩ := hpi
      have hx1 : x ^ ((p : ℤ) * m) = 1 := by
        rw [zpow_mul, zpow_natCast, hexp x, one_zpow]
      have hcH : c ∈ H := by
        have h1 : c * x ^ ((p : ℤ) * m) ∈ H := hyH
        rw [hx1, mul_one] at h1
        exact h1
      have hcb : c ∈ C ⊓ H := ⟨hc, hcH⟩
      rw [hC, Subgroup.mem_bot] at hcb
      rw [hx1, mul_one, hcb]
      exact Subgroup.mem_bot.2 rfl
    · have hcop : IsCoprime (p : ℤ) i :=
        (Nat.prime_iff_prime_int.mp hp).irreducible.coprime_iff_not_dvd.2 hpi
      obtain ⟨u, v, huv⟩ := hcop
      have hxi : x ^ i ∈ C ⊔ H := by
        have h1 : x ^ i = c⁻¹ * (c * x ^ i) := by group
        rw [h1]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_left hc)) (Subgroup.mem_sup_right hyH)
      have huv' : (p : ℤ) * u + v * i = 1 := by rw [← huv]; ring
      have hxeq : x = (x ^ i) ^ v := by
        calc x = x ^ ((p : ℤ) * u + v * i) := by rw [huv', zpow_one]
          _ = (x ^ (p : ℤ)) ^ u * x ^ (v * i) := by rw [zpow_add, zpow_mul]
          _ = (x ^ i) ^ v := by
            rw [zpow_natCast, hexp x, one_zpow, one_mul, ← zpow_mul, mul_comm v i]
      exact absurd (hxeq ▸ Subgroup.zpow_mem _ hxi v) hx
  have hlt : C < C ⊔ Subgroup.zpowers x := by
    refine lt_of_le_of_ne le_sup_left (fun h => hx ?_)
    have hxs : x ∈ C ⊔ Subgroup.zpowers x := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
    rw [← h] at hxs
    exact Subgroup.mem_sup_left hxs
  exact hmax _ hC'H hlt

theorem comm_card_complement {p : ℕ} (hp : p.Prime) (hexp : ∀ a : A, a ^ p = 1) (H : Subgroup A)
    (hlt : p * Nat.card H < Nat.card A) :
    ∃ D : Subgroup A, (∀ d ∈ D, d ^ p = 1) ∧ Nat.card D = p ^ 2 ∧ D ⊓ H = ⊥ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨C, hCH, hCtop⟩ := comm_exists_complement hp hexp H
  have hnorm : H ≤ Subgroup.normalizer (C : Set A) := by
    intro h _
    rw [Subgroup.mem_normalizer_iff]
    intro g
    rw [show h * g * h⁻¹ = g by rw [mul_comm h g, mul_inv_cancel_right]]
  have hmul : Nat.card C * Nat.card H = Nat.card A := by
    have h := card_sup_mul_card_inf_of_le_normalizer hnorm
    rw [hCtop, hCH, Subgroup.card_top, Subgroup.card_bot, mul_one] at h
    exact h.symm
  have hpC : p < Nat.card C := by
    have h1 : p * Nat.card H < Nat.card C * Nat.card H := by rw [hmul]; exact hlt
    exact Nat.lt_of_mul_lt_mul_right h1
  have hPC : IsPGroup p C := fun g => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hexp g.1)⟩
  obtain ⟨n, hn⟩ := hPC.exists_card_eq
  have hn2 : 2 ≤ n := by
    by_contra h
    push_neg at h
    have h1 : p ^ n ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (by omega)
    rw [pow_one, ← hn] at h1
    omega
  have hdvd : p ^ 2 ∣ Nat.card C := by
    rw [hn]
    exact pow_dvd_pow p hn2
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := C) p hdvd
  refine ⟨K.map C.subtype, ?_, ?_, ?_⟩
  · rintro d hd
    obtain ⟨k, -, rfl⟩ := Subgroup.mem_map.1 hd
    exact hexp _
  · rw [Subgroup.card_map_of_injective Subtype.val_injective, hK]
  · rw [eq_bot_iff]
    rintro d ⟨hd, hdH⟩
    obtain ⟨k, -, rfl⟩ := Subgroup.mem_map.1 hd
    have hkb : (k : A) ∈ C ⊓ H := ⟨k.2, hdH⟩
    rw [hCH, Subgroup.mem_bot] at hkb
    rw [Subgroup.mem_bot]
    exact hkb

end CommComplement

section Ambient

variable {M : Type} [Group M]

private theorem elemAbelian_of_comm_exp {p : ℕ} {E : Subgroup M}
    (hc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hp : ∀ x ∈ E, x ^ p = 1) : IsElemAbelian p E :=
  ⟨⟨⟨fun a b => Subtype.ext (hc a a.2 b b.2)⟩⟩, hp⟩

theorem exists_sq_complement {p : ℕ} (hp : p.Prime) [Finite M] {P H : Subgroup M}
    (hP : IsElemAbelian p P) (hlt : p * Nat.card ↥(P ⊓ H) < Nat.card ↥P) :
    ∃ D : Subgroup M, D ≤ P ∧ IsElemAbelian p D ∧ Nat.card D = p ^ 2 ∧ D ⊓ H = ⊥ := by
  classical
  letI : CommGroup ↥P :=
    { (inferInstance : Group ↥P) with
      mul_comm := fun a b => Subtype.ext (isElemAbelian_commute hP a.2 b.2) }
  have hexp : ∀ a : ↥P, a ^ p = 1 := fun a => Subtype.ext (hP.2 a.1 a.2)
  have hcardHA : Nat.card ↥((P ⊓ H).subgroupOf P) = Nat.card ↥(P ⊓ H) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  obtain ⟨DA, hDexp, hDc, hDH⟩ :=
    comm_card_complement hp hexp ((P ⊓ H).subgroupOf P) (by rw [hcardHA]; exact hlt)
  refine ⟨DA.map P.subtype, Subgroup.map_subtype_le DA, ?_, ?_, ?_⟩
  · refine elemAbelian_of_comm_exp ?_ ?_
    · intro a ha b hb
      obtain ⟨a', -, rfl⟩ := Subgroup.mem_map.1 ha
      obtain ⟨b', -, rfl⟩ := Subgroup.mem_map.1 hb
      exact isElemAbelian_commute hP a'.2 b'.2
    · intro x hx
      obtain ⟨k, hkD, rfl⟩ := Subgroup.mem_map.1 hx
      have hk : k ^ p = 1 := hDexp k hkD
      show (k : M) ^ p = 1
      rw [← Subgroup.coe_pow, hk, Subgroup.coe_one]
  · rw [Subgroup.card_map_of_injective Subtype.val_injective, hDc]
  · rw [eq_bot_iff]
    rintro x ⟨hx, hxH⟩
    obtain ⟨k, hkD, rfl⟩ := Subgroup.mem_map.1 hx
    have hkI : k ∈ (P ⊓ H).subgroupOf P := by
      rw [Subgroup.mem_subgroupOf]
      exact ⟨k.2, hxH⟩
    have hkb : k ∈ DA ⊓ (P ⊓ H).subgroupOf P := ⟨hkD, hkI⟩
    rw [hDH, Subgroup.mem_bot] at hkb
    rw [Subgroup.mem_bot]
    show (k : M) = 1
    rw [hkb, Subgroup.coe_one]

theorem le_mul_card_of_no_sq {p : ℕ} (hp : p.Prime) [Finite M] {P H : Subgroup M}
    (hP : IsElemAbelian p P)
    (hno : ∀ D : Subgroup M, D ≤ P → IsElemAbelian p D → Nat.card D = p ^ 2 → D ⊓ H = ⊥ → False) :
    Nat.card ↥P ≤ p * Nat.card ↥(P ⊓ H) := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨D, hDP, hD, hc, hDH⟩ := exists_sq_complement hp hP hlt
  exact hno D hDP hD hc hDH

end Ambient

end CFSG.LocalAnalysis.GLTheoremA
