module

public import CFSG.FeitThompson.Foundations.PolynomialRootCountDegree
public import CFSG.FeitThompson.Representations.AbelianGroupIrreducibleCharacters

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Polynomial

theorem exists_lt_pow_eq_of_pow_eq_one {r : ℕ} (hr : 0 < r) {ω z : ℂ} (hω : orderOf ω = r)
    (hz : z ^ r = 1) : ∃ i < r, ω ^ i = z := by
  classical
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  have hωr : ω ^ r = 1 := hω ▸ pow_orderOf_eq_one ω
  set f : ℂ[X] := X ^ r - C 1 with hf
  have hfne : f ≠ 0 := X_pow_sub_C_ne_zero hr 1
  have hfdeg : f.natDegree = r := natDegree_X_pow_sub_C
  have hinj : Set.InjOn (fun n : ℕ => ω ^ n) (Set.Iio r) := by
    rw [← hω]; exact pow_injOn_Iio_orderOf
  set S : Finset ℂ := insert z ((Finset.range r).image (fun n => ω ^ n)) with hS
  have hz' : z ∉ (Finset.range r).image (fun n => ω ^ n) := by
    simp only [Finset.mem_image, Finset.mem_range, not_exists, not_and]
    exact fun a ha h => hcon a ha h
  have hcard : S.card = r + 1 := by
    rw [hS, Finset.card_insert_of_notMem hz', Finset.card_image_of_injOn, Finset.card_range]
    exact fun a ha b hb hab =>
      hinj (by simpa using Finset.mem_range.1 ha) (by simpa using Finset.mem_range.1 hb) hab
  have hroots : ∀ x ∈ S, f.eval x = 0 := by
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · simp [hf, hz]
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hx
      simp only [hf, eval_sub, eval_pow, eval_X, eval_C]
      rw [← pow_mul, mul_comm a r, pow_mul, hωr, one_pow, sub_self]
  have hle := card_le_natDegree_of_forall_eval_eq_zero hfne hroots
  rw [hcard, hfdeg] at hle
  omega

theorem Irr.apply_pow {A : Type*} [CommGroup A] {χ : A → ℂ} (hχ : χ ∈ Irr A) (a : A) (k : ℕ) :
    χ (a ^ k) = χ a ^ k := by
  obtain ⟨ψ, rfl⟩ := exists_linearCharFun_eq_of_mem_Irr hχ
  simp [linearCharFun_apply, map_pow]

theorem exists_pow_apply_eq_of_mem_Irr_of_natCard_eq_prime {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0)
    {C : Type*} [Group C] (hC : Nat.card C = p) {θ η : C → ℂ} (hθ : θ ∈ Irr C) (hθ1 : θ ≠ 1)
    (hη : η ∈ Irr C) (hη1 : η ≠ 1) :
    ∃ k : ℕ, 1 ≤ k ∧ Nat.Coprime k n ∧ ∀ c : C, η c = θ (c ^ k) := by
  have hp' := Fact.mk hp
  have hfin : Finite C := Nat.finite_of_card_ne_zero (by rw [hC]; exact hp.ne_zero)
  obtain ⟨c0, hc0⟩ := exists_prime_orderOf_dvd_card' (G := C) p (by rw [hC])
  have hcyc : IsCyclic C := isCyclic_of_orderOf_eq_card c0 (by rw [hc0, hC])
  let _ : CommGroup C := IsCyclic.commGroup
  have htop : Subgroup.zpowers c0 = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, hc0, hC])
  have hgen : ∀ c : C, ∃ j : ℤ, c0 ^ j = c := fun c =>
    Subgroup.mem_zpowers_iff.1 (htop ▸ Subgroup.mem_top c)
  obtain ⟨ψθ, hψθ⟩ := exists_linearCharFun_eq_of_mem_Irr hθ
  obtain ⟨ψη, hψη⟩ := exists_linearCharFun_eq_of_mem_Irr hη
  have htriv : ∀ f : C →* ℂˣ, f c0 = 1 → linearCharFun f = 1 := by
    intro f hf
    funext c
    obtain ⟨j, rfl⟩ := hgen c
    simp [linearCharFun_apply, map_zpow, hf]
  set ω : ℂˣ := ψθ c0 with hω
  have hωp : (ω : ℂ) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, hω, ← map_pow, ← hc0, pow_orderOf_eq_one, map_one,
      Units.val_one]
  have hωne : (ω : ℂ) ≠ 1 := fun h => hθ1 (hψθ ▸ htriv ψθ (Units.ext h))
  have hordω : orderOf (ω : ℂ) = p := by
    rcases hp.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one hωp) with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hωne
    · exact h
  have hordωu : orderOf ω = p := by rw [← orderOf_units, hordω]
  obtain ⟨i, hip, hiω⟩ := exists_lt_pow_eq_of_pow_eq_one hp.pos hordω (z := ((ψη c0 : ℂ)))
    (by rw [← Units.val_pow_eq_pow_val, ← map_pow, ← hc0, pow_orderOf_eq_one, map_one,
      Units.val_one])
  have hi0 : i ≠ 0 := by
    intro h
    refine hη1 (hψη ▸ htriv ψη (Units.ext ?_))
    rw [← hiω, h, pow_zero, Units.val_one]
  have hnotdvd : ¬ p ∣ i := fun h =>
    absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hi0) h) (by omega)
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder (Nat.coprime_ordCompl hp hn) i 1
  have hk0 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exact absurd ((Nat.modEq_zero_iff_dvd).1 (h ▸ hk1).symm) hnotdvd
    · exact h
  have hkp : Nat.Coprime k p := by
    unfold Nat.Coprime
    rw [hk1.gcd_eq]
    exact Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hnotdvd)
  have hkm : Nat.Coprime k (ordCompl[p] n) := by
    unfold Nat.Coprime
    rw [hk2.gcd_eq]
    exact Nat.gcd_one_left _
  have hkn : Nat.Coprime k n := by
    rw [← Nat.ordProj_mul_ordCompl_eq_self n p]
    exact Nat.Coprime.mul_right (hkp.pow_right _) hkm
  refine ⟨k, hk0, hkn, ?_⟩
  have hik : ω ^ i = ω ^ k := by
    rw [pow_eq_pow_iff_modEq, hordωu]
    exact hk1.symm
  have hηc0 : ψη c0 = ω ^ k := Units.ext (by rw [← hik, Units.val_pow_eq_pow_val, ← hiω])
  have key : ∀ c : C, ψη c = ψθ (c ^ k) := by
    intro c
    obtain ⟨j, rfl⟩ := hgen c
    rw [map_zpow, hηc0, ← zpow_natCast (c0 ^ j) k, ← zpow_mul, map_zpow, ← hω,
      ← zpow_natCast ω k, ← zpow_mul, mul_comm]
  intro c
  rw [← hψη, ← hψθ, linearCharFun_apply, linearCharFun_apply, key c]

theorem exists_pow_apply_eq_of_mem_Irr {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n) (hpn : p ∣ n)
    {C : Type*} [Group C] (hC : Nat.card C = p) {θ η : C → ℂ} (hθ : θ ∈ Irr C) (hθ1 : θ ≠ 1)
    (hη : η ∈ Irr C) (hη1 : η ≠ 1) :
    ∃ k : ℕ, 1 ≤ k ∧ Nat.Coprime k n ∧ ∀ c : C, η c = θ (c ^ k) :=
  have _ : p ∣ n := hpn
  exists_pow_apply_eq_of_mem_Irr_of_natCard_eq_prime hp (Nat.one_le_iff_ne_zero.1 hn) hC hθ hθ1
    hη hη1

end CFSG.FeitThompson
