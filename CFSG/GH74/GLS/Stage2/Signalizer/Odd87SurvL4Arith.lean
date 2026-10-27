module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherGraphFieldInvolution

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  Matrix

theorem exists_pow_frob {F : Type} [Field F] [Finite F] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hcard : Nat.card F = p ^ f) (σ : F ≃+* F) : ∃ k : ℕ, ∀ x : F, σ x = x ^ p ^ k := by
  obtain ⟨φ, hφ, hord, hzp, -⟩ := finite_field_automorphism_fixed_field_cardinality hp hf hcard
  have hφfin : IsOfFinOrder φ := orderOf_pos_iff.mp (by rw [hord]; omega)
  have hmem : σ ∈ Subgroup.zpowers φ := hzp ▸ Subgroup.mem_top σ
  rw [← hφfin.mem_powers_iff_mem_zpowers] at hmem
  obtain ⟨k, hk⟩ := hmem
  refine ⟨k, fun x => ?_⟩
  rw [← hk, pow_apply_of_frobenius hφ]

theorem exists_pow_four_of_frob {F : Type} [Field F] [Finite F] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hfodd : Odd f) (hcard : Nat.card F = p ^ f) (k : ℕ) (a : Fˣ) :
    ∃ y : Fˣ, a ^ (p ^ k) = a * y ^ 4 := by
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have htodd : Odd (p ^ k) := hpodd.pow
  have ht4 : p ^ k % 4 = 1 ∨ p ^ k % 4 = 3 := by
    obtain ⟨r, hr⟩ := htodd
    omega
  rcases ht4 with h1 | h3
  · obtain ⟨w, hw⟩ : ∃ w, p ^ k = 4 * w + 1 := ⟨p ^ k / 4, by omega⟩
    refine ⟨a ^ w, ?_⟩
    rw [hw, pow_add, pow_mul, pow_one, mul_comm, ← pow_mul, ← pow_mul, mul_comm w 4]
  · obtain ⟨w, hw⟩ : ∃ w, p ^ k = 4 * w + 3 := ⟨p ^ k / 4, by omega⟩
    have hp4 : p % 4 = 3 := by
      by_contra hne
      have h1 : p % 4 = 1 := by
        obtain ⟨r, hr⟩ := hpodd
        omega
      have : p ^ k % 4 = 1 := by rw [Nat.pow_mod, h1]; simp
      omega
    have hq4 : p ^ f % 4 = 3 := by
      obtain ⟨g, hg⟩ := hfodd
      rw [hg, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod, Nat.pow_mod p, hp4]
      norm_num
    obtain ⟨v, hv⟩ : ∃ v, p ^ f = 4 * v + 3 := ⟨p ^ f / 4, by omega⟩
    have hN : a ^ (4 * v + 2) = 1 := by
      have h1 : Nat.card Fˣ = 4 * v + 2 := by
        rw [Nat.card_units, hcard]
        omega
      rw [← h1]
      exact pow_card_eq_one'
    refine ⟨(a ^ (2 * w + 1)) ^ (v + 1), ?_⟩
    have e1 : ((a ^ (2 * w + 1)) ^ (v + 1)) ^ 4 = (a ^ (2 * w + 1)) ^ 2 := by
      have : ((a ^ (2 * w + 1)) ^ (v + 1)) ^ 4 =
          (a ^ (4 * v + 2)) ^ (2 * w + 1) * (a ^ (2 * w + 1)) ^ 2 := by
        rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_add]
        congr 1
        ring
      rw [this, hN, one_pow, one_mul]
    rw [e1, hw, ← pow_mul, ← pow_succ']
    congr 1
    ring

theorem exists_pow_four_of_odd_pow {G : Type} [CommGroup G] {u z : G} {S : ℕ} (hS : S % 2 = 1)
    (h : u ^ S = z ^ 4) : ∃ y : G, u = y ^ 4 := by
  obtain ⟨r, hr⟩ : ∃ r, S = 2 * r + 1 := ⟨S / 2, by omega⟩
  obtain ⟨T, hT⟩ := Nat.even_mul_succ_self r
  refine ⟨z ^ S * (u ^ (2 * T))⁻¹, ?_⟩
  have h1 : S * S = 8 * T + 1 := by
    subst hr
    nlinarith
  calc u = u ^ (S * S) * (u ^ (8 * T))⁻¹ := by
        rw [h1, pow_add, pow_one]; group
    _ = ((u ^ S) ^ S) * (u ^ (8 * T))⁻¹ := by rw [pow_mul]
    _ = ((z ^ 4) ^ S) * (u ^ (8 * T))⁻¹ := by rw [h]
    _ = (z ^ S * (u ^ (2 * T))⁻¹) ^ 4 := by
        rw [mul_pow, inv_pow, ← pow_mul, ← pow_mul, ← pow_mul]
        have e1 : 4 * S = S * 4 := mul_comm _ _
        have e2 : 8 * T = 2 * T * 4 := by ring
        rw [e1, e2]

theorem conjAut_mem_range_conj_of_det_four {F : Type} [Field F] {C : GL (Fin 4) F} {y : Fˣ}
    (hC : GeneralLinearGroup.det C = y ^ 4) :
    conjAut 4 F C ∈ (MulAut.conj : projectiveSL 4 F →* MulAut (projectiveSL 4 F)).range := by
  have hdet : ((GeneralLinearGroup.scalar (Fin 4) y⁻¹ * C : GL (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F).det = 1 := by
    rw [← GeneralLinearGroup.val_det_apply, map_mul, hC, ← Units.val_one]
    congr 1
    rw [GeneralLinearGroup.det_scalar, Fintype.card_fin, inv_pow, inv_mul_cancel]
  obtain ⟨g, hg⟩ : ∃ g : SpecialLinearGroup (Fin 4) F,
      SpecialLinearGroup.toGL g = GeneralLinearGroup.scalar (Fin 4) y⁻¹ * C :=
    ⟨⟨_, hdet⟩, Units.ext rfl⟩
  refine ⟨proj 4 F g, ?_⟩
  rw [← conjAut_toGL, hg, map_mul, conjAut_scalar, one_mul]

theorem exists_pow_conjAut_fieldAut {F : Type} [Field F] {n : ℕ} (C : GL (Fin n) F) (σ : F ≃+* F)
    {t : ℕ} (hσ : ∀ x, σ x = x ^ t) (ht : t % 2 = 1) (k : ℕ) :
    ∃ (N : GL (Fin n) F) (S : ℕ),
      (conjAut n F C * fieldAut n F σ) ^ k = conjAut n F N * fieldAut n F (σ ^ k) ∧
      GeneralLinearGroup.det N = (GeneralLinearGroup.det C) ^ S ∧ S % 2 = k % 2 := by
  have hu : ∀ a : Fˣ, Units.map ((σ : F →+* F) : F →* F) a = a ^ t :=
    fun a => Units.ext (by simp [hσ])
  induction k with
  | zero => exact ⟨1, 0, by simp, by simp, rfl⟩
  | succ k ih =>
    obtain ⟨N, S, hN, hd, hS⟩ := ih
    refine ⟨C * GeneralLinearGroup.map (σ : F →+* F) N, 1 + t * S, ?_, ?_, ?_⟩
    · rw [pow_succ', hN, conjAut_mul_fieldAut_mul, pow_succ']
    · rw [map_mul, GeneralLinearGroup.map_det, hd, map_pow, hu, ← pow_mul, pow_add, pow_one]
    · rw [Nat.add_mod, Nat.mul_mod, ht, hS]
      omega

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
