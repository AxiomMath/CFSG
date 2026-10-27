module

public import CFSG.HardMathSupport.Dickson.Sec6.Gen3D4Aux.Real

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.Gen3D4

open CFSG.Quasithin CFSG.AGLEmbedding.ChevOuter

section Build

variable {X C : Type} [Group X] [Group C] (ρ : X →* MulAut C) (ψ : C →* GL (Fin 8) GF64)
  (φ : MulAut C)

@[expose] def PairRep (p : Pr) (x : X) : Prop :=
  p.1.size = 64 ∧ p.2 < 3 ∧ ∃ g : C, (ψ g : Matrix (Fin 8) (Fin 8) GF64) = toMat p.1 ∧
    ρ x = MulAut.conj g * φ ^ p.2

variable {ρ ψ φ}

theorem mulAut_mul_conj_eq (α : MulAut C) (h : C) :
    α * MulAut.conj h = MulAut.conj (α h) * α := by
  refine MulEquiv.ext fun c => ?_
  simp [MulAut.conj_apply]

theorem psi_phi_pow (hφψ : ∀ g, (ψ (φ g) : Matrix (Fin 8) (Fin 8) GF64) =
    (ψ g : Matrix (Fin 8) (Fin 8) GF64).map frobF) (n : ℕ) (h : C) :
    (ψ ((φ ^ n) h) : Matrix (Fin 8) (Fin 8) GF64) =
      ((fun M : Matrix (Fin 8) (Fin 8) GF64 => M.map frobF)^[n])
        (ψ h : Matrix (Fin 8) (Fin 8) GF64) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', MulAut.mul_apply, hφψ, ih, Function.iterate_succ_apply']

theorem phi_pow_mod (hφ3 : φ ^ 3 = 1) (n : ℕ) : φ ^ n = φ ^ (n % 3) := by
  conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, hφ3, one_pow, one_mul]

theorem pairRep_mul (hφ3 : φ ^ 3 = 1) (hφψ : ∀ g, (ψ (φ g) : Matrix (Fin 8) (Fin 8) GF64) =
    (ψ g : Matrix (Fin 8) (Fin 8) GF64).map frobF) {p q : Pr} {x y : X}
    (hp : PairRep ρ ψ φ p x) (hq : PairRep ρ ψ φ q y) : PairRep ρ ψ φ (mulP p q) (x * y) := by
  obtain ⟨hpa, hpj, g, hg, hx⟩ := hp
  obtain ⟨hqa, hqj, h, hh, hy⟩ := hq
  refine ⟨size_mulArr _ _, snd_mulP_lt p q, g * (φ ^ p.2) h, ?_, ?_⟩
  · rw [map_mul, Units.val_mul, hg, psi_phi_pow hφψ, hh]
    show toMat p.1 * _ = toMat (mulArr p.1 (frobPow p.2 q.1))
    rw [toMat_mulArr, toMat_frobPow]
  · show ρ (x * y) = MulAut.conj (g * (φ ^ p.2) h) * φ ^ ((p.2 + q.2) % 3)
    rw [map_mul, hx, hy, map_mul, ← phi_pow_mod hφ3]
    calc MulAut.conj g * φ ^ p.2 * (MulAut.conj h * φ ^ q.2)
        = MulAut.conj g * (φ ^ p.2 * MulAut.conj h) * φ ^ q.2 := by simp only [mul_assoc]
      _ = MulAut.conj g * (MulAut.conj ((φ ^ p.2) h) * φ ^ p.2) * φ ^ q.2 := by
        rw [mulAut_mul_conj_eq]
      _ = MulAut.conj g * MulAut.conj ((φ ^ p.2) h) * (φ ^ p.2 * φ ^ q.2) := by
        simp only [mul_assoc]
      _ = MulAut.conj g * MulAut.conj ((φ ^ p.2) h) * φ ^ (p.2 + q.2) := by rw [pow_add]

theorem pairRep_ext (hρ : Function.Injective ρ) (hψ : Function.Injective ψ) {p q : Pr} {x y : X}
    (hp : PairRep ρ ψ φ p x) (hq : PairRep ρ ψ φ q y) (h : p = q) : x = y := by
  subst h
  obtain ⟨-, -, g, hg, hx⟩ := hp
  obtain ⟨-, -, h, hh, hy⟩ := hq
  have : g = h := hψ (Units.ext (hg.trans hh.symm))
  subst this
  exact hρ (hx.trans hy.symm)

theorem pairRep_inj (hφ3 : φ ^ 3 = 1) (hψ : Function.Injective ψ)
    (hid : ∀ (g : C) (j : ℕ), j < 3 → MulAut.conj g * φ ^ j = 1 → j = 0 ∧ g = 1) {p q : Pr}
    {x : X} (hp : PairRep ρ ψ φ p x) (hq : PairRep ρ ψ φ q x) : p = q := by
  obtain ⟨hpa, hpj, g, hg, hx⟩ := hp
  obtain ⟨hqa, hqj, h, hh, hy⟩ := hq
  have hgh : MulAut.conj g * φ ^ p.2 = MulAut.conj h * φ ^ q.2 := hx.symm.trans hy
  have hA : MulAut.conj (h⁻¹ * g) * φ ^ p.2 = φ ^ q.2 := by
    rw [map_mul, map_inv, mul_assoc, hgh, ← mul_assoc, inv_mul_cancel, one_mul]
  have hB : MulAut.conj (h⁻¹ * g) * φ ^ ((p.2 + (3 - q.2)) % 3) = 1 := by
    rw [← phi_pow_mod hφ3, pow_add, ← mul_assoc, hA, ← pow_add, Nat.add_sub_cancel' hqj.le]
    exact hφ3
  obtain ⟨hm, hhg⟩ := hid (h⁻¹ * g) _ (Nat.mod_lt _ (by norm_num)) hB
  have hij : p.2 = q.2 := by omega
  have hgh' : h = g := inv_mul_eq_one.1 hhg
  subst hgh'
  have h1 : toMat p.1 = toMat q.1 := by rw [← hg, ← hh]
  exact Prod.ext (eq_of_toMat_eq hpa hqa h1) hij

theorem pairRep_id (hid : ∀ (g : C) (j : ℕ), j < 3 →
    MulAut.conj g * φ ^ j = 1 → j = 0 ∧ g = 1) {p : Pr}
    (hp : PairRep ρ ψ φ p 1) : p = oneP := by
  obtain ⟨hpa, hpj, g, hg, hx⟩ := hp
  rw [map_one] at hx
  obtain ⟨hj, rfl⟩ := hid g p.2 hpj hx.symm
  have h1 : toMat p.1 = toMat oneArr := by
    rw [← hg, map_one, oneArr, toMat_ofMat]
    rfl
  exact Prod.ext (eq_of_toMat_eq hpa size_oneArr h1) hj

variable (ρ ψ φ)

theorem pairRep_one : PairRep ρ ψ φ oneP 1 :=
  ⟨size_oneArr, by norm_num [oneP], 1, by simp [oneP, oneArr, toMat_ofMat], by simp [oneP]⟩

@[expose] noncomputable def buildReal (hφ3 : φ ^ 3 = 1)
    (hφψ : ∀ g, (ψ (φ g) : Matrix (Fin 8) (Fin 8) GF64) =
      (ψ g : Matrix (Fin 8) (Fin 8) GF64).map frobF)
    (hρ : Function.Injective ρ) (hψ : Function.Injective ψ)
    (hid : ∀ (g : C) (j : ℕ), j < 3 → MulAut.conj g * φ ^ j = 1 → j = 0 ∧ g = 1)
    (lt : ℕ → X) (hlt : ∀ k, k < 16 → ∃ g : C,
      (ψ g : Matrix (Fin 8) (Fin 8) GF64) = letterMat k ∧ ρ (lt k) = MulAut.conj g)
    (ph : X) (hph : ρ ph = φ) : Realization X where
  Rep := PairRep ρ ψ φ
  rep_one := pairRep_one ρ ψ φ
  rep_mul := fun hp hq => pairRep_mul hφ3 hφψ hp hq
  rep_ext := fun hp hq h => pairRep_ext hρ hψ hp hq h
  rep_id := fun hp => pairRep_id hid hp
  rep_inj := fun hp hq => pairRep_inj hφ3 hψ hid hp hq
  letter := lt
  rep_letter := by
    intro k hk
    obtain ⟨g, hg, hl⟩ := hlt k hk
    refine ⟨?_, ?_, g, ?_, ?_⟩
    · simpa [symP, hk] using size_letterArr k
    · simp [symP, hk]
    · simpa [symP, hk] using hg.trans (toMat_letterArr hk).symm
    · simp [symP, hk, hl]
  phi := ph
  rep_phi := by
    refine ⟨?_, ?_, 1, ?_, ?_⟩
    · simp [symP, size_oneArr]
    · simp [symP]
    · simp [symP, oneArr, toMat_ofMat]
    · simp [symP, hph]

end Build

end CFSG.HardMathSupport.Dickson.Sec6.Gen3D4
