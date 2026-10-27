module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Swap.Structure
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Swap.Simple

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Swap

open Module CFSG.EvenSporadicStandard.HNRecog.Fpf

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)} {c : ℕ} {Fp Fm : Submodule (ZMod 2) V}

private lemma zmod_eq_c_sq_mul (k k' c : ℕ) (hkk' : (k * k') % 5 = 1)
    (hkc : (k * c) % 5 = 1 ∨ (k * c) % 5 = 4) :
    (k' : ZMod 5) = (c : ZMod 5) ^ 2 * (k : ZMod 5) := by
  have hkk'' : (k : ZMod 5) * (k' : ZMod 5) = 1 := by
    have := (ZMod.natCast_eq_natCast_iff' (k * k') 1 5).mpr (by simpa using hkk')
    push_cast at this
    exact this
  have hkc'' : (k : ZMod 5) * (c : ZMod 5) = 1 ∨ (k : ZMod 5) * (c : ZMod 5) = 4 := by
    rcases hkc with h | h
    · left
      have := (ZMod.natCast_eq_natCast_iff' (k * c) 1 5).mpr (by simpa using h)
      push_cast at this
      exact this
    · right
      have := (ZMod.natCast_eq_natCast_iff' (k * c) 4 5).mpr (by simpa using h)
      push_cast at this
      exact this
  have hsq : ((k : ZMod 5) * (c : ZMod 5)) ^ 2 = 1 := by
    rcases hkc'' with h | h <;> rw [h] <;> decide
  calc (k' : ZMod 5) = k' * ((k * c) ^ 2) := by rw [hsq, mul_one]
    _ = (k * k') * (k * c ^ 2) := by ring
    _ = 1 * (k * c ^ 2) := by rw [hkk'']
    _ = c ^ 2 * k := by ring

private lemma cast_five_sub (c : ℕ) (hc : c ≤ 5) :
    (((5 - c : ℕ)) : ZMod 5) = -(c : ZMod 5) := by
  rw [Nat.cast_sub hc, Nat.cast_ofNat]
  rw [show (5 : ZMod 5) = 0 from by decide, zero_sub]

private lemma mod_five_arith (k k' c d : ℕ) (hkk' : (k * k') % 5 = 1)
    (hkc : (k * c) % 5 = 1 ∨ (k * c) % 5 = 4) (hc : c ≤ 5)
    (hd : d = c ∨ d = 5 - c) :
    k' % 5 = (d * (k * d)) % 5 := by
  rw [← ZMod.natCast_eq_natCast_iff']
  rcases hd with hd | hd
  · subst d
    rw [show ((c * (k * c) : ℕ) : ZMod 5) = (c : ZMod 5) ^ 2 * (k : ZMod 5) by
        push_cast; ring]
    exact zmod_eq_c_sq_mul k k' c hkk' hkc
  · subst d
    have hcast : (((5 - c) * (k * (5 - c)) : ℕ) : ZMod 5)
        = (c : ZMod 5) ^ 2 * (k : ZMod 5) := by
      rw [Nat.cast_mul, Nat.cast_mul, cast_five_sub c hc]
      ring
    rw [hcast]
    exact zmod_eq_c_sq_mul k k' c hkk' hkc

private lemma arith_minus_one {k c : ℕ} (hkc : (k * c) % 5 = 4) (hc : c ≤ 5) :
    (k * (5 - c)) % 5 = 1 := by
  have h2 : (4 : ZMod 5) = -1 := by decide
  have hz : (k : ZMod 5) * (c : ZMod 5) = 4 := by
    have := (ZMod.natCast_eq_natCast_iff' (k * c) 4 5).mpr (by simpa using hkc)
    push_cast at this
    exact this
  have hz' : (k : ZMod 5) * (c : ZMod 5) = -1 := by rw [hz, h2]
  have hcast : ((k * (5 - c) : ℕ) : ZMod 5) = 1 := by
    rw [Nat.cast_mul, cast_five_sub c hc, mul_neg, hz']
    ring
  simpa using ((ZMod.natCast_eq_natCast_iff' (k * (5 - c)) 1 5).mp hcast)

private lemma sigma_pair_mul (x y : A5) :
    σ (x, y) = σ (x, 1) * σ (1, y) := by
  rw [← map_mul, show (x, 1) * (1, y) = (x, y) from by ext <;> simp]

private lemma sigma_fst (n : ℕ) : σ (a₀ ^ n, 1) = (σ (a₀, 1)) ^ n := by
  rw [← map_pow]
  congr 1
  ext <;> simp

private lemma sigma_snd (n : ℕ) : σ (1, a₀ ^ n) = (σ (1, a₀)) ^ n := by
  rw [← map_pow]
  congr 1
  ext <;> simp

private lemma a0_pow_five : a₀ ^ 5 = 1 := by
  have := pow_orderOf_eq_one a₀
  rwa [orderOf_a₀] at this

private lemma inv_eq_self_of_mul_self_eq_one {b : V ≃ₗ[ZMod 2] V} (hb : b * b = 1) :
    b⁻¹ = b := by
  calc b⁻¹ = (b * b) * b⁻¹ := by rw [hb, one_mul]
    _ = b * (b * b⁻¹) := by rw [mul_assoc]
    _ = b := by rw [mul_inv_cancel, mul_one]

theorem conj_beta_of_normalized (b : V ≃ₗ[ZMod 2] V) (hb : b * b = 1) {k k' : ℕ}
    (hkk' : (k * k') % 5 = 1) (hα : b * σ (a₀, 1) * b⁻¹ = σ (1, a₀ ^ k)) :
    b * σ (1, a₀) * b⁻¹ = σ (a₀ ^ k', 1) := by
  have hb' : b⁻¹ = b := inv_eq_self_of_mul_self_eq_one hb
  have hαβ : b * σ (a₀, 1) * b⁻¹ = (σ (1, a₀)) ^ k := by
    rw [hα, ← map_pow]
    congr 1
    ext <;> simp
  have hβ5 : (σ (1, a₀)) ^ 5 = 1 := by
    rw [← map_pow]
    have h1 : (((1, a₀) : A5 × A5) ^ 5) = 1 := by ext <;> simp [a0_pow_five]
    rw [h1, map_one]
  have hα_eq : σ (a₀, 1) = (b * σ (1, a₀) * b⁻¹) ^ k := by
    calc σ (a₀, 1) = b⁻¹ * (b * σ (a₀, 1) * b⁻¹) * b := by group
      _ = b⁻¹ * (σ (1, a₀)) ^ k * b := by rw [hαβ]
      _ = b * (σ (1, a₀)) ^ k * b := by rw [hb']
      _ = b * (σ (1, a₀)) ^ k * b⁻¹ := by rw [hb']
      _ = (b * σ (1, a₀) * b⁻¹) ^ k := (conj_pow).symm
  have hγ5 : (b * σ (1, a₀) * b⁻¹) ^ 5 = 1 := by
    rw [conj_pow, hβ5]
    simp
  have hγ_eq : b * σ (1, a₀) * b⁻¹ = (σ (a₀, 1)) ^ k' := by
    calc b * σ (1, a₀) * b⁻¹ = (b * σ (1, a₀) * b⁻¹) ^ (k * k') := by
          rw [pow_eq_pow_mod (k * k') hγ5, hkk', pow_one]
      _ = ((b * σ (1, a₀) * b⁻¹) ^ k) ^ k' := pow_mul _ k k'
      _ = (σ (a₀, 1)) ^ k' := by rw [← hα_eq]
  rw [hγ_eq, ← map_pow]
  congr 1
  ext <;> simp

private lemma pow_apply_eq_self (z : V ≃ₗ[ZMod 2] V) {w : V} (hw : z w = w) (s : ℕ) :
    (z ^ s) w = w := by
  induction s with
  | zero => rfl
  | succ m ih => rw [pow_succ', LinearEquiv.mul_apply, ih, hw]

private lemma mem_of_conj {F : Submodule (ZMod 2) V} (b z : V ≃ₗ[ZMod 2] V) (s : ℕ)
    (hb : b * b = 1) (hzb : b * z * b⁻¹ = z ^ s)
    (hF : ∀ v, v ∈ F ↔ z v = v) :
    ∀ v ∈ F, b v ∈ F := by
  have hb' : b⁻¹ = b := inv_eq_self_of_mul_self_eq_one hb
  have hzb' : b * z * b = z ^ s := by simpa [hb'] using hzb
  have hzbs : z * b = b * z ^ s := by
    calc z * b = (b * b) * (z * b) := by rw [hb, one_mul]
      _ = b * (b * z * b) := by group
      _ = b * z ^ s := by rw [hzb']
  intro v hv
  rw [hF]
  have hv' : z v = v := (hF v).mp hv
  have hzsv : (z ^ s) v = v := pow_apply_eq_self z hv' s
  change z (b v) = b v
  rw [← LinearEquiv.mul_apply, hzbs, LinearEquiv.mul_apply, hzsv]

private lemma b_conj_z (b : V ≃ₗ[ZMod 2] V) (hb : b * b = 1) {k k' c d : ℕ}
    (hkk' : (k * k') % 5 = 1) (hα : b * σ (a₀, 1) * b⁻¹ = σ (1, a₀ ^ k))
    (hkc : (k * c) % 5 = 1 ∨ (k * c) % 5 = 4) (hd : d = c ∨ d = 5 - c) (hc : c ≤ 5) :
    b * σ (a₀ ^ d, a₀) * b⁻¹ = (σ (a₀ ^ d, a₀)) ^ (k * d) := by
  have hαβ : b * σ (a₀, 1) * b⁻¹ = (σ (1, a₀)) ^ k := by
    rw [hα, ← map_pow]
    congr 1
    ext <;> simp
  have hβ' := conj_beta_of_normalized b hb hkk' hα
  have hzL : b * σ (a₀ ^ d, a₀) * b⁻¹ = σ (a₀ ^ k', a₀ ^ (k * d)) := by
    have hdecomp : σ (a₀ ^ d, a₀) = (σ (a₀, 1)) ^ d * σ (1, a₀) := by
      rw [sigma_pair_mul, sigma_fst]
    rw [hdecomp]
    calc b * ((σ (a₀, 1)) ^ d * σ (1, a₀)) * b⁻¹
        = (b * (σ (a₀, 1)) ^ d * b⁻¹) * (b * σ (1, a₀) * b⁻¹) := by group
      _ = (b * σ (a₀, 1) * b⁻¹) ^ d * (b * σ (1, a₀) * b⁻¹) := by rw [← conj_pow]
      _ = ((σ (1, a₀)) ^ k) ^ d * σ (a₀ ^ k', 1) := by rw [hαβ, hβ']
      _ = (σ (1, a₀)) ^ (k * d) * σ (a₀ ^ k', 1) := by rw [pow_mul]
      _ = σ (a₀ ^ k', a₀ ^ (k * d)) := by
            rw [← sigma_snd, ← map_mul]
            congr 1
  have hzR : (σ (a₀ ^ d, a₀)) ^ (k * d)
      = σ (a₀ ^ (d * (k * d)), a₀ ^ (k * d)) := by
    rw [← map_pow]
    congr 1
    ext <;> simp [pow_mul]
  have hcomp : a₀ ^ k' = a₀ ^ (d * (k * d)) :=
    pow_eq_pow_of_modEq (n := 5)
      (show k' ≡ d * (k * d) [MOD 5] from mod_five_arith k k' c d hkk' hkc hc hd)
      a0_pow_five
  rw [hzL, hzR]
  exact congrArg σ (Prod.ext hcomp rfl)

private lemma commute_on_of_beta_eq {b : V ≃ₗ[ZMod 2] V} (hb : b * b = 1) {k k' e : ℕ}
    (hkk' : (k * k') % 5 = 1) (hα : b * σ (a₀, 1) * b⁻¹ = σ (1, a₀ ^ k))
    (hek : (e * k) % 5 = 1) {F : Submodule (ZMod 2) V}
    (hbF : ∀ v ∈ F, b v ∈ F) (hαF : ∀ v ∈ F, σ (a₀, 1) v ∈ F)
    (hβeq : ∀ v ∈ F, σ (1, a₀) v = (σ (a₀, 1) ^ e) v) :
    ∀ v ∈ F, (b : V →ₗ[ZMod 2] V) ((σ (a₀, 1) : V →ₗ[ZMod 2] V) v)
      = (σ (a₀, 1) : V →ₗ[ZMod 2] V) ((b : V →ₗ[ZMod 2] V) v) := by
  have hα5 : (σ (a₀, 1)) ^ 5 = 1 := by
    rw [← map_pow]
    have h1 : (((a₀, 1) : A5 × A5) ^ 5) = 1 := by ext <;> simp [a0_pow_five]
    rw [h1, map_one]
  have hαpow_mem : ∀ n v, v ∈ F → ((σ (a₀, 1)) ^ n) v ∈ F := by
    intro n
    induction n with
    | zero => intro v hv; simpa using hv
    | succ n ih =>
        intro v hv
        rw [pow_succ', LinearEquiv.mul_apply]
        exact hαF _ (ih v hv)
  have hβpow : ∀ m v, v ∈ F → ((σ (1, a₀)) ^ m) v = ((σ (a₀, 1)) ^ (e * m)) v := by
    intro m
    induction m with
    | zero => intro v hv; simp
    | succ m ih =>
        intro v hv
        have hmem : ((σ (1, a₀)) ^ m) v ∈ F := by
          rw [ih v hv]
          exact hαpow_mem (e * m) v hv
        rw [pow_succ', LinearEquiv.mul_apply, hβeq _ hmem, ih v hv]
        rw [← LinearEquiv.mul_apply, ← pow_add]
        congr 1
        ring
  have hβk : ∀ v ∈ F, ((σ (1, a₀)) ^ k) v = (σ (a₀, 1)) v := by
    intro v hv
    rw [hβpow k v hv]
    have : (σ (a₀, 1)) ^ (e * k) = (σ (a₀, 1)) ^ 1 :=
      pow_eq_pow_of_modEq (n := 5) (show e * k ≡ 1 [MOD 5] from hek) hα5
    rw [this, pow_one]
  have hσ1k : σ (1, a₀ ^ k) = (σ (1, a₀)) ^ k := sigma_snd k
  intro v hv
  have hbv : b v ∈ F := hbF v hv
  have h1 : b * σ (a₀, 1) = (b * σ (a₀, 1) * b⁻¹) * b := by group
  have hmain : b (σ (a₀, 1) v) = σ (a₀, 1) (b v) := by
    calc b (σ (a₀, 1) v)
        = (b * σ (a₀, 1)) v := (LinearEquiv.mul_apply b (σ (a₀, 1)) v).symm
      _ = ((b * σ (a₀, 1) * b⁻¹) * b) v := congrArg (fun (e : V ≃ₗ[ZMod 2] V) => e v) h1
      _ = (b * σ (a₀, 1) * b⁻¹) (b v) := LinearEquiv.mul_apply _ _ _
      _ = (σ (1, a₀ ^ k)) (b v) := by rw [hα]
      _ = ((σ (1, a₀)) ^ k) (b v) := by rw [hσ1k]
      _ = (σ (a₀, 1)) (b v) := hβk (b v) hbv
  simpa using hmain

private lemma eq_of_mul_mod_aux (b : V ≃ₗ[ZMod 2] V) (hb : b * b = 1) {k k' e : ℕ}
    (hkk' : (k * k') % 5 = 1) (hα : b * σ (a₀, 1) * b⁻¹ = σ (1, a₀ ^ k))
    (hek : (e * k) % 5 = 1) {F : Submodule (ZMod 2) V}
    (hbF : ∀ v ∈ F, b v ∈ F) (hαF : ∀ v ∈ F, σ (a₀, 1) v ∈ F)
    (hfixF : ∀ u ∈ F, σ (a₀, 1) u = u → u = 0) (h4F : finrank (ZMod 2) F = 4)
    (hβeq : ∀ v ∈ F, σ (1, a₀) v = (σ (a₀, 1) ^ e) v) :
    ∀ v ∈ F, b v = v := by
  have hα5 : (σ (a₀, 1)) ^ 5 = 1 := by
    rw [← map_pow]
    have h1 : (((a₀, 1) : A5 × A5) ^ 5) = 1 := by ext <;> simp [a0_pow_five]
    rw [h1, map_one]
  have hγ5 : ((σ (a₀, 1) : V →ₗ[ZMod 2] V)) ^ 5 = 1 := by
    change (LinearEquiv.automorphismGroup.toLinearMapMonoidHom
      (R := ZMod 2) (M := V) (σ (a₀, 1))) ^ 5 = 1
    rw [← map_pow, hα5, map_one]
  have hbb : ∀ x, (b : V →ₗ[ZMod 2] V) ((b : V →ₗ[ZMod 2] V) x) = x := by
    intro x
    have := congrArg (fun (e : V ≃ₗ[ZMod 2] V) => e x) hb
    simpa using this
  let N : V →ₗ[ZMod 2] V := (b : V →ₗ[ZMod 2] V) - 1
  have hcomm := commute_on_of_beta_eq hb hkk' hα hek hbF hαF hβeq
  have hc : ∀ u ∈ F, N ((σ (a₀, 1) : V →ₗ[ZMod 2] V) u)
      = (σ (a₀, 1) : V →ₗ[ZMod 2] V) (N u) := by
    intro u hu
    change (b : V →ₗ[ZMod 2] V) ((σ (a₀, 1) : V →ₗ[ZMod 2] V) u)
        - (σ (a₀, 1) : V →ₗ[ZMod 2] V) u
      = (σ (a₀, 1) : V →ₗ[ZMod 2] V) ((b : V →ₗ[ZMod 2] V) u - u)
    rw [map_sub, hcomm u hu]
  have hNU : ∀ u ∈ F, N u ∈ F := by
    intro u hu
    change (b : V →ₗ[ZMod 2] V) u - u ∈ F
    exact F.sub_mem (hbF u hu) hu
  have hN2 : ∀ u ∈ F, N (N u) = 0 := by
    intro u hu
    have hbbu : (b : V →ₗ[ZMod 2] V) ((b : V →ₗ[ZMod 2] V) u) = u := hbb u
    change (b : V →ₗ[ZMod 2] V) ((b : V →ₗ[ZMod 2] V) u - u)
      - ((b : V →ₗ[ZMod 2] V) u - u) = 0
    rw [map_sub, hbbu]
    have h2 : (2 : ℕ) • (u - (b : V →ₗ[ZMod 2] V) u) = 0 := by
      rw [← Nat.cast_smul_eq_nsmul (R := ZMod 2) 2,
        show ((2 : ℕ) : ZMod 2) = 0 from by decide, zero_smul]
    calc (u - (b : V →ₗ[ZMod 2] V) u) - ((b : V →ₗ[ZMod 2] V) u - u)
        = (u - (b : V →ₗ[ZMod 2] V) u) + -((b : V →ₗ[ZMod 2] V) u - u) :=
          sub_eq_add_neg _ _
      _ = (u - (b : V →ₗ[ZMod 2] V) u) + (u - (b : V →ₗ[ZMod 2] V) u) := by rw [neg_sub]
      _ = (2 : ℕ) • (u - (b : V →ₗ[ZMod 2] V) u) := (two_nsmul _).symm
      _ = 0 := h2
  have hNzero : ∀ u ∈ F, N u = 0 :=
    eq_zero_of_sq_eq_zero (σ (a₀, 1) : V →ₗ[ZMod 2] V) N hγ5 F hαF hfixF h4F hNU hc hN2
  intro v hv
  have h := hNzero v hv
  change (b : V →ₗ[ZMod 2] V) v - v = 0 at h
  exact sub_eq_zero.mp h

theorem EigenData.map_mem_of_mul_mod (hS : StdHyp σ) (hE : EigenData σ c Fp Fm)
    (b : V ≃ₗ[ZMod 2] V) (hb : b * b = 1) {k k' : ℕ} (hkk' : (k * k') % 5 = 1)
    (hα : b * σ (a₀, 1) * b⁻¹ = σ (1, a₀ ^ k))
    (hkc : (k * c) % 5 = 1 ∨ (k * c) % 5 = 4) :
    (∀ v ∈ Fp, b v ∈ Fp) ∧ (∀ v ∈ Fm, b v ∈ Fm) := by
  have hc5 : c ≤ 5 := by have h := hE.le_four; omega
  constructor
  · have hz := b_conj_z b hb hkk' hα hkc (Or.inr rfl) hc5
    exact mem_of_conj b _ _ hb hz (fun v => hE.mem_plus v)
  · have hz := b_conj_z b hb hkk' hα hkc (Or.inl rfl) hc5
    exact mem_of_conj b _ _ hb hz (fun v => hE.mem_minus v)

theorem EigenData.eq_of_mul_mod_one (hS : StdHyp σ) (hE : EigenData σ c Fp Fm)
    (b : V ≃ₗ[ZMod 2] V) (hb : b * b = 1) {k k' : ℕ} (hkk' : (k * k') % 5 = 1)
    (hα : b * σ (a₀, 1) * b⁻¹ = σ (1, a₀ ^ k)) (hkc : (k * c) % 5 = 1) :
    ∀ v ∈ Fp, b v = v := by
  have hbF : ∀ v ∈ Fp, b v ∈ Fp :=
    (EigenData.map_mem_of_mul_mod hS hE b hb hkk' hα (Or.inl hkc)).1
  have hfixF : ∀ u ∈ Fp, σ (a₀, 1) u = u → u = 0 := by
    intro u _
    simpa using hS.fixedFree_left_pow (n := 1) (by decide) u
  have hek : (c * k) % 5 = 1 := by rw [Nat.mul_comm]; exact hkc
  exact eq_of_mul_mod_aux b hb hkk' hα hek hbF hE.alpha_mem.1 hfixF hE.finrank_plus hE.beta_eq.1

theorem EigenData.eq_of_mul_mod_four (hS : StdHyp σ) (hE : EigenData σ c Fp Fm)
    (b : V ≃ₗ[ZMod 2] V) (hb : b * b = 1) {k k' : ℕ} (hkk' : (k * k') % 5 = 1)
    (hα : b * σ (a₀, 1) * b⁻¹ = σ (1, a₀ ^ k)) (hkc : (k * c) % 5 = 4) :
    ∀ v ∈ Fm, b v = v := by
  have hbF : ∀ v ∈ Fm, b v ∈ Fm :=
    (EigenData.map_mem_of_mul_mod hS hE b hb hkk' hα (Or.inr hkc)).2
  have hfixF : ∀ u ∈ Fm, σ (a₀, 1) u = u → u = 0 := by
    intro u _
    simpa using hS.fixedFree_left_pow (n := 1) (by decide) u
  have hek : ((5 - c) * k) % 5 = 1 := by
    rw [Nat.mul_comm]
    exact arith_minus_one hkc (by have h := hE.le_four; omega)
  exact eq_of_mul_mod_aux b hb hkk' hα hek hbF hE.alpha_mem.2 hfixF hE.finrank_minus hE.beta_eq.2

end CFSG.EvenSporadicStandard.HNRecog.Swap
