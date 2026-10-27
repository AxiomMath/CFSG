module

public import CFSG.CGT.PushingUpLit.BHS.NatSL2
public import CFSG.CGT.PushingUpLit.BHS.SL2Normalizer

public section

namespace CFSG.AGLEmbeddingD2.Tits.E23

open CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS.NatSL2
  CFSG.QuasithinUnique.Setup.Campbell CFSG.QuasithinUnique.Setup.Offender Matrix

variable {W : Type} [CommGroup W] [Finite W] {F : Type} [Field F] [Finite F] [CharP F 2]
  {L : Subgroup (MulAut W)} {n : ℕ}

omit [Finite F] [CharP F 2] in
theorem eq_one_of_pow_two_pow_eq_one (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n) {a : F} {k : ℕ}
    (ha : a ^ 2 ^ k = 1) : a = 1 := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_pow (pow_ne_zero _ two_ne_zero)] at ha
    exact zero_ne_one ha
  let u : Fˣ := Units.mk0 a ha0
  have hu : u ^ 2 ^ k = 1 := Units.ext (by simp [u, ha])
  have hcard : u ^ Nat.card Fˣ = 1 := pow_card_eq_one'
  have hc : Nat.card Fˣ = 2 ^ n - 1 := by rw [Nat.card_units, hF]
  have hcop : Nat.Coprime (2 ^ k) (2 ^ n - 1) := by
    refine Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 ?_)
    have : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    omega
  have h1 : u ^ Nat.gcd (2 ^ k) (2 ^ n - 1) = 1 := pow_gcd_eq_one.2 ⟨hu, hc ▸ hcard⟩
  rw [hcop, pow_one] at h1
  exact congrArg Units.val h1

namespace NatSL2.NatData

variable (D : NatData L F n)

omit [Finite W] in
theorem exists_agree {w₀ : Fin 2 → F} (hw₀ : w₀ ≠ 0) {y : MulAut W}
    (hyL : ∀ l ∈ L, y * l * y⁻¹ ∈ L) (hyL' : ∀ l ∈ L, y⁻¹ * l * y ∈ L)
    (hy2 : ∃ k : ℕ, y ^ 2 ^ k = 1) (hyfix : ∀ v ∈ D.Vw w₀, y v = v) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) F, (g : Matrix (Fin 2) (Fin 2) F).mulVec w₀ = w₀ ∧
      ∀ v, D.vec (y v) = (g : Matrix (Fin 2) (Fin 2) F).mulVec (D.vec v) := by
  classical
  have hsm : ∀ (g : Matrix.SpecialLinearGroup (Fin 2) F) (w : Fin 2 → F),
      g • w = (g : Matrix (Fin 2) (Fin 2) F).mulVec w := fun g w => by
    rw [Matrix.SpecialLinearGroup.smul_def]; rfl
  have hvec : ∀ (g : Matrix.SpecialLinearGroup (Fin 2) F) (v : W),
      D.vec (D.ι g v) = (g : Matrix (Fin 2) (Fin 2) F).mulVec (D.vec v) := fun g v => by
    rw [D.vec_ι, smul_def']
  have hfixL : ∀ z : MulAut W, (∀ l ∈ L, z⁻¹ * l * z ∈ L) → ∀ v ∈ fixV L, z v ∈ fixV L := by
    intro z hz v hv l hl
    have h1 := hv _ (hz l hl)
    have : l (z v) = z ((z⁻¹ * l * z) v) := by simp [MulAut.mul_apply]
    rw [this, h1]
  have hwd : ∀ z : MulAut W, (∀ l ∈ L, z⁻¹ * l * z ∈ L) →
      ∀ v v' : W, D.vec v = D.vec v' → D.vec (z v) = D.vec (z v') := by
    intro z hz v v' hvv'
    have h1 : v * v'⁻¹ ∈ fixV L := by
      rw [← D.vec_eq_zero_iff, D.vec_div, hvv', sub_self]
    have h2 := (D.vec_eq_zero_iff _).2 (hfixL z hz _ h1)
    rw [map_mul, map_inv, D.vec_div] at h2
    exact sub_eq_zero.1 h2
  have hzL : ∀ l ∈ L, (y⁻¹)⁻¹ * l * y⁻¹ ∈ L := fun l hl => by rw [inv_inv]; exact hyL l hl
  choose s hs using D.exists_vec
  let f : (Fin 2 → F) → (Fin 2 → F) := fun w => D.vec (y (s w))
  have hf : ∀ v, f (D.vec v) = D.vec (y v) := fun v => hwd y hyL' _ _ (hs _)
  have hfadd : ∀ a b, f (a + b) = f a + f b := by
    intro a b
    have : a + b = D.vec (s a * s b) := by rw [D.vec_mul, hs, hs]
    rw [this, hf, map_mul, D.vec_mul]
  have hfinj : Function.Injective f := by
    intro a b hab
    have h1 : D.vec (y (s a)) = D.vec (y (s b)) := hab
    have h2 := hwd y⁻¹ hzL _ _ h1
    simp only [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply] at h2
    rw [← hs a, ← hs b]
    exact h2
  let b : Equiv.Perm (Fin 2 → F) := Equiv.ofBijective f hfinj.bijective_of_finite
  have hb : ∀ v, b (D.vec v) = D.vec (y v) := hf
  have hbadd : ∀ w w' : Fin 2 → F, b (w + w') = b w + b w' := hfadd
  have hnorm : ∀ g : Matrix.SpecialLinearGroup (Fin 2) F,
      ∃ g' : Matrix.SpecialLinearGroup (Fin 2) F, b⁻¹ * slPerm F g * b = slPerm F g' := by
    intro g
    obtain ⟨g', hg'⟩ := D.exists_ι_eq (hyL' _ (D.ι_mem g))
    refine ⟨g', ?_⟩
    have key : slPerm F g * b = b * slPerm F g' := by
      ext w : 1
      obtain ⟨v, rfl⟩ := D.exists_vec w
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, slPerm_apply, slPerm_apply, hsm, hsm, hb,
        ← hvec, ← hvec, hb, hg']
      simp [MulAut.mul_apply]
    rw [mul_assoc, key, ← mul_assoc, inv_mul_cancel, one_mul]
  obtain ⟨σ, hσ⟩ := exists_isSemilinearWith_of_normalizes b hbadd hnorm
  have hline : ∀ c : F, b (c • w₀) = c • w₀ := by
    intro c
    obtain ⟨v, hv⟩ := D.exists_vec (c • w₀)
    rw [← hv, hb, hyfix v ((D.mem_Vw).2 ⟨c, hv⟩)]
  have hbw : b w₀ = w₀ := by simpa using hline 1
  have hσid : ∀ c : F, σ c = c := by
    intro c
    have h1 := hσ c w₀
    rw [hline, hbw] at h1
    by_contra hne
    have h2 : (c - σ c) • w₀ = 0 := by rw [sub_smul, h1, sub_self]
    rcases smul_eq_zero.1 h2 with h3 | h3
    · exact hne (sub_eq_zero.1 h3).symm
    · exact hw₀ h3
  set N := columnMat b with hN
  have hbN : ∀ w, b w = N.mulVec w := by
    intro w
    have := columnMat_mulVec hbadd hσ w
    simp only [hσid] at this
    exact this.symm
  have hbpow : ∀ m : ℕ, ∀ v, (b ^ m) (D.vec v) = D.vec ((y ^ m) v) := by
    intro m
    induction m with
    | zero => intro v; simp
    | succ m ih =>
      intro v
      rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, ih, hb, MulAut.mul_apply]
  obtain ⟨k, hk⟩ := hy2
  have hNpow : N ^ 2 ^ k = 1 := by
    have hall : ∀ w, (N ^ 2 ^ k).mulVec w = w := by
      have hbN' : ∀ m : ℕ, ∀ w, (b ^ m) w = (N ^ m).mulVec w := by
        intro m
        induction m with
        | zero => intro w; simp
        | succ m ih =>
          intro w
          rw [pow_succ', Equiv.Perm.mul_apply, ih, hbN, pow_succ', Matrix.mulVec_mulVec]
      intro w
      obtain ⟨v, rfl⟩ := D.exists_vec w
      rw [← hbN', hbpow, hk, MulAut.one_apply]
    ext i j
    have := congrFun (hall (Pi.single j 1)) i
    simpa [Matrix.mulVec_single, Matrix.one_apply, Pi.single_apply, eq_comm] using this
  have hdet : N.det = 1 := by
    have h1 : N.det ^ 2 ^ k = 1 := by rw [← Matrix.det_pow, hNpow, Matrix.det_one]
    exact eq_one_of_pow_two_pow_eq_one D.card_F D.one_le h1
  refine ⟨⟨N, hdet⟩, ?_, fun v => ?_⟩
  · show N.mulVec w₀ = w₀
    rw [← hbN, hbw]
  · show D.vec (y v) = N.mulVec (D.vec v)
    rw [← hbN, hb]

end NatSL2.NatData

end CFSG.AGLEmbeddingD2.Tits.E23
