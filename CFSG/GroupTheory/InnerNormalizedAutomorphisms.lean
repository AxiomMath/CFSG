module

public import CFSG.Walter.Bender1970.S3.Coprime

public section

namespace CFSG.InnerNormalizedAutomorphisms

variable {X : Type} [Group X]

theorem mem_center_of_conj_eq_one {z : X} (hz : MulAut.conj z = 1) :
    z ∈ Subgroup.center X := by
  rw [Subgroup.mem_center_iff]
  intro g
  have h1 : z * g * z⁻¹ = g := by
    have := congrArg (fun τ : MulAut X => τ g) hz
    simpa [MulAut.conj_apply] using this
  calc g * z = z * g * z⁻¹ * z := by rw [h1]
    _ = z * g := by group

theorem mul_conj_mul_inv_eq (t : MulAut X) (x : X) :
    t * MulAut.conj x * t⁻¹ = MulAut.conj (t x) := by
  ext g
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]
  rw [show t (t⁻¹ g) = g from MulEquiv.apply_symm_apply t g]

variable [Finite X]

theorem isPGroup_comap_conj {T : Subgroup (MulAut X)}
    (hZ : Subgroup.center X = ⊥) (hT : IsPGroup 2 T) :
    IsPGroup 2 (T.comap (MulAut.conj : X →* MulAut X)) := by
  have hinj : Function.Injective (MulAut.conj : X →* MulAut X) := by
    intro x y hxy
    have h1 : MulAut.conj (x * y⁻¹) = 1 := by
      rw [map_mul, map_inv, hxy, mul_inv_cancel]
    have h2 := mem_center_of_conj_eq_one h1
    rw [hZ, Subgroup.mem_bot] at h2
    exact mul_inv_eq_one.mp h2
  intro y
  obtain ⟨k, hk⟩ := hT ⟨MulAut.conj (y : X), y.2⟩
  refine ⟨k, Subtype.ext ?_⟩
  apply hinj
  have hk' : (MulAut.conj (y : X)) ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    rwa [Subgroup.coe_pow] at this
  rw [Subgroup.coe_pow, map_pow, hk']
  simp

theorem fixed_of_mem {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    {B : Subgroup X} (hBcomm : IsMulCommutative B) (hBexp : ∀ x ∈ B, x ^ r = 1)
    (hBcard : r ^ 2 ≤ Nat.card B) (hZ : Subgroup.center X = ⊥)
    (hcent : ∀ b ∈ B, b ≠ 1 → ∀ y : X, y * b = b * y → ∀ k : ℕ, y ^ 2 ^ k = 1 → y = 1)
    {T : Subgroup (MulAut X)} (hT : IsPGroup 2 T)
    (hTB : ∀ b ∈ B, ∀ t ∈ T, MulAut.conj b * t * (MulAut.conj b)⁻¹ ∈ T) :
    (∀ y : X, MulAut.conj y ∈ T → y = 1) ∧ ∀ t ∈ T, ∀ b ∈ B, t b = b := by
  set R := T.comap (MulAut.conj : X →* MulAut X) with hR
  have hR2 : IsPGroup 2 R := isPGroup_comap_conj hZ hT
  have hforward : ∀ b ∈ B, ∀ y : X, y ∈ R → b * y * b⁻¹ ∈ R := by
    intro b hb y hy
    change MulAut.conj (b * y * b⁻¹) ∈ T
    rw [map_mul, map_mul, map_inv]
    exact hTB b hb (MulAut.conj y) hy
  have hRN : B ≤ Subgroup.normalizer (R : Set X) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact hforward b hb y
    · intro hy
      have h := hforward b⁻¹ (B.inv_mem hb) (b * y * b⁻¹) hy
      rwa [show b⁻¹ * (b * y * b⁻¹) * (b⁻¹)⁻¹ = y by group] at h
  have hcop : ¬ r ∣ Nat.card R := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card.mp hR2)
    rw [hk]
    intro hd
    rcases (Nat.dvd_prime Nat.prime_two).mp (hr.dvd_of_dvd_pow hd) with h | h
    · exact hr.ne_one h
    · exact hr2 h
  have hcen : ∀ e ∈ B, e ≠ 1 → R ⊓ Subgroup.centralizer ({e} : Set X) = ⊥ := by
    intro e he he1
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyR, hyC⟩ := Subgroup.mem_inf.mp hy
    have hec : y * e = e * y := Subgroup.mem_centralizer_singleton_iff.mp hyC
    obtain ⟨k, hk⟩ := hR2 ⟨y, hyR⟩
    have hyk : y ^ 2 ^ k = 1 := congrArg Subtype.val hk
    rw [Subgroup.mem_bot]
    exact hcent e he he1 y hec k hyk
  have hRbot : R = ⊥ :=
    CFSG.Walter.eq_bot_of_forall_inf_centralizer_eq_bot_of_elementary
      (E := B) (N := R) hr hBcomm hBexp hBcard hRN hcop hcen
  have hinn : ∀ y : X, MulAut.conj y ∈ T → y = 1 := by
    intro y hy
    have hyR : y ∈ R := hy
    rw [hRbot, Subgroup.mem_bot] at hyR
    exact hyR
  refine ⟨hinn, fun t ht b hb => ?_⟩
  have h2 : MulAut.conj (b * (t b)⁻¹) ∈ T := by
    have hct : MulAut.conj (t b) = t * MulAut.conj b * t⁻¹ := by
      rw [← mul_conj_mul_inv_eq t b]
    rw [map_mul, map_inv, hct]
    rw [show MulAut.conj b * (t * MulAut.conj b * t⁻¹)⁻¹ =
      MulAut.conj b * t * (MulAut.conj b)⁻¹ * t⁻¹ by group]
    exact mul_mem (hTB b hb t ht) (inv_mem ht)
  have h1 := hinn (b * (t b)⁻¹) h2
  rw [mul_inv_eq_one] at h1
  exact h1.symm

end CFSG.InnerNormalizedAutomorphisms
