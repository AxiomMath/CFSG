module

public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.HeisRoot

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

theorem two_pow_le_card_of_heis_root_of_inj {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {L : Subgroup (MulAut W)} {S : Type} [Group S] (π : ↥L →* S)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center ↥L)
    (hZ : ¬ p ∣ Nat.card π.ker)
    {K V : Type} [Field K] [Finite K] [CharP K p] [AddCommGroup V] [Module K V]
    [Module.Finite K V]
    (z : Multiplicative K →* S) (a : Multiplicative V →* S) (b : V → S)
    (β : V →ₗ[K] V →ₗ[K] K) (hβ : ∀ v : V, v ≠ 0 → ∃ u, β u v ≠ 0)
    (hβl : ∀ u : V, u ≠ 0 → ∃ v, β u v ≠ 0)
    (hz : ∀ c : K, z (Multiplicative.ofAdd c) = 1 → c = 0)
    (hza : ∀ c u, z c * a u = a u * z c)
    (hab : ∀ u v, b v * a (Multiplicative.ofAdd u) * (b v)⁻¹ =
      a (Multiplicative.ofAdd u) * z (Multiplicative.ofAdd (β u v)))
    (hbz : ∀ (c : Multiplicative K) (v : V), b v * z c = z c * b v)
    {T : Type} [Group T] (t : T →* S) (χ : T →* Kˣ)
    (htz : ∀ s c, t s * z (Multiplicative.ofAdd c) * (t s)⁻¹ =
      z (Multiplicative.ofAdd ((χ s : K) * c)))
    (hta : ∀ s u, ∃ u', t s * a (Multiplicative.ofAdd u) * (t s)⁻¹ =
      a (Multiplicative.ofAdd u')) :
    2 ^ (orderOf (2 : ZMod p) * (Nat.card χ.range * Nat.card V / (p - 1))) ≤ Nat.card W := by
  refine two_pow_le_card_of_heis_root hW hp2 π hπ hker hZ z a b β hβ ?_ hza hab hbz t χ htz hta
  intro c u h
  have ha : a (Multiplicative.ofAdd u) = (z (Multiplicative.ofAdd c))⁻¹ :=
    eq_inv_of_mul_eq_one_right h
  have hβ0 : ∀ v, β u v = 0 := by
    intro v
    apply hz
    have h1 := hab u v
    have h2 : b v * (z (Multiplicative.ofAdd c))⁻¹ * (b v)⁻¹ = (z (Multiplicative.ofAdd c))⁻¹ := by
      rw [← map_inv, hbz, mul_inv_cancel_right]
    rw [ha, h2] at h1
    exact mul_eq_left.1 h1.symm
  have hu : u = 0 := by
    by_contra hu0
    obtain ⟨v, hv⟩ := hβl u hu0
    exact hv (hβ0 v)
  subst hu
  refine ⟨hz c ?_, rfl⟩
  rwa [ofAdd_zero, map_one, mul_one] at h

theorem two_pow_le_card_of_heis_root_of_inj_one {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {L : Subgroup (MulAut W)} {S : Type} [Group S] (π : ↥L →* S)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center ↥L)
    (hZ : ¬ p ∣ Nat.card π.ker)
    {K V : Type} [Field K] [Finite K] [CharP K p] [AddCommGroup V] [Module K V]
    [Module.Finite K V]
    (z : Multiplicative K →* S) (a : Multiplicative V →* S) (b : V → S)
    (β : V →ₗ[K] V →ₗ[K] K) (hβ : ∀ v : V, v ≠ 0 → ∃ u, β u v ≠ 0)
    (hβl : ∀ u : V, u ≠ 0 → ∃ v, β u v ≠ 0)
    (hz : ∀ c : K, z (Multiplicative.ofAdd c) = 1 → c = 0)
    (hza : ∀ c u, z c * a u = a u * z c)
    (hab : ∀ u v, b v * a (Multiplicative.ofAdd u) * (b v)⁻¹ =
      a (Multiplicative.ofAdd u) * z (Multiplicative.ofAdd (β u v)))
    (hbz : ∀ (c : Multiplicative K) (v : V), b v * z c = z c * b v) :
    2 ^ (orderOf (2 : ZMod p) * (Nat.card V / (p - 1))) ≤ Nat.card W := by
  have h := two_pow_le_card_of_heis_root_of_inj hW hp2 π hπ hker hZ z a b β hβ hβl hz hza hab
    hbz (T := Unit) 1 1 (fun s c => by simp) (fun s u => ⟨u, by simp⟩)
  have h1 : Nat.card (1 : Unit →* Kˣ).range = 1 := by
    rw [MonoidHom.range_one, Subgroup.card_bot]
  rwa [h1, one_mul] at h

end CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit
