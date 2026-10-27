module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GenCell

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87.U4Red

open Subgroup
open scoped commutatorElement

@[expose] def OutCommFour (Y : Type) [Group Y] : Prop :=
  ∀ α β : MulAut Y, (α * β * α⁻¹ * β⁻¹) ^ 4 ∈ (MulAut.conj : Y →* MulAut Y).range

theorem outCommFour_of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : OutCommFour Y) : OutCommFour Y' := by
  intro α β
  obtain ⟨g, hg⟩ := h (MulAut.congr e.symm α) (MulAut.congr e.symm β)
  refine ⟨e g, ?_⟩
  have hg' : (MulAut.congr e.symm) ((α * β * α⁻¹ * β⁻¹) ^ 4) = MulAut.conj g := by
    rw [hg]
    simp only [map_pow, map_mul, map_inv]
  apply (MulAut.congr e.symm).injective
  rw [hg']
  ext y
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem mem_sup_centralizer_of_inner {A : Type} [Group A] (K : Subgroup A) [K.Normal] {y : A}
    (hy : (MulAut.conjNormal y : MulAut ↥K) ∈ (MulAut.conj : ↥K →* MulAut ↥K).range) :
    y ∈ K ⊔ centralizer (K : Set A) := by
  obtain ⟨k, hk⟩ := hy
  have hc : (k : A)⁻¹ * y ∈ centralizer (K : Set A) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have h1 := congrArg (fun σ : MulAut ↥K => ((σ ⟨w, hw⟩ : ↥K) : A)) hk
    simp only [MulAut.conj_apply, MulAut.conjNormal_apply] at h1
    have h2 : (k : A) * w * (k : A)⁻¹ = y * w * y⁻¹ := h1
    calc w * ((k : A)⁻¹ * y) = (k : A)⁻¹ * ((k : A) * w * (k : A)⁻¹) * y := by group
      _ = (k : A)⁻¹ * (y * w * y⁻¹) * y := by rw [h2]
      _ = (k : A)⁻¹ * y * w := by group
  have : y = (k : A) * ((k : A)⁻¹ * y) := by group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left k.2) (Subgroup.mem_sup_right hc)

theorem mem_of_pow_prime_pow_of_pow_four {G : Type} [Group G] (I : Subgroup G) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {a : G} {n : ℕ} (ha : a ^ (p ^ n) = 1) (h4 : a ^ 4 ∈ I) :
    a ∈ I := by
  have hcop : Nat.Coprime (p ^ n) 4 := by
    have h2 : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).mpr hp2
    have : Nat.Coprime (p ^ n) (2 ^ 2) := Nat.Coprime.pow n 2 h2
    simpa using this
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  have : a = (a ^ (p ^ n)) ^ u * (a ^ 4) ^ v := by
    rw [← zpow_natCast, ← zpow_natCast a 4, ← zpow_mul, ← zpow_mul, ← zpow_add]
    have h1 : (((p ^ n : ℕ) : ℤ) * u + ((4 : ℕ) : ℤ) * v : ℤ) = 1 := by
      linarith
    rw [h1, zpow_one]
  rw [this, ha, one_zpow, one_mul]
  exact I.zpow_mem h4 v

theorem comm_mem_sup_centralizer_of_outCommFour {A : Type} [Group A] (K : Subgroup A) [K.Normal]
    (hOut : OutCommFour ↥K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Subgroup A}
    (hX : IsPGroup p ↥X) {z : A} (hz : z ∈ normalizer (X : Set A)) {x : A} (hx : x ∈ X) :
    ⁅x, z⁆ ∈ K ⊔ centralizer (K : Set A) := by
  have hyX : ⁅x, z⁆ ∈ X := by
    have h1 : z * x⁻¹ * z⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hz x⁻¹).mp (X.inv_mem hx)
    have : ⁅x, z⁆ = x * (z * x⁻¹ * z⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [this]
    exact X.mul_mem hx h1
  obtain ⟨n, hn⟩ := hX ⟨⁅x, z⁆, hyX⟩
  have hyn : ⁅x, z⁆ ^ (p ^ n) = 1 := congrArg Subtype.val hn
  let ρ : A →* MulAut ↥K := MulAut.conjNormal
  apply mem_sup_centralizer_of_inner K
  refine mem_of_pow_prime_pow_of_pow_four _ hp hp2 (n := n) ?_ ?_
  · show (ρ ⁅x, z⁆) ^ (p ^ n) = 1
    rw [← map_pow, hyn, map_one]
  · have := hOut (ρ x) (ρ z)
    have e : ρ ⁅x, z⁆ = ρ x * ρ z * (ρ x)⁻¹ * (ρ z)⁻¹ := by
      simp only [commutatorElement_def, map_mul, map_inv]
    show (ρ ⁅x, z⁆) ^ 4 ∈ _
    rw [e]
    exact this

theorem core_transport {Y Y' : Type} [Group Y] [Group Y'] (ε : Y ≃* Y') {α : MulAut Y}
    {α' : MulAut Y'} (hcomm : ∀ y, ε (α y) = α' (ε y)) {p : ℕ} {X : Subgroup Y}
    (hXp : IsPGroup p ↥X) (hXne : X ≠ ⊥)
    (hcl : Subgroup.closure ((fun x => x * (α x)⁻¹) '' (X : Set Y)) = X)
    (hN : fixSub α ≤ normalizer (X : Set Y)) :
    IsPGroup p ↥(X.map ε.toMonoidHom) ∧ X.map ε.toMonoidHom ≠ ⊥ ∧
      Subgroup.closure ((fun x => x * (α' x)⁻¹) '' ((X.map ε.toMonoidHom : Subgroup Y') : Set Y')) =
        X.map ε.toMonoidHom ∧
      fixSub α' ≤ normalizer ((X.map ε.toMonoidHom : Subgroup Y') : Set Y') := by
  refine ⟨hXp.of_equiv (X.equivMapOfInjective ε.toMonoidHom ε.injective), ?_, ?_, ?_⟩
  · intro h
    exact hXne ((Subgroup.map_eq_bot_iff_of_injective _ ε.injective).mp h)
  · have hset : (fun x => x * (α' x)⁻¹) '' ((X.map ε.toMonoidHom : Subgroup Y') : Set Y') =
        ε.toMonoidHom '' ((fun x => x * (α x)⁻¹) '' (X : Set Y)) := by
      rw [Subgroup.coe_map, Set.image_image, Set.image_image]
      refine Set.image_congr fun x _ => ?_
      simp [hcomm]
    rw [hset, ← MonoidHom.map_closure, hcl]
  · intro y' hy'
    have hy : ε.symm y' ∈ fixSub α := by
      show α (ε.symm y') = ε.symm y'
      apply ε.injective
      rw [hcomm, MulEquiv.apply_symm_apply]
      exact hy'
    have hyN := Subgroup.mem_normalizer_iff.mp (hN hy)
    rw [Subgroup.mem_normalizer_iff]
    intro h'
    have h1 := hyN (ε.symm h')
    simp only [Subgroup.mem_map_equiv] at ⊢
    rw [map_mul, map_mul, map_inv]
    exact h1

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87.U4Red
