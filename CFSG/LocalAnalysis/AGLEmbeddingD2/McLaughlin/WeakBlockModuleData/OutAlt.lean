module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open Equiv

variable {Q : Type*} [Group Q]

@[expose] def conjOnNormalizer (A : Subgroup Q) (u : Q) (hu : u ∈ Subgroup.normalizer (A : Set Q)) :
    A ≃* A where
  toFun a := ⟨u * a * u⁻¹, (Subgroup.mem_normalizer_iff.mp hu a).mp a.2⟩
  invFun a := ⟨u⁻¹ * a * u, by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hu) (a : Q)).mp a.2
    simpa using this⟩
  left_inv a := by ext; simp [mul_assoc]
  right_inv a := by ext; simp [mul_assoc]
  map_mul' a b := by ext; simp [mul_assoc]

theorem conjOnNormalizer_apply (A : Subgroup Q) (u : Q) (hu : u ∈ Subgroup.normalizer (A : Set Q))
    (a : A) : ((conjOnNormalizer A u hu a : A) : Q) = u * a * u⁻¹ := rfl

theorem mem_sup_centralizer_of_three_pow_normalizer_alt {N : ℕ} (hN : 5 ≤ N) (hN6 : N ≠ 6)
    (A : Subgroup Q) (e : A ≃* alternatingGroup (Fin N)) {u : Q}
    (hu : u ∈ Subgroup.normalizer (A : Set Q)) {k : ℕ} (huk : u ^ (3 ^ k) = 1) :
    u ∈ A ⊔ Subgroup.centralizer (A : Set Q) := by
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj N hN hN6
  set ψ : MulAut (alternatingGroup (Fin N)) :=
    (e.symm.trans (conjOnNormalizer A u hu)).trans e with hψ
  obtain ⟨σ, hσ⟩ := hbij.2 ψ
  have hconj : ∀ b : A, ((e (conjOnNormalizer A u hu b) : alternatingGroup (Fin N)) : Perm (Fin N)) =
      σ * (e b : Perm (Fin N)) * σ⁻¹ := by
    intro b
    have h := congrArg (fun φ : MulAut (alternatingGroup (Fin N)) =>
      ((φ (e b) : alternatingGroup (Fin N)) : Perm (Fin N))) hσ
    simpa [hψ, MulAut.conjNormal_apply] using h.symm
  have hiter : ∀ (j : ℕ) (b : A), ((e ⟨u ^ j * b * (u ^ j)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hu j) b).mp b.2⟩ :
        alternatingGroup (Fin N)) : Perm (Fin N)) = σ ^ j * (e b : Perm (Fin N)) * (σ ^ j)⁻¹ := by
    intro j
    induction j with
    | zero => intro b; simp
    | succ j ih =>
      intro b
      have h1 := hconj ⟨u ^ j * b * (u ^ j)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hu j) b).mp b.2⟩
      have e1 : (conjOnNormalizer A u hu ⟨u ^ j * b * (u ^ j)⁻¹,
          (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hu j) b).mp b.2⟩) =
          ⟨u ^ (j + 1) * b * (u ^ (j + 1))⁻¹,
          (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hu (j + 1)) b).mp b.2⟩ := by
        apply Subtype.ext
        simp [conjOnNormalizer_apply, pow_succ', mul_assoc]
      rw [e1] at h1
      rw [h1, ih b]
      simp [pow_succ', mul_assoc]
  have hσk : σ ^ (3 ^ k) = 1 := by
    apply hbij.1
    rw [map_one]
    apply MulEquiv.ext
    intro x
    have hx := hiter (3 ^ k) (e.symm x)
    have hx' : (⟨u ^ (3 ^ k) * (e.symm x : Q) * (u ^ (3 ^ k))⁻¹,
        (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hu (3 ^ k)) (e.symm x)).mp
          (e.symm x).2⟩ : A) = e.symm x := by
      apply Subtype.ext; simp [huk]
    rw [hx'] at hx
    simp only [MulEquiv.apply_symm_apply] at hx
    apply Subtype.ext
    simp only [MulAut.conjNormal_apply, MulAut.one_apply]
    exact hx.symm
  have hsign : Perm.sign σ = 1 := by
    have h := congrArg Perm.sign hσk
    rw [map_pow, map_one] at h
    rcases Int.units_eq_one_or (Perm.sign σ) with h1 | h1
    · exact h1
    · rw [h1] at h
      exact absurd h (by
        have : Odd (3 ^ k) := Odd.pow (by decide)
        rw [this.neg_one_pow]; decide)
  have hσA : σ ∈ alternatingGroup (Fin N) := Perm.mem_alternatingGroup.mpr hsign
  set a : A := e.symm ⟨σ, hσA⟩ with ha
  have hea : (e a : Perm (Fin N)) = σ := by simp [ha]
  have hua : ∀ b : A, u * (b : Q) * u⁻¹ = (a : Q) * b * (a : Q)⁻¹ := by
    intro b
    have h1 := hconj b
    have h2 : e (conjOnNormalizer A u hu b) = e (a * b * a⁻¹) := by
      apply Subtype.ext
      rw [h1]
      simp [hea]
    have h3 := e.injective h2
    exact congrArg Subtype.val h3
  have hc : (a : Q)⁻¹ * u ∈ Subgroup.centralizer (A : Set Q) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have := hua ⟨b, hb⟩
    simp only at this
    calc b * ((a : Q)⁻¹ * u) = (a : Q)⁻¹ * ((a : Q) * b * (a : Q)⁻¹) * u := by group
      _ = (a : Q)⁻¹ * (u * b * u⁻¹) * u := by rw [this]
      _ = (a : Q)⁻¹ * u * b := by group
  have : u = (a : Q) * ((a : Q)⁻¹ * u) := by group
  rw [this]
  exact Subgroup.mul_mem_sup a.2 hc

theorem mem_sup_centralizer_of_isPGroup_three_normalizer_alt {N : ℕ} (hN : 5 ≤ N) (hN6 : N ≠ 6)
    (A : Subgroup Q) (e : A ≃* alternatingGroup (Fin N)) {u : Q}
    (hu : u ∈ Subgroup.normalizer (A : Set Q)) (hp : IsPGroup 3 (Subgroup.zpowers u)) :
    u ∈ A ⊔ Subgroup.centralizer (A : Set Q) := by
  obtain ⟨k, hk⟩ := hp ⟨u, Subgroup.mem_zpowers u⟩
  exact mem_sup_centralizer_of_three_pow_normalizer_alt hN hN6 A e hu
    (by simpa using congrArg Subtype.val hk)

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
