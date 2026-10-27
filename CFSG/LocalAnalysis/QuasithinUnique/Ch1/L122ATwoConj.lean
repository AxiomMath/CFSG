module

public import CFSG.Quasithin.Background.A3Structure38Basic

public section

namespace CFSG.QuasithinUnique.Vol2Native.L122A

open CFSG.Quasithin

variable {X : Type} [Group X]

@[expose] def conjSub (g : X) (K : Subgroup X) : Subgroup X :=
  K.map (MulAut.conj g).toMonoidHom

theorem conjSub_conjSub (h g : X) (K : Subgroup X) : conjSub h (conjSub g K) = conjSub (h * g) K := by
  unfold conjSub
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem conjSub_one (K : Subgroup X) : conjSub 1 K = K := by
  unfold conjSub
  ext x
  simp [Subgroup.mem_map]

theorem conjSub_eq_iff {t : X} {K : Subgroup X} :
    conjSub t K = K ↔ t ∈ Subgroup.normalizer (K : Set X) :=
  A38.map_conj_eq_iff

theorem normalizes_of_two_conjugates {N₁ N₂ : Subgroup X} (hne : N₁ ≠ N₂)
    (h₁ : ∀ g : X, conjSub g N₁ = N₁ ∨ conjSub g N₁ = N₂)
    (h₂ : ∀ g : X, conjSub g N₂ = N₁ ∨ conjSub g N₂ = N₂) {x : X} {m : ℕ}
    (hx : x ^ (2 * m + 1) = 1) : x ∈ Subgroup.normalizer (N₁ : Set X) := by
  by_contra hxn
  have hx1 : conjSub x N₁ ≠ N₁ := fun h => hxn (conjSub_eq_iff.mp h)
  have hx2 : conjSub x N₁ = N₂ := (h₁ x).resolve_left hx1
  have hx3 : conjSub x N₂ = N₁ := by
    refine (h₂ x).resolve_right fun h => ?_
    apply hne
    have h4 : conjSub x⁻¹ (conjSub x N₁) = N₁ := by
      rw [conjSub_conjSub, inv_mul_cancel, conjSub_one]
    have h5 : conjSub x⁻¹ (conjSub x N₂) = N₂ := by
      rw [conjSub_conjSub, inv_mul_cancel, conjSub_one]
    rw [hx2] at h4
    rw [h] at h5
    rw [← h4, h5]
  have hsq : x * x ∈ Subgroup.normalizer (N₁ : Set X) := by
    rw [← conjSub_eq_iff, ← conjSub_conjSub, hx2, hx3]
  have hpow : x = ((x * x) ^ m)⁻¹ := by
    have : x ^ (2 * m + 1) = x * (x * x) ^ m := by
      rw [pow_succ', pow_mul, sq]
    rw [this] at hx
    exact eq_inv_of_mul_eq_one_left hx
  apply hxn
  rw [hpow]
  exact (Subgroup.normalizer (N₁ : Set X)).inv_mem
    ((Subgroup.normalizer (N₁ : Set X)).pow_mem hsq m)

theorem normalizes_of_pElement {N₁ N₂ : Subgroup X} (hne : N₁ ≠ N₂)
    (h₁ : ∀ g : X, conjSub g N₁ = N₁ ∨ conjSub g N₁ = N₂)
    (h₂ : ∀ g : X, conjSub g N₂ = N₁ ∨ conjSub g N₂ = N₂) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {x : X} {k : ℕ} (hx : x ^ (p ^ k) = 1) :
    x ∈ Subgroup.normalizer (N₁ : Set X) ∧ x ∈ Subgroup.normalizer (N₂ : Set X) := by
  obtain ⟨m, hm⟩ := (hp.odd_of_ne_two hp2).pow (n := k)
  rw [hm] at hx
  exact ⟨normalizes_of_two_conjugates hne h₁ h₂ hx,
    normalizes_of_two_conjugates hne.symm (fun g => (h₂ g).symm) (fun g => (h₁ g).symm) hx⟩

end CFSG.QuasithinUnique.Vol2Native.L122A
