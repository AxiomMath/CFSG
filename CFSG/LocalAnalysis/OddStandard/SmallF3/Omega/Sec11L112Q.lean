module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L112Lam

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem sec11_mem_zpowers_two {z x : G} (hz : z * z = 1) (hx : x ∈ zpowers z) :
    x = 1 ∨ x = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hz2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two, hz]
  have hk : k = 2 * (k / 2) + k % 2 := (Int.mul_ediv_add_emod k 2).symm
  have hr : k % 2 = 0 ∨ k % 2 = 1 := Int.emod_two_eq_zero_or_one k
  rw [hk, zpow_add, zpow_mul, hz2, one_zpow, one_mul]
  rcases hr with h | h
  · left
    rw [h, zpow_zero]
  · right
    rw [h, zpow_one]

namespace Sec11Perm

variable {A M : Subgroup G} {Alt : Subgroup (Equiv.Perm (Fin 6))} {φ : (Fin 6 → ZMod 2) → G}

theorem inU_of_mem_zpowers (h : Sec11Perm A M Alt φ) {x v : Fin 6 → ZMod 2}
    (hx : φ x * (φ v)⁻¹ ∈ zpowers (φ (Pi.single 0 1 + Pi.single 1 1))) : sec11InU (x + v) := by
  rcases sec11_mem_zpowers_two (h.sq _) hx with h1 | h1
  · have h2 : φ x = φ v := mul_inv_eq_one.mp h1
    rcases (h.eq_iff x v).mp h2 with h3 | h3
    · exact Or.inl h3
    · exact Or.inr (Or.inl h3)
  · have h2 : φ x = φ (Pi.single 0 1 + Pi.single 1 1 + v) := by
      rw [h.mul, ← h1]
      group
    have key : ∀ a b c : ZMod 2, a + b = a + (c + b) + c := by decide
    have hk : x + v = (x + (Pi.single 0 1 + Pi.single 1 1 + v)) +
        (Pi.single 0 1 + Pi.single 1 1) := by
      funext i
      exact key _ _ _
    rcases (h.eq_iff x _).mp h2 with h3 | h3
    · right
      right
      left
      rw [hk, h3, zero_add]
    · right
      right
      right
      rw [hk, h3]
      abel

theorem lambda_data (h : Sec11Perm A M Alt φ) (Q : Subgroup G)
    (hz : φ (Pi.single 0 1 + Pi.single 1 1) ∈ Q)
    (hAQ : ∀ v, φ v ∈ Q → ∑ i, v i = 0)
    (hidx : ∀ v w, ∑ i, v i = 0 → ∑ i, w i = 0 → φ v ∉ Q → φ w ∉ Q → φ (v + w) ∈ Q) :
    ∃ c : Fin 5 → ZMod 2, c 0 = 0 ∧ ∑ i, c i = 0 ∧
      ∀ v, φ v ∈ Q ↔ (∑ i, v i = 0 ∧ sec11Lam c v = 0) := by
  classical
  let f : (Fin 6 → ZMod 2) → ZMod 2 := fun v => if φ v ∈ Q then 0 else 1
  have hone : φ (fun _ => 1) = 1 := (h.ker _).2 (Or.inr rfl)
  have hf0 : f 0 = 0 := by
    simp only [f, h.map_zero, Q.one_mem, if_true]
  have hadd : ∀ v w : Fin 6 → ZMod 2, ∑ i, v i = 0 → ∑ i, w i = 0 → f (v + w) = f v + f w := by
    intro v w hv hw
    simp only [f]
    by_cases hQv : φ v ∈ Q <;> by_cases hQw : φ w ∈ Q
    · have : φ (v + w) ∈ Q := by rw [h.mul]; exact Q.mul_mem hQv hQw
      simp [hQv, hQw, this]
    · have : φ (v + w) ∉ Q := by
        intro hvw
        apply hQw
        have h1 : φ w = (φ v)⁻¹ * φ (v + w) := by rw [h.mul]; group
        rw [h1]
        exact Q.mul_mem (Q.inv_mem hQv) hvw
      simp [hQv, hQw, this]
    · have : φ (v + w) ∉ Q := by
        intro hvw
        apply hQv
        have h1 : φ v = φ (v + w) * (φ w)⁻¹ := by rw [h.mul]; group
        rw [h1]
        exact Q.mul_mem hvw (Q.inv_mem hQw)
      simp [hQv, hQw, this]
    · have := hidx v w hv hw hQv hQw
      simp only [hQv, hQw, this, if_true, if_false]
      decide
  have hrepr := sec11_lam_repr f hf0 hadd
  refine ⟨fun i : Fin 5 => f (Pi.single 0 1 + Pi.single i.succ 1), ?_, ?_, fun v => ?_⟩
  · simp only [f]
    have h01 : (Pi.single (Fin.succ (0 : Fin 5)) (1 : ZMod 2) : Fin 6 → ZMod 2) =
        Pi.single 1 1 := rfl
    rw [h01, if_pos hz]
  · have h1 := hrepr (fun _ => 1) (by decide)
    have h2 : f (fun _ => 1) = 0 := by simp only [f, hone, Q.one_mem, if_true]
    rw [h2] at h1
    rw [h1]
    unfold sec11Lam
    simp
  · constructor
    · intro hv
      have hev := hAQ v hv
      refine ⟨hev, ?_⟩
      rw [← hrepr v hev]
      simp only [f, hv, if_true]
    · rintro ⟨hev, hl⟩
      by_contra hv
      have := hrepr v hev
      rw [hl] at this
      simp only [f, hv, if_false] at this
      exact one_ne_zero this

end Sec11Perm

end CFSG.OddStandard.SmallF3.Omega
