module

public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Subgroup.Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem sec10L104_exists_proj {N K K0 : Subgroup G}
    (hc : ∀ n ∈ N, ∀ k ∈ K, n * k = k * n) (hd : ∀ x ∈ N, x ∈ K → x = 1) (hK : K ≤ K0)
    (hdec : ∀ x ∈ K0, ∃ n ∈ N, ∃ k ∈ K, x = n * k) :
    ∃ π : G → G, (∀ x ∈ K0, π x ∈ K ∧ ∃ n ∈ N, x = n * π x) ∧
      (∀ x ∈ K0, ∀ y ∈ K0, π (x * y) = π x * π y) ∧ (∀ k ∈ K, π k = k) := by
  classical
  have huniq : ∀ n n' k k' : G, n ∈ N → n' ∈ N → k ∈ K → k' ∈ K → n * k = n' * k' → k = k' := by
    intro n n' k k' hn hn' hk hk' h
    have h1 : n'⁻¹ * n = k' * k⁻¹ := by
      calc n'⁻¹ * n = n'⁻¹ * (n * k) * k⁻¹ := by group
        _ = n'⁻¹ * (n' * k') * k⁻¹ := by rw [h]
        _ = k' * k⁻¹ := by group
    have h2 : n'⁻¹ * n = 1 :=
      hd _ (N.mul_mem (N.inv_mem hn') hn) (h1 ▸ K.mul_mem hk' (K.inv_mem hk))
    have h3 : k' * k⁻¹ = 1 := by rw [← h1]; exact h2
    exact (mul_inv_eq_one.mp h3).symm
  have hex : ∀ x ∈ K0, ∃ k, k ∈ K ∧ ∃ n ∈ N, x = n * k := fun x hx => by
    obtain ⟨n, hn, k, hk, h⟩ := hdec x hx
    exact ⟨k, hk, n, hn, h⟩
  let π : G → G := fun x => if hx : x ∈ K0 then Classical.choose (hex x hx) else 1
  have hπ : ∀ x, x ∈ K0 → π x ∈ K ∧ ∃ n ∈ N, x = n * π x := by
    intro x hx
    have h := Classical.choose_spec (hex x hx)
    simp only [π, dif_pos hx]
    exact h
  refine ⟨π, hπ, ?_, ?_⟩
  · intro x hx y hy
    obtain ⟨hk, n, hn, hxe⟩ := hπ x hx
    obtain ⟨hk', n', hn', hye⟩ := hπ y hy
    obtain ⟨hk'', n'', hn'', hxye⟩ := hπ (x * y) (K0.mul_mem hx hy)
    have hxy : x * y = (n * n') * (π x * π y) := by
      calc x * y = (n * π x) * (n' * π y) := by rw [← hxe, ← hye]
        _ = n * (π x * n') * π y := by group
        _ = n * (n' * π x) * π y := by rw [← hc n' hn' (π x) hk]
        _ = (n * n') * (π x * π y) := by group
    exact huniq _ _ _ _ hn'' (N.mul_mem hn hn') hk'' (K.mul_mem hk hk') (hxye.symm.trans hxy)
  · intro k hk
    obtain ⟨hk', n, hn, hke⟩ := hπ k (hK hk)
    exact huniq n 1 (π k) k hn N.one_mem hk' hk (by rw [← hke, one_mul])

end CFSG.OddStandard.SmallF3.Omega
