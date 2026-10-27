module

public import CFSG.Certificates.Kernel.SporCov.BaseKit
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.KD.SporCov.PermKit

open CFSG.KC.SporCov CFSG.KD.SporCov CFSG.Sporadic.Th Equiv

variable {n : ℕ} {K : Subgroup (Perm (Fin n))}

theorem idx_coe (g : K) {x : ℕ} (hx : x < n) : idx n g x = ((g : Perm (Fin n)) ⟨x, hx⟩).val :=
  idx_of_lt g hx

theorem range_lt : ∀ x ∈ List.range n, x < n := fun _ hx => List.mem_range.1 hx

theorem sep (g : K) (h : ∀ x ∈ List.range n, idx n g x = x) : g = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  have e := h x.val (List.mem_range.2 x.isLt)
  rw [idx_coe g x.isLt] at e
  exact Fin.ext e

theorem model {a b : K} {fA fAi fB fBi : ℕ → ℕ} (hA : ∀ x < n, fA x = idx n a x)
    (hAi : ∀ x < n, fAi x = idx n a⁻¹ x) (hB : ∀ x < n, fB x = idx n b x)
    (hBi : ∀ x < n, fBi x = idx n b⁻¹ x) :
    Model letP (eqB fA fAi fB fBi (List.range n)) (wE (fP a b)) ∧
      ∀ u, chW letP u = true → wE (fP a b) u = 1 →
        eqB fA fAi fB fBi (List.range n) u [] = true :=
  eqB_model hA hAi hB hBi range_lt sep

variable {a b : Perm (Fin n)} (hK : K = Subgroup.closure {a, b})
include hK

theorem a_mem : a ∈ K := by
  rw [hK]
  exact Subgroup.subset_closure (by simp)

theorem b_mem : b ∈ K := by
  rw [hK]
  exact Subgroup.subset_closure (by simp)

theorem closure_seeds :
    Subgroup.closure ({⟨a, a_mem hK⟩, ⟨b, b_mem hK⟩} : Set K) = ⊤ := by
  apply Subgroup.map_injective K.subtype_injective
  have hset : K.subtype '' ({⟨a, a_mem hK⟩, ⟨b, b_mem hK⟩} : Set K) = {a, b} :=
    Set.image_pair _ _ _
  rw [MonoidHom.map_closure, Subgroup.map_top, Subgroup.range_subtype, hset, hK]

theorem top_of_seeds {R : List (List ℕ)} (e0 : nthW R 0 = [0]) (e1 : nthW R 1 = [2])
    {T : Subgroup K} (h : ∀ k, wE (fP ⟨a, a_mem hK⟩ ⟨b, b_mem hK⟩) (nthW R k) ∈ T) : T = ⊤ := by
  have h0 := h 0
  have h1 := h 1
  rw [e0, wE_cons, wE_nil, one_mul, fP_zero] at h0
  rw [e1, wE_cons, wE_nil, one_mul, fP_two] at h1
  rw [eq_top_iff, ← closure_seeds hK, Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact h0
  · exact h1

end CFSG.KD.SporCov.PermKit

end
