module

public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.Transfer

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Subgroup

theorem mem_commutator_of_mem_center_of_perfect {L : Type*} [Group L]
    (hperf : commutator L = ⊤) {S : Subgroup L} [S.FiniteIndex] {z : L}
    (hz : z ∈ center L) (hzS : z ∈ S) (hcop : Nat.Coprime S.index (orderOf z)) :
    (⟨z, hzS⟩ : S) ∈ commutator S := by
  classical
  have key : ∀ (k : ℕ) (g₀ : L), g₀⁻¹ * z ^ k * g₀ ∈ S → g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    have hk : z ^ k ∈ center L := pow_mem hz k
    rw [mul_assoc, ← mem_center_iff.mp hk g₀, ← mul_assoc, inv_mul_cancel, one_mul]
  let ϕ : S →* Abelianization S := Abelianization.of
  have h1 := MonoidHom.transfer_eq_pow ϕ z key
  have h2 : (MonoidHom.transfer ϕ) z = 1 :=
    Abelianization.commutator_subset_ker (MonoidHom.transfer ϕ) (hperf ▸ mem_top z)
  rw [h2] at h1
  have h3 : (⟨z ^ S.index, S.pow_mem hzS _⟩ : S) ∈ commutator S :=
    by rw [← Abelianization.ker_of S, MonoidHom.mem_ker]; exact h1.symm
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  have : (⟨z, hzS⟩ : S) = (⟨z ^ S.index, S.pow_mem hzS _⟩ : S) ^ m :=
    Subtype.ext (by simpa using hm.symm)
  rw [this]
  exact pow_mem h3 m

end CFSG.LocalAnalysis.RankThreeTheoremC
