module

public import CFSG.Goldschmidt75.TheoremBa

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt Subgroup
open scoped Pointwise commutatorElement

universe u

variable {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem theoremB_b (P : Sylow p G) {S : Subgroup G} (hSP : S ≤ P)
    (hS : fusionStronglyClosed (S : Set G) P) :
    (commutator G ⊓ P) ⊔ S =
      (⁅normalizer (S : Set G), normalizer (S : Set G)⁆ ⊓ P) ⊔ S := by
  set N := normalizer (S : Set G)
  refine le_antisymm ?_ (sup_le_sup_right (inf_le_inf_right _
    (Subgroup.commutator_mono le_top le_top)) _)
  refine sup_le ?_ le_sup_right
  rw [Subgroup.commutator_inf_eq_focalSubgroup P, Subgroup.focalSubgroup_def, closure_le]
  rintro _ ⟨hcP, x, hx, u, rfl⟩
  have hy : u * x * u⁻¹ ∈ (P : Subgroup G) := by
    have h1 : x⁻¹ * ⁅x, u⁆ ∈ (P : Subgroup G) := P.mul_mem (P.inv_mem hx) hcP
    have h2 : (x⁻¹ * ⁅x, u⁆)⁻¹ = u * x * u⁻¹ := by
      rw [commutatorElement_def]; group
    rw [← h2]
    exact P.inv_mem h1
  have hUx : ({x} : Set G) ⊆ P := Set.singleton_subset_iff.mpr hx
  have hconj : rconj u⁻¹ {x} = {u * x * u⁻¹} := by
    ext z
    simp only [mem_rconj, inv_inv, Set.mem_singleton_iff]
    constructor
    · intro h; rw [← h]; group
    · intro h; rw [h]; group
  obtain ⟨n, hn, heq⟩ := baFor p G P S hSP hS {x} hUx u⁻¹
    (by rw [hconj]; exact Set.singleton_subset_iff.mpr hy)
  rw [hconj] at heq
  have hmem : n⁻¹ * x * n ∈ (S : Set G) * {u * x * u⁻¹} := by
    rw [← heq]
    exact conj_mem_rconj ⟨1, S.one_mem, x, rfl, one_mul x⟩
  obtain ⟨s, hs, _, rfl, hseq⟩ := hmem
  have hxN : x ∈ N := sylow_le_normalizer P hSP hS hx
  have hcomm : ⁅x, n⁻¹⁆ ∈ ⁅N, N⁆ := commutator_mem_commutator hxN (N.inv_mem hn)
  have hcommP : ⁅x, n⁻¹⁆ ∈ (P : Subgroup G) := by
    have h1 : n⁻¹ * x * n ∈ (P : Subgroup G) := by
      rw [← hseq]; exact P.mul_mem (hSP hs) hy
    have h2 : ⁅x, n⁻¹⁆ = x * (n⁻¹ * x * n)⁻¹ := by
      rw [commutatorElement_def]; group
    rw [h2]
    exact P.mul_mem hx (P.inv_mem h1)
  have hgen : ⁅x, u⁆ = ⁅x, n⁻¹⁆ * s := by
    have hs' : s = n⁻¹ * x * n * (u * x * u⁻¹)⁻¹ := by
      rw [← hseq]; group
    rw [hs', commutatorElement_def, commutatorElement_def]
    group
  rw [SetLike.mem_coe, hgen]
  exact Subgroup.mul_mem _ (mem_sup_left ⟨hcomm, hcommP⟩) (mem_sup_right hs)

end CFSG.Goldschmidt75
