module

public import CFSG.Holt.Basic

public section

namespace CFSG.Holt

open MulAction CFSG.Open

variable {X : Type*} [Group X] {Ω : Type*} [MulAction X Ω]

variable [Finite X] [Finite Ω] {z : X}

theorem fusionStronglyEmbedded_stabilizer_of_forall_existsUnique {G : Type*} [Group G]
    [Finite G] {Δ : Type*} [MulAction G Δ] [IsPretransitive G Δ] [Nontrivial Δ]
    (heven : Even (Nat.card G)) (hinv : ∀ g : G, orderOf g = 2 → ∃! δ : Δ, g • δ = δ)
    (δ : Δ) : fusionStronglyEmbedded (stabilizer G δ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨fun htop => ?_, ?_, fun g hg => ?_⟩
  · obtain ⟨δ', hδ'⟩ := exists_ne δ
    obtain ⟨g, hg⟩ := exists_smul_eq G δ δ'
    have hgδ : g • δ = δ := mem_stabilizer_iff.mp (htop ▸ Subgroup.mem_top g)
    exact hδ' (hg.symm.trans hgδ)
  · obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp heven)
    obtain ⟨δ₀, hδ₀, -⟩ := hinv t ht
    obtain ⟨g, rfl⟩ := exists_smul_eq G δ₀ δ
    have hmem : g * t * g⁻¹ ∈ stabilizer G (g • δ₀) := by
      rw [mem_stabilizer_iff, mul_smul, mul_smul, inv_smul_smul, hδ₀]
    have hord : orderOf (⟨g * t * g⁻¹, hmem⟩ : stabilizer G (g • δ₀)) = 2 := by
      rw [Subgroup.orderOf_mk, ← orderOf_eq_of_isConj (isConj_iff.mpr ⟨g, rfl⟩), ht]
    exact even_iff_two_dvd.mpr (hord ▸ orderOf_dvd_natCard _)
  · rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
    intro h2
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hx1 : (x : G) • δ = δ := x.2.1
    have hx2 : (x : G) ∈ (stabilizer G δ).map (MulAut.conj g⁻¹).toMonoidHom := x.2.2
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, inv_inv, mem_stabilizer_iff, mul_smul,
      mul_smul, ← eq_inv_smul_iff] at hx2
    obtain ⟨δ₀, -, huniq⟩ := hinv x (by rw [Subgroup.orderOf_coe, hx])
    exact hg (mem_stabilizer_iff.mpr
      (inv_smul_eq_iff.mp ((huniq _ hx2).trans (huniq _ hx1).symm)).symm)

variable [IsPretransitive X Ω]

end CFSG.Holt
