module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Rank

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G]

theorem map_conj_centralizer_singleton (a g : G) :
    (centralizer ({a} : Set G)).map (MulAut.conj g⁻¹).toMonoidHom =
      centralizer ({g⁻¹ * a * g} : Set G) := by
  ext w
  rw [mem_map_equiv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  simp only [inv_inv, MulAut.conj_symm_apply]
  constructor
  · intro hw
    calc w * (g⁻¹ * a * g) = g⁻¹ * ((g * w * g⁻¹) * a) * g := by group
      _ = g⁻¹ * (a * (g * w * g⁻¹)) * g := by rw [hw]
      _ = g⁻¹ * a * g * w := by group
  · intro hw
    calc g * w * g⁻¹ * a = g * (w * (g⁻¹ * a * g)) * g⁻¹ := by group
      _ = g * (g⁻¹ * a * g * w) * g⁻¹ := by rw [hw]
      _ = a * (g * w * g⁻¹) := by group

theorem gsUnbalancingTriple_conjugate {a x : G} {J : Subgroup G}
    (hU : GSUnbalancingTriple a x J) (g : G) :
    GSUnbalancingTriple (g⁻¹ * a * g) (g⁻¹ * x * g) (conjugate J g) := by
  obtain ⟨ha, hx, hax, hJa, hJ, hJx, hJF⟩ := gsUnbalancingTriple_iff.mp hU
  set f := (MulAut.conj g⁻¹).toMonoidHom with hf
  have hfy : ∀ y : G, f y = g⁻¹ * y * g := fun y => by
    rw [hf, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have hfinj : Function.Injective f := (MulAut.conj g⁻¹).injective
  have hCaf : (centralizer ({a} : Set G)).map f = centralizer ({g⁻¹ * a * g} : Set G) :=
    map_conj_centralizer_singleton a g
  have hOf : ((pPrimeCore 2 (centralizer ({x} : Set G))).map
      (centralizer ({x} : Set G)).subtype).map f =
      (pPrimeCore 2 (centralizer ({g⁻¹ * x * g} : Set G))).map
        (centralizer ({g⁻¹ * x * g} : Set G)).subtype := by
    rw [← hfy x]
    exact map_pPrimeCore_centralizer_of_mulAut (MulAut.conj g⁻¹) x
  obtain ⟨hJg, hJgp⟩ := GSThmB.Six.isPComponent_conjugate hJa hJ g
  have hCg : conjugate (centralizer ({a} : Set G)) g = centralizer ({g⁻¹ * a * g} : Set G) :=
    hCaf
  rw [hCg] at hJg hJgp
  refine gsUnbalancingTriple_iff.mpr ⟨?_, ?_, ?_, hJg, hJgp, ?_, ?_⟩
  · rw [← hfy a, hf, MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq, ha]
  · rw [← hfy x, hf, MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq, hx]
  · rw [← hfy a, ← hfy x, ← map_mul, ← map_mul, hax]
  · have h1 := congrArg (Subgroup.map f) hJx
    rw [map_commutator, MonoidHom.map_zpowers, hfy x] at h1
    exact h1
  · have h1 := congrArg (Subgroup.map f) hJF
    rw [map_commutator, Subgroup.map_inf _ _ _ hfinj, hOf, hCaf] at h1
    exact h1

variable [Finite G]

theorem exists_unbalancing_commute_of_sylow {a x t : G} {J S : Subgroup G}
    (hT : GSUnbalancingTriple a x J) (hSyl : IsSylowTwoIn S (normalizer (J : Set G)))
    (hcent : ∀ s ∈ S, s * a = a * s) (ht : orderOf t = 2)
    (hJt : J ≤ centralizer ({t} : Set G)) :
    ∃ a' x' : G, GSUnbalancingTriple a' x' J ∧ a' * t = t * a' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htN : t ∈ normalizer (J : Set G) :=
    mem_normalizer_of_commute fun j hj => (mem_centralizer_singleton_iff.mp (hJt hj)).symm
  have ht2 : IsPGroup 2 (zpowers t) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, ht, pow_one])
  obtain ⟨n, hnN, hn⟩ := exists_conjugate_le_of_isSylowTwoIn hSyl (zpowers_le.mpr htN) ht2
  have htn : n⁻¹ * t * n ∈ S := hn ⟨t, mem_zpowers t, by
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩
  have hcomm := hcent _ htn
  have hT' := gsUnbalancingTriple_conjugate hT n⁻¹
  rw [inv_inv, conjugate_eq_of_mem_normalizer (inv_mem hnN)] at hT'
  refine ⟨n * a * n⁻¹, n * x * n⁻¹, hT', ?_⟩
  calc n * a * n⁻¹ * t = n * (a * (n⁻¹ * t * n)) * n⁻¹ := by group
    _ = n * ((n⁻¹ * t * n) * a) * n⁻¹ := by rw [hcomm]
    _ = t * (n * a * n⁻¹) := by group

end CFSG.ComponentClassification.GrSLit.GrS5
