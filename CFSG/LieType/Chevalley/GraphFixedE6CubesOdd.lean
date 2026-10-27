module

public import CFSG.LieType.Chevalley.GraphFixedE6DiagonalCubes

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {K : Type} [Field K]

theorem orbitField_E6_eq_top_of_card {q : ℕ} {σ : K ≃+* K} (hK : Nat.card K = q ^ 2)
    (hσ : ∀ c, σ c = c ^ q) {a : Fin TwistTag.E6.foldedTag.rank}
    (ha : (TwistTag.E6.orbit a).card = 2) : orbitField TwistTag.E6 K σ.toRingHom a = ⊤ := by
  have hq0 : q ≠ 0 := by
    rintro rfl
    have h := hσ 0
    rw [map_zero, pow_zero] at h
    exact zero_ne_one h
  have hfin : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ hq0)
  have : Fintype K := Fintype.ofFinite K
  refine eq_top_iff.2 fun c _ => (mem_orbitField).2 ?_
  rw [ha, pow_two, RingHom.coe_mul, Function.comp_apply]
  change σ (σ c) = c
  rw [hσ, hσ, ← pow_mul, ← sq, ← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]

theorem twisted_E6_odd_compatible_diagonal_cubes_inner
    {q : ℕ} (K : Type) [Field K]
    (hK : Nat.card K = q ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ q) :
    orbitField TwistTag.E6 K σ.toRingHom ⟨0, by decide⟩ = ⊤ ∧
    orbitField TwistTag.E6 K σ.toRingHom ⟨1, by decide⟩ = ⊤ ∧
    (∀ c, c ∈ orbitField TwistTag.E6 K σ.toRingHom ⟨2, by decide⟩ ↔ σ c = c) ∧
    (∀ c, c ∈ orbitField TwistTag.E6 K σ.toRingHom ⟨3, by decide⟩ ↔ σ c = c) ∧
    (∀ u, compatDiag TwistTag.E6 σ.toRingHom u =
      ![orbitFieldUnit TwistTag.E6 σ.toRingHom (u ⟨0, by decide⟩),
        orbitFieldUnit TwistTag.E6 σ.toRingHom (u ⟨3, by decide⟩),
        orbitFieldUnit TwistTag.E6 σ.toRingHom (u ⟨1, by decide⟩),
        orbitFieldUnit TwistTag.E6 σ.toRingHom (u ⟨2, by decide⟩),
        Units.map σ.toRingHom.toMonoidHom
          (orbitFieldUnit TwistTag.E6 σ.toRingHom (u ⟨1, by decide⟩)),
        Units.map σ.toRingHom.toMonoidHom
          (orbitFieldUnit TwistTag.E6 σ.toRingHom (u ⟨0, by decide⟩))]) ∧
    cubeMatrixE6 * TwistTag.E6.tag.cartan =
      3 • (1 : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ) ∧
    TwistTag.E6.tag.cartan * cubeMatrixE6 =
      3 • (1 : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ) ∧
    (∀ u i, cubeParam (compatDiag TwistTag.E6 σ.toRingHom u) (TwistTag.E6.perm i) =
      Units.map σ.toRingHom.toMonoidHom (cubeParam (compatDiag TwistTag.E6 σ.toRingHom u) i)) ∧
    (∀ u, rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u) ^ 3 =
      ((List.finRange TwistTag.E6.tag.rank).map fun i => torusElt TwistTag.E6.tag K i
        (cubeParam (compatDiag TwistTag.E6 σ.toRingHom u) i)).prod) ∧
    (∀ u, ∃ s : (a : Fin TwistTag.E6.foldedTag.rank) → (orbitField TwistTag.E6 K σ.toRingHom a)ˣ,
      (∀ a, orbitFieldUnit TwistTag.E6 σ.toRingHom (s a) =
        cubeParam (compatDiag TwistTag.E6 σ.toRingHom u) (TwistTag.E6.orbitMin a)) ∧
      rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u) ^ 3 =
        ((List.finRange TwistTag.E6.foldedTag.rank).map fun a =>
          (orbitH TwistTag.E6 K σ.toRingHom a (s a) : ModGL TwistTag.E6.tag K)).prod) ∧
    (∀ u, rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u) ^ 3 ∈
      graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ∧
    ∀ u, ∃ c : graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
      compatDiagAutHom TwistTag.E6 K σ.toRingHom u ^ 3 = MulAut.conj c := by
  have hcube : ∀ u, ∃ s : (a : Fin TwistTag.E6.foldedTag.rank) →
      (orbitField TwistTag.E6 K σ.toRingHom a)ˣ,
      (∀ a, orbitFieldUnit TwistTag.E6 σ.toRingHom (s a) =
        cubeParam (compatDiag TwistTag.E6 σ.toRingHom u) (TwistTag.E6.orbitMin a)) ∧
      rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u) ^ 3 =
        ((List.finRange TwistTag.E6.foldedTag.rank).map fun a =>
          (orbitH TwistTag.E6 K σ.toRingHom a (s a) : ModGL TwistTag.E6.tag K)).prod := by
    intro u
    obtain ⟨s, hs⟩ := exists_compatDiag_eq (cubeParam_perm (compatDiag_perm u))
    refine ⟨s, fun a => ?_, ?_⟩
    · rw [← compatDiag_orbitMin, hs]
    · rw [list_prod_orbitH, hs, rootDiagUnit_pow_three]
  have hmem : ∀ u, rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u) ^ 3 ∈
      graphFixedRootGroup TwistTag.E6 K σ.toRingHom := fun u => by
    obtain ⟨s, -, hs⟩ := hcube u
    rw [hs]
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
    exact orbitH_mem_graphFixedRootGroup TwistTag.E6 σ.toRingHom a (s a)
  exact ⟨orbitField_E6_eq_top_of_card hK hσ (by decide),
    orbitField_E6_eq_top_of_card hK hσ (by decide),
    fun c => mem_orbitField_iff_of_card_eq_one (by decide),
    fun c => mem_orbitField_iff_of_card_eq_one (by decide), compatDiag_E6,
    cubeMatrixE6_mul_cartan, cartan_mul_cubeMatrixE6, fun u => cubeParam_perm (compatDiag_perm u),
    fun u => rootDiagUnit_pow_three _, hcube, hmem,
    fun u => ⟨_, compatDiagAutHom_pow_eq_conj u 3 (hmem u)⟩⟩

end CFSG.LieType.Chevalley
