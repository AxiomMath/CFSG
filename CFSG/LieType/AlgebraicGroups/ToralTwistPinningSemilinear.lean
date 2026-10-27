module

public import CFSG.LieType.AlgebraicGroups.ToralTwistPinningGeneral
public import CFSG.LieType.Chevalley.RationalToralSignDiagram

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Chevalley.ToralSign

section Words

variable {τ : Tag} {k : Type} [Field k]

variable (τ k) in
@[expose] def wordWeylMatrix
    (l : List (Fin τ.rank)) : ModGL τ k :=
  (l.reverse.map fun i => weylElt τ k i 1).prod

theorem wordWeylMatrix_conj_pinnedX
    (l : List (Fin τ.rank)) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) :
    ∃ ε : k, ε * ε = 1 ∧ ∀ c : k, wordWeylMatrix τ k l * pinnedX τ k γ c *
      (wordWeylMatrix τ k l)⁻¹ = pinnedX τ k (ToralSign.wordElt τ l • γ) (ε * c) :=
  exists_prod_weylElt_mul_pinnedX_mul_inv k l.reverse hγ

theorem wordWeylMatrix_mem_normalizer
    (l : List (Fin τ.rank)) :
    wordWeylMatrix τ k l ∈ Subgroup.normalizer (torusGroup τ k : Set (ModGL τ k)) := by
  refine Subgroup.list_prod_mem _ fun g hg => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
  rw [← canonicalRep_simple (coxeterSystem τ) k i]
  exact canonicalRep_mem_normalizer _

theorem map_conj_diagramMap_torusGroup
    (t : TwistTag) :
    (torusGroup t.tag k).map (MulAut.conj (diagramMap t k)).toMonoidHom = torusGroup t.tag k := by
  have hid : ∀ u : kˣ, Units.map (RingHom.id k).toMonoidHom u = u := fun u => Units.ext rfl
  rw [torusGroup, MonoidHom.map_closure, conj_diagramMap_eq_twistHom]
  congr 1
  ext g
  constructor
  · rintro ⟨_, ⟨⟨i, u⟩, rfl⟩, rfl⟩
    exact ⟨⟨t.perm i, u⟩, by rw [twistHom_torusElt, hid]⟩
  · rintro ⟨⟨i, u⟩, rfl⟩
    refine ⟨torusElt t.tag k (t.perm.symm i) u, ⟨⟨t.perm.symm i, u⟩, rfl⟩, ?_⟩
    rw [twistHom_torusElt, Equiv.apply_symm_apply, hid]

theorem diagramMap_mem_normalizer
    (t : TwistTag) :
    diagramMap t k ∈ Subgroup.normalizer (torusGroup t.tag k : Set (ModGL t.tag k)) := by
  rw [Subgroup.mem_normalizer_iff_conj_image_eq]
  have h := congrArg SetLike.coe (map_conj_diagramMap_torusGroup (k := k) t)
  rw [Subgroup.coe_map] at h
  exact h

end Words

section Theta

variable {τ : Tag}

theorem thetaMap_neg
    (ω : WeylGroup τ) (ρ : Equiv.Perm (Fin τ.rank)) (v : Fin τ.rank → ℤ) :
    thetaMap ω ρ (-v) = -thetaMap ω ρ v := by
  rw [thetaMap, thetaMap, permLattice_neg, smul_neg]

theorem simpleUnion_eq_unionSimpleRoots (χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ) :
    simpleUnion χ = unionSimpleRoots χ Set.univ := by
  ext β
  simp [simpleUnion, unionSimpleRoots]

end Theta

section Conj

variable {k : Type} [Field k]

theorem wordWeylMatrix_mul_diagramMap_conj_pinnedX
    (t : TwistTag) (l : List (Fin t.tag.rank))
    {γ : Fin t.tag.rank → ℤ} (hγ : IsRoot t.tag γ) :
    ∃ μ : kˣ, ∀ c : k, (wordWeylMatrix t.tag k l * diagramMap t k) * pinnedX t.tag k γ c *
      (wordWeylMatrix t.tag k l * diagramMap t k)⁻¹ =
        pinnedX t.tag k (thetaMap (ToralSign.wordElt t.tag l) t.perm γ) (μ * c) := by
  obtain ⟨ε, hε, hD⟩ := diagramMap_conj_pinnedX (K := k) t hγ
  obtain ⟨ε', hε', hN⟩ := wordWeylMatrix_conj_pinnedX (k := k) l (hγ.permLattice t.cartan_perm)
  refine ⟨Units.mkOfMulEqOne (ε' * ε) (ε' * ε) (by linear_combination (ε' * ε') * hε + hε'),
    fun c => ?_⟩
  calc (wordWeylMatrix t.tag k l * diagramMap t k) * pinnedX t.tag k γ c *
        (wordWeylMatrix t.tag k l * diagramMap t k)⁻¹ =
      wordWeylMatrix t.tag k l * (diagramMap t k * pinnedX t.tag k γ c * (diagramMap t k)⁻¹) *
        (wordWeylMatrix t.tag k l)⁻¹ := by group
    _ = _ := by rw [hD, hN, Units.val_mkOfMulEqOne, mul_assoc]; rfl

theorem wordWeylMatrix_mul_one_conj_pinnedX
    {τ : Tag} (l : List (Fin τ.rank))
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    ∃ μ : kˣ, ∀ c : k, (wordWeylMatrix τ k l * 1) * pinnedX τ k γ c *
      (wordWeylMatrix τ k l * 1)⁻¹ =
        pinnedX τ k (thetaMap (ToralSign.wordElt τ l) 1 γ) (μ * c) := by
  obtain ⟨ε', hε', hN⟩ := wordWeylMatrix_conj_pinnedX (k := k) l hγ
  refine ⟨Units.mkOfMulEqOne ε' ε' hε', fun c => ?_⟩
  rw [mul_one, hN, Units.val_mkOfMulEqOne]
  rfl

end Conj

section Main

variable (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p]

theorem isTwistPinningNormalization_of_thetaProperties
    (hp : p ≠ 2) {e : ℕ} (he : 1 ≤ e)
    {τ : Tag} {ρ : Equiv.Perm (Fin τ.rank)} {r : ℕ} {χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ}
    {l : List (Fin τ.rank)} {D : ModGL τ k}
    (hρ : ∀ i j, τ.cartan (ρ i) (ρ j) = τ.cartan i j)
    (hD : ∀ γ, IsRoot τ γ → ∃ μ : kˣ, ∀ c : k, (wordWeylMatrix τ k l * D) * pinnedX τ k γ c *
      (wordWeylMatrix τ k l * D)⁻¹ = pinnedX τ k (thetaMap (ToralSign.wordElt τ l) ρ γ) (μ * c))
    (hDT : D ∈ Subgroup.normalizer (torusGroup τ k : Set (ModGL τ k)))
    (hθ : ThetaProperties ρ r χ (ToralSign.wordElt τ l)) :
    IsTwistPinningNormalization τ k p e χ (thetaMap (ToralSign.wordElt τ l) ρ)
      (wordWeylMatrix τ k l * D) :=
  isTwistPinningNormalization_of_conj p hp he χ hD
    (mul_mem (wordWeylMatrix_mem_normalizer l) hDT) (fun _ hγ => isRoot_thetaMap hρ hγ)
    (thetaMap_neg _ ρ) thetaMap_injective hθ.image_kernelRoots
    (by rw [← simpleUnion_eq_unionSimpleRoots]; exact hθ.image_simpleUnion)

variable (k) in
theorem rational_toral_twist_semilinear_pinning_normalization
    (hp : p ≠ 2) (e : ℕ) (he : 1 ≤ e) :
    (∀ m ∈ e7SignDiagramReps, ∀ l ∈ m.omegaWords,
      IsTwistPinningNormalization .E7 k p e (signMaskChar .E7 m.mask)
        (thetaMap (ToralSign.wordElt .E7 l) 1) (wordWeylMatrix .E7 k l * 1)) ∧
    (∀ m ∈ e6SignDiagramReps, ∀ l ∈ m.omegaWords,
      IsTwistPinningNormalization TwistTag.E6.tag k p e (signMaskChar TwistTag.E6.tag m.mask)
        (thetaMap (ToralSign.wordElt TwistTag.E6.tag l) TwistTag.E6.perm)
        (wordWeylMatrix TwistTag.E6.tag k l * diagramMap TwistTag.E6 k)) ∧
    (∀ m ∈ d4SignDiagramReps, ∀ l ∈ m.omegaWords,
      IsTwistPinningNormalization TwistTag.D4.tag k p e (signMaskChar TwistTag.D4.tag m.mask)
        (thetaMap (ToralSign.wordElt TwistTag.D4.tag l) TwistTag.D4.perm)
        (wordWeylMatrix TwistTag.D4.tag k l * diagramMap TwistTag.D4 k)) := by
  obtain ⟨h7, h6, h4⟩ := rational_toral_sign_diagram_arithmetic
  refine ⟨fun m hm l hl => ?_, fun m hm l hl => ?_, fun m hm l hl => ?_⟩
  · exact isTwistPinningNormalization_of_thetaProperties p hp he (fun _ _ => rfl)
      (fun _ hγ => wordWeylMatrix_mul_one_conj_pinnedX l hγ) (one_mem _) (h7.theta m hm l hl)
  · exact isTwistPinningNormalization_of_thetaProperties p hp he TwistTag.E6.cartan_perm
      (fun _ hγ => wordWeylMatrix_mul_diagramMap_conj_pinnedX TwistTag.E6 l hγ)
      (diagramMap_mem_normalizer TwistTag.E6) (h6.theta m hm l hl)
  · exact isTwistPinningNormalization_of_thetaProperties p hp he TwistTag.D4.cartan_perm
      (fun _ hγ => wordWeylMatrix_mul_diagramMap_conj_pinnedX TwistTag.D4 l hγ)
      (diagramMap_mem_normalizer TwistTag.D4) (h4.theta m hm l hl)

end Main

end CFSG.LieType.AlgebraicGroups
