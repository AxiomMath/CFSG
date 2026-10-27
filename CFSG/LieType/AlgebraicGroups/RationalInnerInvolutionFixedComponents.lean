module

public import CFSG.LieType.AlgebraicGroups.ToralTwistSemilinearDatum
public import CFSG.LieType.AlgebraicGroups.RationalInnerInvolutionReduction

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ToralSign
  CFSG.LocalAnalysis.ComponentInitial

section Twists

variable {τ : Tag} {k : Type} [Field k]

theorem wordWeylMatrix_mem_adjointGroup
    (l : List (Fin τ.rank)) :
    wordWeylMatrix τ k l ∈ adjointGroup τ k :=
  Subgroup.list_prod_mem _ fun g hg => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
    exact weylElt_mem_adjointGroup i 1

theorem map_conj_wordWeylMatrix_mul
    (l : List (Fin τ.rank)) {D : ModGL τ k}
    (hD : (adjointGroup τ k).map (MulAut.conj D).toMonoidHom = adjointGroup τ k) :
    (adjointGroup τ k).map (MulAut.conj (wordWeylMatrix τ k l * D)).toMonoidHom =
      adjointGroup τ k := by
  have e1 : (MulAut.conj (wordWeylMatrix τ k l * D)).toMonoidHom =
      (MulAut.conj (wordWeylMatrix τ k l)).toMonoidHom.comp (MulAut.conj D).toMonoidHom := by
    ext y
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MonoidHom.comp_apply, mul_inv_rev]
    group
  rw [e1, ← Subgroup.map_map, hD]
  exact map_conj_eq_of_mem_normalizer
    (Subgroup.le_normalizer (wordWeylMatrix_mem_adjointGroup l))

theorem symmetrizedCartan_perm_E6 (i j : Fin TwistTag.E6.tag.rank) :
    TwistTag.E6.tag.symmetrizedCartan (TwistTag.E6.perm i) (TwistTag.E6.perm j) =
      TwistTag.E6.tag.symmetrizedCartan i j := by
  have h1 : TwistTag.E6.tag.symmetrizedCartan = TwistTag.E6.tag.cartan := by
    change Tag.E6.symmetrizer * Tag.E6.cartan = Tag.E6.cartan
    rw [show Tag.E6.symmetrizer = 1 from rfl, one_mul]
  rw [h1]
  exact TwistTag.cartan_perm _ i j

theorem symmetrizedCartan_perm_D4 (i j : Fin TwistTag.D4.tag.rank) :
    TwistTag.D4.tag.symmetrizedCartan (TwistTag.D4.perm i) (TwistTag.D4.perm j) =
      TwistTag.D4.tag.symmetrizedCartan i j := by
  have h1 : TwistTag.D4.tag.symmetrizedCartan = TwistTag.D4.tag.cartan := by
    change Tag.D4.symmetrizer * Tag.D4.cartan = Tag.D4.cartan
    rw [show Tag.D4.symmetrizer = 1 from rfl, one_mul]
  rw [h1]
  exact TwistTag.cartan_perm _ i j

end Twists

variable (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p]

theorem isQuasisimple_of_isFiniteToralTwistReduction
    (hp : p ≠ 2)
    (hk : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k) {e : ℕ} (he : 1 ≤ e)
    {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7) {ρ : Equiv.Perm (Fin τ.rank)}
    (hA : ∀ i j, τ.cartan (ρ i) (ρ j) = τ.cartan i j)
    (hB : ∀ i j, τ.symmetrizedCartan (ρ i) (ρ j) = τ.symmetrizedCartan i j) {r₀ : ℕ}
    {reps : List (SignRep τ)}
    (htheta : ∀ m ∈ reps, ∀ l ∈ m.omegaWords,
      ThetaProperties ρ r₀ (signMaskChar τ m.mask) (ToralSign.wordElt τ l))
    {D : ModGL τ k}
    (hDX : ∀ (l : List (Fin τ.rank)) (γ : Fin τ.rank → ℤ), IsRoot τ γ → ∃ μ : kˣ, ∀ c : k,
      (wordWeylMatrix τ k l * D) * pinnedX τ k γ c * (wordWeylMatrix τ k l * D)⁻¹ =
        pinnedX τ k (thetaMap (ToralSign.wordElt τ l) ρ γ) (μ * c))
    (hDT : D ∈ Subgroup.normalizer (torusGroup τ k : Set (ModGL τ k)))
    (hDG : (adjointGroup τ k).map (MulAut.conj D).toMonoidHom = adjointGroup τ k)
    (hpin : ∀ m ∈ reps, ∀ l ∈ m.omegaWords,
      IsTwistPinningNormalization τ k p e (signMaskChar τ m.mask)
        (thetaMap (ToralSign.wordElt τ l) ρ) (wordWeylMatrix τ k l * D))
    {x : ModGL τ k} (hred : IsFiniteToralTwistReduction τ k p e D reps x) (ℓ : ℕ)
    (hℓ : ℓ.Prime) (L : Subgroup (ModGL τ k))
    (hL : L ≤ ⁅fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D),
      fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D)⁆ ⊓ Subgroup.centralizer {x})
    (hLc : CFSG.IsPComponent ℓ (L.subgroupOf (⁅fixedPointsIn (adjointGroup τ k)
      (frobTwistGL τ k p e D), fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D)⁆ ⊓
        Subgroup.centralizer {x}))) :
    CFSG.IsQuasisimple L := by
  obtain ⟨r, hr, l, hl, -, hQfin, g₁, -, hcomp⟩ := hred
  obtain ⟨hL₁, hL₁c⟩ := ((hcomp ℓ hℓ).1 L).1 ⟨hL, hLc⟩
  have hqQ : ∀ J : Subgroup (fixedPointsIn
      (torusGroup τ k ⊔ rootSpan τ k (kernelRoots (signMaskChar τ r.mask)))
      (frobTwistGL τ k p e (wordWeylMatrix τ k l * D))),
      CFSG.IsPComponent ℓ J → CFSG.IsQuasisimple J := by
    intro J hJ
    rcases (kernelRoots (signMaskChar τ r.mask)).eq_empty_or_nonempty with hK | hK
    · exact absurd hJ (not_isPComponent_of_kernelRoots_eq_empty hK inf_le_left J)
    · obtain ⟨Dd, -, ⟨eqv⟩⟩ := exists_datum_mulEquiv p hp hk he hτ hA hB (htheta r hr l hl)
        (hDX l) (mul_mem (wordWeylMatrix_mem_normalizer l) hDT) (map_conj_wordWeylMatrix_mul l hDG)
        (hpin r hr l hl) hK
      have : Finite Dd.totalFixedGroup := Finite.of_equiv _ eqv.symm.toEquiv
      exact OddToralFixed.pComponent_quasisimple_of_mulEquiv eqv.symm
        (orthogonal_semilinear_total_fixed_p_components Dd this ℓ hℓ) J hJ
  have hq' : CFSG.IsQuasisimple (L.map (MulAut.conj g₁).toMonoidHom) :=
    (isQuasisimple_congr (Subgroup.subgroupOfEquivOfLe hL₁)).1 (hqQ _ hL₁c)
  exact (isQuasisimple_congr (L.equivMapOfInjective _ (MulAut.conj g₁).injective)).2 hq'

variable (k) in
@[expose] def InvolutionCentralizerPComponentsQuasisimple (τ : Tag) (e : ℕ) (D : ModGL τ k) :
    Prop :=
  ∀ x ∈ fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D), x ^ 2 = 1 →
    ∀ ℓ : ℕ, ℓ.Prime → ∀ L : Subgroup (ModGL τ k),
      L ≤ ⁅fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D),
        fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D)⁆ ⊓ Subgroup.centralizer {x} →
      CFSG.IsPComponent ℓ (L.subgroupOf (⁅fixedPointsIn (adjointGroup τ k)
        (frobTwistGL τ k p e D), fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D)⁆ ⊓
          Subgroup.centralizer {x})) →
      CFSG.IsQuasisimple L

variable (k) in
theorem e7_twisted_e6_triality_rational_inner_involution_fixed_p_components
    (hp : p ≠ 2)
    (hk : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k) (e : ℕ) (he : 1 ≤ e) :
    InvolutionCentralizerPComponentsQuasisimple p k .E7 e 1 ∧
    InvolutionCentralizerPComponentsQuasisimple p k TwistTag.E6.tag e
      (diagramMap TwistTag.E6 k) ∧
    InvolutionCentralizerPComponentsQuasisimple p k TwistTag.D4.tag e
      (diagramMap TwistTag.D4 k) := by
  obtain ⟨h7, h6, h4⟩ := rational_toral_sign_diagram_arithmetic
  obtain ⟨r7, r6, r4⟩ := rational_inner_involution_finite_toral_twist_reduction p k hp e he
  obtain ⟨n7, n6, n4⟩ := rational_toral_twist_semilinear_pinning_normalization p k hp e he
  refine ⟨fun x hx hx2 ℓ hℓ L hL hLc => ?_, fun x hx hx2 ℓ hℓ L hL hLc => ?_,
    fun x hx hx2 ℓ hℓ L hL hLc => ?_⟩
  · exact isQuasisimple_of_isFiniteToralTwistReduction p hp hk he (Or.inr (Or.inr rfl))
      (ρ := 1) (fun _ _ => rfl) (fun _ _ => rfl) h7.theta
      (fun l _ hγ => wordWeylMatrix_mul_one_conj_pinnedX l hγ) (one_mem _)
      (map_conj_one_adjointGroup _ k) n7 (r7 x hx hx2) ℓ hℓ L hL hLc
  · exact isQuasisimple_of_isFiniteToralTwistReduction p hp hk he (Or.inr (Or.inl rfl))
      TwistTag.E6.cartan_perm symmetrizedCartan_perm_E6 h6.theta
      (fun l _ hγ => wordWeylMatrix_mul_diagramMap_conj_pinnedX TwistTag.E6 l hγ)
      (diagramMap_mem_normalizer TwistTag.E6) (map_conj_diagramMap TwistTag.E6 k (Or.inl rfl))
      n6 (r6 x hx hx2) ℓ hℓ L hL hLc
  · exact isQuasisimple_of_isFiniteToralTwistReduction p hp hk he (Or.inl rfl)
      TwistTag.D4.cartan_perm symmetrizedCartan_perm_D4 h4.theta
      (fun l _ hγ => wordWeylMatrix_mul_diagramMap_conj_pinnedX TwistTag.D4 l hγ)
      (diagramMap_mem_normalizer TwistTag.D4) (map_conj_diagramMap TwistTag.D4 k (Or.inl rfl))
      n4 (r4 x hx hx2) ℓ hℓ L hL hLc

end CFSG.LieType.AlgebraicGroups
