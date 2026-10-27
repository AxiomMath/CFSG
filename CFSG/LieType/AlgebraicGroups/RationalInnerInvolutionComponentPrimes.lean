module

public import CFSG.LieType.AlgebraicGroups.RationalInnerInvolutionFixedComponents
public import CFSG.LieType.Chevalley.OrthogonalSemilinearFixedComponentPrimes

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ToralSign
  CFSG.LocalAnalysis.ComponentInitial

theorem pComponent_prime_of_mulEquiv {A B : Type*} [Group A] [Group B] {p ℓ : ℕ} (e : A ≃* B)
    (hB : ∀ J : Subgroup B, CFSG.IsPComponent ℓ J → (∃ g ∈ J, orderOf g = p) ∧ p ∣ Nat.card J)
    (J : Subgroup A) (hJ : CFSG.IsPComponent ℓ J) :
    (∃ g ∈ J, orderOf g = p) ∧ p ∣ Nat.card J := by
  obtain ⟨⟨g, hg, hgo⟩, hdvd⟩ := hB _ (isPComponent_map_of_isPComponent ℓ e hJ)
  obtain ⟨j, hj, rfl⟩ := hg
  refine ⟨⟨j, hj, ?_⟩, ?_⟩
  · rw [← hgo, MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq]
  · rwa [Subgroup.card_map_of_injective e.injective] at hdvd

variable (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p]

theorem prime_of_isFiniteToralTwistReduction
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
    (∃ g ∈ L, orderOf g = p) ∧ p ∣ Nat.card L := by
  obtain ⟨r, hr, l, hl, -, hQfin, g₁, -, hcomp⟩ := hred
  obtain ⟨hL₁, hL₁c⟩ := ((hcomp ℓ hℓ).1 L).1 ⟨hL, hLc⟩
  have hqQ : ∀ J : Subgroup (fixedPointsIn
      (torusGroup τ k ⊔ rootSpan τ k (kernelRoots (signMaskChar τ r.mask)))
      (frobTwistGL τ k p e (wordWeylMatrix τ k l * D))),
      CFSG.IsPComponent ℓ J → (∃ g ∈ J, orderOf g = p) ∧ p ∣ Nat.card J := by
    intro J hJ
    rcases (kernelRoots (signMaskChar τ r.mask)).eq_empty_or_nonempty with hK | hK
    · exact absurd hJ (not_isPComponent_of_kernelRoots_eq_empty hK inf_le_left J)
    · obtain ⟨Dd, -, ⟨eqv⟩⟩ := exists_datum_mulEquiv p hp hk he hτ hA hB (htheta r hr l hl)
        (hDX l) (mul_mem (wordWeylMatrix_mem_normalizer l) hDT) (map_conj_wordWeylMatrix_mul l hDG)
        (hpin r hr l hl) hK
      have : Finite Dd.totalFixedGroup := Finite.of_equiv _ eqv.symm.toEquiv
      exact pComponent_prime_of_mulEquiv eqv.symm
        ((orthogonal_semilinear_fixed_components_defining_prime_divisibility Dd this).2 ℓ hℓ) J hJ
  obtain ⟨⟨g, hg, hgo⟩, hdvd⟩ := hqQ _ hL₁c
  obtain ⟨y, hy, hyg⟩ := Subgroup.mem_subgroupOf.1 hg
  refine ⟨⟨y, hy, ?_⟩, ?_⟩
  · rw [← hgo, ← Subgroup.orderOf_coe g, ← hyg, MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq]
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL₁).toEquiv,
      Subgroup.card_map_of_injective (MulAut.conj g₁).injective] at hdvd
    exact hdvd

variable (k) in
@[expose] def InvolutionCentralizerPComponentsDefiningPrime (τ : Tag) (e : ℕ) (D : ModGL τ k) :
    Prop :=
  ∀ x ∈ fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D), x ^ 2 = 1 →
    ∀ ℓ : ℕ, ℓ.Prime → ∀ L : Subgroup (ModGL τ k),
      L ≤ ⁅fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D),
        fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D)⁆ ⊓ Subgroup.centralizer {x} →
      CFSG.IsPComponent ℓ (L.subgroupOf (⁅fixedPointsIn (adjointGroup τ k)
        (frobTwistGL τ k p e D), fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D)⁆ ⊓
          Subgroup.centralizer {x})) →
      (∃ g ∈ L, orderOf g = p) ∧ p ∣ Nat.card L

variable (k) in
theorem rational_e7_twisted_e6_triality_component_prime_divisibility
    (hp : p ≠ 2)
    (hk : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k) (e : ℕ) (he : 1 ≤ e) :
    InvolutionCentralizerPComponentsDefiningPrime p k .E7 e 1 ∧
    InvolutionCentralizerPComponentsDefiningPrime p k TwistTag.E6.tag e
      (diagramMap TwistTag.E6 k) ∧
    InvolutionCentralizerPComponentsDefiningPrime p k TwistTag.D4.tag e
      (diagramMap TwistTag.D4 k) := by
  obtain ⟨h7, h6, h4⟩ := rational_toral_sign_diagram_arithmetic
  obtain ⟨r7, r6, r4⟩ := rational_inner_involution_finite_toral_twist_reduction p k hp e he
  obtain ⟨n7, n6, n4⟩ := rational_toral_twist_semilinear_pinning_normalization p k hp e he
  refine ⟨fun x hx hx2 ℓ hℓ L hL hLc => ?_, fun x hx hx2 ℓ hℓ L hL hLc => ?_,
    fun x hx hx2 ℓ hℓ L hL hLc => ?_⟩
  · exact prime_of_isFiniteToralTwistReduction p hp hk he (Or.inr (Or.inr rfl))
      (ρ := 1) (fun _ _ => rfl) (fun _ _ => rfl) h7.theta
      (fun l _ hγ => wordWeylMatrix_mul_one_conj_pinnedX l hγ) (one_mem _)
      (map_conj_one_adjointGroup _ k) n7 (r7 x hx hx2) ℓ hℓ L hL hLc
  · exact prime_of_isFiniteToralTwistReduction p hp hk he (Or.inr (Or.inl rfl))
      TwistTag.E6.cartan_perm symmetrizedCartan_perm_E6 h6.theta
      (fun l _ hγ => wordWeylMatrix_mul_diagramMap_conj_pinnedX TwistTag.E6 l hγ)
      (diagramMap_mem_normalizer TwistTag.E6) (map_conj_diagramMap TwistTag.E6 k (Or.inl rfl))
      n6 (r6 x hx hx2) ℓ hℓ L hL hLc
  · exact prime_of_isFiniteToralTwistReduction p hp hk he (Or.inl rfl)
      TwistTag.D4.cartan_perm symmetrizedCartan_perm_D4 h4.theta
      (fun l _ hγ => wordWeylMatrix_mul_diagramMap_conj_pinnedX TwistTag.D4 l hγ)
      (diagramMap_mem_normalizer TwistTag.D4) (map_conj_diagramMap TwistTag.D4 k (Or.inl rfl))
      n4 (r4 x hx hx2) ℓ hℓ L hL hLc

end CFSG.LieType.AlgebraicGroups
