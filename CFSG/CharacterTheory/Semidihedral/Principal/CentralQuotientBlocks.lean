module

public import CFSG.CharacterTheory.Semidihedral.Principal.ResidueCentralIdempotents
public import CFSG.CharacterTheory.Wreathed.WeightedCentralInvolutionSum
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Blocks.NormalComplementPrincipal

public noncomputable section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers

section Kernel

variable {H : Type*} [Group H] [Fintype H] (Z : Subgroup H) [Z.Normal]

@[expose] def quotientKernelGenerators (S : Type*) [CommRing S] :
    Fin (Fintype.card Z) → MonoidAlgebra S H :=
  fun i => MonoidAlgebra.single ((Fintype.equivFin Z).symm i : H) 1 - 1

omit [Z.Normal] in
theorem quotientKernelGenerators_mem_center (S : Type*) [CommRing S] (hZ : Z ≤ Subgroup.center H)
    (i : Fin (Fintype.card Z)) :
    quotientKernelGenerators Z S i ∈ Subring.center (MonoidAlgebra S H) := by
  refine Subring.sub_mem _ ?_ (Subring.one_mem _)
  rw [mem_center_iff_coeff_conj]
  intro g c
  set z : H := ((Fintype.equivFin Z).symm i : H)
  have hz : z ∈ Subgroup.center H := hZ ((Fintype.equivFin Z).symm i).2
  have hiff : z = c * g * c⁻¹ ↔ z = g := by
    have hz' : c * z = z * c := Subgroup.mem_center_iff.mp hz c
    constructor
    · intro h
      have h2 : c * z = c * g := by
        rw [hz', h]
        group
      exact mul_left_cancel h2
    · intro h
      rw [← h, hz', mul_inv_cancel_right]
  simp only [MonoidAlgebra.coeff_single, Finsupp.single_apply, hiff]

theorem mapDomainRingHom_quotient_surjective (S : Type*) [CommRing S] :
    Function.Surjective (MonoidAlgebra.mapDomainRingHom S (QuotientGroup.mk' Z)) := by
  intro y
  refine ⟨∑ q, MonoidAlgebra.single (Quotient.out q : H) (y.coeff q), ?_⟩
  rw [map_sum]
  simp only [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single,
    QuotientGroup.mk'_apply, QuotientGroup.out_eq']
  exact groupAlgebra_sum_single y

theorem ker_mapDomainRingHom_quotient_eq_span (S : Type*) [CommRing S] :
    RingHom.ker (MonoidAlgebra.mapDomainRingHom S (QuotientGroup.mk' Z)) =
      Ideal.span (Set.range (quotientKernelGenerators Z S)) := by
  apply le_antisymm
  · intro x hx
    rw [RingHom.mem_ker] at hx
    set s : H ⧸ Z → H := fun q => Quotient.out q with hs
    have hsq : ∀ q : H ⧸ Z, ((s q : H) : H ⧸ Z) = q := fun q => QuotientGroup.out_eq' q
    have hz : ∀ g : H, (s (g : H ⧸ Z))⁻¹ * g ∈ Z := fun g => QuotientGroup.eq.mp (hsq g)
    set y : MonoidAlgebra S H := ∑ g : H, MonoidAlgebra.single (s (g : H ⧸ Z)) (x.coeff g)
      with hy
    have hy0 : y = 0 := by
      have hfib : y = ∑ q : H ⧸ Z, ∑ g ∈ Finset.univ.filter (fun g : H => (g : H ⧸ Z) = q),
          MonoidAlgebra.single (s q) (x.coeff g) := by
        rw [hy, ← Finset.sum_fiberwise Finset.univ (fun g : H => (g : H ⧸ Z))]
        refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun g hg => ?_
        rw [(Finset.mem_filter.mp hg).2]
      rw [hfib]
      refine Finset.sum_eq_zero fun q _ => ?_
      have hpull : MonoidAlgebra.single (s q)
          (∑ g ∈ Finset.univ.filter (fun g : H => (g : H ⧸ Z) = q), x.coeff g) =
          ∑ g ∈ Finset.univ.filter (fun g : H => (g : H ⧸ Z) = q),
            MonoidAlgebra.single (s q) (x.coeff g) := by
        rw [← MonoidAlgebra.singleAddHom_apply, map_sum]
        simp only [MonoidAlgebra.singleAddHom_apply]
      rw [← hpull]
      have hcoeff := groupAlgebra_quotient_coeff_sum (QuotientGroup.mk' Z) x q
      rw [hx, MonoidAlgebra.coeff_zero] at hcoeff
      have hsum : ∑ g ∈ Finset.univ.filter (fun g : H => (g : H ⧸ Z) = q), x.coeff g = 0 := by
        rw [Finset.sum_filter]
        have h0 := hcoeff.symm
        simp only [QuotientGroup.mk'_apply, Finsupp.coe_zero, Pi.zero_apply] at h0
        convert h0 using 2 with g
        by_cases hg : (g : H ⧸ Z) = q <;> simp [hg]
      rw [hsum, MonoidAlgebra.single_zero]
    have hdecomp : x = y + ∑ g : H, MonoidAlgebra.single (s (g : H ⧸ Z)) (x.coeff g) *
        quotientKernelGenerators Z S (Fintype.equivFin Z ⟨_, hz g⟩) := by
      rw [hy, ← Finset.sum_add_distrib]
      conv_lhs => rw [← groupAlgebra_sum_single x]
      refine Finset.sum_congr rfl fun g _ => ?_
      simp only [quotientKernelGenerators, Equiv.symm_apply_apply, mul_sub, mul_one,
        MonoidAlgebra.single_mul_single, mul_inv_cancel_left]
      abel
    rw [hdecomp, hy0, zero_add]
    exact Ideal.sum_mem _ fun g _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, rfl⟩)
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, quotientKernelGenerators, map_sub, map_one,
      MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single,
      QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff _).mpr ((Fintype.equivFin Z).symm i).2,
      ← MonoidAlgebra.one_def, sub_self]

theorem quotient_centralIdempotentCorrespondence_field (k : Type*) [Field k] (p : ℕ)
    [Fact p.Prime] [CharP k p] (hZ : Z ≤ Subgroup.center H) (hZp : IsPGroup p Z) :
    CentralIdempotentCorrespondence (MonoidAlgebra.mapDomainRingHom k (QuotientGroup.mk' Z)) := by
  obtain ⟨n, hn⟩ := normal_p_quotient_kernel_nilpotent (field := k) p Z hZp
  rw [ker_mapDomainRingHom_quotient_eq_span] at hn
  refine centralIdempotentCorrespondence_of_ker_eq_span_central k p _
    (mapDomainRingHom_quotient_surjective Z k) (quotientKernelGenerators Z k)
    (quotientKernelGenerators_mem_center Z k hZ) (ker_mapDomainRingHom_quotient_eq_span Z k)
    (d := n + 1) (by omega) ?_
  rw [Submodule.pow_succ, hn, Ideal.zero_eq_bot, Submodule.bot_mul]

end Kernel

section Relative

variable (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
variable {H : Type*} [Group H] [Fintype H] (Z : Subgroup H) [Z.Normal]

omit [Fintype H] in
theorem residue_comp_mapDomain_quotient :
    (MonoidAlgebra.mapRingHom (H ⧸ Z) (localizedComplexIntegerResidue ideal)).comp
        (MonoidAlgebra.mapDomainRingHom (localizedComplexIntegerRing ideal) (QuotientGroup.mk' Z)) =
      (MonoidAlgebra.mapDomainRingHom (ComplexAlgebraicIntegers ⧸ ideal) (QuotientGroup.mk' Z)).comp
        (MonoidAlgebra.mapRingHom H (localizedComplexIntegerResidue ideal)) := by
  apply MonoidAlgebra.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, MonoidAlgebra.mapDomainRingHom_apply,
      MonoidAlgebra.mapDomain_single, MonoidAlgebra.mapRingHom_single, map_one]
  · intro m
    simp only [RingHom.comp_apply, MonoidAlgebra.mapDomainRingHom_apply,
      MonoidAlgebra.mapDomain_single, MonoidAlgebra.mapRingHom_single, map_one]

omit [Fintype H] in
theorem subtype_comp_mapDomain_quotient :
    (MonoidAlgebra.mapRingHom (H ⧸ Z) (localizedComplexIntegerRing ideal).subtype).comp
        (MonoidAlgebra.mapDomainRingHom (localizedComplexIntegerRing ideal) (QuotientGroup.mk' Z)) =
      (MonoidAlgebra.mapDomainRingHom ℂ (QuotientGroup.mk' Z)).comp
        (MonoidAlgebra.mapRingHom H (localizedComplexIntegerRing ideal).subtype) := by
  apply MonoidAlgebra.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, MonoidAlgebra.mapDomainRingHom_apply,
      MonoidAlgebra.mapDomain_single, MonoidAlgebra.mapRingHom_single, map_one]
  · intro m
    simp only [RingHom.comp_apply, MonoidAlgebra.mapDomainRingHom_apply,
      MonoidAlgebra.mapDomain_single, MonoidAlgebra.mapRingHom_single, map_one]

theorem quotient_bijOn_centralIdempotents (p : ℕ) [Fact p.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (hZ : Z ≤ Subgroup.center H) (hZp : IsPGroup p Z)
    (basisH : FiniteIrreducibleCharacterBasis H)
    (basisQ : FiniteIrreducibleCharacterBasis (H ⧸ Z)) :
    Set.BijOn (MonoidAlgebra.mapDomainRingHom (localizedComplexIntegerRing ideal)
        (QuotientGroup.mk' Z))
      (centralIdempotents (MonoidAlgebra (localizedComplexIntegerRing ideal) H))
      (centralIdempotents (MonoidAlgebra (localizedComplexIntegerRing ideal) (H ⧸ Z))) := by
  set PR := MonoidAlgebra.mapDomainRingHom (localizedComplexIntegerRing ideal)
    (QuotientGroup.mk' Z)
  set Pk := MonoidAlgebra.mapDomainRingHom (ComplexAlgebraicIntegers ⧸ ideal) (QuotientGroup.mk' Z)
  set ρH := MonoidAlgebra.mapRingHom H (localizedComplexIntegerResidue ideal)
  set ρQ := MonoidAlgebra.mapRingHom (H ⧸ Z) (localizedComplexIntegerResidue ideal)
  have hsq : ∀ x, ρQ (PR x) = Pk (ρH x) := fun x =>
    congrArg (fun f => f x) (residue_comp_mapDomain_quotient ideal Z)
  have hH := residueMap_bijOn_centralIdempotents ideal basisH
  have hQ := residueMap_bijOn_centralIdempotents ideal basisQ
  let : Field (ComplexAlgebraicIntegers ⧸ ideal) := Ideal.Quotient.field ideal
  have hk := (quotient_centralIdempotentCorrespondence_field Z (ComplexAlgebraicIntegers ⧸ ideal)
    p hZ hZp).bijOn
  refine ⟨fun e he => map_mem_centralIdempotents PR
    (mapDomainRingHom_quotient_surjective Z _) he, ?_, ?_⟩
  · intro e he e' he' hee'
    apply hH.injOn he he'
    apply hk.injOn (hH.mapsTo he) (hH.mapsTo he')
    rw [← hsq, ← hsq, hee']
  · intro f hf
    obtain ⟨x, hx, hxf⟩ := hk.surjOn (hQ.mapsTo hf)
    obtain ⟨e, he, hex⟩ := hH.surjOn hx
    have hPe := map_mem_centralIdempotents PR (mapDomainRingHom_quotient_surjective Z _) he
    refine ⟨e, he, hQ.injOn hPe hf ?_⟩
    rw [hsq, hex, hxf]

end Relative

section Inflation

universe u

variable {H : Type u} [Group H] [Fintype H] (Z : Subgroup H) [Z.Normal]

omit [Fintype H] in
theorem inflated_asAlgebraHom (data : FiniteComplexRepresentation (H ⧸ Z))
    (x : MonoidAlgebra ℂ H) :
    (inflatedFiniteComplexRepresentation (QuotientGroup.mk' Z) data).representation.asAlgebraHom x =
      data.representation.asAlgebraHom
        (MonoidAlgebra.mapDomainRingHom ℂ (QuotientGroup.mk' Z) x) := by
  induction x using MonoidAlgebra.induction_on with
  | of h =>
    rw [MonoidAlgebra.of_apply, MonoidAlgebra.mapDomainRingHom_apply,
      MonoidAlgebra.mapDomain_single, Representation.asAlgebraHom_single_one,
      Representation.asAlgebraHom_single_one]
    rfl
  | add x y hx hy =>
    rw [map_add, map_add, map_add, hx, hy]
    rfl
  | smul r x hx =>
    rw [map_smul, hx, MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomainRingHom_apply,
      MonoidAlgebra.mapDomain_smul, map_smul]
    rfl

theorem characterIdempotentExpansion_action_of_character_eq {G : Type u} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (c : basis.index → ℂ)
    (V : FiniteComplexRepresentation G) (hV : V.IsIrreducible) {ψ : basis.index}
    (hψ : (basis.representation ψ).character = V.character) :
    V.representation.asAlgebraHom (characterIdempotentExpansion basis c) = c ψ • 1 := by
  unfold characterIdempotentExpansion
  rw [map_sum]
  simp only [map_smul, complexCharacterIdempotent_irreducible_action _ V (basis.irreducible _) hV]
  rw [Finset.sum_eq_single ψ]
  · rw [ite_eq_left hψ]
  · intro χ _ hχ
    rw [ite_eq_right (fun h => hχ (basis.distinct (h.trans hψ.symm))), smul_zero]
  · intro h
    exact absurd (Finset.mem_univ ψ) h

variable (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]

theorem mem_coefficientBlock_iff_of_inflation (basisH : FiniteIrreducibleCharacterBasis H)
    (basisQ : FiniteIrreducibleCharacterBasis (H ⧸ Z)) {χ : basisH.index} {θ : basisQ.index}
    (hblock : MonoidAlgebra.mapDomainRingHom (localizedComplexIntegerRing ideal)
      (QuotientGroup.mk' Z) (blockIdempotent ideal basisH χ) = blockIdempotent ideal basisQ θ)
    (θ' : basisQ.index) (ψ : basisH.index)
    (hψ : (basisH.representation ψ).character =
      (basisQ.representation θ').character ∘ QuotientGroup.mk' Z) :
    ψ ∈ coefficientBlock basisH (localizedComplexIntegerRing ideal) χ ↔
      θ' ∈ coefficientBlock basisQ (localizedComplexIntegerRing ideal) θ := by
  set B := coefficientBlock basisH (localizedComplexIntegerRing ideal) χ
  set B' := coefficientBlock basisQ (localizedComplexIntegerRing ideal) θ
  have hC : MonoidAlgebra.mapDomainRingHom ℂ (QuotientGroup.mk' Z)
      (characterSubsetIdempotent basisH B) = characterSubsetIdempotent basisQ B' := by
    rw [← blockIdempotent_map_subtype, ← blockIdempotent_map_subtype, ← hblock]
    exact (congrArg (fun f => f (blockIdempotent ideal basisH χ))
      (subtype_comp_mapDomain_quotient ideal Z)).symm
  set V := inflatedFiniteComplexRepresentation (QuotientGroup.mk' Z) (basisQ.representation θ')
  have hVirr : V.IsIrreducible := CFSG.LyonsUnitaryFour.isIrreducible_comp_surjective
    (QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z) _ (basisQ.irreducible θ')
  have h1 := characterIdempotentExpansion_action_of_character_eq basisH
    (fun l => if l ∈ B then 1 else 0) V hVirr hψ
  have h2 : V.representation.asAlgebraHom (characterSubsetIdempotent basisH B) =
      (basisQ.representation θ').representation.asAlgebraHom
        (characterSubsetIdempotent basisQ B') := by
    rw [inflated_asAlgebraHom, hC]
  have h3 := characterIdempotentExpansion_action basisQ (fun l => if l ∈ B' then 1 else 0) θ'
  have hscalar := irreducible_scalar_identity_injective V hVirr
    (h1.symm.trans (h2.trans h3))
  by_cases hψB : ψ ∈ B <;> by_cases hθB : θ' ∈ B' <;> simp [hψB, hθB] at hscalar ⊢

theorem blockIdempotent_eq_iff {G : Type u} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (χ ψ : basis.index) :
    blockIdempotent ideal basis χ = blockIdempotent ideal basis ψ ↔
      coefficientBlock basis (localizedComplexIntegerRing ideal) χ =
        coefficientBlock basis (localizedComplexIntegerRing ideal) ψ := by
  constructor
  · intro h
    have hval := congrArg Subtype.val
      (centralCoefficientLiftHom_injective (localizedComplexIntegerRing ideal) h)
    exact characterSubsetIdempotent_injective basis hval
  · intro h
    have hval : coefficientBlockIdempotent basis (localizedComplexIntegerRing ideal) χ =
        coefficientBlockIdempotent basis (localizedComplexIntegerRing ideal) ψ :=
      Subtype.ext (by
        change characterSubsetIdempotent basis
            (coefficientBlock basis (localizedComplexIntegerRing ideal) χ) =
          characterSubsetIdempotent basis
            (coefficientBlock basis (localizedComplexIntegerRing ideal) ψ)
        rw [h])
    change centralCoefficientLiftHom _ (coefficientBlockIdempotent basis _ χ) =
      centralCoefficientLiftHom _ (coefficientBlockIdempotent basis _ ψ)
    rw [hval]

theorem central_p_quotient_relative_block_correspondence (p : ℕ) [Fact p.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (hZ : Z ≤ Subgroup.center H)
    (hZp : IsPGroup p Z) (basisH : FiniteIrreducibleCharacterBasis H)
    (basisQ : FiniteIrreducibleCharacterBasis (H ⧸ Z)) (principalH : basisH.index)
    (hprincipalH : (basisH.representation principalH).character = 1) (principalQ : basisQ.index)
    (hprincipalQ : (basisQ.representation principalQ).character = 1) :
    let R := localizedComplexIntegerRing ideal
    let P := MonoidAlgebra.mapDomainRingHom R (QuotientGroup.mk' Z)
    CentralIdempotentCorrespondence P ∧
    (∀ χ, ∃ θ, P (blockIdempotent ideal basisH χ) = blockIdempotent ideal basisQ θ) ∧
    (∀ χ θ θ', P (blockIdempotent ideal basisH χ) = blockIdempotent ideal basisQ θ →
      P (blockIdempotent ideal basisH χ) = blockIdempotent ideal basisQ θ' →
        coefficientBlock basisQ R θ = coefficientBlock basisQ R θ') ∧
    (∀ χ χ', P (blockIdempotent ideal basisH χ) = P (blockIdempotent ideal basisH χ') ↔
      coefficientBlock basisH R χ = coefficientBlock basisH R χ') ∧
    (∀ θ, ∃ χ, P (blockIdempotent ideal basisH χ) = blockIdempotent ideal basisQ θ) ∧
    (∀ χ θ, P (blockIdempotent ideal basisH χ) = blockIdempotent ideal basisQ θ →
      ∀ θ' ψ, (basisH.representation ψ).character =
          (basisQ.representation θ').character ∘ QuotientGroup.mk' Z →
        (ψ ∈ coefficientBlock basisH R χ ↔ θ' ∈ coefficientBlock basisQ R θ)) ∧
    (∀ χ θ, P (blockIdempotent ideal basisH χ) = blockIdempotent ideal basisQ θ →
      (fun ψ => (basisH.representation ψ).character) ''
          (coefficientBlock basisH R χ : Set basisH.index) ∩
        Set.range (fun θ' => (basisQ.representation θ').character ∘ QuotientGroup.mk' Z) =
      (fun θ' => (basisQ.representation θ').character ∘ QuotientGroup.mk' Z) ''
        (coefficientBlock basisQ R θ : Set basisQ.index)) ∧
    P (blockIdempotent ideal basisH principalH) = blockIdempotent ideal basisQ principalQ ∧
    ∀ θ ∈ coefficientBlock basisQ R principalQ, ∃ ψ ∈ coefficientBlock basisH R principalH,
      (basisH.representation ψ).character =
        (basisQ.representation θ).character ∘ QuotientGroup.mk' Z := by
  intro R P
  have hcorr : CentralIdempotentCorrespondence P := CentralIdempotentCorrespondence.of_bijOn P
    (quotient_bijOn_centralIdempotents ideal Z p hZ hZp basisH basisQ)
  have hexists : ∀ χ, ∃ θ, P (blockIdempotent ideal basisH χ) = blockIdempotent ideal basisQ θ :=
    fun χ => (exists_blockIdempotent_eq ideal basisQ
      (hcorr.primitive_bijOn.mapsTo (blockIdempotent_isPrimitive ideal basisH χ))).imp
        fun _ h => h
  have hchar := fun χ θ (hblock : P (blockIdempotent ideal basisH χ) =
      blockIdempotent ideal basisQ θ) => mem_coefficientBlock_iff_of_inflation Z ideal basisH
    basisQ hblock
  have hinflate : ∀ θ' : basisQ.index, ∃ ψ : basisH.index, (basisH.representation ψ).character =
      (basisQ.representation θ').character ∘ QuotientGroup.mk' Z := by
    intro θ'
    obtain ⟨ψ, hψ, -⟩ := CFSG.Wreathed.complete_character_basis_contains_irreducible basisH
      (inflatedFiniteComplexRepresentation (QuotientGroup.mk' Z) (basisQ.representation θ'))
      (CFSG.LyonsUnitaryFour.isIrreducible_comp_surjective (QuotientGroup.mk' Z)
        (QuotientGroup.mk'_surjective Z) _ (basisQ.irreducible θ'))
    exact ⟨ψ, hψ⟩
  have hprincipal : P (blockIdempotent ideal basisH principalH) =
      blockIdempotent ideal basisQ principalQ := by
    obtain ⟨θ₀, hθ₀⟩ := hexists principalH
    have hψ : (basisH.representation principalH).character =
        (basisQ.representation principalQ).character ∘ QuotientGroup.mk' Z := by
      rw [hprincipalH, hprincipalQ]
      rfl
    have hmem := (hchar principalH θ₀ hθ₀ principalQ principalH hψ).mp
      (coefficientBlock_self_mem _ _ _)
    rw [hθ₀, blockIdempotent_eq_iff]
    exact (coefficientBlock_eq_of_mem basisQ R hmem).symm
  refine ⟨hcorr, hexists, ?_, ?_, ?_, hchar, ?_, hprincipal, ?_⟩
  · intro χ θ θ' h h'
    exact (blockIdempotent_eq_iff ideal basisQ θ θ').mp (h.symm.trans h')
  · intro χ χ'
    rw [← blockIdempotent_eq_iff ideal basisH χ χ']
    constructor
    · intro h
      exact hcorr.bijOn.injOn (blockIdempotent_isPrimitive ideal basisH χ).1
        (blockIdempotent_isPrimitive ideal basisH χ').1 h
    · intro h
      rw [h]
  · intro θ
    obtain ⟨e, he, hPe⟩ := hcorr.primitive_bijOn.surjOn
      (blockIdempotent_isPrimitive ideal basisQ θ)
    obtain ⟨χ, rfl⟩ := exists_blockIdempotent_eq ideal basisH he
    exact ⟨χ, hPe⟩
  · intro χ θ hblock
    ext f
    simp only [Set.mem_inter_iff, Set.mem_image, Finset.mem_coe, Set.mem_range]
    constructor
    · rintro ⟨⟨ψ, hψB, rfl⟩, θ', hθ'⟩
      exact ⟨θ', (hchar χ θ hblock θ' ψ hθ'.symm).mp hψB, hθ'⟩
    · rintro ⟨θ', hθ'B, rfl⟩
      obtain ⟨ψ, hψ⟩ := hinflate θ'
      exact ⟨⟨ψ, (hchar χ θ hblock θ' ψ hψ).mpr hθ'B, hψ⟩, θ', rfl⟩
  · intro θ hθ
    obtain ⟨ψ, hψ⟩ := hinflate θ
    exact ⟨ψ, (hchar principalH principalQ hprincipal θ ψ hψ).mpr hθ, hψ⟩

end Inflation

end CFSG.Semidihedral.Principal
