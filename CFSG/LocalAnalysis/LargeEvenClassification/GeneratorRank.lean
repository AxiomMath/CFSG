module

public import CFSG.LocalAnalysis.LargeEvenClassification.FrattiniRank

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse quotientUniverse

theorem quotient_generators_span {Source : Type groupUniverse} [Group Source]
    {Elementary : Type quotientUniverse} [CommGroup Elementary] {prime : ℕ}
    [Module (ZMod prime) (Additive Elementary)] (quotient : Source →* Elementary)
    (hsurjective : Function.Surjective quotient) (generators : Set Source)
    (hgenerates : Subgroup.closure generators = ⊤) :
    Submodule.span (ZMod prime) ((fun element => Additive.ofMul (quotient element)) '' generators) =
      ⊤ := by
  let span := Submodule.span (ZMod prime)
    ((fun element => Additive.ofMul (quotient element)) '' generators)
  have hclosure : ∀ element ∈ Subgroup.closure generators,
      Additive.ofMul (quotient element) ∈ span := by
    intro element helement
    induction helement using Subgroup.closure_induction with
    | mem element helement =>
      exact Submodule.subset_span ⟨element, helement, rfl⟩
    | one =>
      simpa only [map_one, ofMul_one] using span.zero_mem
    | mul first second _ _ hfirst hsecond =>
      simpa only [map_mul, ofMul_mul] using span.add_mem hfirst hsecond
    | inv element _ helement =>
      simpa only [map_inv, ofMul_inv] using span.neg_mem helement
  apply top_unique
  intro vector _
  obtain ⟨element, helement⟩ := hsurjective vector.toMul
  have hmem := hclosure element (hgenerates ▸ Subgroup.mem_top element)
  rw [helement] at hmem
  change vector ∈ span at hmem
  exact hmem

theorem quotient_frattini_dimension_le_generators {Source : Type groupUniverse} [Group Source]
    {Elementary : Type quotientUniverse} [CommGroup Elementary] {prime : ℕ}
    [Module (ZMod prime) (Additive Elementary)] [Fact prime.Prime] [Finite Elementary]
    (quotient : Source →* Elementary) (hsurjective : Function.Surjective quotient)
    (generators : Finset Source) (hgenerates : Subgroup.closure (generators : Set Source) = ⊤) :
    Module.finrank (ZMod prime) (Additive Elementary) ≤ generators.card := by
  classical
  let images := generators.image (fun element => Additive.ofMul (quotient element))
  have hspan : Submodule.span (ZMod prime) (images : Set (Additive Elementary)) = ⊤ := by
    rw [Finset.coe_image]
    exact quotient_generators_span quotient hsurjective generators hgenerates
  have hbound := finrank_span_finset_le_card (R := ZMod prime) images
  rw [Set.finrank, hspan] at hbound
  rw [(Submodule.topEquiv (R := ZMod prime) (M := Additive Elementary)).finrank_eq] at hbound
  exact hbound.trans Finset.card_image_le

theorem frattini_generators_of_span {Ambient : Type groupUniverse} [Group Ambient] [Finite Ambient]
    {prime : ℕ} (hprime : prime.Prime) (hpgroup : IsPGroup prime Ambient) :
    let _ : CommGroup (Ambient ⧸ frattini Ambient) := pGroupFrattiniCommGroup hprime hpgroup
    ∀ (module : Module (ZMod prime) (Additive (Ambient ⧸ frattini Ambient))),
      let _ := module
      ∀ (generators : Set Ambient), Submodule.span (ZMod prime)
        ((fun element => Additive.ofMul ((QuotientGroup.mk' (frattini Ambient)) element)) '' generators) =
        ⊤ → Subgroup.closure generators = ⊤ := by
  dsimp only
  let : CommGroup (Ambient ⧸ frattini Ambient) := pGroupFrattiniCommGroup hprime hpgroup
  intro module
  let := module
  intro generators hspan
  let quotient := QuotientGroup.mk' (frattini Ambient)
  let image := (Subgroup.closure generators).map quotient
  let subspace := (AddSubgroup.toZModSubmodule prime) (Subgroup.toAddSubgroup image)
  have hspanLe : Submodule.span (ZMod prime)
      ((fun element => Additive.ofMul (quotient element)) '' generators) ≤ subspace := by
    apply Submodule.span_le.mpr
    rintro _ ⟨element, helement, rfl⟩
    change quotient element ∈ image
    exact Subgroup.mem_map.mpr ⟨element, Subgroup.subset_closure helement, rfl⟩
  have hsubspace : subspace = ⊤ := top_unique (hspan ▸ hspanLe)
  have himage : image = ⊤ := by
    apply Subgroup.toAddSubgroup.injective
    apply (AddSubgroup.toZModSubmodule prime).injective
    simpa only [OrderIso.map_top] using hsubspace
  apply frattini_nongenerating
  have hpreimage := congrArg (Subgroup.comap quotient) himage
  rw [Subgroup.comap_map_eq, Subgroup.comap_top] at hpreimage
  change Subgroup.closure generators ⊔ (QuotientGroup.mk' (frattini Ambient)).ker = ⊤ at hpreimage
  rwa [QuotientGroup.ker_mk'] at hpreimage

theorem exists_frattini_basis_generators {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] {prime : ℕ} (hprime : prime.Prime) (hpgroup : IsPGroup prime Ambient) :
    let _ : CommGroup (Ambient ⧸ frattini Ambient) := pGroupFrattiniCommGroup hprime hpgroup
    ∀ (module : Module (ZMod prime) (Additive (Ambient ⧸ frattini Ambient))),
      let _ := module
      ∃ generators : Finset Ambient, Subgroup.closure (generators : Set Ambient) = ⊤ ∧
        generators.card ≤ Module.finrank (ZMod prime) (Additive (Ambient ⧸ frattini Ambient)) := by
  dsimp only
  let : Fact prime.Prime := ⟨hprime⟩
  let : CommGroup (Ambient ⧸ frattini Ambient) := pGroupFrattiniCommGroup hprime hpgroup
  intro module
  let := module
  classical
  let basis := Module.finBasis (ZMod prime) (Additive (Ambient ⧸ frattini Ambient))
  let lifts := fun index => Classical.choose
    (QuotientGroup.mk'_surjective (frattini Ambient) (basis index).toMul)
  have hlifts : ∀ index, (QuotientGroup.mk' (frattini Ambient)) (lifts index) = (basis index).toMul := by
    intro index
    exact Classical.choose_spec
      (QuotientGroup.mk'_surjective (frattini Ambient) (basis index).toMul)
  let generators := Finset.univ.image lifts
  refine ⟨generators, ?_, Finset.card_image_le.trans (by simp)⟩
  apply frattini_generators_of_span hprime hpgroup module
  have himage : ((fun element => Additive.ofMul ((QuotientGroup.mk' (frattini Ambient)) element)) ''
      (generators : Set Ambient)) = Set.range basis := by
    ext vector
    constructor
    · rintro ⟨element, helement, rfl⟩
      obtain ⟨index, _, rfl⟩ := Finset.mem_image.mp helement
      refine ⟨index, ?_⟩
      dsimp only
      rw [hlifts]
      rfl
    · rintro ⟨index, rfl⟩
      refine ⟨lifts index, Finset.mem_image.mpr ⟨index, Finset.mem_univ index, rfl⟩, ?_⟩
      dsimp only
      rw [hlifts]
      rfl
  rw [himage]
  exact basis.span_eq

theorem charTwo_local_core_generator_bound {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] {prime rank : ℕ} (hprime : prime.Prime) (hodd : prime ≠ 2)
    (hchar : IsCharTwoType Ambient) (Local Elementary : Subgroup Ambient)
    (hlocal : IsTwoLocal Local) (hle : Elementary ≤ Local)
    (helementary : IsElemAbelian prime Elementary) (hcard : Nat.card Elementary = prime ^ rank)
    (generators : Finset (pCore 2 Local))
    (hgenerates : Subgroup.closure (generators : Set (pCore 2 Local)) = ⊤) :
    2 * rank ≤ generators.card := by
  let : CommGroup ((pCore 2 Local) ⧸ frattini (pCore 2 Local)) :=
    pGroupFrattiniCommGroup Nat.prime_two (pCore_isPGroup Local 2)
  obtain ⟨module, hdimension⟩ := charTwo_local_elementary_frattini_rank hprime hodd
    hchar Local Elementary hlocal hle helementary hcard
  let := module
  exact hdimension.trans (quotient_frattini_dimension_le_generators (prime := 2)
    (QuotientGroup.mk' (frattini (pCore 2 Local)))
    (QuotientGroup.mk'_surjective _) generators hgenerates)

theorem large_even_local_core_generator_bound (Ambient : Type groupUniverse) [Group Ambient]
    [Finite Ambient] [IsSimpleGroup Ambient]
    (hnonab : ∃ first second : Ambient, first * second ≠ second * first)
    (hK : IsKProperByOrder Ambient) (hchar : IsCharTwoType Ambient)
    (hrank : 4 ≤ evenRank Ambient) :
    ∃ (prime : ℕ) (Local Elementary : Subgroup Ambient),
      prime ∈ oddLocalPrimes 4 Ambient ∧ IsTwoLocal Local ∧ Local ≠ ⊤ ∧
        IsKProperByOrder Local ∧ Elementary ≤ Local ∧ IsElemAbelian prime Elementary ∧
        Nat.card Elementary = prime ^ evenRank Ambient ∧ pCoreOf 2 Local ≠ ⊥ ∧
        ∀ generators : Finset (pCore 2 Local),
          Subgroup.closure (generators : Set (pCore 2 Local)) = ⊤ →
            2 * evenRank Ambient ≤ generators.card := by
  obtain ⟨prime, Local, Elementary, hprime, hlocal, hproper, hlocalK, hle,
    helementary, hcard, hcoreNontrivial, _, _⟩ :=
    large_even_entry_with_K Ambient hnonab hK hchar hrank
  refine ⟨prime, Local, Elementary, hprime, hlocal, hproper, hlocalK, hle,
    helementary, hcard, hcoreNontrivial, ?_⟩
  intro generators hgenerates
  exact charTwo_local_core_generator_bound hprime.1 hprime.2.1 hchar Local Elementary
    hlocal hle helementary hcard generators hgenerates

end CFSG.LargeEvenClassification.Helpers
