module

public import CFSG.CharacterTheory.TwoRankLowerBound.NormalComplementBlock
public import CFSG.CharacterTheory.TwoRankLowerBound.BlockSectionOrthogonality
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Blocks.CosetConstantKernel

public section

namespace CFSG.LyonsUnitaryFour

open CFSG.TwoRankLowerBound.Helpers
open scoped BigOperators Classical

universe u

@[expose] noncomputable def subrepresentationInflation {k : Type*} [Field k]
    {G Q : Type*} [Group G] [Group Q] (π : G →* Q) (hπ : Function.Surjective π) {V : Type*}
    [AddCommGroup V] [Module k V] (ρ : Representation k Q V) :
    Subrepresentation (ρ.comp π) ≃o Subrepresentation ρ where
  toFun W := {
    toSubmodule := W.toSubmodule
    apply_mem_toSubmodule q := by
      intro v hv
      obtain ⟨g, rfl⟩ := hπ q
      exact W.apply_mem_toSubmodule g hv }
  invFun W := {
    toSubmodule := W.toSubmodule
    apply_mem_toSubmodule g := W.apply_mem_toSubmodule (π g) }
  left_inv _ := Subrepresentation.ext rfl
  right_inv _ := Subrepresentation.ext rfl
  map_rel_iff' := Iff.rfl

theorem isIrreducible_of_comp_surjective {k : Type*} [Field k] {G Q : Type*} [Group G]
    [Group Q] (π : G →* Q) (hπ : Function.Surjective π) {V : Type*} [AddCommGroup V]
    [Module k V] (ρ : Representation k Q V) (h : Representation.IsIrreducible (ρ.comp π)) :
    ρ.IsIrreducible := by
  let : IsSimpleOrder (Subrepresentation (ρ.comp π)) := h
  exact (subrepresentationInflation π hπ ρ).symm.isSimpleOrder

theorem isIrreducible_comp_surjective {k : Type*} [Field k] {G Q : Type*} [Group G] [Group Q]
    (π : G →* Q) (hπ : Function.Surjective π) {V : Type*} [AddCommGroup V] [Module k V]
    (ρ : Representation k Q V) (h : ρ.IsIrreducible) :
    Representation.IsIrreducible (ρ.comp π) := by
  let : IsSimpleOrder (Subrepresentation ρ) := h
  exact (subrepresentationInflation π hπ ρ).isSimpleOrder

theorem le_ker_of_character_eq_degree {G : Type*} [Group G] {V : Type*} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (H : Subgroup G)
    [Finite H] (hH : ∀ h ∈ H, ρ.character h = ρ.character 1) : H ≤ MonoidHom.ker ρ := by
  let := Fintype.ofFinite H
  have hHne : (Nat.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have htr : LinearMap.trace ℂ V (subgroupAverage ρ H) = ρ.character 1 := by
    have h := trace_mul_subgroupAverage ρ H 1
    rw [map_one, one_mul] at h
    simp only [one_mul] at h
    rw [h, Finset.sum_congr rfl (fun (h : H) _ => hH h h.property),
      Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, nsmul_eq_mul]
    field_simp
  have hidem : IsIdempotentElem (1 - subgroupAverage ρ H) :=
    (subgroupAverage_idempotent ρ H).one_sub
  have htr0 : LinearMap.trace ℂ V (1 - subgroupAverage ρ H) = 0 := by
    rw [map_sub, htr, LinearMap.trace_one, Representation.char_one]
    simp
  have heq : 1 - subgroupAverage ρ H = 0 :=
    LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero hidem htr0
  have heH1 : subgroupAverage ρ H = 1 := (sub_eq_zero.mp heq).symm
  intro h hh
  rw [MonoidHom.mem_ker]
  have := mul_subgroupAverage ρ H h hh
  rw [heH1, mul_one] at this
  exact this

theorem principal_block_eq_normalSubgroupCharacterSupport {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (p : ℕ) [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (N : Subgroup G) [N.Normal] (hcoprime : Nat.Coprime p (Nat.card N))
    (hquotient : IsPGroup p (G ⧸ N)) :
    coefficientBlock basis (localizedComplexIntegerRing ideal) principal =
      normalSubgroupCharacterSupport basis (QuotientGroup.mk' N).ker := by
  let R := localizedComplexIntegerRing ideal
  let := localizedComplexIntegerRing_residue_charP ideal p
  have hKN : (QuotientGroup.mk' N).ker = N := QuotientGroup.ker_mk' N
  have hunit : IsUnit ((Nat.card (QuotientGroup.mk' N).ker : ℤ) : R) := by
    rw [localizedComplexInteger_integer_unit_iff ideal p, hKN]
    intro hdvd
    have hdvd' : p ∣ Nat.card N := Int.natCast_dvd_natCast.mp hdvd
    exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mp hcoprime hdvd'
  have hcardUnit : ((hunit.unit : Rˣ) : R) = Nat.card (QuotientGroup.mk' N).ker := by
    rw [IsUnit.unit_spec, Int.cast_natCast]
  exact normalComplement_characterSupport_eq_block basis R p (QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N) hquotient hunit.unit hcardUnit principal
    (normalSubgroupCharacterSupport_principal_mem basis _ principal hprincipal)

theorem normal_p_complement_principal_block {G : Type u} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (p : ℕ) [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (N : Subgroup G) [N.Normal] (hcoprime : Nat.Coprime p (Nat.card N))
    (hquotient : IsPGroup p (G ⧸ N)) :
    (∀ label, label ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal ↔
      N ≤ MonoidHom.ker (basis.representation label).representation) ∧
    (∀ label, label ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal ↔
      ∃ data : FiniteComplexRepresentation.{u, u} (G ⧸ N), data.IsIrreducible ∧
        (basis.representation label).character = data.character ∘ QuotientGroup.mk' N) ∧
    (∀ data : FiniteComplexRepresentation.{u, u} (G ⧸ N), data.IsIrreducible →
      ∃ label ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        (basis.representation label).character = data.character ∘ QuotientGroup.mk' N) := by
  have hblock := principal_block_eq_normalSubgroupCharacterSupport basis ideal p principal
    hprincipal N hcoprime hquotient
  rw [QuotientGroup.ker_mk'] at hblock
  have hker : ∀ label, label ∈ coefficientBlock basis (localizedComplexIntegerRing ideal)
      principal ↔ N ≤ MonoidHom.ker (basis.representation label).representation := by
    intro label
    rw [hblock]
    simp only [normalSubgroupCharacterSupport, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h n hn
      exact h ⟨n, hn⟩
    · intro h n
      exact h n.property
  have hinfl : ∀ label (data : FiniteComplexRepresentation.{u, u} (G ⧸ N)),
      (basis.representation label).character = data.character ∘ QuotientGroup.mk' N →
      label ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal := by
    intro label data hchar
    rw [hker]
    apply le_ker_of_character_eq_degree
    intro n hn
    change (basis.representation label).character n = (basis.representation label).character 1
    rw [hchar]
    simp only [Function.comp_apply, map_one]
    have hn1 : (QuotientGroup.mk' N) n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
    rw [hn1]
  refine ⟨hker, ?_, ?_⟩
  · intro label
    constructor
    · intro hmem
      have hN := (hker label).mp hmem
      let ρ := (basis.representation label).representation
      let ρ' : Representation ℂ (G ⧸ N) (basis.representation label).vector :=
        QuotientGroup.lift N ρ hN
      have hcomp : ρ'.comp (QuotientGroup.mk' N) = ρ := by
        ext g
        simp [ρ']
      refine ⟨{ vector := (basis.representation label).vector, representation := ρ' }, ?_, ?_⟩
      · apply isIrreducible_of_comp_surjective (QuotientGroup.mk' N)
          (QuotientGroup.mk'_surjective N)
        rw [hcomp]
        exact basis.irreducible label
      · funext g
        change LinearMap.trace ℂ _ (ρ g) = LinearMap.trace ℂ _ (ρ' (QuotientGroup.mk' N g))
        rw [← MonoidHom.comp_apply, hcomp]
    · rintro ⟨data, -, hchar⟩
      exact hinfl label data hchar
  · intro data hdata
    let inflated : FiniteComplexRepresentation.{u, u} G :=
      { vector := data.vector, representation := data.representation.comp (QuotientGroup.mk' N) }
    have hirr : inflated.IsIrreducible :=
      isIrreducible_comp_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
        data.representation hdata
    obtain ⟨label, hlabel⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basis inflated
      hirr
    exact ⟨label, hinfl label data hlabel, hlabel⟩

end CFSG.LyonsUnitaryFour
