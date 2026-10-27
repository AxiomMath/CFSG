module

public import CFSG.LieType.Chevalley.CoordinateFieldFixedStructure
public import CFSG.LieType.Chevalley.GraphFixedF4GroupDescent
public import CFSG.LieType.Chevalley.E6GraphInvolutionFiniteReduction
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley
open scoped commutatorElement

theorem map_adjointGroup_baseChangeGL_eq_of_range_eq
    {τ : Tag} {A B L : Type} [Field A]
    [Field B] [Field L] (f : A →+* L) (g : B →+* L) (h : Set.range f = Set.range g) :
    (adjointGroup τ A).map (baseChangeGL f) = (adjointGroup τ B).map (baseChangeGL g) := by
  rw [map_baseChangeGL_adjointGroup, map_baseChangeGL_adjointGroup]
  congr 1
  ext x
  constructor
  · rintro ⟨i, c, hc⟩
    have hmem : f c ∈ Set.range g := by
      rw [← h]
      exact ⟨c, rfl⟩
    obtain ⟨d, hd⟩ := hmem
    exact ⟨i, d, by rwa [hd]⟩
  · rintro ⟨i, d, hd⟩
    have hmem : g d ∈ Set.range f := by
      rw [h]
      exact ⟨d, rfl⟩
    obtain ⟨c, hc⟩ := hmem
    exact ⟨i, c, by rwa [hc]⟩

theorem exists_finite_subfield_of_finset {K L : Type} [Field K] [Finite K] [Field L]
    [Algebra K L] [Algebra.IsAlgebraic K L] (S : Finset L) :
    ∃ E : Subfield L, Finite E ∧ (S : Set L) ⊆ E ∧ Set.range (algebraMap K L) ⊆ E := by
  let F := IntermediateField.adjoin K (S : Set L)
  have : FiniteDimensional K F := IntermediateField.finiteDimensional_adjoin
    fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  have hF : Finite F := Module.finite_of_finite K
  refine ⟨F.toSubfield, hF, IntermediateField.subset_adjoin K _, ?_⟩
  rintro _ ⟨a, rfl⟩
  exact F.algebraMap_mem a

theorem ringChar_ne_two_of_two_ne_zero {F : Type*} [Field F] (h : (2 : F) ≠ 0) :
    ringChar F ≠ 2 := by
  intro h2
  apply h
  have h0 := ringChar.Nat.cast_ringChar (R := F)
  rw [h2] at h0
  exact_mod_cast h0

section Frobenius

variable {τ : Tag} {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L]

theorem exists_subfieldFrobenius_data
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (E : Subfield L) [Finite E] (hKE : Set.range (algebraMap K L) ⊆ E) :
    ∃ σE : E ≃+* E, (∀ e : E, (σE e : L) = Fr e) ∧
      (fixedFieldImage τ σE).map (baseChangeGL E.subtype) =
        (adjointGroup τ K).map (baseChangeGL (algebraMap K L)) ∧
      ∀ y ∈ adjointGroup τ E,
        Units.map (entrywiseHom Fr) (baseChangeGL E.subtype y) = baseChangeGL E.subtype y →
          y ∈ entrywiseFixedGroup τ σE := by
  have : Fintype K := Fintype.ofFinite K
  have hFrE : ∀ x ∈ E, Fr x ∈ E := fun x hx => by
    rw [hFr]
    exact pow_mem hx _
  let f : E →+* E := Fr.restrict E E hFrE
  let σE : E ≃+* E := RingEquiv.ofBijective f (Finite.injective_iff_bijective.1 f.injective)
  have hσE : ∀ e : E, (σE e : L) = Fr e := fun _ => rfl
  have hcomp : E.subtype.comp σE.toRingHom = Fr.comp E.subtype := RingHom.ext fun e => hσE e
  refine ⟨σE, hσE, ?_, fun y hy hfix => ⟨hy, ?_⟩⟩
  · rw [fixedFieldImage, Subgroup.map_map]
    have e1 : (baseChangeGL E.subtype).comp (baseChangeGL (fixSubfield σE).subtype) =
        baseChangeGL (τ := τ) (E.subtype.comp (fixSubfield σE).subtype) :=
      MonoidHom.ext fun g => baseChangeGL_baseChangeGL _ _ g
    rw [e1]
    apply map_adjointGroup_baseChangeGL_eq_of_range_eq
    ext x
    constructor
    · rintro ⟨⟨e, he⟩, rfl⟩
      have he' : σE e = e := he
      have hpow : (e : L) ^ Nat.card K = e := by
        rw [← hFr, ← hσE, he']
      exact mem_range_algebraMap_of_pow_card_eq hpow
    · rintro ⟨a, rfl⟩
      refine ⟨⟨⟨algebraMap K L a, hKE ⟨a, rfl⟩⟩, Subtype.ext ?_⟩, rfl⟩
      change (σE ⟨algebraMap K L a, hKE ⟨a, rfl⟩⟩ : L) = algebraMap K L a
      rw [hσE, hFr, ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]
  · show Units.map (entrywiseHom σE.toRingHom) y = y
    apply baseChangeGL_injective E.subtype
    change baseChangeGL E.subtype (baseChangeGL σE.toRingHom y) = baseChangeGL E.subtype y
    rw [baseChangeGL_baseChangeGL, hcomp, ← baseChangeGL_baseChangeGL]
    exact hfix

end Frobenius

theorem exceptional_Lang_Frobenius_fixed_derived_root_group
    (τ : Tag) (K : Type) [Field K]
    [Finite K] (hK : Odd (Nat.card K)) (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L]
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K) :
    (∃ F : MulAut (adjointGroup τ L), ∀ g : adjointGroup τ L,
      (F g : ModGL τ L) = Units.map (entrywiseHom Fr) (g : ModGL τ L)) ∧
    (adjointGroup τ K).map (baseChangeGL (algebraMap K L)) ≤
      adjointGroup τ L ⊓ (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) ∧
    adjointGroup τ L ⊓ (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) ≤
      Subgroup.normalizer
        ((adjointGroup τ K).map (baseChangeGL (algebraMap K L)) : Set (ModGL τ L)) ∧
    ⁅adjointGroup τ L ⊓ (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _),
        adjointGroup τ L ⊓ (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _)⁆ =
      (adjointGroup τ K).map (baseChangeGL (algebraMap K L)) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Algebra.IsAlgebraic K L := IsAlgClosure.isAlgebraic
  have hK2 : ringChar K ≠ 2 := by
    intro h2
    have h := (FiniteField.even_card_iff_char_two (F := K)).1 h2
    rw [Nat.card_eq_fintype_card, Nat.odd_iff] at hK
    omega
  have hL2 : (2 : L) ≠ 0 := by
    rw [← map_ofNat (algebraMap K L) 2]
    exact (map_ne_zero _).2 (Ring.two_ne_zero hK2)
  have hE2 : ∀ E : Subfield L, ringChar E ≠ 2 := fun E =>
    ringChar_ne_two_of_two_ne_zero fun h => hL2 (by
      have := congrArg E.subtype h
      rwa [map_ofNat, map_zero] at this)
  set σ : L ≃+* L := RingEquiv.ofBijective Fr (frobenius_bijective (k := K) Fr hFr) with hσ
  have hσFr : σ.toRingHom = Fr := RingHom.ext fun _ => rfl
  set H := (adjointGroup τ K).map (baseChangeGL (algebraMap K L)) with hH
  set R := adjointGroup τ L ⊓ (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) with hR
  have hHR : H ≤ R := by
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨baseChangeGL_mem_adjointGroup _ hg,
      units_map_entrywiseHom_baseChangeGL_algebraMap Fr hFr g⟩
  have hconj : ∀ r ∈ R, ∀ h ∈ H, r * h * r⁻¹ ∈ H := by
    intro r hr h hh
    obtain ⟨S, hS⟩ := exists_finset_descent hr.1
    obtain ⟨E, hEf, hSE, hKE⟩ := exists_finite_subfield_of_finset (K := K) S
    obtain ⟨y, hy, rfl⟩ := hS E hSE
    obtain ⟨σE, -, hJ, hfix⟩ := exists_subfieldFrobenius_data (τ := τ) Fr hFr E hKE
    rw [← hH] at hJ
    have hyΓ := hfix y hy hr.2
    obtain ⟨-, -, -, hJΓ, -, hnormal, -, -⟩ :=
      Chevalley_coordinate_field_fixed_structure τ E (hE2 E) σE
    rw [← hJ] at hh ⊢
    obtain ⟨j, hj, rfl⟩ := hh
    have hmem := hnormal.conj_mem ⟨j, hJΓ hj⟩ (Subgroup.mem_subgroupOf.2 hj) ⟨y, hyΓ⟩
    refine ⟨y * j * y⁻¹, Subgroup.mem_subgroupOf.1 hmem, ?_⟩
    rw [map_mul, map_mul, map_inv]
  have hnorm : R ≤ Subgroup.normalizer (H : Set (ModGL τ L)) := by
    intro r hr
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨hconj r hr h, fun h' => ?_⟩
    have := hconj r⁻¹ (inv_mem hr) _ h'
    rwa [inv_inv, show r⁻¹ * (r * h * r⁻¹) * r = h by group] at this
  have hder : ⁅R, R⁆ = H := by
    refine le_antisymm ?_ ?_
    · rw [Subgroup.commutator_le]
      intro r hr s hs
      obtain ⟨S₁, hS₁⟩ := exists_finset_descent hr.1
      obtain ⟨S₂, hS₂⟩ := exists_finset_descent hs.1
      obtain ⟨E, hEf, hSE, hKE⟩ := exists_finite_subfield_of_finset (K := K) (S₁ ∪ S₂)
      rw [Finset.coe_union, Set.union_subset_iff] at hSE
      obtain ⟨y, hy, rfl⟩ := hS₁ E hSE.1
      obtain ⟨z, hz, rfl⟩ := hS₂ E hSE.2
      obtain ⟨σE, -, hJ, hfix⟩ := exists_subfieldFrobenius_data (τ := τ) Fr hFr E hKE
      rw [← hH] at hJ
      obtain ⟨-, -, -, -, -, -, -, hcomm⟩ :=
        Chevalley_coordinate_field_fixed_structure τ E (hE2 E) σE
      rw [← hJ, ← map_commutatorElement]
      refine Subgroup.mem_map_of_mem _ ?_
      rw [← hcomm]
      exact Subgroup.commutator_mem_commutator (hfix y hy hr.2) (hfix z hz hs.2)
    · have hperf : ⁅H, H⁆ = H := by
        rw [hH, ← Subgroup.map_commutator, commutator_adjointGroup_eq_of_ringChar τ K hK2]
      rw [← hperf]
      exact Subgroup.commutator_mono hHR hHR
  refine ⟨⟨mulAutRestrict (adjointGroup τ L) (exactEntrywiseAut τ σ)
    (map_exactEntrywiseAut σ (Or.inl rfl)), fun g => ?_⟩, hHR, hnorm, hder⟩
  rw [coe_mulAutRestrict, exactEntrywiseAut_apply, hσFr]

end CFSG.LieType.Chevalley
