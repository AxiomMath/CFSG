module

public import CFSG.LieType.Chevalley.LangFrobeniusFixedDerived
public import CFSG.LieType.Chevalley.BabyPrereqPerfectAwayFromTwo

public noncomputable section

namespace CFSG.TauCetiBridge.Even

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped commutatorElement

theorem commutator_entrywiseFixedGroup_le
    (τ : Tag) (E : Type) [Field E] [Finite E]
    (σ : E ≃+* E) :
    ⁅entrywiseFixedGroup τ σ, entrywiseFixedGroup τ σ⁆ ≤ fixedFieldImage τ σ := by
  obtain ⟨-, -, -, hJΓ, -, hnormal, hcomm⟩ :=
    Chevalley_coordinate_field_fixed_normal_subgroup τ E σ
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have hq := hcomm (QuotientGroup.mk ⟨a, ha⟩) (QuotientGroup.mk ⟨b, hb⟩)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at hq
  have hmem := Subgroup.mem_subgroupOf.1 hq
  have e : (((⟨a, ha⟩ * ⟨b, hb⟩ : entrywiseFixedGroup τ σ)⁻¹ *
      (⟨b, hb⟩ * ⟨a, ha⟩) : entrywiseFixedGroup τ σ) : ModGL τ E) = b⁻¹ * a⁻¹ * b * a := by
    simp [mul_assoc]
  rw [e] at hmem
  have hinv : (b⁻¹ * a⁻¹ * b * a)⁻¹ ∈ fixedFieldImage τ σ := inv_mem hmem
  have hconj : b * a * (b⁻¹ * a⁻¹ * b * a)⁻¹ * (b * a)⁻¹ ∈ fixedFieldImage τ σ := by
    have := hnormal.conj_mem ⟨_, hJΓ hinv⟩ (Subgroup.mem_subgroupOf.2 hinv)
      (⟨b, hb⟩ * ⟨a, ha⟩)
    simpa [Subgroup.mem_subgroupOf, mul_assoc] using this
  have e2 : b * a * (b⁻¹ * a⁻¹ * b * a)⁻¹ * (b * a)⁻¹ = ⁅a, b⁆ := by
    rw [commutatorElement_def]
    group
  rwa [e2] at hconj

theorem Lang_Frobenius_fixed_derived_of_perfect
    (τ : Tag) (K : Type) [Field K] [Finite K]
    (hperf : ⁅adjointGroup τ K, adjointGroup τ K⁆ = adjointGroup τ K) (L : Type) [Field L]
    [Algebra K L] [IsAlgClosure K L] (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K) :
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
    obtain ⟨-, -, -, hJΓ, -, hnormal, -⟩ :=
      Chevalley_coordinate_field_fixed_normal_subgroup τ E σE
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
      rw [← hJ, ← map_commutatorElement]
      refine Subgroup.mem_map_of_mem _ ?_
      exact commutator_entrywiseFixedGroup_le τ E σE
        (Subgroup.commutator_mem_commutator (hfix y hy hr.2) (hfix z hz hs.2))
    · have hperf' : ⁅H, H⁆ = H := by
        rw [hH, ← Subgroup.map_commutator, hperf]
      rw [← hperf']
      exact Subgroup.commutator_mono hHR hHR
  refine ⟨⟨mulAutRestrict (adjointGroup τ L) (exactEntrywiseAut τ σ)
    (map_exactEntrywiseAut σ (Or.inl rfl)), fun g => ?_⟩, hHR, hnorm, hder⟩
  rw [coe_mulAutRestrict, exactEntrywiseAut_apply, hσFr]

theorem commutator_adjointGroup_eq_of_top (τ : Tag) (K : Type) [Field K]
    (h : commutator (adjointGroup τ K) = ⊤) :
    ⁅adjointGroup τ K, adjointGroup τ K⁆ = adjointGroup τ K := by
  rw [commutator_def] at h
  have e := congrArg (Subgroup.map (adjointGroup τ K).subtype) h
  rwa [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at e

theorem commutator_adjointGroup_eq_of_three_le
    (τ : Tag) (K : Type) [Field K] [Finite K]
    (hK : 3 ≤ Nat.card K) : ⁅adjointGroup τ K, adjointGroup τ K⁆ = adjointGroup τ K :=
  commutator_adjointGroup_eq_of_top τ K (generated_group_perfect_away_from_two τ K (by
    rw [ENat.card_eq_coe_natCard]
    exact_mod_cast hK))

theorem commutator_adjointGroup_eq_of_singleEdge
    (τ : Tag) (K : Type) [Field K]
    (hτ : τ = .F4 ∨ τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    ⁅adjointGroup τ K, adjointGroup τ K⁆ = adjointGroup τ K :=
  commutator_adjointGroup_eq_of_top τ K (single_edge_perfect τ K hτ)

end CFSG.TauCetiBridge.Even
