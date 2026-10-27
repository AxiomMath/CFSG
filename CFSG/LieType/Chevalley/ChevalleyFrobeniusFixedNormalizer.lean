module

public import CFSG.LieType.Chevalley.LangFrobeniusFixedDerived

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley

theorem Chevalley_Frobenius_fixed_ambient_normalizer
    (τ : Tag) (K : Type) [Field K] [Finite K]
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ Nat.card K) :
    (∃ F : MulAut (adjointGroup τ L), ∀ g : adjointGroup τ L,
      (F g : ModGL τ L) = Units.map (entrywiseHom Fr) (g : ModGL τ L)) ∧
    (adjointGroup τ K).map (baseChangeGL (algebraMap K L)) ≤
      adjointGroup τ L ⊓ (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) ∧
    adjointGroup τ L ⊓ (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) ≤
      Subgroup.normalizer
        ((adjointGroup τ K).map (baseChangeGL (algebraMap K L)) : Set (ModGL τ L)) := by
  classical
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Algebra.IsAlgebraic K L := IsAlgClosure.isAlgebraic
  set σ : L ≃+* L := RingEquiv.ofBijective Fr (frobenius_bijective (k := K) Fr hFr)
  have hσFr : σ.toRingHom = Fr := RingHom.ext fun _ => rfl
  set H := (adjointGroup τ K).map (baseChangeGL (algebraMap K L)) with hH
  set R := adjointGroup τ L ⊓ (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _)
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
    obtain ⟨-, -, -, hJΓ, -, hnormal, -⟩ := Chevalley_coordinate_field_fixed_normal_subgroup τ E σE
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
  refine ⟨⟨mulAutRestrict (adjointGroup τ L) (exactEntrywiseAut τ σ)
    (map_exactEntrywiseAut σ (Or.inl rfl)), fun g => ?_⟩, hHR, hnorm⟩
  rw [coe_mulAutRestrict, exactEntrywiseAut_apply, hσFr]

end CFSG.LieType.Chevalley
