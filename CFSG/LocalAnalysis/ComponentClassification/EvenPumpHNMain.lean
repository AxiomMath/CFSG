module

public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpHNSpor
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafL34Fixed
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafL34Swap

public section

namespace CFSG.ComponentClassification.EvenPump

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf

theorem hnNotProperFixedLeaf_of_clauses
    (hGLS : GLS3OddLieAutComponentsInput) (hO : LieOrderFormulasInput)
    (hEO : EvenLieOuterTwoComponentsInput) (hspor : HNSporadicClause) :
    HNNotProperFixedLeaf := by
  intro S _ _ hs hna hcat σ P h
  have : IsSimpleGroup S := hs
  have hodd : OddLieType S → ¬ IsHNType (P ⧸ Open.fusionZStar P) := fun ho =>
    not_isHNType_of_properFixedComponent_oddLie hGLS hO hna ho h
  rcases (Milestones.ct_catalog_nonabelian_type_partition S hna).mp hcat with
    ⟨n, hn, ⟨θ⟩⟩ | ho | he | hsp
  · exact not_isHNType_of_properFixedComponent_alternating hn θ h
  · exact hodd ho
  · rcases not_isHNType_of_properFixedComponent_evenLie hEO hO hna he h with hnh | hU
    · exact hnh
    rcases hU with ho | ⟨n, -, h7, ⟨θ⟩⟩ | hL | hH
    · exact hodd ho
    · exact not_isHNType_of_properFixedComponent_alternating (by omega) θ h
    · intro hH
      have h1 := card_dvd_of_fusionZStar_equiv (Equiv.refl (P ⧸ Open.fusionZStar P))
      rw [card_of_isHNType hH, card_of_isL34Type hL] at h1
      norm_num at h1
    · obtain ⟨eH⟩ := hH
      exact not_isHNType_of_properFixedComponent_held eH h
  · exact hspor S hna hsp σ P h

@[expose] def HNPumpInput : Prop :=
  ∀ (H : Type) [Group H] [Finite H], SectionRank.IsKGroupCat H →
    ∀ M : Subgroup H, IsPComponent 2 M →
    ∀ x : H, orderOf x = 2 → x ∈ normalizer (M : Set H) →
    ∀ T : Subgroup H, T ≤ M → T ≤ centralizer ({x} : Set H) →
      IsPComponent 2 (T.subgroupOf (centralizer ({x} : Set H))) →
      Nonempty (T ⧸ Open.fusionZStar T ≃* NativeSporadic.Carrier .HN) →
      Nonempty (M ⧸ Open.fusionZStar M ≃* NativeSporadic.Carrier .HN)

theorem hnPumpInput_of_leaf (hleaf : HNNotProperFixedLeaf) : HNPumpInput := by
  intro H _ _ hK M hM x hx hxN T hTM hTC hTpc ⟨eT⟩
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMx : conjugate M x = M := mem_normalizer_iff_map_conj_eq.mp (inv_mem hxN)
  have hTC' : T ≤ (M ⊔ conjugate M x) ⊓ centralizer ({x} : Set H) := by
    rw [hMx, sup_idem]
    exact le_inf hTM hTC
  have hTpc' : IsPComponent 2 (T.subgroupOf ((M ⊔ conjugate M x) ⊓ centralizer ({x} : Set H))) :=
    CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hTC' inf_le_right hTpc
  obtain ⟨hle, -, heq⟩ := UnbalancedGS.involution_orbit_fixed_component_quotient_comparison hx M
    hM _ rfl _ rfl T hTC' hTpc'
  have : Group.IsPerfect T := by
    have := CatalogueBHeldSmallCore.pComponent_perfect 2 _ hTpc
    exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hTC).toMonoidHom)
      (subgroupOfEquivOfLe hTC).surjective
  have hTq : IsQuasisimple (T ⧸ pPrimeCore 2 T) :=
    CatalogueBPrimeJoin.quasisimple_primeCore_quotient_of_equiv 2 (subgroupOfEquivOfLe hTC)
      (CatalogueBHeldSmallCore.pComponent_coreQuotient_quasisimple 2 _ hTpc)
  rcases hle.lt_or_eq with hlt | hidx
  swap
  ·
    obtain ⟨e⟩ := stable_case_type hM hTM hTq ((heq hidx).2 hMx.symm)
    exact ⟨e.symm.trans eT⟩
  have hTM' : T ≤ M ⊓ centralizer ({x} : Set H) := le_inf hTM hTC
  have hTp' : IsPComponent 2 (T.subgroupOf (M ⊓ centralizer ({x} : Set H))) :=
    CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hTM' inf_le_right hTpc
  obtain ⟨σ, hPF, ⟨eP⟩⟩ := exists_properFixedComponent_of_stable_image hx hM hMx hTM' hTp' hlt
  have hMq : IsQuasisimple (↥M ⧸ pPrimeCore 2 ↥M) :=
    ((CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 M).mp hM).2.2
  have : IsSimpleGroup ((↥M ⧸ pPrimeCore 2 ↥M) ⧸ center (↥M ⧸ pPrimeCore 2 ↥M)) := hMq.2.1
  have hcat : Blueprint.Catalog ((↥M ⧸ pPrimeCore 2 ↥M) ⧸ center (↥M ⧸ pPrimeCore 2 ↥M)) :=
    SectionRank.catalog_of_isKGroupCat_of_surjective hK M
      ((QuotientGroup.mk' (center (↥M ⧸ pPrimeCore 2 ↥M))).comp
        (QuotientGroup.mk' (pPrimeCore 2 ↥M)))
      ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))
  exact (hleaf _ inferInstance hMq.2.2 hcat σ _ hPF ⟨eP.symm.trans eT⟩).elim

end CFSG.ComponentClassification.EvenPump
