module

public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpA10Defs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafL34Fixed
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafL34Swap

public section

namespace CFSG.ComponentClassification.EvenPump

open CFSG Subgroup CFSG.ComponentClassification.CatLeaf

@[expose] def A10PumpInput : Prop :=
  ∀ (H : Type) [Group H] [Finite H], SectionRank.IsKGroupCat H →
    ∀ M : Subgroup H, IsPComponent 2 M →
    ∀ x : H, orderOf x = 2 → x ∈ normalizer (M : Set H) →
    ∀ T : Subgroup H, T ≤ M → T ≤ centralizer ({x} : Set H) →
      IsPComponent 2 (T.subgroupOf (centralizer ({x} : Set H))) →
      Nonempty (T ⧸ Open.fusionZStar T ≃* alternatingGroup (Fin 10)) →
      (∃ n : ℕ, 10 ≤ n ∧ Nonempty (M ⧸ Open.fusionZStar M ≃* alternatingGroup (Fin n))) ∨
        Nonempty (M ⧸ Open.fusionZStar M ≃* Blueprint.NativeSporadic.Carrier .HN)

theorem a10PumpInput_of_leaf (hleaf : A10PumpLeaf) : A10PumpInput := by
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
    exact Or.inl ⟨10, le_rfl, ⟨e.symm.trans eT⟩⟩
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
  obtain ⟨eMS⟩ := GrSLit.nonempty_quotient_center_equiv_fusionZStar ↥M
  rcases hleaf _ inferInstance hMq.2.2 hcat σ _ hPF ⟨eP.symm.trans eT⟩ with
    ⟨n, hn, ⟨eS⟩⟩ | ⟨⟨eS⟩⟩
  · exact Or.inl ⟨n, hn, ⟨eMS.symm.trans eS⟩⟩
  · exact Or.inr ⟨eMS.symm.trans eS⟩

end CFSG.ComponentClassification.EvenPump
