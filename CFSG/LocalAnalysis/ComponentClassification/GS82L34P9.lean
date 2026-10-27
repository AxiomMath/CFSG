module

public import CFSG.LocalAnalysis.ComponentClassification.GS82L34P9Leaf
public import CFSG.LocalAnalysis.ComponentClassification.GS82L34P9Fixed
import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKFixed
import CFSG.LocalAnalysis.ComponentClassification.CatLeafL34Swap
public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpInputs

public section

namespace CFSG.ComponentClassification.GS82PumpInputs

open CFSG Subgroup CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem l34ExpFourPumpInput_of_fixedLeaf (h : L34ExpFourFixedLeaf) : L34ExpFourPumpInput := by
  intro H _ _ hK M hM x hx hxN T hTM hTC hTpc hTY hTE
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
  rcases hle.lt_or_eq with hlt | hidx
  swap
  ·
    have : Group.IsPerfect T := by
      have := CatalogueBHeldSmallCore.pComponent_perfect 2 _ hTpc
      exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hTC).toMonoidHom)
        (subgroupOfEquivOfLe hTC).surjective
    have hTq : IsQuasisimple (T ⧸ pPrimeCore 2 T) :=
      CatalogueBPrimeJoin.quasisimple_primeCore_quotient_of_equiv 2 (subgroupOfEquivOfLe hTC)
        (CatalogueBHeldSmallCore.pComponent_coreQuotient_quasisimple 2 _ hTpc)
    obtain ⟨e⟩ := stable_case_type hM hTM hTq ((heq hidx).2 hMx.symm)
    exact Or.inl (Blueprint.LieModel.of_mulEquiv ((Sol78.coreQuotientCenterEquiv T).trans e) hTY)
  have hx2 : x * x = 1 := by rw [← pow_two, ← hx, pow_orderOf_eq_one]
  set c : MulAut M := M.normalizerMonoidHom ⟨x, hxN⟩ with hcdef
  have hcapp : ∀ y : M, ((c y : M) : H) = x * y * x⁻¹ := fun y => rfl
  have hc2 : ∀ y, c (c y) = y := by
    intro y
    apply Subtype.ext
    rw [hcapp, hcapp]
    calc x * (x * (y : H) * x⁻¹) * x⁻¹ = (x * x) * y * (x * x)⁻¹ := by group
      _ = y := by rw [hx2]; group
  have hfixC : fixedSubgroup c = (M ⊓ centralizer ({x} : Set H)).subgroupOf M := by
    ext y
    rw [LocalAnalysis.ComponentInitial.mem_fixedSubgroup_iff, mem_subgroupOf, mem_inf,
      mem_centralizer_singleton_iff]
    constructor
    · intro hy
      have h1 := congrArg Subtype.val hy
      rw [hcapp] at h1
      refine ⟨y.2, ?_⟩
      calc (y : H) * x = x * y * x⁻¹ * x := by rw [h1]
        _ = x * y := by group
    · rintro ⟨-, hy⟩
      apply Subtype.ext
      rw [hcapp]
      calc x * (y : H) * x⁻¹ = y * x * x⁻¹ := by rw [hy]
        _ = y := by group
  have hTM' : T ≤ M ⊓ centralizer ({x} : Set H) := le_inf hTM hTC
  have hTp : IsPComponent 2 (T.subgroupOf (M ⊓ centralizer ({x} : Set H))) :=
    CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hTM' inf_le_right hTpc
  set T' := T.subgroupOf M with hT'def
  have hT'C : T' ≤ fixedSubgroup c := by
    rw [hfixC]
    intro y hy
    rw [mem_subgroupOf] at hy ⊢
    exact hTM' hy
  have hT'p : IsPComponent 2 (T'.subgroupOf (fixedSubgroup c)) := by
    rw [hfixC]
    exact (UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' (L := T) inf_le_left 2
      Nat.prime_two).mpr hTp
  let eT : T ≃* T' := (subgroupOfEquivOfLe hTM).symm
  have hlt' : (pPrimeCore 2 T').index < (pPrimeCore 2 M).index := by
    rw [index_eq_card, index_eq_card,
      ← UnbalancingLocal.Correspondence.card_quotient_pPrimeCore_congr eT, ← index_eq_card,
      ← index_eq_card]
    exact hlt
  have hMq : IsQuasisimple (M ⧸ pPrimeCore 2 M) :=
    ((CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 M).mp hM).2.2
  obtain ⟨σ, P, hσ, hPF, hP, hPne, f, hf, hfk, -⟩ :=
    GrSLit.HeK.exists_quasisimple_fixed_component c hc2 hT'C hT'p hlt'
  set F : T →* P := f.comp eT.toMonoidHom with hFdef
  have hF : Function.Surjective F := hf.comp eT.surjective
  have hFk : ¬ 2 ∣ Nat.card F.ker := by
    let g : F.ker →* f.ker := (eT.toMonoidHom.comp F.ker.subtype).codRestrict f.ker fun k => k.2
    have hg : Function.Injective g := fun k₁ k₂ hk => by
      have h' := congrArg (fun y : f.ker => (y : T')) hk
      exact Subtype.ext (eT.injective h')
    exact fun h2 => hfk (h2.trans (Subgroup.card_dvd_of_injective g hg))
  obtain ⟨eTP⟩ := GSThmB.OddQuot.nonempty_pPrimeCore_equiv_of_surjective F hF hFk
  have hPY : GH74.GLS.IsL34Quotient (↥P ⧸ pPrimeCore 2 ↥P) :=
    Blueprint.LieModel.of_mulEquiv (Sol78.centerQuotCongr eTP) hTY
  have hPE : ¬ IsElementaryAbelian 2 ↥(center (↥P ⧸ pPrimeCore 2 ↥P)) := fun hE =>
    hTE (IsElementaryAbelian.of_mulEquiv (Subgroup.centerCongr eTP).symm hE)
  have : IsSimpleGroup ((↥M ⧸ pPrimeCore 2 ↥M) ⧸ center (↥M ⧸ pPrimeCore 2 ↥M)) := hMq.2.1
  have hcat : Blueprint.Catalog ((↥M ⧸ pPrimeCore 2 ↥M) ⧸ center (↥M ⧸ pPrimeCore 2 ↥M)) :=
    SectionRank.catalog_of_isKGroupCat_of_surjective hK M
      ((QuotientGroup.mk' (center (↥M ⧸ pPrimeCore 2 ↥M))).comp
        (QuotientGroup.mk' (pPrimeCore 2 ↥M)))
      ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))
  obtain ⟨⟨eON⟩, hcyc, hcard⟩ := h _ hMq (GrSLit.HeK.isPGroup_center_quotient M) hcat σ hσ P
    hPF hP hPne hPY hPE
  obtain ⟨eMS⟩ := GrSLit.nonempty_quotient_center_equiv_fusionZStar ↥M
  exact Or.inr ⟨⟨eMS.symm.trans eON⟩, (MulEquiv.isCyclic (Subgroup.centerCongr eTP)).mpr hcyc,
    (Nat.card_congr (Subgroup.centerCongr eTP).toEquiv).trans hcard⟩

theorem l34ExpFourPumpInput_holds :
    L34ExpFourPumpInput :=
  l34ExpFourPumpInput_of_fixedLeaf (l34ExpFourFixedLeaf_of_pumpLeaf l34ExpFourPumpLeaf_holds)

end CFSG.ComponentClassification.GS82PumpInputs
