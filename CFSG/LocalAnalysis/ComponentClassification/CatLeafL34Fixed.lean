module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic

public section

namespace CFSG.ComponentClassification.CatLeaf

open CFSG Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem exists_properFixedComponent_of_stable_image {G : Type*} [Group G] [Finite G] {a : G}
    (ha : orderOf a = 2) {M T : Subgroup G} (hM : IsPComponent 2 M) (hMa : conjugate M a = M)
    (hTM : T ≤ M ⊓ centralizer ({a} : Set G))
    (hTp : IsPComponent 2 (T.subgroupOf (M ⊓ centralizer ({a} : Set G))))
    (hlt : (pPrimeCore 2 T).index < (pPrimeCore 2 M).index) :
    ∃ σ : MulAut ((M ⧸ pPrimeCore 2 M) ⧸ center (M ⧸ pPrimeCore 2 M)),
      ProperFixedComponent σ (((T.subgroupOf M).map (QuotientGroup.mk' (pPrimeCore 2 M))).map
        (QuotientGroup.mk' (center (M ⧸ pPrimeCore 2 M)))) ∧
      Nonempty (T ⧸ Open.fusionZStar T ≃*
        ↥(((T.subgroupOf M).map (QuotientGroup.mk' (pPrimeCore 2 M))).map
          (QuotientGroup.mk' (center (M ⧸ pPrimeCore 2 M)))) ⧸
        Open.fusionZStar ↥(((T.subgroupOf M).map (QuotientGroup.mk' (pPrimeCore 2 M))).map
          (QuotientGroup.mk' (center (M ⧸ pPrimeCore 2 M))))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have haa : a * a = 1 := by rw [← pow_two, ← ha, pow_orderOf_eq_one]
  have haN : a ∈ normalizer (M : Set G) := by
    rw [mem_normalizer_iff]
    intro y
    rw [← UnbalancedLayer.mem_conjugate_iff, hMa]
  set c : MulAut M := M.normalizerMonoidHom ⟨a, haN⟩ with hcdef
  have hcapp : ∀ x : M, ((c x : M) : G) = a * x * a⁻¹ := fun x => rfl
  have hc : ∀ x, c (c x) = x := by
    intro x
    apply Subtype.ext
    rw [hcapp, hcapp]
    calc a * (a * (x : G) * a⁻¹) * a⁻¹ = (a * a) * x * (a * a)⁻¹ := by group
      _ = x := by rw [haa]; group
  have hfixC : fixedSubgroup c = (M ⊓ centralizer ({a} : Set G)).subgroupOf M := by
    ext x
    rw [LocalAnalysis.ComponentInitial.mem_fixedSubgroup_iff, mem_subgroupOf, mem_inf,
      mem_centralizer_singleton_iff]
    constructor
    · intro hx
      have h1 := congrArg Subtype.val hx
      rw [hcapp] at h1
      refine ⟨x.2, ?_⟩
      calc (x : G) * a = a * x * a⁻¹ * a := by rw [h1]
        _ = a * x := by group
    · rintro ⟨-, hx⟩
      apply Subtype.ext
      rw [hcapp]
      calc a * (x : G) * a⁻¹ = x * a * a⁻¹ := by rw [hx]
        _ = x := by group
  set T' := T.subgroupOf M with hT'def
  have hTM' : T ≤ M := hTM.trans inf_le_left
  have hT'C : T' ≤ fixedSubgroup c := by
    rw [hfixC]
    intro x hx
    rw [mem_subgroupOf] at hx ⊢
    exact hTM hx
  have hT'p : IsPComponent 2 (T'.subgroupOf (fixedSubgroup c)) := by
    rw [hfixC]
    exact (UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' (L := T) inf_le_left 2
      Nat.prime_two).mpr hTp
  let eT : T ≃* T' := (subgroupOfEquivOfLe hTM').symm
  have hlt' : (pPrimeCore 2 T').index < (pPrimeCore 2 M).index := by
    rw [index_eq_card, index_eq_card,
      ← UnbalancingLocal.Correspondence.card_quotient_pPrimeCore_congr eT, ← index_eq_card,
      ← index_eq_card]
    exact hlt
  have hMq : IsQuasisimple (M ⧸ pPrimeCore 2 M) :=
    ((CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 M).mp hM).2.2
  obtain ⟨σ, -, hσ, hPF, hP, hPne, ⟨e⟩⟩ :=
    GrSLit.exists_simple_fixed_component_image hMq c hc hT'C hT'p hlt'
  obtain ⟨eZ⟩ := GrSLit.nonempty_fusionZStar_equiv_of_mulEquiv' eT
  exact ⟨σ, ⟨hσ, hPF, hP, hPne⟩, ⟨eZ.trans e⟩⟩

theorem exists_properFixedComponent_of_stable {G : Type*} [Group G] [Finite G] {a : G}
    (ha : orderOf a = 2) {M T : Subgroup G} (hM : IsPComponent 2 M) (hMa : conjugate M a = M)
    (hTM : T ≤ M ⊓ centralizer ({a} : Set G))
    (hTp : IsPComponent 2 (T.subgroupOf (M ⊓ centralizer ({a} : Set G))))
    (hlt : (pPrimeCore 2 T).index < (pPrimeCore 2 M).index) :
    ∃ (σ : MulAut ((M ⧸ pPrimeCore 2 M) ⧸ center (M ⧸ pPrimeCore 2 M)))
      (P : Subgroup ((M ⧸ pPrimeCore 2 M) ⧸ center (M ⧸ pPrimeCore 2 M))),
      ProperFixedComponent σ P ∧ Nonempty (T ⧸ Open.fusionZStar T ≃* P ⧸ Open.fusionZStar P) := by
  obtain ⟨σ, h, he⟩ := exists_properFixedComponent_of_stable_image ha hM hMa hTM hTp hlt
  exact ⟨σ, _, h, he⟩

end CFSG.ComponentClassification.CatLeaf
