module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafSporOrder
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafAlt
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafAutCore
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitFixedHe
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixA
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixB
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUSporadic
public import CFSG.Sporadic.FischerOddCore.Fi24Block

public section

namespace CFSG.ComponentClassification.CatLeaf

open CFSG Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.Sporadic.FischerOddCore

theorem oddCore_fixedSubgroup_eq_bot_of_mulAut {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a)
    (h : ∀ i : MulAut S, orderOf i = 2 → CFSG.oddCore (centralizer ({i} : Set (MulAut S))) = ⊥)
    {σ : MulAut S} (hσ : orderOf σ = 2) : CFSG.oddCore (fixedSubgroup σ) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hκ := mulAut_conj_injective_of_simple hna
  set C := centralizer ({σ} : Set (MulAut S)) with hCdef
  have hconj : ∀ s : S, MulAut.conj (σ s) = σ * MulAut.conj s * σ⁻¹ := by
    intro s
    apply MulEquiv.ext
    intro y
    simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply]
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  have hmem : ∀ s : S, MulAut.conj s ∈ C ↔ σ s = s := by
    intro s
    rw [hCdef, mem_centralizer_singleton_iff]
    constructor
    · intro hs
      apply hκ
      rw [hconj, ← hs, mul_inv_cancel_right]
    · intro hs
      have h1 := hconj s
      rw [hs] at h1
      calc MulAut.conj s * σ = σ * MulAut.conj s * σ⁻¹ * σ := by rw [← h1]
        _ = σ * MulAut.conj s := by group
  let φ : fixedSubgroup σ →* C :=
    ((MulAut.conj : S →* MulAut S).comp (fixedSubgroup σ).subtype).codRestrict C
    fun x => (hmem x).mpr x.2
  have hφ : Function.Injective φ := fun x y hxy =>
    Subtype.ext (hκ (congrArg (fun z : C => (z : MulAut S)) hxy))
  have hrange : φ.range = (OuterAutomorphisms.inner S).subgroupOf C := by
    ext c
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, rfl⟩
    · rintro ⟨s, hs⟩
      have hsC : MulAut.conj s ∈ C := hs ▸ c.2
      exact ⟨⟨s, (hmem s).mp hsC⟩, Subtype.ext hs⟩
  have hN : ((OuterAutomorphisms.inner S).subgroupOf C).Normal := by
    have := OuterAutomorphisms.inner_normal S
    infer_instance
  have hcore := CatalogueBHeldSmallCore.primeCore_subnormal_intersection 2
    ((OuterAutomorphisms.inner S).subgroupOf C) hN.isSubnormal
  have hC2 : pPrimeCore 2 C = ⊥ := by
    rw [← Sporadic.HeldB.oddCore_eq_pPrimeCore_two']
    exact h σ hσ
  rw [hC2, bot_subgroupOf] at hcore
  let e : fixedSubgroup σ ≃* ((OuterAutomorphisms.inner S).subgroupOf C) :=
    (MonoidHom.ofInjective hφ).trans (MulEquiv.subgroupCongr hrange)
  apply Sporadic.HeldB.oddCore_eq_bot_of_mulEquiv e
  rw [Sporadic.HeldB.oddCore_eq_pPrimeCore_two']
  exact hcore

theorem mulAut_oddCore_eq_bot_of_sporadicOddCoreFree {s : TauCeti.SporadicName}
    (hs : CatalogueU.SporadicOddCoreFree s) {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Carrier s) (i : MulAut S)
    (hi : orderOf i = 2) : CFSG.oddCore (centralizer ({i} : Set (MulAut S))) = ⊥ := by
  have hF := generalizedFitting_mulAut_eq_range hna
  have hκ := mulAut_conj_injective_of_simple hna
  let eI : CFSG.generalizedFitting (MulAut S) ≃* S :=
    (MulEquiv.subgroupCongr hF).trans (MonoidHom.ofInjective hκ).symm
  have : IsSimpleGroup (CFSG.generalizedFitting (MulAut S)) := eI.isSimpleGroup
  have hnc : ∃ a b : CFSG.generalizedFitting (MulAut S), a * b ≠ b * a := by
    obtain ⟨x, y, hxy⟩ := hna
    exact ⟨eI.symm x, eI.symm y, fun h => hxy (eI.symm.injective (by rw [map_mul, map_mul, h]))⟩
  exact hs (MulAut S) inferInstance hnc ⟨eI.trans e⟩ i hi

theorem not_isHeldType_of_properFixedComponent_held {S : Type} [Group S] [Finite S]
    [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.He)
    {σ : MulAut S} {P : Subgroup S} (h : ProperFixedComponent σ P) :
    ¬ GrSLit.IsHeldType (P ⧸ Open.fusionZStar P) := by
  rintro ⟨eH⟩
  obtain ⟨hσ, hPF, hP, hPne⟩ := h
  have hcardP : Nat.card (P ⧸ Open.fusionZStar P) = 4030387200 := by
    rw [Nat.card_congr eH.toEquiv, Sporadic.He.card_He]
  rcases GrSLit.simpleFixedComponents_held GrSLit.HeldFix.isL34Type_of_isPComponent_centralizer_heA0
      GrSLit.HeldFix.not_isPComponent_centralizer_heT1P S
      inferInstance hna ⟨e⟩ σ hσ P hPF hP hPne with hL | hA
  · rw [card_of_isL34Type hL] at hcardP
    norm_num at hcardP
  · obtain ⟨eA⟩ := hA
    rw [Nat.card_congr eA.toEquiv, nat_card_alternatingGroup, Nat.card_fin] at hcardP
    norm_num [Nat.factorial] at hcardP

theorem not_isHeldType_of_properFixedComponent_fi24
    (hFi : RestrictedStd.Spor.Fi24primeOuterComponentsInput) {S : Type} [Group S] [Finite S]
    [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Fi24prime)
    {σ : MulAut S} {P : Subgroup S} (h : ProperFixedComponent σ P) :
    ¬ GrSLit.IsHeldType (P ⧸ Open.fusionZStar P) := by
  rintro ⟨eH⟩
  have hσ1 := h.ne_one
  have hσ2 : orderOf σ = 2 := orderOf_eq_prime (by
    rw [sq]; exact MulEquiv.ext fun y => h.1 y) hσ1
  have hfree : CatalogueU.SporadicOddCoreFree .Fi24Prime := fun X _ _ hF _ hJ t ht =>
    (CTUC_Fi24prime_generalized_Fitting_involution_centralizer_odd_core_trivial
      hF hJ).2 t ht
  have hcore := oddCore_fixedSubgroup_eq_bot_of_mulAut hna
    (mulAut_oddCore_eq_bot_of_sporadicOddCoreFree hfree hna e) hσ2
  obtain ⟨hcomp, ⟨eZ⟩⟩ := h.isComponent_of_oddCore hcore
  set L := P.subgroupOf (fixedSubgroup σ) with hLdef
  have hcardL : Nat.card (L ⧸ center L) = 4030387200 := by
    rw [← Nat.card_congr eZ.toEquiv, Nat.card_congr eH.toEquiv, Sporadic.He.card_He]
  rcases exists_conj_or_not_mem_range σ with ⟨t, ht⟩ | hout
  ·
    obtain ⟨ht2, -, -, -⟩ := h.inner hna ht
    have hfix : fixedSubgroup σ = centralizer ({t} : Set S) := by
      rw [ht]
      ext x
      rw [mem_centralizer_singleton_iff]
      change t * x * t⁻¹ = x ↔ x * t = t * x
      rw [mul_inv_eq_iff_eq_mul]
      exact eq_comm
    let φ := MulEquiv.subgroupCongr hfix
    have hB : IsComponent (L.map φ.toMonoidHom) :=
      ⟨(LocalAnalysis.ComponentInitial.isQuasisimple_congr
        (L.equivMapOfInjective φ.toMonoidHom φ.injective)).1 hcomp.1,
        Subgroup.IsSubnormal.map (f := φ.toMonoidHom) φ.surjective hcomp.2⟩
    have h1 :=
      (CTI_Fi24prime_involution_local_components_simple_quotient_divisible_by_eleven e t ht2 _
        hB).1
    rw [← card_quotient_center_congr (L.equivMapOfInjective φ.toMonoidHom φ.injective),
      hcardL] at h1
    norm_num at h1
  ·
    have hfix : Sporadic.Schreier.fixSub σ = fixedSubgroup σ := by
      ext x
      exact Iff.rfl
    let φ := MulEquiv.subgroupCongr hfix.symm
    have hB : IsComponent (L.map φ.toMonoidHom) :=
      ⟨(LocalAnalysis.ComponentInitial.isQuasisimple_congr
        (L.equivMapOfInjective φ.toMonoidHom φ.injective)).1 hcomp.1,
        Subgroup.IsSubnormal.map (f := φ.toMonoidHom) φ.surjective hcomp.2⟩
    have h1 := hFi S ⟨e⟩ σ (MulEquiv.ext fun y => h.1 y) hout _ hB
    rw [← card_quotient_center_congr (L.equivMapOfInjective φ.toMonoidHom φ.injective),
      hcardL] at h1
    norm_num at h1

theorem not_isHeldType_of_properFixedComponent_monster (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) (oM : CatalogueU.SporadicOddCoreFree .M)
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a)
    (e : S ≃* NativeSporadic.M) {σ : MulAut S} {P : Subgroup S} (h : ProperFixedComponent σ P) :
    ¬ GrSLit.IsHeldType (P ⧸ Open.fusionZStar P) := by
  rintro ⟨eH⟩
  have hσ1 := h.ne_one
  have hσ2 : orderOf σ = 2 := orderOf_eq_prime (by
    rw [sq]; exact MulEquiv.ext fun y => h.1 y) hσ1
  have hcore := oddCore_fixedSubgroup_eq_bot_of_mulAut hna
    (mulAut_oddCore_eq_bot_of_sporadicOddCoreFree oM hna e) hσ2
  obtain ⟨hcomp, ⟨eZ⟩⟩ := h.isComponent_of_oddCore hcore
  set L := P.subgroupOf (fixedSubgroup σ) with hLdef
  have hcardL : Nat.card (L ⧸ center L) = 4030387200 := by
    rw [← Nat.card_congr eZ.toEquiv, Nat.card_congr eH.toEquiv, Sporadic.He.card_He]
  obtain ⟨t, ht⟩ := hMinn S inferInstance ⟨e⟩ σ
  obtain ⟨ht2, -, -, -⟩ := h.inner hna ht.symm
  have hfix : fixedSubgroup σ = centralizer ({t} : Set S) := by
    rw [← ht]
    ext x
    rw [mem_centralizer_singleton_iff]
    change t * x * t⁻¹ = x ↔ x * t = t * x
    rw [mul_inv_eq_iff_eq_mul]
    exact eq_comm
  let φ := MulEquiv.subgroupCongr hfix
  have hB : IsComponent (L.map φ.toMonoidHom) :=
    ⟨(LocalAnalysis.ComponentInitial.isQuasisimple_congr
      (L.equivMapOfInjective φ.toMonoidHom φ.injective)).1 hcomp.1,
      Subgroup.IsSubnormal.map (f := φ.toMonoidHom) φ.surjective hcomp.2⟩
  have h1 := (hMcomp S inferInstance ⟨e⟩ t ht2 _ hB).1
  rw [← card_quotient_center_congr (L.equivMapOfInjective φ.toMonoidHom φ.injective),
    hcardL] at h1
  norm_num at h1

theorem not_isHeldType_of_properFixedComponent_sporadic
    (hFi : RestrictedStd.Spor.Fi24primeOuterComponentsInput) (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) (oM : CatalogueU.SporadicOddCoreFree .M)
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a)
    (hspor : NativeSporadic.SporadicRep S) {σ : MulAut S} {P : Subgroup S}
    (h : ProperFixedComponent σ P) : ¬ GrSLit.IsHeldType (P ⧸ Open.fusionZStar P) := by
  obtain ⟨s, ⟨e⟩⟩ := hspor
  by_cases hHe : s = .He
  · subst hHe
    exact not_isHeldType_of_properFixedComponent_held hna e h
  by_cases hFi24 : s = .Fi24Prime
  · subst hFi24
    exact not_isHeldType_of_properFixedComponent_fi24 hFi hna e h
  by_cases hM : s = .M
  · subst hM
    exact not_isHeldType_of_properFixedComponent_monster hMinn hMcomp oM hna e h
  exact not_isHeldType_of_properFixedComponent_sporadic_order hHe hFi24 hM e h

end CFSG.ComponentClassification.CatLeaf
