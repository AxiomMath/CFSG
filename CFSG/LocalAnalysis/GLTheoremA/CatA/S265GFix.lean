module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265GF2
public import CFSG.RankThree.Chevalley.SteinbergBTCanonicalFieldCommon
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265G

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType
open CFSG.StandardType.TableBF4TwoTB (tE)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

private theorem fixSubgroup_conj_eq_centralizer {G : Type*} [Group G] (a : G) :
    fixSubgroup (MulAut.conj a) = Subgroup.centralizer ({a} : Set G) := by
  ext g
  rw [mem_fixSubgroup, MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff,
    mul_inv_eq_iff_eq_mul]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

section F4Eight

variable
  {K : Type} [Field K] [Finite K] [CharP K 2]

private theorem exists_fixEmb (σ : K ≃+* K) :
    ∃ ι : adjointGroup .F4 (fixSubfield σ) →* adjointGroup .F4 K, Function.Injective ι ∧
      ι.range = fixSubgroup (entrywiseAdjointAut .F4 σ) := by
  have hJC : fixedFieldImage .F4 σ ≤ adjointGroup .F4 K := fun g hg => (fixedFieldImage_le hg).1
  refine ⟨(Subgroup.inclusion hJC).comp (fixedFieldImageEquiv σ).toMonoidHom,
    (Subgroup.inclusion_injective hJC).comp (fixedFieldImageEquiv σ).injective, ?_⟩
  have hΓ := entrywiseFixedGroup_eq_fixedFieldImage_of_ringChar_two (τ := .F4)
    (Or.inr (Or.inl rfl)) (ringChar.eq K 2) σ
  ext g
  rw [MonoidHom.mem_range, mem_fixSubgroup]
  constructor
  · rintro ⟨y, rfl⟩
    have hy : (((fixedFieldImageEquiv σ y : fixedFieldImage .F4 σ)) : ModGL .F4 K) ∈
        entrywiseFixedGroup .F4 σ := by
      rw [hΓ]
      exact (fixedFieldImageEquiv σ y).2
    apply Subtype.ext
    rw [coe_entrywiseAdjointAut]
    exact (mem_entrywiseFixedGroup.1 hy).2
  · intro hg
    have hmem : (g : ModGL .F4 K) ∈ fixedFieldImage .F4 σ := by
      rw [← hΓ, mem_entrywiseFixedGroup]
      refine ⟨g.2, ?_⟩
      rw [← coe_entrywiseAdjointAut, hg]
    obtain ⟨y, hy⟩ := (fixedFieldImageEquiv σ).surjective
      (⟨(g : ModGL .F4 K), hmem⟩ : fixedFieldImage .F4 σ)
    refine ⟨y, Subtype.ext ?_⟩
    show (((fixedFieldImageEquiv σ y : fixedFieldImage .F4 σ)) : ModGL .F4 K) = g
    rw [hy]

private theorem card_fixSubfield_eq_two (hK : Nat.card K = 2 ^ 3) {σ : K ≃+* K}
    (hσ : orderOf σ = 3) : Nat.card (fixSubfield σ) = 2 := by
  have h := (CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield Nat.prime_two (by norm_num)
    hK σ).2
  rw [hσ] at h
  simpa using h

private theorem glaPLayer_fix_of_emb {σ : K ≃+* K}
    {ι : adjointGroup .F4 (fixSubfield σ) →* adjointGroup .F4 K} (hι : Function.Injective ι)
    (hιr : ι.range = fixSubgroup (entrywiseAdjointAut .F4 σ)) {a : adjointGroup .F4 (fixSubfield σ)}
    (ha : GLAPLayer 3 (Subgroup.centralizer ({a} : Set (adjointGroup .F4 (fixSubfield σ)))) ≠ ⊥) :
    GLAPLayer 3 (fixSubgroup (entrywiseAdjointAut .F4 σ) ⊓ fixSubgroup (MulAut.conj (ι a))) ≠ ⊥ := by
  rw [← hιr, fixSubgroup_conj_eq_centralizer]
  exact glaPLayer_range_inf_centralizer_ne_bot Nat.prime_three ι hι ha

theorem exists_fix_glaPLayer_of_card_ge_81 (hK : Nat.card K = 2 ^ 3) {σ : K ≃+* K}
    (hσ : orderOf σ = 3) {A : Subgroup (adjointGroup .F4 K)} (hA : IsElemAbelian 3 A)
    (hAσ : ∀ a ∈ A, entrywiseAdjointAut .F4 σ a = a) (h81 : 3 ^ 4 ≤ Nat.card A) :
    ∃ a ∈ A, a ≠ 1 ∧
      GLAPLayer 3 (fixSubgroup (entrywiseAdjointAut .F4 σ) ⊓ fixSubgroup (MulAut.conj a)) ≠ ⊥ := by
  obtain ⟨ι, hι, hιr⟩ := exists_fixEmb σ
  have hk := card_fixSubfield_eq_two hK hσ
  have hAι : A ≤ ι.range := by
    rw [hιr]
    exact fun a ha => mem_fixSubgroup.2 (hAσ a ha)
  have hcard : Nat.card (A.comap ι) = Nat.card A := by
    conv_rhs => rw [← Subgroup.map_comap_eq_self hAι]
    rw [Subgroup.card_map_of_injective hι]
  obtain ⟨a', ha', ha'1, hlay⟩ := exists_glaPLayer_of_card_ge_81 (K := fixSubfield σ) hk
    (hA.comap hι) (by rw [hcard]; exact h81)
  exact ⟨ι a', ha', fun h => ha'1 (hι (h.trans (map_one ι).symm)), glaPLayer_fix_of_emb hι hιr hlay⟩

theorem exists_fix_glaPLayer_of_card_ge_27 (hK : Nat.card K = 2 ^ 3) {σ : K ≃+* K}
    (hσ : orderOf σ = 3) {A : Subgroup (adjointGroup .F4 K)} (hA : IsElemAbelian 3 A)
    (hAσ : ∀ a ∈ A, entrywiseAdjointAut .F4 σ a = a) (h27 : 3 ^ 3 ≤ Nat.card A)
    {U : Subgroup (adjointGroup .F4 K)} (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    (hUσ : ∀ u ∈ U, entrywiseAdjointAut .F4 σ u = u)
    (hAU : A ≤ Subgroup.normalizer (U : Set (adjointGroup .F4 K))) :
    ∃ a ∈ A, a ≠ 1 ∧
      GLAPLayer 3 (fixSubgroup (entrywiseAdjointAut .F4 σ) ⊓ fixSubgroup (MulAut.conj a)) ≠ ⊥ := by
  obtain ⟨ι, hι, hιr⟩ := exists_fixEmb σ
  have hk := card_fixSubfield_eq_two hK hσ
  have hAι : A ≤ ι.range := by
    rw [hιr]
    exact fun a ha => mem_fixSubgroup.2 (hAσ a ha)
  have hUι : U ≤ ι.range := by
    rw [hιr]
    exact fun u hu => mem_fixSubgroup.2 (hUσ u hu)
  have hcard : Nat.card (A.comap ι) = Nat.card A := by
    conv_rhs => rw [← Subgroup.map_comap_eq_self hAι]
    rw [Subgroup.card_map_of_injective hι]
  have hU' : ∃ U' : Subgroup (adjointGroup .F4 (fixSubfield σ)), U' ≠ ⊥ ∧ IsPGroup 2 U' ∧
      A.comap ι ≤ Subgroup.normalizer (U' : Set (adjointGroup .F4 (fixSubfield σ))) := by
    refine ⟨U.comap ι, fun hbot => hU ?_, hU2.comap_of_injective ι hι, fun a ha => ?_⟩
    · rw [← Subgroup.map_comap_eq_self hUι, hbot, Subgroup.map_bot]
    · rw [Subgroup.mem_normalizer_iff]
      intro u
      have h := Subgroup.mem_normalizer_iff.1 (hAU ha) (ι u)
      rw [Subgroup.mem_comap, Subgroup.mem_comap, map_mul, map_mul, map_inv]
      exact h
  obtain ⟨a', ha', ha'1, hlay⟩ := exists_glaPLayer_of_card_ge_27 (K := fixSubfield σ) hk
    (hA.comap hι) (by rw [hcard]; exact h27) hU'
  exact ⟨ι a', ha', fun h => ha'1 (hι (h.trans (map_one ι).symm)), glaPLayer_fix_of_emb hι hιr hlay⟩

theorem exists_fix_elemAb_81 {σ : K ≃+* K} :
    ∃ E : Subgroup (adjointGroup .F4 K), IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 ∧
      ∀ e ∈ E, entrywiseAdjointAut .F4 σ e = e := by
  obtain ⟨ι, hι, hιr⟩ := exists_fixEmb σ
  obtain ⟨hE, hcard⟩ := tE_rank_data (K := fixSubfield σ)
  refine ⟨(tE (fixSubfield σ)).range.map ι, hE.map ι, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective hι, hcard]
  · rintro _ ⟨e, -, rfl⟩
    have h : ι e ∈ ι.range := ⟨e, rfl⟩
    rw [hιr] at h
    exact mem_fixSubgroup.1 h

theorem exists_fix_elemAb_27 {σ : K ≃+* K} :
    ∃ (E : Subgroup (adjointGroup .F4 K)) (t : adjointGroup .F4 K), IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ 3 ∧ orderOf t = 2 ∧ entrywiseAdjointAut .F4 σ t = t ∧
      (∀ e ∈ E, entrywiseAdjointAut .F4 σ e = e) ∧
      E ≤ Subgroup.centralizer ({t} : Set (adjointGroup .F4 K)) := by
  obtain ⟨ι, hι, hιr⟩ := exists_fixEmb σ
  obtain ⟨hE, hcard, ht2, hEt⟩ := torus3_rank_data (K := fixSubfield σ)
  have hfix : ∀ y, entrywiseAdjointAut .F4 σ (ι y) = ι y := by
    intro y
    have h : ι y ∈ ι.range := ⟨y, rfl⟩
    rw [hιr] at h
    exact mem_fixSubgroup.1 h
  refine ⟨(TableBF4Two.torus3 (fixSubfield σ)).range.map ι, ι (TableBF4Two.rootInv (fixSubfield σ)),
    hE.map ι, ?_, ?_, hfix _, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective hι, hcard]
  · rw [orderOf_injective ι hι, ht2]
  · rintro _ ⟨e, -, rfl⟩
    exact hfix e
  · rintro _ ⟨e, he, rfl⟩
    have h := Subgroup.mem_centralizer_singleton_iff.1 (hEt he)
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, h]

end F4Eight

end CFSG.LocalAnalysis.GLTheoremA.S265G

end
