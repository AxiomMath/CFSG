module

public import CFSG.LieType.Chevalley.EvenCanonicalFieldCentralizer
public import CFSG.LieType.Chevalley.EvenF4AutomorphismNormalForm

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Ree

section Inclusion

variable {τ : Tag} {K : Type} [Field K]

@[expose] def fixedFieldInclusion
    (σ : K ≃+* K) :
    adjointGroup τ (fixSubfield σ) →* adjointGroup τ K :=
  ((baseChangeGL (fixSubfield σ).subtype).comp (adjointGroup τ (fixSubfield σ)).subtype).codRestrict
    (adjointGroup τ K) fun g => by
      have h : baseChangeGL (fixSubfield σ).subtype (g : ModGL τ (fixSubfield σ)) ∈
          fixedFieldImage τ σ := ⟨g, g.2, rfl⟩
      exact (fixedFieldImage_le h).1

theorem coe_fixedFieldInclusion
    (σ : K ≃+* K) (g : adjointGroup τ (fixSubfield σ)) :
    (fixedFieldInclusion σ g : ModGL τ K) = baseChangeGL (fixSubfield σ).subtype g :=
  rfl

theorem fixedFieldInclusion_injective
    (σ : K ≃+* K) :
    Function.Injective (fixedFieldInclusion (τ := τ) σ) := fun _ _ h =>
  Subtype.ext (baseChangeGL_injective _ (congrArg Subtype.val h))

theorem fixedFieldInclusion_xElement
    (σ : K ≃+* K) (i : Fin τ.rank) (c : fixSubfield σ) :
    fixedFieldInclusion σ (xElement i c) = xElement i (c : K) :=
  Subtype.ext (baseChangeGL_xUnit _ i c)

theorem fixedFieldInclusion_yElement
    (σ : K ≃+* K) (i : Fin τ.rank) (c : fixSubfield σ) :
    fixedFieldInclusion σ (yElement i c) = yElement i (c : K) :=
  Subtype.ext (baseChangeGL_yUnit _ i c)

theorem mem_fixedFieldImage_iff_exists
    (σ : K ≃+* K) (g : adjointGroup τ K) :
    (g : ModGL τ K) ∈ fixedFieldImage τ σ ↔ ∃ g', fixedFieldInclusion σ g' = g := by
  constructor
  · rintro ⟨g', hg', hgg'⟩
    exact ⟨⟨g', hg'⟩, Subtype.ext hgg'⟩
  · rintro ⟨g', rfl⟩
    exact ⟨g', g'.2, rfl⟩

end Inclusion

section F4

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem entrywiseAdjointAut_eq_finiteFrobeniusAut_pow
    {e : ℕ} {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ e) :
    entrywiseAdjointAut ReeTag.F4.tag σ = ReeTag.F4.finiteFrobeniusAut K ^ e := by
  refine mulAut_ext_adjX_adjY (fun i c => ?_) fun i c => ?_
  · rw [show adjX ReeTag.F4.tag K i c = xElement i c from rfl,
      ReeTag.finiteFrobeniusAut_pow_xElement]
    refine Subtype.ext ?_
    rw [coe_entrywiseAdjointAut]
    exact (units_map_entrywiseHom_xUnit σ.toRingHom i c).trans (congrArg _ (hσ c))
  · rw [show adjY ReeTag.F4.tag K i c = yElement i c from rfl,
      ReeTag.finiteFrobeniusAut_pow_yElement]
    refine Subtype.ext ?_
    rw [coe_entrywiseAdjointAut]
    exact (units_map_entrywiseHom_yUnit σ.toRingHom i c).trans (congrArg _ (hσ c))

theorem finiteExceptionalAut_comp_fixedFieldInclusion
    (σ : K ≃+* K)
    [CharP (fixSubfield σ) ReeTag.F4.prime] :
    (ReeTag.F4.finiteExceptionalAut K).toMonoidHom.comp (fixedFieldInclusion σ) =
      (fixedFieldInclusion σ).comp
        (ReeTag.F4.finiteExceptionalAut (fixSubfield σ)).toMonoidHom := by
  refine adjointGroup_hom_ext (fun i c => ?_) fun i c => ?_
  · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, fixedFieldInclusion_xElement,
      ReeTag.finiteExceptionalAut_xElement]
    rfl
  · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, fixedFieldInclusion_yElement,
      ReeTag.finiteExceptionalAut_yElement]
    rfl

theorem finiteExceptionalAut_pow_fixedFieldInclusion
    (σ : K ≃+* K)
    [CharP (fixSubfield σ) ReeTag.F4.prime] (j : ℕ)
    (g : adjointGroup ReeTag.F4.tag (fixSubfield σ)) :
    (ReeTag.F4.finiteExceptionalAut K ^ j) (fixedFieldInclusion σ g) =
      fixedFieldInclusion σ ((ReeTag.F4.finiteExceptionalAut (fixSubfield σ) ^ j) g) := by
  induction j generalizing g with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply]
    have h := DFunLike.congr_fun (finiteExceptionalAut_comp_fixedFieldInclusion σ) g
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at h
    rw [h, ih]

theorem even_F4_canonical_field_full_centralizer
    {e : ℕ} (he : 1 ≤ e) (K : Type) [Field K]
    [Finite K] [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * e)) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ e) :
    (∀ c : K, c ∈ fixSubfield σ ↔ c ^ 2 ^ e = c) ∧ Nat.card (fixSubfield σ) = 2 ^ e ∧
      ReeTag.F4.finiteFrobeniusAut K ^ e = ReeTag.F4.finiteExceptionalAut K ^ (2 * e) ∧
      entrywiseAdjointAut ReeTag.F4.tag σ = ReeTag.F4.finiteFrobeniusAut K ^ e ∧
      fixedFieldImage ReeTag.F4.tag σ ≤ adjointGroup ReeTag.F4.tag K ∧
      ((ReeTag.F4.finiteExceptionalAut K ^ (2 * e)).toMonoidHom.eqLocus (MonoidHom.id _)).map
          (adjointGroup ReeTag.F4.tag K).subtype = fixedFieldImage ReeTag.F4.tag σ ∧
      (Finite (fixedFieldImage ReeTag.F4.tag σ) ∧ IsSimpleGroup (fixedFieldImage ReeTag.F4.tag σ) ∧
        Even (Nat.card (fixedFieldImage ReeTag.F4.tag σ)) ∧
        ChevalleyExceptionalModel (fixedFieldImage ReeTag.F4.tag σ) .F4 2 e) ∧
      (∃ ι : ↥((fixedFieldImage ReeTag.F4.tag σ).subgroupOf (adjointGroup ReeTag.F4.tag K)) ≃*
          ↥(((fixedFieldImage ReeTag.F4.tag σ).subgroupOf
            (adjointGroup ReeTag.F4.tag K)).map MulAut.conj),
        ∀ j, (ι j : MulAut (adjointGroup ReeTag.F4.tag K)) =
          MulAut.conj (j : adjointGroup ReeTag.F4.tag K)) ∧
      (∀ β ∈ Subgroup.centralizer {ReeTag.F4.finiteExceptionalAut K ^ (2 * e)},
        ∃! gj : adjointGroup ReeTag.F4.tag K × ℕ, gj.2 < 4 * e ∧
          (gj.1 : ModGL ReeTag.F4.tag K) ∈ fixedFieldImage ReeTag.F4.tag σ ∧
          β = MulAut.conj gj.1 * ReeTag.F4.finiteExceptionalAut K ^ gj.2) ∧
      (∀ g : adjointGroup ReeTag.F4.tag K,
        (g : ModGL ReeTag.F4.tag K) ∈ fixedFieldImage ReeTag.F4.tag σ → ∀ j : ℕ,
        MulAut.conj g * ReeTag.F4.finiteExceptionalAut K ^ j ∈
          Subgroup.centralizer {ReeTag.F4.finiteExceptionalAut K ^ (2 * e)}) ∧
      ((fixedFieldImage ReeTag.F4.tag σ).subgroupOf (adjointGroup ReeTag.F4.tag K)).map
          MulAut.conj ≤ Subgroup.centralizer {ReeTag.F4.finiteExceptionalAut K ^ (2 * e)} ∧
      ((((fixedFieldImage ReeTag.F4.tag σ).subgroupOf
          (adjointGroup ReeTag.F4.tag K)).map MulAut.conj).subgroupOf
        (Subgroup.centralizer {ReeTag.F4.finiteExceptionalAut K ^ (2 * e)})).Normal ∧
      Subgroup.centralizer {ReeTag.F4.finiteExceptionalAut K ^ (2 * e)} ⊓
          Subgroup.centralizer ((((fixedFieldImage ReeTag.F4.tag σ).subgroupOf
            (adjointGroup ReeTag.F4.tag K)).map MulAut.conj :
              Subgroup (MulAut (adjointGroup ReeTag.F4.tag K))) :
                Set (MulAut (adjointGroup ReeTag.F4.tag K))) =
        Subgroup.zpowers (ReeTag.F4.finiteExceptionalAut K ^ (2 * e)) := by
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  have hchar : ringChar K = 2 := ringChar.eq K 2
  set C := adjointGroup ReeTag.F4.tag K
  set φ := ReeTag.F4.finiteExceptionalAut K with hφ
  set δ := φ ^ (2 * e) with hδ
  set J := fixedFieldImage ReeTag.F4.tag σ with hJ
  have hZ : Subgroup.center C = ⊥ := center_adjointGroup_eq_bot
  have hinj := mulAut_conj_injective_of_center_eq_bot hZ
  have hFr : ReeTag.F4.finiteFrobeniusAut K ^ e = δ :=
    (finiteExceptionalAut_pow_two_mul ReeTag.F4 e).symm
  have hσδ : entrywiseAdjointAut ReeTag.F4.tag σ = δ := by
    rw [entrywiseAdjointAut_eq_finiteFrobeniusAut_pow hσ, hFr]
  have h2e : 2 ≤ 2 * e := by omega
  have hσ' : ∀ c, σ c = c ^ 2 ^ (2 * e / 2) := fun c => by
    rw [hσ, show 2 * e / 2 = e by omega]
  obtain ⟨hσσ, hσ1, -⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.SpChain.mem_zpowers_of_forall_fixed h2e
      ⟨e, two_mul e⟩ hK hσ'
  have hk : Nat.card (fixSubfield σ) = 2 ^ e := by
    obtain ⟨-, -, hcard⟩ := ringEquiv_sq_eq_one_facts Nat.prime_two (by omega) hK
      (by rw [sq]; exact hσσ) hσ1
    rw [show 2 * e / 2 = e by omega] at hcard
    exact hcard
  have : CharP (fixSubfield σ) ReeTag.F4.prime := inferInstance
  have hΓJ := entrywiseFixedGroup_eq_fixedFieldImage_of_ringChar_two (τ := ReeTag.F4.tag)
    (Or.inr (Or.inl rfl)) hchar σ
  have hJC : J ≤ C := fun j hj => (fixedFieldImage_le hj).1
  have hmemJ : ∀ g : C, (g : ModGL ReeTag.F4.tag K) ∈ J ↔ δ g = g := by
    intro g
    refine (Subgroup.ext_iff.1 hΓJ (g : ModGL ReeTag.F4.tag K)).symm.trans ?_
    rw [mem_entrywiseFixedGroup, ← hσδ]
    constructor
    · rintro ⟨-, h⟩
      exact Subtype.ext h
    · intro h
      exact ⟨g.2, congrArg Subtype.val h⟩
  obtain ⟨-, hNF, -⟩ := even_F4_exact_automorphism_normal_form (f := 2 * e) (by omega) K hK
  obtain ⟨hordk, hNFk, -⟩ := even_F4_exact_automorphism_normal_form he (fixSubfield σ) hk
  have hconjδ : ∀ (g : C) (j : ℕ), δ * (MulAut.conj g * φ ^ j) =
      MulAut.conj (δ g) * φ ^ j * δ := fun g j => by
    have hcomm : δ * φ ^ j = φ ^ j * δ := (Commute.pow_pow_self φ (2 * e) j).eq
    rw [← mul_assoc, mulAut_mul_conj, mul_assoc, hcomm, ← mul_assoc]
  have hcentJ : ∀ (g : C) (j : ℕ), MulAut.conj g * φ ^ j ∈ Subgroup.centralizer {δ} ↔
      (g : ModGL ReeTag.F4.tag K) ∈ J := by
    intro g j
    rw [Subgroup.mem_centralizer_singleton_iff, hmemJ, hconjδ]
    constructor
    · intro h
      exact hinj (mul_right_cancel (mul_right_cancel h.symm))
    · intro h
      rw [h]
  have hNδ : ((J.subgroupOf C).map MulAut.conj) ≤ Subgroup.centralizer {δ} := by
    rintro _ ⟨j, hj, rfl⟩
    refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
    rw [Set.mem_singleton_iff.1 hh, mulAut_mul_conj,
      (hmemJ j).1 (Subgroup.mem_subgroupOf.1 hj)]
  have hZk : Subgroup.center (adjointGroup ReeTag.F4.tag (fixSubfield σ)) = ⊥ :=
    center_adjointGroup_eq_bot
  have hmodel : ChevalleyExceptionalModel J .F4 2 e :=
    ⟨⟨Nat.prime_two, he, rfl⟩, fixSubfield σ, inferInstance, inferInstance, hk,
      ⟨(fixedFieldImageEquiv σ).symm.trans
        ((QuotientGroup.quotientMulEquivOfEq hZk).trans QuotientGroup.quotientBot).symm⟩⟩
  have hsimple : IsSimpleGroup J := (CFSG.LieType.Simplicity.fam_f4_simplicity _ 2 e hmodel).2
  refine ⟨fun c => by rw [mem_fixSubfield, hσ], hk, hFr,
    entrywiseAdjointAut_eq_finiteFrobeniusAut_pow hσ, hJC, ?_,
    ⟨inferInstance, hsimple, even_card_fixedFieldImage (by decide) σ, hmodel⟩,
    ⟨(J.subgroupOf C).equivMapOfInjective _ hinj, fun j => rfl⟩, fun β hβ => ?_,
    fun g hg j => (hcentJ g j).2 hg, hNδ, ⟨fun n hn g => ?_⟩, le_antisymm (fun β hβ => ?_) ?_⟩
  ·
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact (hmemJ g).2 hg
    · intro hx
      exact ⟨⟨x, hJC hx⟩, (hmemJ _).1 hx, rfl⟩
  ·
    obtain ⟨⟨g, j⟩, hgj, huniq⟩ := hNF β
    have hgJ : (g : ModGL ReeTag.F4.tag K) ∈ J := (hcentJ g j).1 (hgj ▸ hβ)
    refine ⟨(g, j), ⟨by have := j.isLt; omega, hgJ, hgj⟩, fun q hq => ?_⟩
    obtain ⟨hq4, -, hqβ⟩ := hq
    have h := huniq (q.1, ⟨q.2, by omega⟩) hqβ
    have h1 : q.1 = g := congrArg Prod.fst h
    have h2 : q.2 = (j : ℕ) := congrArg (fun x => (x.2 : ℕ)) h
    exact Prod.ext h1 h2
  ·
    obtain ⟨j, hj, hjn⟩ := Subgroup.mem_subgroupOf.1 hn
    rw [SetLike.mem_coe] at hj
    have hgδ : δ * (g : MulAut C) = g * δ :=
      Subgroup.mem_centralizer_iff.1 g.2 δ (Set.mem_singleton δ)
    refine Subgroup.mem_subgroupOf.2 ⟨(g : MulAut C) j, ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, hmemJ]
      calc δ ((g : MulAut C) j) = (δ * (g : MulAut C)) j := rfl
        _ = (g * δ : MulAut C) j := by rw [hgδ]
        _ = (g : MulAut C) (δ j) := rfl
        _ = (g : MulAut C) j := by rw [(hmemJ j).1 (Subgroup.mem_subgroupOf.1 hj)]
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv, ← hjn]
      exact (mulAut_mul_conj_mul_inv _ _).symm
  ·
    obtain ⟨hβδ, hβN⟩ := Subgroup.mem_inf.1 hβ
    obtain ⟨⟨g, j⟩, hgj, -⟩ := hNF β
    dsimp only at hgj
    have hgJ : (g : ModGL ReeTag.F4.tag K) ∈ J := (hcentJ g j).1 (hgj ▸ hβδ)
    have hfix : ∀ x : C, (x : ModGL ReeTag.F4.tag K) ∈ J → β x = x := by
      intro x hx
      have hn : MulAut.conj x ∈ (J.subgroupOf C).map MulAut.conj :=
        ⟨x, Subgroup.mem_subgroupOf.2 hx, rfl⟩
      have h1 : MulAut.conj x * β = β * MulAut.conj x :=
        Subgroup.mem_centralizer_iff.1 hβN _ hn
      have h2 : MulAut.conj (β x) = MulAut.conj x := by
        rw [← mulAut_mul_conj_mul_inv, ← h1, mul_inv_cancel_right]
      exact hinj h2
    obtain ⟨g', rfl⟩ := (mem_fixedFieldImage_iff_exists σ g).1 hgJ
    set φk := ReeTag.F4.finiteExceptionalAut (fixSubfield σ)
    have hidk : MulAut.conj g' * φk ^ (j : ℕ) = 1 := by
      refine MulEquiv.ext fun y => fixedFieldInclusion_injective σ ?_
      have h1 := hfix (fixedFieldInclusion σ y) ⟨y, y.2, rfl⟩
      rw [hgj, MulAut.mul_apply, finiteExceptionalAut_pow_fixedFieldInclusion σ (j : ℕ) y,
        MulAut.conj_apply] at h1
      rw [MulAut.one_apply, MulAut.mul_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]
      exact h1
    have hmod : φk ^ ((j : ℕ) % (2 * e)) = φk ^ (j : ℕ) := by
      have h := pow_mod_orderOf φk (j : ℕ)
      rwa [hordk] at h
    obtain ⟨q, -, hq⟩ := hNFk 1
    have h1 := hq (1, ⟨0, by omega⟩) (by simp)
    have h2 := hq (g', ⟨(j : ℕ) % (2 * e), Nat.mod_lt _ (by omega)⟩) (by
      show 1 = MulAut.conj g' * φk ^ ((j : ℕ) % (2 * e))
      rw [hmod, hidk])
    have h3 := h2.trans h1.symm
    have hg'1 : g' = 1 := congrArg Prod.fst h3
    have hj0 : (j : ℕ) % (2 * e) = 0 := congrArg (fun x => (x.2 : ℕ)) h3
    have hj : (j : ℕ) = 0 ∨ (j : ℕ) = 2 * e := by
      obtain ⟨m, hm⟩ := Nat.dvd_of_mod_eq_zero hj0
      have hlt := j.isLt
      have hm2 : m < 2 := by
        by_contra h
        have h2m : 2 * e * 2 ≤ 2 * e * m := Nat.mul_le_mul_left _ (by omega)
        omega
      interval_cases m
      · left
        omega
      · right
        omega
    subst hg'1
    rw [hgj, map_one, map_one, one_mul]
    rcases hj with h | h
    · rw [h, pow_zero]
      exact one_mem _
    · rw [h]
      exact Subgroup.mem_zpowers _
  ·
    refine Subgroup.zpowers_le.2 (Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2
      fun h hh => by rw [Set.mem_singleton_iff.1 hh], Subgroup.mem_centralizer_iff.2
        fun n hn => (Subgroup.mem_centralizer_iff.1 (hNδ hn) δ (Set.mem_singleton δ)).symm⟩)

end F4

end CFSG.LieType.Chevalley
