module

public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
public import CFSG.FeitThompson.Representations.TypeIIIVLocalCharacterConstants
public import CFSG.FeitThompson.Representations.TypeIIDerivedFrobeniusOrEqualDegreePair
import CFSG.FeitThompson.OddOrder.PTypeClausesIndependentOfComplement
public import CFSG.FeitThompson.Representations.DadeInductionExtendedSupportTypeII
public import CFSG.FeitThompson.Representations.PrimeDadeFourFamilyCoherenceOrientation
public import CFSG.FeitThompson.Representations.FrobeniusAbelianKernelInducedCharacters

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup
open _root_.CFSG.FeitThompson.Prep05

variable {G : Type*} [Group G]

theorem cfIP_eq_cfInner {X : Type*} [Fintype X] (f h : X → ℂ) : cfIP f h = cfInner f h := by
  unfold cfIP
  congr 1
  exact Subsingleton.elim _ _

theorem indToTop_eq_indClassFun [Fintype G] (X : Subgroup G) (f : ↥X → ℂ) :
    indToTop X f = indClassFun X f := by
  unfold indToTop
  congr 1
  exact Subsingleton.elim _ _

theorem isSignedIrr_iff_mem_signedIrr {X : Type*} [Group X] (f : X → ℂ) :
    IsSignedIrr f ↔ f ∈ signedIrr X := by
  rw [mem_signedIrr]
  exact Iff.rfl

theorem cconj_eq_star {X : Type*} (f : X → ℂ) : cconj f = star f := rfl

theorem cyclicTIset_eq_cyclicTIDiff (W₁ W₂ : Subgroup G) :
    cyclicTIset W₁ W₂ = cyclicTIDiff (W₁ ⊔ W₂) W₁ W₂ := by
  ext x
  rw [mem_cyclicTIDiff, mem_cyclicTIset]

theorem map_subtype_sup_subgroupOf_of_le {N A B : Subgroup G} (hA : A ≤ N) (hB : B ≤ N) :
    Subgroup.map N.subtype (A.subgroupOf N ⊔ B.subgroupOf N) = A ⊔ B := by
  rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.2 hA, inf_eq_left.2 hB]

theorem isCyclicTIPair_map_subtype_of_isWitnessedPConfiguration [Finite G]
    (hodd : Odd (Nat.card G)) {N E W₂ W₁ : Subgroup G}
    (hc : IsWitnessedPConfiguration N E W₂ W₁) :
    IsCyclicTIPair ((W₂ ⊔ W₁ : Subgroup G)) W₂ W₁ := by
  have h := hc.isPrimeCyclicTIHyp_subgroupOf hodd
  have hmap := map_subtype_sup_subgroupOf_of_le hc.le_M_W₁ hc.le_M_W₂
  have hm2 : Subgroup.map N.subtype (W₂.subgroupOf N) = W₂ := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hc.le_M_W₁]
  have hm1 : Subgroup.map N.subtype (W₁.subgroupOf N) = W₁ := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hc.le_M_W₂]
  have key := h.isCyclicTIPair_map_subtype
    (hstab := by
      rw [hmap, hm2, hm1, ← cyclicTIset_eq_cyclicTIDiff, setOf_conj_eq_self_eq_normalizer,
        hc.isTIWithNormalizer_cyclicTIset.normalizer_eq])
    (hdisj := by
      intro g hg
      rw [hmap, hm2, hm1] at *
      rw [← cyclicTIset_eq_cyclicTIDiff, Set.inter_comm]
      exact Set.disjoint_iff_inter_eq_empty.1
        (hc.isTIWithNormalizer_cyclicTIset.disjoint_image_conj_inv hg))
  rwa [hmap, hm2, hm1] at key

theorem isCyclicTIIsometry_of_data [Fintype G] {W₁ W₂ : Subgroup G} [Fintype ↥(W₁ ⊔ W₂)]
    {ω : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun G}
    (hiso : ∀ f g, cfIP ((ω f : G → ℂ)) ((ω g : G → ℂ)) =
      cfIP ((f : ↥(W₁ ⊔ W₂) → ℂ)) ((g : ↥(W₁ ⊔ W₂) → ℂ)))
    (hZ : ∀ f : classFun ↥(W₁ ⊔ W₂), (f : ↥(W₁ ⊔ W₂) → ℂ) ∈ virtualChars ↥(W₁ ⊔ W₂) →
      (ω f : G → ℂ) ∈ virtualChars G)
    (hone : ∀ f : classFun ↥(W₁ ⊔ W₂), (f : ↥(W₁ ⊔ W₂) → ℂ) = 1 → (ω f : G → ℂ) = 1)
    (hind : ∀ f : classFun ↥(W₁ ⊔ W₂),
      (∀ z : ↥(W₁ ⊔ W₂), (z : G) ∉ cyclicTIset W₁ W₂ → (f : ↥(W₁ ⊔ W₂) → ℂ) z = 0) →
      (ω f : G → ℂ) = indToTop (W₁ ⊔ W₂) (f : ↥(W₁ ⊔ W₂) → ℂ)) :
    IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ ω where
  inner_eq f g := by
    have := hiso f g
    rwa [cfIP_eq_cfInner, cfIP_eq_cfInner] at this
  map_virtualChars := hZ
  map_principalClassFun := Subtype.ext (by
    simpa using hone (principalClassFun ↥(W₁ ⊔ W₂)) (by simp))
  eq_indClassFun f hf := by
    have := hind f (by
      intro z hz
      exact hf z (by rwa [cyclicTIset_eq_cyclicTIDiff] at hz))
    rwa [indToTop_eq_indClassFun] at this

theorem hasEqualDegreeCharacterPair_of_exists_centralizerIn_ne_bot [Finite G]
    {N E W₂ W₁ : Subgroup G} (hG : IsMinimalSimpleOdd G) (hN' : IsCoatom N) (hN : IsTypeII N)
    (hc : IsWitnessedPConfiguration N E W₂ W₁)
    (he : ∃ e ∈ E, e ≠ 1 ∧ centralizerIn (hallCoreOf N) (zpowers e) ≠ ⊥) :
    HasEqualDegreeCharacterPair hc := by
  obtain ⟨e, heE, he1, hne⟩ := he
  have hsolv : Group.IsSolvable ↥N := hG.isSolvable_of_ne_top N hN'.1
  refine (hN.frobenius_or_equalDegreeCharacterPair hG.odd_natCard hsolv hc).resolve_left
    fun hfree => ?_
  refine hne ?_
  rw [centralizerIn_eq, centralizer_coe_zpowers, hallCoreOf_eq]
  exact hfree e heE he1

theorem eq_prodChar_of_apply_mul {W₁ W₂ : Subgroup G}
    (hW : IsCyclicTIPair (W₁ ⊔ W₂) W₁ W₂) {f : ↥(W₁ ⊔ W₂) → ℂ} {a : ↥W₁ → ℂ} {b : ↥W₂ → ℂ}
    (hf : ∀ (x y : G) (hx : x ∈ W₁) (hy : y ∈ W₂) (hxy : x * y ∈ W₁ ⊔ W₂),
      f ⟨x * y, hxy⟩ = a ⟨x, hx⟩ * b ⟨y, hy⟩) :
    f = hW.prodChar a b := by
  funext z
  obtain ⟨⟨u, v⟩, hz⟩ : ∃ p : ↥W₁ × ↥W₂, hW.mulEquivProd p = z :=
    ⟨hW.mulEquivProd.symm z, by simp⟩
  have hcoe : ((u : G) * (v : G)) = (z : G) := by
    rw [← hW.coe_mulEquivProd_apply (u, v), hz]
  have hzeq : z = ⟨(u : G) * (v : G), mul_mem (hW.left_le u.2) (hW.right_le v.2)⟩ :=
    Subtype.ext hcoe.symm
  rw [hzeq, hf _ _ u.2 v.2 _, hW.prodChar_apply_mul a b u.2 v.2]

theorem eta_eq_prodCharEta_of_data {W₁ W₂ : Subgroup G}
    (hW : IsCyclicTIPair (W₁ ⊔ W₂) W₁ W₂)
    {ω : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun G}
    {I J : Type*} {a : I → (↥W₁ → ℂ)} {b : J → (↥W₂ → ℂ)}
    (harange : Set.range a = Irr ↥W₁) (hbrange : Set.range b = Irr ↥W₂)
    {w : I → J → (↥(W₁ ⊔ W₂) → ℂ)}
    (hw : ∀ (i : I) (j : J) (x y : G) (hx : x ∈ W₁) (hy : y ∈ W₂) (hxy : x * y ∈ W₁ ⊔ W₂),
      w i j ⟨x * y, hxy⟩ = a i ⟨x, hx⟩ * b j ⟨y, hy⟩)
    {η : I → J → (G → ℂ)}
    (hη : ∀ (i : I) (j : J) (hwm : w i j ∈ classFun ↥(W₁ ⊔ W₂)),
      η i j = (ω ⟨w i j, hwm⟩ : G → ℂ))
    (i : I) (j : J) :
    ∃ (p : ↑(Irr ↥W₁)) (q : ↑(Irr ↥W₂)), (p : ↥W₁ → ℂ) = a i ∧ (q : ↥W₂ → ℂ) = b j ∧
      η i j = hW.prodCharEta ω p q := by
  have ha : ∀ i, a i ∈ Irr ↥W₁ := fun i => harange ▸ Set.mem_range_self i
  have hb : ∀ j, b j ∈ Irr ↥W₂ := fun j => hbrange ▸ Set.mem_range_self j
  refine ⟨⟨a i, ha i⟩, ⟨b j, hb j⟩, rfl, rfl, ?_⟩
  have hwij : w i j = hW.prodChar (a i) (b j) :=
    eq_prodChar_of_apply_mul hW fun x y hx hy hxy => hw i j x y hx hy hxy
  have hmem : w i j ∈ classFun ↥(W₁ ⊔ W₂) := by
    rw [hwij]
    exact Irr_subset_classFun (hW.prodChar_mem_Irr (ha i) (hb j))
  have heq : (⟨w i j, hmem⟩ : classFun ↥(W₁ ⊔ W₂))
      = hW.basisProdIrr (⟨a i, ha i⟩, ⟨b j, hb j⟩) := by
    refine Subtype.ext ?_
    change w i j = _
    rw [hwij, hW.coe_basisProdIrr_apply]
  rw [hη i j hmem, hW.prodCharEta_eq_coe_apply, heq]

theorem eq_principalIrr_of_eq_one {W : Subgroup G} {p : ↑(Irr ↥W)} (hp : (p : ↥W → ℂ) = 1) :
    p = principalIrr ↥W :=
  Subtype.ext (by rw [hp, coe_principalIrr])

open CFSG.FeitThompson.Prep06 in
theorem derivedOf_eq_subgroupOf (M : Subgroup G) :
    derivedOf M = (⁅M, M⁆ : Subgroup G).subgroupOf M := by
  rw [derivedOf_eq, Subgroup.subgroupOf, ← Subgroup.map_subtype_commutator M,
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective]

open CFSG.FeitThompson.Prep06 in
noncomputable def derivedOfEquiv (M : Subgroup G) :
    ↥(derivedOf M) ≃* ↥(⁅M, M⁆ : Subgroup G) :=
  (MulEquiv.subgroupCongr (derivedOf_eq_subgroupOf M)).trans
    (Subgroup.subgroupOfEquivOfLe (Subgroup.commutator_le_self M))

open CFSG.FeitThompson.Prep06 in
@[simp]
theorem coe_coe_derivedOfEquiv (M : Subgroup G) (x : ↥(derivedOf M)) :
    ((derivedOfEquiv M x : ↥(⁅M, M⁆ : Subgroup G)) : G) = ((x : ↥M) : G) := (rfl)

open CFSG.FeitThompson.Prep06 in
@[simp]
theorem coe_coe_derivedOfEquiv_symm (M : Subgroup G) (y : ↥(⁅M, M⁆ : Subgroup G)) :
    (((derivedOfEquiv M).symm y : ↥(derivedOf M)) : ↥M)
      = ⟨(y : G), Subgroup.commutator_le_self M y.2⟩ := by
  have := coe_coe_derivedOfEquiv M ((derivedOfEquiv M).symm y)
  rw [MulEquiv.apply_symm_apply] at this
  exact Subtype.ext this

open CFSG.FeitThompson.Prep06 in
instance derivedOf_normal (M : Subgroup G) : (derivedOf M).Normal := by
  rw [derivedOf_eq]; infer_instance

open CFSG.FeitThompson.Prep06 in
theorem forall_charConj_eq_iff_le_inertiaGroup {M W : Subgroup G} (hW : W ≤ M)
    (hEN : W ≤ normalizer ((⁅M, M⁆ : Subgroup G) : Set G)) (α : ↥(⁅M, M⁆ : Subgroup G) → ℂ) :
    (∀ w : ↥W, charConj hEN w α = α) ↔
      W.subgroupOf M ≤ inertiaGroup (derivedOf M) (α ∘ derivedOfEquiv M) := by
  rw [le_inertiaGroup_iff_forall_conj]
  constructor
  · intro h x hx k k' hk'
    have hxW : (x : G) ∈ W := by simpa [Subgroup.mem_subgroupOf] using hx
    have hcoe : ((derivedOfEquiv M k' : ↥(⁅M, M⁆ : Subgroup G)) : G)
        = ((⟨(x : G), hxW⟩ : ↥W) : G)⁻¹ * ((derivedOfEquiv M k : ↥(⁅M, M⁆ : Subgroup G)) : G)
          * ((⟨(x : G), hxW⟩ : ↥W) : G) := by
      rw [coe_coe_derivedOfEquiv, coe_coe_derivedOfEquiv]
      exact congrArg (fun y : ↥M => (y : G)) hk'
    have hkey := congrFun (h ⟨(x : G), hxW⟩) (derivedOfEquiv M k)
    rw [charConj_apply hEN _ α hcoe] at hkey
    exact hkey
  · intro h w
    funext y
    have hwM : (w : G) ∈ M := hW w.2
    have hxmem : (⟨(w : G), hwM⟩ : ↥M) ∈ W.subgroupOf M := by simp [Subgroup.mem_subgroupOf]
    have hconjmem : (w : G)⁻¹ * (y : G) * (w : G) ∈ (⁅M, M⁆ : Subgroup G) :=
      (Subgroup.mem_normalizer_iff''.1 (hEN w.2) (y : G)).1 y.2
    set y' : ↥(⁅M, M⁆ : Subgroup G) := ⟨(w : G)⁻¹ * (y : G) * (w : G), hconjmem⟩ with hy'
    have hk' : (((derivedOfEquiv M).symm y' : ↥(derivedOf M)) : ↥M)
        = (⟨(w : G), hwM⟩ : ↥M)⁻¹ * (((derivedOfEquiv M).symm y : ↥(derivedOf M)) : ↥M)
          * (⟨(w : G), hwM⟩ : ↥M) := by
      rw [coe_coe_derivedOfEquiv_symm, coe_coe_derivedOfEquiv_symm]
      exact Subtype.ext (by simp [hy'])
    have hkey := h _ hxmem ((derivedOfEquiv M).symm y) ((derivedOfEquiv M).symm y') hk'
    simp only [Function.comp_apply, MulEquiv.apply_symm_apply] at hkey
    rw [charConj_apply hEN w α (x := y) (y := y') (by simp [hy'])]
    exact hkey

open CFSG.FeitThompson.Prep06 in
theorem mem_Irr_comp_derivedOfEquiv {M : Subgroup G} {α : ↥(⁅M, M⁆ : Subgroup G) → ℂ}
    (hα : α ∈ Irr ↥(⁅M, M⁆ : Subgroup G)) : α ∘ derivedOfEquiv M ∈ Irr ↥(derivedOf M) :=
  FrobeniusInduction.mem_Irr_comp_mulEquiv hα _

open CFSG.FeitThompson.Prep06 in
theorem not_subset_charValueKernel_comp_derivedOfEquiv {M : Subgroup G}
    {α : ↥(⁅M, M⁆ : Subgroup G) → ℂ}
    (h : ∃ x : ↥(⁅M, M⁆ : Subgroup G),
      (x : G) ∈ (hallCore ↥M).map M.subtype ∧ x ∉ charValueKernel α) :
    ¬ (((hallCore ↥M).subgroupOf (derivedOf M) : Subgroup ↥(derivedOf M)) : Set ↥(derivedOf M))
      ⊆ charValueKernel (α ∘ derivedOfEquiv M) := by
  obtain ⟨x, hxH, hxker⟩ := h
  intro hsub
  refine hxker ?_
  have hmem : ((derivedOfEquiv M).symm x : ↥(derivedOf M))
      ∈ (hallCore ↥M).subgroupOf (derivedOf M) := by
    rw [Subgroup.mem_subgroupOf, coe_coe_derivedOfEquiv_symm]
    obtain ⟨y, hy, hyx⟩ := hxH
    have hxy : (⟨(x : G), Subgroup.commutator_le_self M x.2⟩ : ↥M) = y := Subtype.ext hyx.symm
    rw [hxy]; exact hy
  have hval := hsub hmem
  rw [mem_charValueKernel] at hval ⊢
  simpa using hval

open CFSG.FeitThompson.Prep06 in
theorem exists_local_equalDegreePair_of_hasEqualDegreeCharacterPair [Finite G]
    {M U W₁ W₂ : Subgroup G} (hc : IsWitnessedPConfiguration M U W₁ W₂)
    (h : HasEqualDegreeCharacterPair hc) :
    ∃ α ∈ Irr ↥(derivedOf M), ∃ β ∈ Irr ↥(derivedOf M), α 1 = β 1 ∧
      ¬ (((hallCore ↥M).subgroupOf (derivedOf M) : Subgroup ↥(derivedOf M)) :
          Set ↥(derivedOf M)) ⊆ charValueKernel α ∧
      ¬ (((hallCore ↥M).subgroupOf (derivedOf M) : Subgroup ↥(derivedOf M)) :
          Set ↥(derivedOf M)) ⊆ charValueKernel β ∧
      W₁.subgroupOf M ≤ inertiaGroup (derivedOf M) α ∧
      ¬ W₁.subgroupOf M ≤ inertiaGroup (derivedOf M) β := by
  rw [hasEqualDegreeCharacterPair_iff] at h
  obtain ⟨α, hα, β, hβ, hdeg, hdα, hdβ, hinv, hmov⟩ := h
  refine ⟨α ∘ derivedOfEquiv M, mem_Irr_comp_derivedOfEquiv hα,
    β ∘ derivedOfEquiv M, mem_Irr_comp_derivedOfEquiv hβ, ?_,
    not_subset_charValueKernel_comp_derivedOfEquiv hdα,
    not_subset_charValueKernel_comp_derivedOfEquiv hdβ,
    (forall_charConj_eq_iff_le_inertiaGroup hc.le_M_W₁ hc.le_normalizer_commutator_W₁ α).1 hinv,
    fun hcon => ?_⟩
  · simpa using hdeg
  · obtain ⟨w, hw⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hc.ne_bot_W₁
    have hall := (forall_charConj_eq_iff_le_inertiaGroup hc.le_M_W₁
      hc.le_normalizer_commutator_W₁ β).2 hcon
    refine hw (hmov ?_)
    simp only []
    rw [hall w, charConj_one]

open CFSG.FeitThompson.Prep06 in
theorem exists_row_witness_of_hasEqualDegreeCharacterPair [Finite G]
    {M U W₁ W₂ : Subgroup G} [Fintype ↥M] [Fintype ↥(W₁.subgroupOf M ⊔ W₂.subgroupOf M)]
    [Fintype ↑(Irr ↥(W₁.subgroupOf M))]
    (hc : IsWitnessedPConfiguration M U W₁ W₂)
    {σ : classFun ↥(W₁.subgroupOf M ⊔ W₂.subgroupOf M) →ₗ[ℂ] classFun ↥M}
    (hσ : IsCyclicTIIsometry (W₁.subgroupOf M ⊔ W₂.subgroupOf M) (W₁.subgroupOf M)
      (W₂.subgroupOf M) σ)
    (h : IsPrimeCyclicTIHyp (derivedOf M) (W₁.subgroupOf M) (W₂.subgroupOf M))
    (hq : (Nat.card ↥W₁).Prime)
    (hpair : HasEqualDegreeCharacterPair hc) :
    ∃ (β : ↥(derivedOf M) → ℂ) (j : Irr ↥(W₂.subgroupOf M)),
      j ≠ principalIrr ↥(W₂.subgroupOf M) ∧
      β ∈ Irr ↥(derivedOf M) ∧
      indClassFun (derivedOf M) β ∈ Irr ↥M ∧
      indClassFun (derivedOf M) β 1 = h.primeTIrow σ j 1 ∧
      (∀ (i : ↑(Irr ↥(W₁.subgroupOf M))) (t : ↑(Irr ↥(W₂.subgroupOf M))),
        IsOrthogonal (indClassFun (derivedOf M) β) (h.primeTIirr σ i t)) ∧
      ¬ (((hallCore ↥M).subgroupOf (derivedOf M) : Subgroup ↥(derivedOf M)) :
        Set ↥(derivedOf M)) ⊆ charValueKernel β := by
  obtain ⟨α, hα, β, hβ, hdeg, hkα, hkβ, hinv, hmov⟩ :=
    exists_local_equalDegreePair_of_hasEqualDegreeCharacterPair hc hpair
  have hq' : (Nat.card ↥(W₁.subgroupOf M)).Prime := by
    rwa [natCard_subgroupOf_eq_of_le hc.le_M_W₁]
  obtain ⟨j, hj, -, hξ, hdegξ, horth, hker⟩ :=
    h.exists_ne_principalIrr_primeTIres_eq_and_indClassFun_mem_Irr hσ hq'
      (H := hallCore ↥M) hα hβ hdeg hkα hkβ hinv hmov
  exact ⟨β, j, hj, hβ, hξ, hdegξ, horth, hker⟩

theorem coreFixedSet_hallCoreIn_eq_fixedSet (M : Subgroup G) :
    CFSG.FeitThompson.Prep09.coreFixedSet (CFSG.FeitThompson.Prep09.hallCoreIn M) (⁅M, M⁆ : Subgroup G)
      = fixedSet (⁅M, M⁆ : Subgroup G) (hallCoreOf M) := by
  ext a
  rw [CFSG.FeitThompson.Prep09.mem_coreFixedSet, mem_fixedSet, centralizerIn_eq,
    centralizer_coe_zpowers, CFSG.FeitThompson.Prep09.centIn_def, hallCoreOf_eq,
    CFSG.FeitThompson.Prep09.hallCoreIn_def]

theorem isMinimalSimpleOddOrder_of_isMinimalSimpleOdd [Finite G] (hG : IsMinimalSimpleOdd G) :
    CFSG.FeitThompson.Prep09.IsMinimalSimpleOddOrder G where
  odd_natCard := hG.odd_natCard
  isSimpleGroup := hG.isSimpleGroup
  not_isMulCommutative := hG.not_isMulCommutative
  isSolvable_of_ne_top := hG.isSolvable_of_ne_top

theorem isTypeIIWitness_of_isTypeII_of_isSolvable [Finite G] {M E W₁ W₂ : Subgroup G}
    (htype : IsTypeII M) (hsolv : Group.IsSolvable ↥M)
    (hc : IsWitnessedPConfiguration M E W₁ W₂) :
    CFSG.FeitThompson.Prep09.IsTypeIIWitness M E W₁ W₂ :=
  htype.clauses_of_isWitnessedPConfiguration hsolv hc

section Dade

variable {L : Subgroup G} {A₀ : Set G} {T : G → Subgroup G}

noncomputable def dadeBaselineHom [Fintype G] {S : Set (↥L → ℂ)} (hD : IsDadeData L A₀ T)
    (hS : charSpanZero S ≤ dadeZDomain L A₀) : charSpanZero S →+ virtualChars G :=
  (spanIrrToVirtualChars G).comp
    (((Submodule.inclusion (charSpanZero_le (Irr G))).toAddMonoidHom).comp
      ((dadeZMap hD).comp (Submodule.inclusion hS).toAddMonoidHom))

theorem coe_dadeBaselineHom_eq_dadeZMap [Fintype G] {S : Set (↥L → ℂ)} (hD : IsDadeData L A₀ T)
    (hS : charSpanZero S ≤ dadeZDomain L A₀) (f : charSpanZero S) :
    ((dadeBaselineHom hD hS f : virtualChars G) : G → ℂ)
      = ((dadeZMap hD ⟨(f : ↥L → ℂ), hS f.2⟩ : charSpanZero (Irr G)) : G → ℂ) := by
  rw [dadeBaselineHom]
  simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, coe_spanIrrToVirtualChars]
  rfl

theorem coe_dadeBaselineHom [Fintype G] {S : Set (↥L → ℂ)} (hD : IsDadeData L A₀ T)
    (hS : charSpanZero S ≤ dadeZDomain L A₀) (f : charSpanZero S) (F : dadeDomain L A₀)
    (hF : (F : ↥L → ℂ) = (f : ↥L → ℂ)) :
    ((dadeBaselineHom hD hS f : virtualChars G) : G → ℂ)
      = ((dadeMap hD F : classFun G) : G → ℂ) := by
  have harg : (⟨(f : ↥L → ℂ), mem_dadeDomain_of_mem_dadeZDomain (hS f.2)⟩ : dadeDomain L A₀) = F :=
    Subtype.ext hF.symm
  rw [coe_dadeBaselineHom_eq_dadeZMap, coe_dadeZMap, harg]

theorem cfInner_dadeBaselineHom [Fintype G] [Fintype ↥L] {S : Set (↥L → ℂ)}
    (hD : IsDadeData L A₀ T) (hS : charSpanZero S ≤ dadeZDomain L A₀) (f g : charSpanZero S) :
    cfInner ((dadeBaselineHom hD hS f : virtualChars G) : G → ℂ)
        ((dadeBaselineHom hD hS g : virtualChars G) : G → ℂ)
      = cfInner (f : ↥L → ℂ) (g : ↥L → ℂ) := by
  rw [coe_dadeBaselineHom_eq_dadeZMap, coe_dadeBaselineHom_eq_dadeZMap, cfInner_dadeZMap]

theorem dadeBaselineHom_apply_one [Fintype G] {S : Set (↥L → ℂ)} (hD : IsDadeData L A₀ T)
    (hS : charSpanZero S ≤ dadeZDomain L A₀) (f : charSpanZero S) :
    ((dadeBaselineHom hD hS f : virtualChars G) : G → ℂ) 1 = 0 := by
  rw [coe_dadeBaselineHom_eq_dadeZMap, dadeZMap_apply_one]

universe u

theorem isDadeData_of_isTypeII {G : Type u} [Group G] [Finite G] (hG : IsMinimalSimpleOdd G)
    (h₁ : CFSG.FeitThompson.Statements.FTS_canonical_signalizer_structure.{u})
    (h₂ : CFSG.FeitThompson.Statements.FTS_type_II_extended_support_ti.{u})
    {N E W₁ W₂ : Subgroup G} (hN : IsCoatom N) (htype : IsTypeII N)
    (hc : IsWitnessedPConfiguration N E W₁ W₂) :
    IsDadeData N (CFSG.FeitThompson.Prep09.coreFixedSet (CFSG.FeitThompson.Prep09.hallCoreIn N)
        (⁅N, N⁆ : Subgroup G) ∪ CFSG.FeitThompson.Prep09.conjUnion N (cyclicTIset W₁ W₂))
      (CFSG.FeitThompson.Prep09.hallSignalizerOn N) := by
  have hsolv : Group.IsSolvable ↥N := hG.isSolvable_of_ne_top N hN.1
  obtain ⟨-, -, -, -, -, -, -, hD, -⟩ :=
    CFSG.FeitThompson.Proofs.FTS_type_II_extended_dade_induction h₁ h₂ G
      (isMinimalSimpleOddOrder_of_isMinimalSimpleOdd hG) N E W₁ W₂ hN htype
      (isTypeIIWitness_of_isTypeII_of_isSolvable htype hsolv hc) _ rfl
  exact hD

end Dade

section Swap

variable {G : Type*} [Group G]

theorem cyclicTIDiff_comm (W W₁ W₂ : Subgroup G) :
    cyclicTIDiff W W₁ W₂ = cyclicTIDiff W W₂ W₁ := by
  ext x; simp [and_comm]

theorem IsCyclicTIPair.swap {W W₁ W₂ : Subgroup G} (h : IsCyclicTIPair W W₁ W₂) :
    IsCyclicTIPair W W₂ W₁ where
  left_ne_bot := h.right_ne_bot
  right_ne_bot := h.left_ne_bot
  mul_eq := by
    rw [← h.mul_eq]
    ext x
    simp only [Set.mem_mul, SetLike.mem_coe]
    constructor
    · rintro ⟨u, hu, v, hv, hx⟩
      exact ⟨v, hv, u, hu, by rw [← hx]; exact h.commute_of_mem hv hu⟩
    · rintro ⟨u, hu, v, hv, hx⟩
      exact ⟨v, hv, u, hu, by rw [← hx]; exact (h.commute_of_mem hu hv).symm⟩
  inf_eq_bot := by rw [inf_comm]; exact h.inf_eq_bot
  commute x hx y hy := (h.commute_of_mem hy hx).symm
  isCyclic := h.isCyclic
  odd_natCard := h.odd_natCard
  setOf_conj_eq_self := by rw [cyclicTIDiff_comm]; exact h.setOf_conj_eq_self
  inter_eq_empty := fun g hg => by rw [cyclicTIDiff_comm]; exact h.inter_eq_empty g hg

theorem IsCyclicTIIsometry.swap [Fintype G] {W W₁ W₂ : Subgroup G} [Fintype ↥W]
    {ω : classFun ↥W →ₗ[ℂ] classFun G} (hω : IsCyclicTIIsometry W W₁ W₂ ω) :
    IsCyclicTIIsometry W W₂ W₁ ω where
  inner_eq := hω.inner_eq
  map_virtualChars := hω.map_virtualChars
  map_principalClassFun := hω.map_principalClassFun
  eq_indClassFun f hf := hω.eq_indClassFun f fun x hx =>
    hf x (by rwa [cyclicTIDiff_comm] at hx)

theorem prodCharEta_swap {W W₁ W₂ : Subgroup G}
    (hW : IsCyclicTIPair W W₁ W₂) (hW' : IsCyclicTIPair W W₂ W₁)
    (ω : classFun ↥W →ₗ[ℂ] classFun G) (p : Irr ↥W₁) (q : Irr ↥W₂) :
    hW'.prodCharEta ω q p = hW.prodCharEta ω p q := by
  have hbasis : hW'.basisProdIrr (q, p) = hW.basisProdIrr (p, q) := by
    refine Subtype.ext ?_
    rw [hW.coe_basisProdIrr_apply, hW'.coe_basisProdIrr_apply]
    funext z
    obtain ⟨⟨u, v⟩, hz⟩ : ∃ r : ↥W₁ × ↥W₂, hW.mulEquivProd r = z :=
      ⟨hW.mulEquivProd.symm z, by simp⟩
    have hcoe : ((u : G) * (v : G)) = (z : G) := by
      rw [← hW.coe_mulEquivProd_apply (u, v), hz]
    have hzeq : z = ⟨(u : G) * (v : G), mul_mem (hW.left_le u.2) (hW.right_le v.2)⟩ :=
      Subtype.ext hcoe.symm
    have hzeq' : z = ⟨(v : G) * (u : G), mul_mem (hW'.left_le v.2) (hW'.right_le u.2)⟩ :=
      Subtype.ext (by rw [← hcoe]; exact hW.commute_of_mem u.2 v.2)
    have e1 : hW'.prodChar ((q : ↥W₂ → ℂ)) ((p : ↥W₁ → ℂ)) z
        = (q : ↥W₂ → ℂ) v * (p : ↥W₁ → ℂ) u := by
      rw [hzeq']; exact hW'.prodChar_apply_mul _ _ v.2 u.2
    have e2 : hW.prodChar ((p : ↥W₁ → ℂ)) ((q : ↥W₂ → ℂ)) z
        = (p : ↥W₁ → ℂ) u * (q : ↥W₂ → ℂ) v := by
      rw [hzeq]; exact hW.prodChar_apply_mul _ _ u.2 v.2
    simp only []
    rw [e1, e2]
    ring
  rw [IsCyclicTIPair.prodCharEta_eq_coe_apply, IsCyclicTIPair.prodCharEta_eq_coe_apply, hbasis]

theorem prodCharEtaColSum_swap_eq_sum {W W₁ W₂ : Subgroup G} [Fintype ↑(Irr ↥W₂)]
    (hW : IsCyclicTIPair W W₁ W₂) (hW' : IsCyclicTIPair W W₂ W₁)
    (ω : classFun ↥W →ₗ[ℂ] classFun G) (p : Irr ↥W₁) :
    hW'.prodCharEtaColSum ω p = ∑ q : Irr ↥W₂, hW.prodCharEta ω p q := by
  rw [hW'.prodCharEtaColSum_eq_sum]
  exact Finset.sum_congr rfl fun q _ => prodCharEta_swap hW hW' ω p q

end Swap

section Vanishing

variable {G : Type*} [Group G]

theorem mem_conjClosure_of_isConj {S : Set G} {x y : G} (hx : x ∈ S) (h : IsConj x y) :
    y ∈ conjClosure S := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  exact Set.mem_iUnion.2 ⟨(c : G)⁻¹, x, hx, by simpa using hc⟩

theorem notMem_totalDadeSupport_of_notMem_conjClosure [Finite G] {S : Set G}
    {T : G → Subgroup G} (hT : ∀ u ∈ S, T u = ⊥) {z : G} (hz : z ∉ conjClosure S) :
    z ∉ totalDadeSupport S T := fun hcon => by
  obtain ⟨u, hu, hconj⟩ := (CFSG.FeitThompson.Proofs.mem_totalDadeSupport_iff_of_trivial hT).1 hcon
  exact hz (mem_conjClosure_of_isConj hu hconj)

end Vanishing

section FixedSetIn

variable {G : Type*} [Group G]

def fixedSetIn {X : Type*} [Group X] (H K : Subgroup X) : Set X :=
  {x | x ∈ K ∧ x ≠ 1 ∧ (H ⊓ Subgroup.centralizer {x} : Subgroup X) ≠ ⊥}

theorem mem_fixedSetIn {X : Type*} [Group X] {H K : Subgroup X} {x : X} :
    x ∈ fixedSetIn H K ↔ x ∈ K ∧ x ≠ 1 ∧ (H ⊓ Subgroup.centralizer {x} : Subgroup X) ≠ ⊥ :=
  Iff.rfl

theorem fixedSetIn_subset_sdiff {X : Type*} [Group X] (H K : Subgroup X) :
    fixedSetIn H K ⊆ (K : Set X) \ {1} := fun _ hx => ⟨hx.1, hx.2.1⟩

theorem sdiff_inf_centralizer_subset_fixedSetIn {X : Type*} [Group X] (H K : Subgroup X) {y : X}
    (hy : y ∈ H) (hy1 : y ≠ 1) :
    ((K ⊓ Subgroup.centralizer {y} : Subgroup X) : Set X) \ {1} ⊆ fixedSetIn H K := by
  rintro x ⟨hxmem, hx1⟩
  obtain ⟨hxK, hxC⟩ := Subgroup.mem_inf.1 hxmem
  refine ⟨hxK, hx1, fun hbot => hy1 ?_⟩
  have hymem : y ∈ (H ⊓ Subgroup.centralizer {x} : Subgroup X) :=
    Subgroup.mem_inf.2 ⟨hy, Subgroup.mem_centralizer_singleton_iff.2
      (Subgroup.mem_centralizer_singleton_iff.1 hxC).symm⟩
  rw [hbot, Subgroup.mem_bot] at hymem
  exact hymem

private theorem conj_mem_fixedSetIn {X : Type*} [Group X] (H K : Subgroup X) [H.Normal]
    [K.Normal] (s : X) {x : X} (hx : x ∈ fixedSetIn H K) : s⁻¹ * x * s ∈ fixedSetIn H K := by
  obtain ⟨hxK, hx1, hxC⟩ := hx
  refine ⟨by simpa [mul_assoc] using ‹K.Normal›.conj_mem x hxK s⁻¹, ?_, ?_⟩
  · intro hcon
    exact hx1 (by simpa [mul_assoc] using congrArg (fun z => s * z * s⁻¹) hcon)
  · intro hbot
    obtain ⟨u, hu⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hxC
    obtain ⟨huH, huC⟩ := Subgroup.mem_inf.1 u.2
    have hu' : (s⁻¹ * (u : X) * s) ∈ (H ⊓ Subgroup.centralizer {s⁻¹ * x * s} : Subgroup X) := by
      refine Subgroup.mem_inf.2 ⟨by simpa [mul_assoc] using ‹H.Normal›.conj_mem _ huH s⁻¹, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hcomm := Subgroup.mem_centralizer_singleton_iff.1 huC
      calc (s⁻¹ * (u : X) * s) * (s⁻¹ * x * s)
          = s⁻¹ * ((u : X) * x) * s := by group
        _ = s⁻¹ * (x * (u : X)) * s := by rw [hcomm]
        _ = (s⁻¹ * x * s) * (s⁻¹ * (u : X) * s) := by group
    rw [hbot, Subgroup.mem_bot] at hu'
    exact hu (Subtype.ext (by simpa [mul_assoc] using congrArg (fun z => s * z * s⁻¹) hu'))

theorem conj_image_fixedSetIn {X : Type*} [Group X] (H K : Subgroup X) [H.Normal] [K.Normal]
    (t : X) : (fun v => t⁻¹ * v * t) '' fixedSetIn H K = fixedSetIn H K := by
  refine Set.Subset.antisymm ?_ fun x hx => ⟨t * x * t⁻¹, ?_, by group⟩
  · rintro y ⟨x, hx, rfl⟩
    exact conj_mem_fixedSetIn H K t hx
  · simpa [mul_assoc] using conj_mem_fixedSetIn H K t⁻¹ hx

open CFSG.FeitThompson.Prep06 in
theorem image_fixedSetIn_subset_fixedSet [Finite G] (N : Subgroup G) :
    (fun x : ↥N => (x : G)) '' fixedSetIn (hallCore ↥N) (derivedOf N)
      ⊆ fixedSet (⁅N, N⁆ : Subgroup G) (hallCoreOf N) := by
  rintro g ⟨x, ⟨hxK, hx1, hxC⟩, rfl⟩
  refine ⟨?_, fun hcon => hx1 (Subtype.ext hcon), ?_⟩
  · rw [← map_subtype_derivedOf N]
    exact ⟨x, hxK, rfl⟩
  · rw [centralizerIn_eq, centralizer_coe_zpowers, hallCoreOf_eq]
    obtain ⟨u, hu⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hxC
    obtain ⟨huH, huC⟩ := Subgroup.mem_inf.1 u.2
    have hu1 : ((u : ↥N) : G) ≠ 1 := fun hcon => hu (Subtype.ext (Subtype.ext hcon))
    refine Subgroup.ne_bot_iff_exists_ne_one.2 ⟨⟨((u : ↥N) : G), ?_⟩, ?_⟩
    · exact Subgroup.mem_inf.2 ⟨⟨(u : ↥N), huH, rfl⟩,
        Subgroup.mem_centralizer_singleton_iff.2 (congrArg (fun z : ↥N => (z : G))
          (Subgroup.mem_centralizer_singleton_iff.1 huC))⟩
    · exact fun hcon => hu1 (Subtype.ext_iff.1 hcon)

open CFSG.FeitThompson.Prep06 in
theorem image_bridgeSupport_subset [Finite G] {N E W₁ W₂ : Subgroup G}
    (hc : IsWitnessedPConfiguration N E W₂ W₁) :
    (fun x : ↥N => (x : G)) ''
        bridgeSupport (fixedSetIn (hallCore ↥N) (derivedOf N)) (W₂.subgroupOf N) (W₁.subgroupOf N)
      ⊆ CFSG.FeitThompson.Prep09.coreFixedSet (CFSG.FeitThompson.Prep09.hallCoreIn N)
          (⁅N, N⁆ : Subgroup G) ∪ CFSG.FeitThompson.Prep09.conjUnion N (cyclicTIset W₂ W₁) := by
  have hmap1 : (W₂.subgroupOf N).map N.subtype = W₂ := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hc.le_M_W₁]
  have hmap2 : (W₁.subgroupOf N).map N.subtype = W₁ := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hc.le_M_W₂]
  have hmapW : ((W₂.subgroupOf N) ⊔ (W₁.subgroupOf N)).map N.subtype = W₂ ⊔ W₁ :=
    map_subtype_sup_subgroupOf_of_le hc.le_M_W₁ hc.le_M_W₂
  rintro g ⟨x, hx, rfl⟩
  rcases mem_bridgeSupport.1 hx with hxA | hxV
  · refine Or.inl ?_
    rw [coreFixedSet_hallCoreIn_eq_fixedSet]
    exact image_fixedSetIn_subset_fixedSet N ⟨x, hxA, rfl⟩
  · refine Or.inr ?_
    obtain ⟨t, v, hv, htv⟩ := mem_cyclicTIsetConj.1 hxV
    refine CFSG.FeitThompson.Prep09.mem_conjUnion.2 ⟨(t : G), t.2, ⟨((v : ↥N) : G), ?_, ?_⟩⟩
    · have hmem := image_cyclicTIset_eq N (W₂.subgroupOf N) (W₁.subgroupOf N) ▸
        (Set.mem_image_of_mem (fun x : ↥N => (x : G)) hv)
      rwa [hmapW, hmap1, hmap2, cyclicTIDiff_sup_eq_cyclicTIset] at hmem
    · exact congrArg (fun z : ↥N => (z : G)) htv

theorem subgroupOf_le_hallCore_of_le [Finite G] {N W : Subgroup G}
    (h : W ≤ (hallCore ↥N).map N.subtype) : W.subgroupOf N ≤ hallCore ↥N := by
  intro x hx
  obtain ⟨y, hy, hyx⟩ := h (by simpa [Subgroup.mem_subgroupOf] using hx)
  have hxy : x = y := Subtype.ext hyx.symm
  rw [hxy]; exact hy

end FixedSetIn

section FourFamily

variable {G : Type*} [Group G]

theorem charSpanZero_le_dadeZDomain_of_forall_eq_zero {L : Subgroup G} {A₀ : Set G}
    {S : Set (↥L → ℂ)} (hgen : S ⊆ (virtualChars ↥L : Set (↥L → ℂ)))
    (hsupp : ∀ x : ↥L, (x : G) ∉ A₀ → x ≠ 1 → ∀ s ∈ S, s x = 0) :
    charSpanZero S ≤ dadeZDomain L A₀ := by
  intro f hf
  obtain ⟨hspan, h1⟩ := mem_charSpanZero.1 hf
  refine mem_dadeZDomain.2 ⟨Submodule.span_le.2 hgen hspan, fun x hx => ?_⟩
  by_cases hx1 : x = 1
  · rw [hx1]; exact h1
  · exact eq_zero_of_mem_span_of_forall_eq_zero (fun s hs => hsupp x hx hx1 s hs) hspan

theorem coe_dadeBaselineHom_eq_dadeMapFun [Fintype G] {L : Subgroup G} {A₀ : Set G}
    {T : G → Subgroup G} {S : Set (↥L → ℂ)}
    (hD : IsDadeData L A₀ T) (hS : charSpanZero S ≤ dadeZDomain L A₀) (f : charSpanZero S) :
    ((dadeBaselineHom hD hS f : virtualChars G) : G → ℂ)
      = dadeMapFun L A₀ T (f : ↥L → ℂ) := by
  have hF : (f : ↥L → ℂ) ∈ dadeDomain L A₀ := mem_dadeDomain_of_mem_dadeZDomain (hS f.2)
  rw [coe_dadeBaselineHom hD hS f ⟨(f : ↥L → ℂ), hF⟩ rfl, coe_dadeMap hD ⟨_, hF⟩]

theorem dadeBaselineHom_apply_eq_zero_of_notMem [Fintype G] {L : Subgroup G} {A₀ B : Set G}
    {T : G → Subgroup G} {S : Set (↥L → ℂ)}
    (hD : IsDadeData L A₀ T) (hS : charSpanZero S ≤ dadeZDomain L A₀)
    (hsupp : ∀ x : ↥L, (x : G) ∉ B → x ≠ 1 → ∀ s ∈ S, s x = 0)
    (f : charSpanZero S) {z : G} (hz : z ∉ totalDadeSupport B T) :
    ((dadeBaselineHom hD hS f : virtualChars G) : G → ℂ) z = 0 := by
  rw [coe_dadeBaselineHom_eq_dadeMapFun hD hS f]
  refine dadeMapFun_eq_zero_of_notMem_totalDadeSupport hD
    (mem_dadeDomain_of_mem_dadeZDomain (hS f.2)) ?_ hz
  intro x hx
  obtain ⟨hspan, h1⟩ := mem_charSpanZero.1 f.2
  by_cases hx1 : x = 1
  · rw [hx1]; exact h1
  · exact eq_zero_of_mem_span_of_forall_eq_zero (fun s hs => hsupp x hx hx1 s hs) hspan

theorem coe_nu_sub_apply_eq_zero_of_notMem [Fintype G] {L : Subgroup G} [Fintype ↥L]
    {A₀ B : Set G} {T : G → Subgroup G} {S : Set (↥L → ℂ)}
    (hD : IsDadeData L A₀ T) (hS : charSpanZero S ≤ dadeZDomain L A₀)
    (hsupp : ∀ x : ↥L, (x : G) ∉ B → x ≠ 1 → ∀ s ∈ S, s x = 0)
    {ν : Submodule.span ℤ S →+ virtualChars G}
    (hν : IsCoherentWith S (dadeBaselineHom hD hS) ν)
    (f g : Submodule.span ℤ S) (h1 : (f : ↥L → ℂ) 1 = (g : ↥L → ℂ) 1)
    {z : G} (hz : z ∉ totalDadeSupport B T) :
    ((ν f : virtualChars G) : G → ℂ) z - ((ν g : virtualChars G) : G → ℂ) z = 0 := by
  have hmem : (f : ↥L → ℂ) - (g : ↥L → ℂ) ∈ charSpanZero S :=
    mem_charSpanZero.2 ⟨Submodule.sub_mem _ f.2 g.2, by simp [h1]⟩
  have hincl : Submodule.inclusion (charSpanZero_le S) ⟨_, hmem⟩ = f - g := Subtype.ext rfl
  have hkey := hν.eq_on_zero ⟨(f : ↥L → ℂ) - (g : ↥L → ℂ), hmem⟩
  rw [hincl] at hkey
  have hz0 := dadeBaselineHom_apply_eq_zero_of_notMem hD hS hsupp
    ⟨(f : ↥L → ℂ) - (g : ↥L → ℂ), hmem⟩ hz
  have hfinal : ((ν (f - g) : virtualChars G) : G → ℂ) z = 0 := by rw [hkey]; exact hz0
  rw [map_sub] at hfinal
  simpa using hfinal

variable {L : Subgroup G} [Fintype G] [Fintype ↥L] {K X₁ X₂ : Subgroup ↥L}
  [Fintype ↥(X₁ ⊔ X₂)] [Fintype ↑(Irr ↥X₁)] [Fintype ↥((X₁ ⊔ X₂).map L.subtype)]
  {σ : classFun ↥(X₁ ⊔ X₂) →ₗ[ℂ] classFun ↥L}
  {ω : classFun ↥((X₁ ⊔ X₂).map L.subtype) →ₗ[ℂ] classFun G}
  {A₀ B : Set G} {T : G → Subgroup G}

theorem fourFamily_apply_eq_zero_of_notMem
    (h : IsPrimeCyclicTIHyp K X₁ X₂) (hσ : IsCyclicTIIsometry (X₁ ⊔ X₂) X₁ X₂ σ)
    {H : Subgroup ↥L} [H.Normal] (hWH : X₂ ≤ H)
    {A : Set ↥L}
    (hAconj : ∀ t : ↥L, (fun v => t⁻¹ * v * t) '' A = A)
    (hA : ∀ y ∈ H, y ≠ 1 → ((K ⊓ Subgroup.centralizer {y} : Subgroup ↥L) : Set ↥L) \ {1} ⊆ A)
    (hA₀ : (fun x : ↥L => (x : G)) '' bridgeSupport A X₁ X₂ ⊆ A₀)
    (hD : IsDadeData L A₀ T)
    (hstab : {g : G | (fun x => g⁻¹ * x * g) ''
        cyclicTIDiff ((X₁ ⊔ X₂).map L.subtype) (X₁.map L.subtype) (X₂.map L.subtype)
      = cyclicTIDiff ((X₁ ⊔ X₂).map L.subtype) (X₁.map L.subtype) (X₂.map L.subtype)}
      = ((((X₁ ⊔ X₂).map L.subtype) : Subgroup G) : Set G))
    (hdisj : ∀ g ∉ (X₁ ⊔ X₂).map L.subtype,
      (fun x => g⁻¹ * x * g) ''
          cyclicTIDiff ((X₁ ⊔ X₂).map L.subtype) (X₁.map L.subtype) (X₂.map L.subtype)
        ∩ cyclicTIDiff ((X₁ ⊔ X₂).map L.subtype) (X₁.map L.subtype) (X₂.map L.subtype) = ∅)
    (hω : IsCyclicTIIsometry ((X₁ ⊔ X₂).map L.subtype) (X₁.map L.subtype) (X₂.map L.subtype) ω)
    (hodd : Odd (Nat.card G))
    {j : Irr ↥X₂} (hj : j ≠ principalIrr ↥X₂)
    {θ : ↥K → ℂ} (hθ : θ ∈ Irr ↥K) (hHθ : ∃ y : ↥K, (y : ↥L) ∈ H ∧ y ∉ charValueKernel θ)
    (hξ : indClassFun K θ ∈ Irr ↥L) (hdeg : indClassFun K θ 1 = h.primeTIrow σ j 1)
    (hAB : (fun x : ↥L => (x : G)) '' A ⊆ B) :
    ∀ x : ↥L, (x : G) ∉ B → x ≠ 1 →
      ∀ s ∈ ({indClassFun K θ, star (indClassFun K θ), h.primeTIrow σ j,
        h.primeTIrow σ (starIrr j)} : Set (↥L → ℂ)), s x = 0 := by
  obtain ⟨-, -, -, -, -, -, hsupp, -⟩ :=
    primeDade_four_family_antireal_blocks h hσ hWH hAconj hA hA₀ hD hstab hdisj hω hodd hj hθ
      hHθ hξ hdeg
  intro x hx hx1 s hs
  have hxA : x ∉ A ∪ {1} := by
    rintro (hcon | hcon)
    · exact hx (hAB ⟨x, hcon, rfl⟩)
    · exact hx1 hcon
  obtain ⟨h1, h2, h3, h4⟩ := hsupp x hxA
  rcases hs with rfl | rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem charSpanZero_fourFamily_le_dadeZDomain
    (h : IsPrimeCyclicTIHyp K X₁ X₂) (hσ : IsCyclicTIIsometry (X₁ ⊔ X₂) X₁ X₂ σ)
    {H : Subgroup ↥L} [H.Normal] (hWH : X₂ ≤ H)
    {A : Set ↥L}
    (hAconj : ∀ t : ↥L, (fun v => t⁻¹ * v * t) '' A = A)
    (hA : ∀ y ∈ H, y ≠ 1 → ((K ⊓ Subgroup.centralizer {y} : Subgroup ↥L) : Set ↥L) \ {1} ⊆ A)
    (hA₀ : (fun x : ↥L => (x : G)) '' bridgeSupport A X₁ X₂ ⊆ A₀)
    (hD : IsDadeData L A₀ T)
    (hstab : {g : G | (fun x => g⁻¹ * x * g) ''
        cyclicTIDiff ((X₁ ⊔ X₂).map L.subtype) (X₁.map L.subtype) (X₂.map L.subtype)
      = cyclicTIDiff ((X₁ ⊔ X₂).map L.subtype) (X₁.map L.subtype) (X₂.map L.subtype)}
      = ((((X₁ ⊔ X₂).map L.subtype) : Subgroup G) : Set G))
    (hdisj : ∀ g ∉ (X₁ ⊔ X₂).map L.subtype,
      (fun x => g⁻¹ * x * g) ''
          cyclicTIDiff ((X₁ ⊔ X₂).map L.subtype) (X₁.map L.subtype) (X₂.map L.subtype)
        ∩ cyclicTIDiff ((X₁ ⊔ X₂).map L.subtype) (X₁.map L.subtype) (X₂.map L.subtype) = ∅)
    (hω : IsCyclicTIIsometry ((X₁ ⊔ X₂).map L.subtype) (X₁.map L.subtype) (X₂.map L.subtype) ω)
    (hodd : Odd (Nat.card G))
    {j : Irr ↥X₂} (hj : j ≠ principalIrr ↥X₂)
    {θ : ↥K → ℂ} (hθ : θ ∈ Irr ↥K) (hHθ : ∃ y : ↥K, (y : ↥L) ∈ H ∧ y ∉ charValueKernel θ)
    (hξ : indClassFun K θ ∈ Irr ↥L) (hdeg : indClassFun K θ 1 = h.primeTIrow σ j 1) :
    charSpanZero ({indClassFun K θ, star (indClassFun K θ), h.primeTIrow σ j,
        h.primeTIrow σ (starIrr j)} : Set (↥L → ℂ)) ≤ dadeZDomain L A₀ := by
  refine charSpanZero_le_dadeZDomain_of_forall_eq_zero ?_
    (fourFamily_apply_eq_zero_of_notMem h hσ hWH hAconj hA hA₀ hD hstab hdisj hω hodd hj hθ
      hHθ hξ hdeg (B := A₀) (fun y hy => by
        obtain ⟨x, hx, rfl⟩ := hy
        exact hA₀ ⟨x, subset_bridgeSupport_left hx, rfl⟩))
  rintro g (rfl | rfl | rfl | rfl)
  · exact mem_virtualChars_of_mem_span_Irr (Submodule.subset_span hξ)
  · exact mem_virtualChars_of_mem_span_Irr (Submodule.subset_span (star_mem_Irr hξ))
  · exact primeTIrow_mem_virtualChars h hσ j
  · exact primeTIrow_mem_virtualChars h hσ (starIrr j)

end FourFamily

section ColumnWitness

open PrimeDadeFourFamilyOrientation

variable {G : Type*} [Group G] {L : Subgroup G} [Fintype G] [Fintype ↥L]
  {K X₁ X₂ : Subgroup ↥L} [Fintype ↥(X₁ ⊔ X₂)] [Fintype ↑(Irr ↥X₁)]
  {σ : classFun ↥(X₁ ⊔ X₂) →ₗ[ℂ] classFun ↥L} {A₀ B : Set G} {T : G → Subgroup G}

set_option maxHeartbeats 1600000 in
theorem exists_column_witness_of_fourFamily {Wamb V₁ V₂ : Subgroup G} [Fintype ↥Wamb]
    {ω : classFun ↥Wamb →ₗ[ℂ] classFun G}
    (hmapW : (X₁ ⊔ X₂).map L.subtype = Wamb) (hmap1 : X₁.map L.subtype = V₁)
    (hmap2 : X₂.map L.subtype = V₂)
    (h : IsPrimeCyclicTIHyp K X₁ X₂) (hσ : IsCyclicTIIsometry (X₁ ⊔ X₂) X₁ X₂ σ)
    {H : Subgroup ↥L} [H.Normal] (hWH : X₂ ≤ H)
    {A : Set ↥L} (hAK : A ⊆ (K : Set ↥L) \ {1})
    (hAconj : ∀ t : ↥L, (fun v => t⁻¹ * v * t) '' A = A)
    (hA : ∀ y ∈ H, y ≠ 1 → ((K ⊓ Subgroup.centralizer {y} : Subgroup ↥L) : Set ↥L) \ {1} ⊆ A)
    (hA₀ : (fun x : ↥L => (x : G)) '' bridgeSupport A X₁ X₂ ⊆ A₀)
    (hD : IsDadeData L A₀ T)
    (hstab : {g : G | (fun x => g⁻¹ * x * g) '' cyclicTIDiff Wamb V₁ V₂ = cyclicTIDiff Wamb V₁ V₂}
      = (Wamb : Set G))
    (hdisj : ∀ g ∉ Wamb,
      (fun x => g⁻¹ * x * g) '' cyclicTIDiff Wamb V₁ V₂ ∩ cyclicTIDiff Wamb V₁ V₂ = ∅)
    (hWpair : IsCyclicTIPair Wamb V₁ V₂) (hω : IsCyclicTIIsometry Wamb V₁ V₂ ω)
    (hodd : Odd (Nat.card G))
    {j : Irr ↥X₂} (hj : j ≠ principalIrr ↥X₂)
    {θ : ↥K → ℂ} (hθ : θ ∈ Irr ↥K) (hHθ : ∃ y : ↥K, (y : ↥L) ∈ H ∧ y ∉ charValueKernel θ)
    (hξ : indClassFun K θ ∈ Irr ↥L) (hdeg : indClassFun K θ 1 = h.primeTIrow σ j 1)
    (hAB : (fun x : ↥L => (x : G)) '' A ⊆ B) :
    ∃ q : Irr ↥V₂, q ≠ principalIrr ↥V₂ ∧ ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧
      ∃ lam : G → ℂ, lam ∈ virtualChars G ∧ lam ∈ signedIrr G ∧ star lam ≠ lam ∧
        (∀ (p : Irr ↥V₁) (r : Irr ↥V₂), cfInner lam (hWpair.prodCharEta ω p r) = 0) ∧
        (∀ z : G, z ∉ totalDadeSupport B T → (lam - star lam) z = 0) ∧
        (∀ z : G, z ∉ totalDadeSupport B T →
          (ε • hWpair.prodCharEtaColSum ω q - lam) z = 0) := by
  classical
  subst hmapW hmap1 hmap2
  set S : Set (↥L → ℂ) := {indClassFun K θ, star (indClassFun K θ), h.primeTIrow σ j,
      h.primeTIrow σ (starIrr j)} with hSdef
  have hS : charSpanZero S ≤ dadeZDomain L A₀ :=
    charSpanZero_fourFamily_le_dadeZDomain h hσ hWH hAconj hA hA₀ hD hstab hdisj hω
      hodd hj hθ hHθ hξ hdeg
  have hsuppB : ∀ x : ↥L, (x : G) ∉ B → x ≠ 1 → ∀ s ∈ S, s x = 0 :=
    fourFamily_apply_eq_zero_of_notMem h hσ hWH hAconj hA hA₀ hD hstab hdisj hω
      hodd hj hθ hHθ hξ hdeg hAB
  obtain ⟨-, -, -, -, ⟨d, -, hdξ, hdsξ, hdj, -⟩, -, -, -, -, -⟩ :=
    primeDade_four_family_antireal_blocks h hσ hWH hAconj hA hA₀ hD hstab hdisj hω hodd hj hθ
      hHθ hξ hdeg
  obtain ⟨ν, hν, hnu1, hnu2, hnu3⟩ :=
    primeDade_four_family_coherence_orientation h hσ hWH hAK hAconj hA hA₀ hD hstab hdisj hω hodd
      hj hθ hHθ hξ hdeg hSdef (τ := dadeBaselineHom hD hS)
      (fun f F hfF => coe_dadeBaselineHom hD hS f F hfF.symm)
  have hmemξ : indClassFun K θ ∈ S := Set.mem_insert _ _
  have hmemsξ : star (indClassFun K θ) ∈ S := Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  have hmemj : h.primeTIrow σ j ∈ S :=
    Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hmemk : h.primeTIrow σ (starIrr j) ∈ S :=
    Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  set wξ : Submodule.span ℤ S := ⟨indClassFun K θ, Submodule.subset_span hmemξ⟩ with hwξ
  set wsξ : Submodule.span ℤ S := ⟨star (indClassFun K θ), Submodule.subset_span hmemsξ⟩ with hwsξ
  set wj : Submodule.span ℤ S := ⟨h.primeTIrow σ j, Submodule.subset_span hmemj⟩ with hwj
  set wk : Submodule.span ℤ S := ⟨h.primeTIrow σ (starIrr j),
    Submodule.subset_span hmemk⟩ with hwk
  obtain ⟨hlamIrr, hlamnr, hlamorth⟩ := hnu1 wξ rfl
  have hconj := hnu2 wξ wsξ rfl rfl
  have hor := hnu3 wj wk rfl rfl
  have hdegj : (wj : ↥L → ℂ) 1 = (wξ : ↥L → ℂ) 1 := by
    change h.primeTIrow σ j 1 = indClassFun K θ 1
    rw [hdj, hdξ]
  have hanti : ∀ z : G, z ∉ totalDadeSupport B T →
      (((ν wξ : virtualChars G) : G → ℂ) - star ((ν wξ : virtualChars G) : G → ℂ)) z = 0 := by
    intro z hz
    have hd1 : (wξ : ↥L → ℂ) 1 = (wsξ : ↥L → ℂ) 1 := by
      change indClassFun K θ 1 = star (indClassFun K θ) 1
      rw [hdξ, hdsξ]
    have hkey := coe_nu_sub_apply_eq_zero_of_notMem hD hS hsuppB hν wξ wsξ hd1 hz
    rw [hconj] at hkey
    simpa using hkey
  rcases hor with ⟨hcol, -⟩ | ⟨hcol, -⟩
  · refine ⟨irrMapSubtype L X₂ j, ?_, h.primeTISign σ j,
      h.primeTISign_eq_one_or_eq_neg_one j, ((ν wξ : virtualChars G) : G → ℂ),
      (ν wξ).2, hlamIrr, hlamnr, hlamorth, hanti, ?_⟩
    · rw [← irrMapSubtype_principal L X₂]
      exact fun hcon => hj (irrMapSubtype_injective L X₂ hcon)
    · intro z hz
      have hsub := coe_nu_sub_apply_eq_zero_of_notMem hD hS hsuppB hν wj wξ hdegj hz
      rw [hcol] at hsub
      simpa using hsub
  · refine ⟨irrMapSubtype L X₂ (starIrr j), ?_, -h.primeTISign σ j, ?_,
      ((ν wξ : virtualChars G) : G → ℂ), (ν wξ).2, hlamIrr, hlamnr, hlamorth, hanti, ?_⟩
    · rw [← irrMapSubtype_principal L X₂]
      exact fun hcon => (h.starIrr_ne_principalIrr_right hj) (irrMapSubtype_injective L X₂ hcon)
    · rcases h.primeTISign_eq_one_or_eq_neg_one (σ := σ) j with hh | hh
      · exact Or.inr (by rw [hh])
      · exact Or.inl (by rw [hh]; ring)
    · intro z hz
      have hsub := coe_nu_sub_apply_eq_zero_of_notMem hD hS hsuppB hν wj wξ hdegj hz
      rw [hcol] at hsub
      simpa using hsub

end ColumnWitness

section Signalizer

universe u

theorem hallSignalizerOn_eq_bot_of_isTypeII {G : Type u} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G)
    (h₁ : CFSG.FeitThompson.Statements.FTS_canonical_signalizer_structure.{u})
    (h₂ : CFSG.FeitThompson.Statements.FTS_type_II_extended_support_ti.{u})
    {N E W₁ W₂ : Subgroup G} (hN : IsCoatom N) (htype : IsTypeII N)
    (hc : IsWitnessedPConfiguration N E W₁ W₂) :
    ∀ u ∈ (CFSG.FeitThompson.Prep09.coreFixedSet (CFSG.FeitThompson.Prep09.hallCoreIn N)
        (⁅N, N⁆ : Subgroup G) ∪ CFSG.FeitThompson.Prep09.conjUnion N (cyclicTIset W₁ W₂)),
      CFSG.FeitThompson.Prep09.hallSignalizerOn N u = ⊥ := by
  have hsolv : Group.IsSolvable ↥N := hG.isSolvable_of_ne_top N hN.1
  obtain ⟨hJ, -⟩ :=
    CFSG.FeitThompson.Proofs.FTS_type_II_extended_dade_induction h₁ h₂ G
      (isMinimalSimpleOddOrder_of_isMinimalSimpleOdd hG) N E W₁ W₂ hN htype
      (isTypeIIWitness_of_isTypeII_of_isSolvable htype hsolv hc) _ rfl
  exact hJ

end Signalizer

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

open Subgroup CFSG.FeitThompson
open CFSG.FeitThompson.Prep05
open _root_.CFSG.FeitThompson.Prep06

universe u v

set_option maxHeartbeats 2000000 in
private theorem FPF_type_ii_nonfrobenius_crossed_column_data_aux
    (h₁ : Statements.FTS_canonical_signalizer_structure.{u})
    (h₂ : Statements.FTS_type_II_extended_support_ti.{u}) :
    Statements.FPF_type_ii_nonfrobenius_crossed_column_data.{u, v} := by
  intro G _ _ hG N E W₁ W₂ hN htype hc I J _ _ a b i₀ j₀ hainj harange hai₀ hbinj hbrange hbj₀
    w hw ω hiso hZ hone hind η hη he
  classical
  have : Fintype G := Fintype.ofFinite _
  have : Fintype ↥N := Fintype.ofFinite _
  have : Fintype ↥(W₁ ⊔ W₂) := Fintype.ofFinite _
  have : Fintype ↑(Irr ↥W₂) := Fintype.ofFinite _
  set X₁ : Subgroup ↥N := W₂.subgroupOf N with hX₁
  set X₂ : Subgroup ↥N := W₁.subgroupOf N with hX₂
  have : Fintype ↥(X₁ ⊔ X₂) := Fintype.ofFinite _
  have : Fintype ↑(Irr ↥X₁) := Fintype.ofFinite _
  have hsolv : Group.IsSolvable ↥N := hG.isSolvable_of_ne_top N hN.1
  have hmap1 : X₁.map N.subtype = W₂ := by
    rw [hX₁, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hc.le_M_W₁]
  have hmap2 : X₂.map N.subtype = W₁ := by
    rw [hX₂, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hc.le_M_W₂]
  have hmapW : (X₁ ⊔ X₂).map N.subtype = W₁ ⊔ W₂ := by
    rw [map_subtype_sup_subgroupOf_of_le hc.le_M_W₁ hc.le_M_W₂, sup_comm]
  have hWamb : IsCyclicTIPair ((W₂ ⊔ W₁ : Subgroup G)) W₂ W₁ :=
    isCyclicTIPair_map_subtype_of_isWitnessedPConfiguration hG.odd_natCard hc
  have hsup : (W₂ ⊔ W₁ : Subgroup G) = W₁ ⊔ W₂ := sup_comm _ _
  have hWpair : IsCyclicTIPair ((W₁ ⊔ W₂ : Subgroup G)) W₂ W₁ := hsup ▸ hWamb
  have hWspec : IsCyclicTIPair ((W₁ ⊔ W₂ : Subgroup G)) W₁ W₂ := hWpair.swap
  have hω12 : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ ω :=
    isCyclicTIIsometry_of_data hiso hZ hone hind
  have hω : IsCyclicTIIsometry (W₁ ⊔ W₂) W₂ W₁ ω := hω12.swap
  have hlocal : IsPrimeCyclicTIHyp (derivedOf N) X₁ X₂ :=
    hc.isPrimeCyclicTIHyp_subgroupOf hG.odd_natCard
  obtain ⟨σ, hσ⟩ := hlocal.exists_isCyclicTIIsometry
  have hwit : CFSG.FeitThompson.Prep09.IsTypeIIWitness N E W₂ W₁ :=
    isTypeIIWitness_of_isTypeII_of_isSolvable htype hsolv hc
  have hq : (Nat.card ↥W₂).Prime := hwit.1.prime_natCard_W₁
  have hpair : HasEqualDegreeCharacterPair hc :=
    hasEqualDegreeCharacterPair_of_exists_centralizerIn_ne_bot hG hN htype hc he
  obtain ⟨β, j, hj, hβ, hξ, hdegβ, -, hker⟩ :=
    exists_row_witness_of_hasEqualDegreeCharacterPair hc hσ hlocal hq hpair
  have hHθ : ∃ y : ↥(derivedOf N), (y : ↥N) ∈ hallCore ↥N ∧ y ∉ charValueKernel β := by
    rw [Set.not_subset] at hker
    obtain ⟨y, hy, hy'⟩ := hker
    exact ⟨y, (Subgroup.mem_subgroupOf).1 hy, hy'⟩
  have hD := isDadeData_of_isTypeII hG h₁ h₂ hN htype hc
  have hJbot := hallSignalizerOn_eq_bot_of_isTypeII hG h₁ h₂ hN htype hc
  set B : Set G := fixedSet (⁅N, N⁆ : Subgroup G) (hallCoreOf N) with hBdef
  have hAB : (fun x : ↥N => (x : G)) '' fixedSetIn (hallCore ↥N) (derivedOf N) ⊆ B :=
    image_fixedSetIn_subset_fixedSet N
  have hT : ∀ u ∈ B, CFSG.FeitThompson.Prep09.hallSignalizerOn N u = ⊥ := fun u hu =>
    hJbot u (Or.inl (by rw [coreFixedSet_hallCoreIn_eq_fixedSet]; exact hu))
  have hstab : {g : G | (fun x => g⁻¹ * x * g) '' cyclicTIDiff (W₁ ⊔ W₂) W₂ W₁
      = cyclicTIDiff (W₁ ⊔ W₂) W₂ W₁} = ((W₁ ⊔ W₂ : Subgroup G) : Set G) :=
    hWpair.setOf_conj_eq_self
  have hdisj : ∀ g ∉ (W₁ ⊔ W₂ : Subgroup G),
      (fun x => g⁻¹ * x * g) '' cyclicTIDiff (W₁ ⊔ W₂) W₂ W₁ ∩ cyclicTIDiff (W₁ ⊔ W₂) W₂ W₁
        = ∅ := hWpair.inter_eq_empty
  obtain ⟨qw, hqw, ε, hε, lam, hlamV, hlamS, hlamnr, hlamorth, hlam1, hlam2⟩ :=
    exists_column_witness_of_fourFamily hmapW hmap1 hmap2 hlocal hσ
      (H := hallCore ↥N) (subgroupOf_le_hallCore_of_le hc.le_hallCore_W₂)
      (fixedSetIn_subset_sdiff _ _) (conj_image_fixedSetIn _ _)
      (fun y hy hy1 => sdiff_inf_centralizer_subset_fixedSetIn _ _ hy hy1)
      (image_bridgeSupport_subset hc) hD hstab hdisj hWpair hω hG.odd_natCard hj hβ hHθ hξ hdegβ
      hAB
  have ha : ∀ i, a i ∈ Irr ↥W₁ := fun i => harange ▸ Set.mem_range_self i
  have hb : ∀ jj, b jj ∈ Irr ↥W₂ := fun jj => hbrange ▸ Set.mem_range_self jj
  set pI : I → Irr ↥W₁ := fun i => ⟨a i, ha i⟩ with hpI
  set qJ : J → Irr ↥W₂ := fun jj => ⟨b jj, hb jj⟩ with hqJ
  have hqJbij : Function.Bijective qJ := by
    refine ⟨fun x y hxy => hbinj (Subtype.ext_iff.1 hxy), fun q => ?_⟩
    have hmem : (q : ↥W₂ → ℂ) ∈ Set.range b := by rw [hbrange]; exact q.2
    obtain ⟨jj, hjj⟩ := hmem
    exact ⟨jj, Subtype.ext hjj⟩
  have hpIsurj : Function.Surjective pI := fun p => by
    have hmem : (p : ↥W₁ → ℂ) ∈ Set.range a := by rw [harange]; exact p.2
    obtain ⟨i, hi⟩ := hmem
    exact ⟨i, Subtype.ext hi⟩
  have hetaeq : ∀ (i : I) (jj : J), η i jj = hWspec.prodCharEta ω (pI i) (qJ jj) := by
    intro i jj
    obtain ⟨p, q, hp, hq, hval⟩ := eta_eq_prodCharEta_of_data hWspec harange hbrange hw hη i jj
    rw [hval]
    congr 1
    · exact Subtype.ext hp
    · exact Subtype.ext hq
  obtain ⟨i₁, hi₁⟩ := hpIsurj qw
  refine ⟨i₁, ?_, ε, hε, lam, hlamV, ?_, ?_, ?_, ?_, ?_⟩
  · intro hcon
    refine hqw ?_
    rw [← hi₁, hcon]
    exact eq_principalIrr_of_eq_one (by simpa [hpI] using hai₀)
  · rw [isSignedIrr_iff_mem_signedIrr]; exact hlamS
  · rw [cconj_eq_star]; exact fun hcon => hlamnr hcon.symm
  · intro i jj
    rw [cfIP_eq_cfInner, hetaeq i jj, ← prodCharEta_swap hWspec hWpair ω (pI i) (qJ jj)]
    exact hlamorth (qJ jj) (pI i)
  · intro z hz
    have hkey := hlam1 z (notMem_totalDadeSupport_of_notMem_conjClosure hT hz)
    rw [cconj_eq_star]
    simpa using hkey
  · intro z hz
    have hkey := hlam2 z (notMem_totalDadeSupport_of_notMem_conjClosure hT hz)
    have hcol : hWpair.prodCharEtaColSum ω qw = ∑ jj : J, η i₁ jj := by
      rw [← hi₁, prodCharEtaColSum_swap_eq_sum hWspec hWpair ω (pI i₁)]
      exact (Fintype.sum_bijective qJ hqJbij _ _ fun jj => hetaeq i₁ jj).symm
    rw [hcol] at hkey
    exact hkey

theorem FPF_type_ii_nonfrobenius_crossed_column_data
    (h₁ : Statements.FTS_canonical_signalizer_structure.{u})
    (h₂ : Statements.FTS_type_II_extended_support_ti.{u}) :
    Statements.FPF_type_ii_nonfrobenius_crossed_column_data.{u, v} :=
  FPF_type_ii_nonfrobenius_crossed_column_data_aux h₁ h₂

end CFSG.FeitThompson.Proofs

end
