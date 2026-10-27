module

public import CFSG.FeitThompson.Representations.TypePOrientedCoreFamily
public import CFSG.FeitThompson.Local.TypePInnerActionFaithful
public import CFSG.FeitThompson.Representations.DetectingFamilyImagePuncturedNorm
public import CFSG.FeitThompson.Representations.SingleRowPunctureNormLowerBound
public import CFSG.FeitThompson.Representations.DetectingInducedImagePuncturedNormBound
public import CFSG.FeitThompson.Representations.SaturatedSignedArraySingleCharacter
public import CFSG.FeitThompson.Representations.MixedValuesNormTwoArrayDifference

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup Pointwise
open CFSG.FeitThompson.Prep03
open CFSG.FeitThompson.Prep05 (IsMinimalSimpleOdd hallCoreOf fittingOf
  centralizerIn)

attribute [local instance] CFSG.FeitThompson.subgroupFintype

universe u

variable {G : Type*} [Group G]

open scoped Classical in
theorem sumSqOn_sharp_eq_sum_erase [Fintype G] (X : Subgroup G) (f : G → ℂ) :
    sumSqOn (Prep03.sharp X) f = ∑ z ∈ Finset.univ.erase (1 : ↥X), ‖f (z : G)‖ ^ 2 := by
  classical
  have h1 : sumSqOn (Prep03.sharp X) f = ∑ x ∈ (Prep03.sharp X).toFinset, ‖f x‖ ^ 2 := by
    rw [sumSqOn]
    have h := Finset.sum_indicator_subset (fun y => ‖f y‖ ^ 2)
      (s := (Prep03.sharp X).toFinset) (t := Finset.univ) (Finset.subset_univ _)
    rw [Set.coe_toFinset] at h
    exact h
  rw [h1]
  refine (Finset.sum_bij' (i := fun (z : ↥X) _ => (z : G))
    (j := fun (x : G) (hx : x ∈ (Prep03.sharp X).toFinset) =>
      (⟨x, (Set.mem_toFinset.1 hx).1⟩ : ↥X)) ?_ ?_ ?_ ?_ ?_).symm
  · intro z hz
    refine Set.mem_toFinset.2 ⟨z.2, ?_⟩
    simp only [Set.mem_singleton_iff]
    exact fun hc => (Finset.mem_erase.1 hz).1 (Subtype.ext hc)
  · intro x hx
    refine Finset.mem_erase.2 ⟨?_, Finset.mem_univ _⟩
    intro hc
    exact (Set.mem_toFinset.1 hx).2 (by simpa using (Subtype.ext_iff.1 hc))
  · intro z _; rfl
  · intro x _; rfl
  · intro z _; rfl

theorem sum_eq_sum_of_mem_iff {A : Type*} (s t : Finset A) (f : A → ℝ)
    (h : ∀ a, a ∈ s ↔ a ∈ t) : ∑ z ∈ s, f z = ∑ z ∈ t, f z :=
  Finset.sum_congr (Finset.ext h) fun _ _ => rfl

open scoped Classical in
theorem sumSqOn_sharp_map_subtype_eq_sum_erase [Fintype G] {M : Subgroup G} (K : Subgroup ↥M)
    (f : G → ℂ) :
    sumSqOn (Prep03.sharp (K.map M.subtype)) f
      = ∑ z ∈ Finset.univ.erase (1 : ↥K), ‖f ((z : ↥M) : G)‖ ^ 2 := by
  classical
  rw [sumSqOn_sharp_eq_sum_erase]
  set e : ↥K ≃ ↥(K.map M.subtype) :=
    (Subgroup.equivMapOfInjective K M.subtype M.subtype_injective).toEquiv with he
  have hcoe : ∀ z : ↥K, ((e z : ↥(K.map M.subtype)) : G) = ((z : ↥M) : G) := fun z => rfl
  have hone : e 1 = 1 := by
    rw [he]; exact map_one (Subgroup.equivMapOfInjective K M.subtype M.subtype_injective)
  refine (Finset.sum_equiv e ?_ ?_).symm
  · intro z
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact ⟨fun h hc => h (e.injective (by rw [hc, hone])), fun h hc => h (by rw [hc, hone])⟩
  · intro z _
    rw [hcoe]

theorem le_sumSqOn_sharp_map_subtype [Fintype G] {M : Subgroup G} {K : Subgroup ↥M}
    {f : G → ℂ} {c : ℝ} (s : Finset ↥K) (hs : ∀ a, a ∈ s ↔ a ≠ 1)
    (h : c ≤ ∑ z ∈ s, ‖f ((z : ↥M) : G)‖ ^ 2) :
    c ≤ sumSqOn (Prep03.sharp (K.map M.subtype)) f := by
  classical
  rw [sumSqOn_sharp_map_subtype_eq_sum_erase]
  exact h.trans (le_of_eq (sum_eq_sum_of_mem_iff _ _ _ fun a => by simp [Finset.mem_erase, hs a]))

theorem hallCoreIn_le_fittingIn [Finite G] {M U W₁ W₂ : Subgroup G}
    (hc : IsWitnessedPConfiguration M U W₁ W₂) : Prep03.hallCoreIn M ≤ Prep03.fittingIn M := by
  intro x hxH
  have h := hc.coe_fittingRaw_eq
  change x ∈ ((Prep03.fittingIn M : Subgroup G) : Set G)
  rw [Prep03.fittingIn, h]
  exact ⟨x, hxH, 1, one_mem _, mul_one x⟩

theorem two_le_card_fittingIn [Finite G] {M U W₁ W₂ : Subgroup G}
    (hc : IsWitnessedPConfiguration M U W₁ W₂) : 2 ≤ Nat.card ↥(Prep03.fittingIn M) := by
  have hW₂F : W₂ ≤ Prep03.fittingIn M :=
    le_trans (le_trans hc.le_W₂ inf_le_left) (hallCoreIn_le_fittingIn hc)
  have h1 : 1 < Nat.card ↥W₂ := (Subgroup.one_lt_card_iff_ne_bot W₂).2 hc.ne_bot_W₂
  have h2 : Nat.card ↥W₂ ≤ Nat.card ↥(Prep03.fittingIn M) := Subgroup.card_le_of_le hW₂F
  omega

theorem notMem_fittingIn_mul [Finite G] {M U W₁ W₂ : Subgroup G}
    (hcfg : IsWitnessedPConfiguration M U W₁ W₂) {a b : G} (ha : a ∈ W₁) (ha1 : a ≠ 1)
    (hb : b ∈ Prep03.fittingIn M) : a * b ∉ Prep03.fittingIn M := by
  intro hmem
  refine ha1 ?_
  have hbK : b ∈ (⁅M, M⁆ : Subgroup G) := hcfg.fittingRaw_le_commutator hb
  have habK : a * b ∈ (⁅M, M⁆ : Subgroup G) := hcfg.fittingRaw_le_commutator hmem
  have haK : a ∈ (⁅M, M⁆ : Subgroup G) := by
    have h : a = a * b * b⁻¹ := by group
    rw [h]; exact mul_mem habK (inv_mem hbK)
  have h := disjoint_iff.1 hcfg.disjoint_commutator_W₁
  have hmem2 : a ∈ (⁅M, M⁆ : Subgroup G) ⊓ W₁ := ⟨haK, ha⟩
  rw [h, Subgroup.mem_bot] at hmem2
  exact hmem2

theorem natCard_W₁_mul_natCard_commutator [Finite G] {M U W₁ W₂ : Subgroup G}
    (hcfg : IsWitnessedPConfiguration M U W₁ W₂) :
    Nat.card ↥W₁ * Nat.card ↥(⁅M, M⁆ : Subgroup G) = Nat.card ↥M := by
  rw [← hcfg.relIndex_W₁_eq_natCard_commutator, Subgroup.relIndex,
    ← natCard_subgroupOf hcfg.le_M_W₁]
  exact Subgroup.card_mul_index _

theorem two_le_ncard_indFamDetect_of_mem {L : Subgroup G} [Fintype ↥L] {K : Subgroup ↥L}
    [K.Normal] (hodd : Odd (Nat.card ↥L)) {H : Subgroup ↥K} {f : ↥L → ℂ}
    (hf : f ∈ indFamDetect K H) : 2 ≤ (indFamDetect K H).ncard := by
  have h1 : star f ∈ indFamDetect K H := PrimeDadeSubcoherence.star_mem_indFamDetect hf
  have h2 : star f ≠ f := PrimeDadeSubcoherence.star_ne_self_of_mem_indFamDetect hodd hf
  have h3 : ({star f, f} : Set (↥L → ℂ)) ⊆ indFamDetect K H := by
    intro x hx
    rcases hx with hx | hx
    · exact hx ▸ h1
    · exact hx ▸ hf
  calc 2 = ({star f, f} : Set (↥L → ℂ)).ncard := (Set.ncard_pair h2).symm
    _ ≤ (indFamDetect K H).ncard := Set.ncard_le_ncard h3 (finite_indFamDetect K H)

def spanHomOfIsometry [Fintype G] {M : Subgroup G} {Sfam Tfam : Set (↥M → ℂ)}
    {ν : (↥M → ℂ) → (G → ℂ)} (hν : IsAdditiveIsometryOn Sfam ν)
    (hTS : Tfam ⊆ (Submodule.span ℤ Sfam : Set (↥M → ℂ))) :
    Submodule.span ℤ Tfam →+ Submodule.span ℤ (Irr G) where
  toFun f := ⟨ν (f : ↥M → ℂ),
    mem_span_Irr_of_mem_virtualChars (hν.2.1 _ (Submodule.span_le.2 hTS f.2))⟩
  map_zero' := by
    refine Subtype.ext ?_
    have h := hν.1 0 (zero_mem _) 0 (zero_mem _)
    simp only [add_zero] at h
    change ν ((0 : Submodule.span ℤ Tfam) : ↥M → ℂ) = 0
    have h0 : ((0 : Submodule.span ℤ Tfam) : ↥M → ℂ) = 0 := rfl
    rw [h0]
    exact add_eq_left.1 h.symm
  map_add' f g :=
    Subtype.ext (hν.1 _ (Submodule.span_le.2 hTS f.2) _ (Submodule.span_le.2 hTS g.2))

@[simp] theorem coe_spanHomOfIsometry_apply [Fintype G] {M : Subgroup G}
    {Sfam Tfam : Set (↥M → ℂ)} {ν : (↥M → ℂ) → (G → ℂ)} (hν : IsAdditiveIsometryOn Sfam ν)
    (hTS : Tfam ⊆ (Submodule.span ℤ Sfam : Set (↥M → ℂ))) (f : Submodule.span ℤ Tfam) :
    (spanHomOfIsometry hν hTS f : G → ℂ) = ν (f : ↥M → ℂ) := (rfl)

theorem coe_spanHomOfIsometry_charSpanZero [Fintype G] {M : Subgroup G}
    {Sfam Tfam : Set (↥M → ℂ)} {ν : (↥M → ℂ) → (G → ℂ)} (hν : IsAdditiveIsometryOn Sfam ν)
    (hTS : Tfam ⊆ (Submodule.span ℤ Sfam : Set (↥M → ℂ)))
    (hind : ∀ f ∈ Submodule.span ℤ Tfam, f 1 = 0 → ν f = fun x => indG M f x)
    (f : charSpanZero Tfam) :
    (spanHomOfIsometry hν hTS (Submodule.inclusion (charSpanZero_le _) f) : G → ℂ)
      = indClassFun M (f : ↥M → ℂ) := by
  obtain ⟨hspan, h1⟩ := mem_charSpanZero.1 f.2
  rw [coe_spanHomOfIsometry_apply]
  change ν (f : ↥M → ℂ) = indClassFun M (f : ↥M → ℂ)
  rw [hind _ hspan h1]
  rfl

theorem cfInner_spanHomOfIsometry [Fintype G] {M : Subgroup G} {Sfam Tfam : Set (↥M → ℂ)}
    {ν : (↥M → ℂ) → (G → ℂ)} (hν : IsAdditiveIsometryOn Sfam ν)
    (hTS : Tfam ⊆ (Submodule.span ℤ Sfam : Set (↥M → ℂ)))
    (f g : Submodule.span ℤ Tfam) :
    cfInner (spanHomOfIsometry hν hTS f : G → ℂ) (spanHomOfIsometry hν hTS g : G → ℂ)
      = cfInner (f : ↥M → ℂ) (g : ↥M → ℂ) :=
  hν.2.2 _ (Submodule.span_le.2 hTS f.2) _ (Submodule.span_le.2 hTS g.2)

theorem mul_mem_cyclicTIDiff {W₁ W₂ : Subgroup G} (hinf : W₁ ⊓ W₂ = ⊥) {a b : G}
    (ha : a ∈ W₁) (ha1 : a ≠ 1) (hb : b ∈ W₂) (hb1 : b ≠ 1) :
    a * b ∈ cyclicTIDiff (W₁ ⊔ W₂) W₁ W₂ := by
  rw [mem_cyclicTIDiff]
  refine ⟨mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb), ?_, ?_⟩
  · intro h
    refine hb1 ?_
    have hmem : b ∈ W₁ ⊓ W₂ := ⟨by simpa using mul_mem (W₁.inv_mem ha) h, hb⟩
    rw [hinf, Subgroup.mem_bot] at hmem
    exact hmem
  · intro h
    refine ha1 ?_
    have hmem : a ∈ W₁ ⊓ W₂ := ⟨ha, by simpa using mul_mem h (W₂.inv_mem hb)⟩
    rw [hinf, Subgroup.mem_bot] at hmem
    exact hmem

theorem eta_apply_mul [Fintype G] {W₁ W₂ : Subgroup G}
    (hW : IsCyclicTIPair (W₁ ⊔ W₂) W₁ W₂)
    {ω : (↥(W₁ ⊔ W₂) → ℂ) → (G → ℂ)}
    (hω : IsTIExtension W₁ W₂ (⊤ : Subgroup G) (fun f x => ω f (x : G)))
    {I J : Type} {α : I → ↥W₁ → ℂ} {β : J → ↥W₂ → ℂ}
    (hα : ∀ i, α i ∈ Irr ↥W₁) (hβ : ∀ j, β j ∈ Irr ↥W₂)
    (hαinj : Function.Injective α) (hβinj : Function.Injective β)
    (hαsurj : ∀ χ ∈ Irr ↥W₁, ∃ i, α i = χ) (hβsurj : ∀ χ ∈ Irr ↥W₂, ∃ j, β j = χ)
    {w : I → J → ↥(W₁ ⊔ W₂) → ℂ}
    (hw : ∀ i j, ∀ x : ↥W₁, ∀ y : ↥W₂, ∀ z : ↥(W₁ ⊔ W₂), (z : G) = (x : G) * (y : G) →
      w i j z = α i x * β j y)
    {η : I → J → G → ℂ} (hη : ∀ i j, η i j = ω (w i j)) (i : I) (j : J)
    {a b : G} (ha : a ∈ W₁) (ha1 : a ≠ 1) (hb : b ∈ W₂) (hb1 : b ≠ 1) :
    η i j (a * b) = α i ⟨a, ha⟩ * β j ⟨b, hb⟩ := by
  have hiso : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ (tiExtensionHom hω) :=
    isCyclicTIIsometry_tiExtensionHom hω
  have hmem : a * b ∈ cyclicTIDiff (W₁ ⊔ W₂) W₁ W₂ :=
    mul_mem_cyclicTIDiff hW.inf_eq_bot ha ha1 hb hb1
  rw [eta_eq_prodCharEta hW hω hα hβ hαinj hβinj hαsurj hβsurj hw hη i j,
    IsCyclicTIPair.prodCharEta_apply_of_mem_cyclicTIDiff hW hiso _ _ hmem]
  rw [coe_irrEquivOfEnum_apply, coe_irrEquivOfEnum_apply]
  exact hW.prodChar_apply_mul (α i) (β j) ha hb

theorem eta_mem_span_Irr [Fintype G] {W₁ W₂ : Subgroup G}
    (hW : IsCyclicTIPair (W₁ ⊔ W₂) W₁ W₂)
    {ω : (↥(W₁ ⊔ W₂) → ℂ) → (G → ℂ)}
    (hω : IsTIExtension W₁ W₂ (⊤ : Subgroup G) (fun f x => ω f (x : G)))
    {I J : Type} {α : I → ↥W₁ → ℂ} {β : J → ↥W₂ → ℂ}
    (hα : ∀ i, α i ∈ Irr ↥W₁) (hβ : ∀ j, β j ∈ Irr ↥W₂)
    (hαinj : Function.Injective α) (hβinj : Function.Injective β)
    (hαsurj : ∀ χ ∈ Irr ↥W₁, ∃ i, α i = χ) (hβsurj : ∀ χ ∈ Irr ↥W₂, ∃ j, β j = χ)
    {w : I → J → ↥(W₁ ⊔ W₂) → ℂ}
    (hw : ∀ i j, ∀ x : ↥W₁, ∀ y : ↥W₂, ∀ z : ↥(W₁ ⊔ W₂), (z : G) = (x : G) * (y : G) →
      w i j z = α i x * β j y)
    {η : I → J → G → ℂ} (hη : ∀ i j, η i j = ω (w i j)) (i : I) (j : J) :
    η i j ∈ Submodule.span ℤ (Irr G) := by
  rw [eta_eq_prodCharEta hW hω hα hβ hαinj hβinj hαsurj hβsurj hw hη i j]
  exact mem_span_Irr_of_mem_virtualChars
    (hW.prodCharEta_mem_virtualChars (isCyclicTIIsometry_tiExtensionHom hω) _ _)

theorem mem_Irr_comp_zpowers {W₁ : Subgroup G} {χ : ↥W₁ → ℂ} (hχ : χ ∈ Irr ↥W₁)
    {y : G} (hgen : Subgroup.zpowers y = W₁) :
    (fun z : ↥(Subgroup.zpowers y) => χ ⟨(z : G), hgen ▸ z.2⟩)
      ∈ Irr ↥(Subgroup.zpowers y) := by
  have h := FrobeniusInduction.mem_Irr_comp_mulEquiv hχ (MulEquiv.subgroupCongr hgen)
  have heq : (fun z : ↥(Subgroup.zpowers y) => χ ⟨(z : G), hgen ▸ z.2⟩)
      = χ ∘ (MulEquiv.subgroupCongr hgen) :=
    funext fun z => congrArg χ (Subtype.ext (MulEquiv.subgroupCongr_apply hgen z).symm)
  rw [heq]; exact h

theorem index_fittingRaw_eq [Finite G] {M U W₁ W₂ : Subgroup G}
    (hcyc : IsPrimeCyclicTIHyp (commutator ↥M) (W₁.subgroupOf M) (W₂.subgroupOf M))
    (hmac : IsMinimalAbelianCore (commutator ↥M) (W₁.subgroupOf M) (W₂.subgroupOf M)
      (hallCore ↥M) (U.subgroupOf M))
    (hcp : coreProduct (hallCore ↥M) (U.subgroupOf M) = fittingRaw ↥M)
    (hUM : U ≤ M) (hW₁M : W₁ ≤ M) :
    (fittingRaw ↥M).index = Nat.card ↥W₁ * (cent U (Prep03.hallCoreIn M : Set G)).relIndex U := by
  have h := IsMinimalAbelianCore.index_coreProduct hcyc hmac
  rw [hcp] at h
  rw [h, natCard_subgroupOf hW₁M]
  congr 1
  have hC : coreCentralizer (hallCore ↥M) (U.subgroupOf M)
      = (cent U (Prep03.hallCoreIn M : Set G)).subgroupOf M := by
    rw [← OrientedCoreFamily.map_subtype_coreCentralizer M U hUM,
      OrientedCoreFamily.subgroupOf_map_subtype_self]
  rw [hC, Subgroup.relIndex_subgroupOf hUM]

theorem two_mul_add_one_le_pow_of_le_div {p q u : ℕ} (hp : 3 ≤ p)
    (hu : u ≤ (p ^ q - 1) / (p - 1)) : 2 * u + 1 ≤ p ^ q := by
  have h1 : (p ^ q - 1) / (p - 1) ≤ (p ^ q - 1) / 2 :=
    Nat.div_le_div_left (by omega) (by omega)
  have h2 : 2 * ((p ^ q - 1) / 2) ≤ p ^ q - 1 := by
    rw [mul_comm]; exact Nat.div_mul_le_self _ _
  have h3 : 1 ≤ p ^ q := Nat.one_le_pow _ _ (by omega)
  omega

theorem relIndex_le_div_of_elementary_core_structure
    (h₁ : CFSG.FeitThompson.Statements.FNI_type_p_elementary_core_structure.{u}) {G : Type u} [Group G]
    [Finite G] (hG : IsMinimalSimpleOdd G) {M U W₁ W₂ : Subgroup G} (hM : IsCoatom M)
    (hc : IsWitnessedPConfiguration M U W₁ W₂) {p q : ℕ} (hp : p = Nat.card ↥W₂)
    (hq : q = Nat.card ↥W₁) :
    (centralizerIn U (hallCoreOf M)).relIndex U ≤ (p ^ q - 1) / (p - 1) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hVex, -, -, -, -, -, -, -, -, -, -, -⟩ :=
    h₁ G hG M U W₁ W₂ hM hc p q hp hq
  obtain ⟨V, hVadd, hVmod, -, ⟨eV⟩⟩ := hVex
  have hHM : M ≤ normalizer ((hallCoreOf M : Subgroup G) : Set G) :=
    le_normalizer_map_subtype_hallCore M
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hle⟩ :=
    CFSG.FeitThompson.Proofs.FNI_type_p_core_linear_alternative h₁ G hG M U W₁ W₂ hM hc p q
      ((centralizerIn U (hallCoreOf M)).relIndex U) ((p ^ q - 1) / (p - 1)) hp hq rfl rfl
      V eV (conjLinear p hHM eV) (isConjModule_conjLinear p hHM eV) _ _ rfl rfl
  exact hle

theorem exists_intCast_eq_neg_one_pow_mul (e : ℕ) {δ : ℂ} (hδ : δ = 1 ∨ δ = -1)
    (he : e = 0 ∨ e = 1) : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ((ε : ℂ) = (-1 : ℂ) ^ e * δ) := by
  rcases hδ with rfl | rfl
  · exact ⟨(-1) ^ e, by rcases he with rfl | rfl <;> simp, by push_cast; ring⟩
  · exact ⟨-(-1) ^ e, by rcases he with rfl | rfl <;> simp, by push_cast; ring⟩

namespace IsMinimalAbelianCore

theorem mem_indFamDetect_of_mem_indFamDetect_coreProduct_of_mem_Irr
    {L : Type*} [Group L] [Fintype L] {K W₁ W₂ H U : Subgroup L}
    {σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun L} [Fintype ↥(W₁ ⊔ W₂)]
    [(coreProduct H U).Normal] (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hc : IsMinimalAbelianCore K W₁ W₂ H U) (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ)
    {ζ : L → ℂ} (hζ : ζ ∈ indFamDetect (coreProduct H U) (H.subgroupOf (coreProduct H U)))
    (hIrr : ζ ∈ Irr L) : ζ ∈ indFamDetect K (H.subgroupOf K) := by
  classical
  have : Fintype ↑(Irr ↥W₁) := Fintype.ofFinite _
  have hnorm1 : cfInner ζ ζ = 1 := cfInner_self_of_mem_Irr hIrr
  rcases eq_primeTIrow_or_exists_sum_of_mem_indFamDetect_coreProduct h hc hσ hζ with
    ⟨j, hj, rfl⟩ | ⟨n, hn, heq⟩
  · exfalso
    rw [h.cfInner_self_primeTIrow hσ] at hnorm1
    have h1 : Nat.card ↥W₁ = 1 := by exact_mod_cast hnorm1
    exact hc.prime_natCard.one_lt.ne' h1
  · by_contra hnot
    have hzero : cfInner ζ ζ = 0 := by
      nth_rewrite 1 [heq]
      rw [cfInner_sum_smul_left]
      refine Finset.sum_eq_zero fun χ _ => ?_
      by_cases hχ : n χ = 0
      · simp [hχ]
      · have hIrr2 : indClassFun K (χ : ↥K → ℂ) ∈ Irr L := (hn χ hχ).2
        have hne : indClassFun K (χ : ↥K → ℂ) ≠ ζ := fun hc2 => hnot (hc2 ▸ (hn χ hχ).1)
        rw [cfInner_eq_zero_of_mem_Irr hIrr2 hIrr hne, mul_zero]
    rw [hnorm1] at hzero
    exact one_ne_zero hzero

end IsMinimalAbelianCore

set_option maxHeartbeats 2000000 in
theorem threeFittingNormBounds_aux
    (h₁ : CFSG.FeitThompson.Statements.FNI_type_p_elementary_core_structure.{u}) :
    CFSG.FeitThompson.Statements.FCH_type_p_three_fitting_norm_bounds.{u} := by
  classical
  intro G _ _ hG M U W₁ W₂ hcfg u hu I J fI fJ i0 j0' α β hα hβ hαinj hβinj hαsurj hβsurj
    hα0 hβ0 bar hbar w hw σ ω hσ hω δj μ0 ell μ Mrow η hδj hμ0 hμ0Irr hell hμ hMrow hη
    Sfam Tfam ν δ e hS hT hδ he hνiso hTS hdeg hνind hSirr hrow hcolorth hdist hnormrow
    i0' hi0' j₀ hj₀
  have hG5 : IsMinimalSimpleOdd G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.forall_isSolvable⟩
  obtain ⟨-, hpp, hqp, hop, hoq, hpq, hUne, hUab, hsemi1, hsemi2, hcopH, hfreeUW, hVex,
    hcardH, -, hCW, -, hmin, hCltU, hnormC, hdir, hFab, -, -⟩ :=
    h₁ G hG5 M U W₁ W₂ hcfg.isCoatom hcfg.config _ _ rfl rfl
  have hTT : Tfam = indFamDetect (fittingRaw ↥M) ((hallCore ↥M).subgroupOf (fittingRaw ↥M)) :=
    hT.trans (OrientedCoreFamily.detectInd_fittingIn_eq_indFamDetect M)
  have hSS : Sfam = indFamDetect (commutator ↥M) ((hallCore ↥M).subgroupOf (commutator ↥M)) :=
    hS.trans (OrientedCoreFamily.detectInd_commutator_eq_indFamDetect M)
  have hFnormal : (fittingRaw ↥M).Normal := fittingRaw_normal ↥M
  have hPnormal : (hallCore ↥M).Normal := hallCore_normal
  have hFab' : IsMulCommutative ↥(fittingRaw ↥M) :=
    OrientedCoreFamily.isMulCommutative_of_map_subtype hFab
  have hPH : hallCore ↥M ≤ fittingRaw ↥M := hallCore_le_fittingRaw
  have hmac : IsMinimalAbelianCore (commutator ↥M) (W₁.subgroupOf M) (W₂.subgroupOf M)
      (hallCore ↥M) (U.subgroupOf M) :=
    OrientedCoreFamily.isMinimalAbelianCore_of_isWitnessedPConfiguration h₁ hcfg.ambient
      hcfg.isCoatom hcfg.config
  have hcyc : IsPrimeCyclicTIHyp (commutator ↥M) (W₁.subgroupOf M) (W₂.subgroupOf M) :=
    OrientedCoreFamily.isPrimeCyclicTIHyp_commutator hG.odd_natCard hcfg.config
  have hcp : coreProduct (hallCore ↥M) (U.subgroupOf M) = fittingRaw ↥M :=
    OrientedCoreFamily.coreProduct_eq_fittingRaw hcfg.config.le_M_E hdir
  have hcpn : (coreProduct (hallCore ↥M) (U.subgroupOf M)).Normal := hcp ▸ hFnormal
  obtain ⟨σ', hσ'⟩ := hcyc.exists_isCyclicTIIsometry
  have hcopW : (Nat.card ↥W₁).Coprime (Nat.card ↥W₂) :=
    (Nat.coprime_primes hqp hpp).2 (fun h => hpq h.symm)
  have hW : IsCyclicTIPair (W₁ ⊔ W₂) W₁ W₂ :=
    hcfg.config.isCyclicTIPair_sup hG.odd_natCard hcopW
  obtain ⟨hrowT, hrowcoef, hrowoth⟩ := hdist j₀ hj₀
  have hcard : 2 ≤ (indFamDetect (fittingRaw ↥M)
      ((hallCore ↥M).subgroupOf (fittingRaw ↥M))).ncard :=
    two_le_ncard_indFamDetect_of_mem (odd_natCard_subgroup hG.odd_natCard M) (hTT ▸ hrowT)
  have hTS' : indFamDetect (fittingRaw ↥M) ((hallCore ↥M).subgroupOf (fittingRaw ↥M))
      ⊆ (Submodule.span ℤ Sfam : Set (↥M → ℂ)) := hTT ▸ hTS
  set νh := spanHomOfIsometry hνiso hTS' with hνh
  have hνh' : ∀ f : charSpanZero (indFamDetect (fittingRaw ↥M)
        ((hallCore ↥M).subgroupOf (fittingRaw ↥M))),
      (νh (Submodule.inclusion (charSpanZero_le _) f) : G → ℂ)
        = indClassFun M (f : ↥M → ℂ) :=
    coe_spanHomOfIsometry_charSpanZero hνiso hTS' (fun f hf h1 => hνind f (hTT ▸ hf) h1)
  have hνhcoe : ∀ (f : ↥M → ℂ) (hf : f ∈ Submodule.span ℤ (indFamDetect (fittingRaw ↥M)
        ((hallCore ↥M).subgroupOf (fittingRaw ↥M)))),
      (νh ⟨f, hf⟩ : G → ℂ) = ν f := fun f hf => coe_spanHomOfIsometry_apply hνiso hTS' ⟨f, hf⟩
  have hνhiso : ∀ f g : Submodule.span ℤ (indFamDetect (fittingRaw ↥M)
      ((hallCore ↥M).subgroupOf (fittingRaw ↥M))),
      cfInner (νh f : G → ℂ) (νh g : G → ℂ) = cfInner (f : ↥M → ℂ) (g : ↥M → ℂ) :=
    cfInner_spanHomOfIsometry hνiso hTS'
  have hidx : (fittingRaw ↥M).index = Nat.card ↥W₁ * u := by
    rw [index_fittingRaw_eq hcyc hmac hcp hcfg.config.le_M_E hcfg.config.le_M_W₁, ← hu]
  have hu0 : 0 < u := by
    rw [hu, Subgroup.relIndex]
    exact Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hp3 : 3 ≤ Nat.card ↥W₂ := by
    have h2 := hpp.two_le
    have hne : Nat.card ↥W₂ ≠ 2 := fun h => (Nat.not_odd_iff_even.2 (h ▸ (by decide))) hop
    omega
  have hcardP : Nat.card ↥(hallCore ↥M) = Nat.card ↥W₂ ^ Nat.card ↥W₁ := by
    rw [← Subgroup.card_subtype M (hallCore ↥M)]; exact hcardH
  have hPu : 2 * u + 1 ≤ Nat.card ↥(hallCore ↥M) := by
    rw [hcardP]
    refine two_mul_add_one_le_pow_of_le_div hp3 ?_
    rw [hu]
    exact relIndex_le_div_of_elementary_core_structure h₁ hG5 hcfg.isCoatom hcfg.config rfl rfl
  obtain ⟨y0, hy0W, hy01, hy0gen⟩ := exists_zpowers_eq_of_prime_natCard hqp
  obtain ⟨x0, hx0W, hx01⟩ : ∃ x, x ∈ W₂ ∧ x ≠ (1 : G) := by
    obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hcfg.config.ne_bot_W₂
    exact ⟨(x : G), x.2, fun hc => hx (Subtype.ext hc)⟩
  have hxP : (⟨x0, hcfg.config.le_M_W₂ hx0W⟩ : ↥M) ∈ hallCore ↥M :=
    OrientedCoreFamily.le_hallCore_subgroupOf_W₂ hcfg.config (Subgroup.mem_subgroupOf.2 hx0W)
  have hx1 : (⟨x0, hcfg.config.le_M_W₂ hx0W⟩ : ↥M) ≠ 1 :=
    fun hc => hx01 (by simpa using Subtype.ext_iff.1 hc)
  have hx0F : x0 ∈ Prep03.fittingIn M := ⟨⟨x0, hcfg.config.le_M_W₂ hx0W⟩, hPH hxP, rfl⟩
  have hy0ord : orderOf y0 = Nat.card ↥W₁ := by rw [← Nat.card_zpowers y0, hy0gen]
  have hyord : orderOf (⟨y0, hcfg.config.le_M_W₁ hy0W⟩ : ↥M) = Nat.card ↥W₁ := by
    rw [← Subgroup.orderOf_coe (⟨y0, hcfg.config.le_M_W₁ hy0W⟩ : ↥M)]; exact hy0ord
  have hxy : Commute (⟨x0, hcfg.config.le_M_W₂ hx0W⟩ : ↥M)
      (⟨y0, hcfg.config.le_M_W₁ hy0W⟩ : ↥M) :=
    Subtype.ext (hcfg.config.commute_W₁_W₂ hy0W hx0W).symm.eq
  have hy0j : ∀ j : ℕ, 1 ≤ j → j ≤ Nat.card ↥W₁ - 1 → y0 ^ j ∈ W₁ ∧ y0 ^ j ≠ 1 := by
    intro j hj1 hj2
    exact ⟨pow_mem hy0W j, pow_ne_one_of_lt_orderOf (by omega) (by rw [hy0ord]; omega)⟩
  have hcardF : Nat.card ↥(Prep03.fittingIn M) = Nat.card ↥(fittingRaw ↥M) := Subgroup.card_subtype M _
  refine ⟨?_, ?_, ?_⟩
  ·
    have hΘ : (fun z : ↥(Subgroup.zpowers y0) => α i0' ⟨(z : G), hy0gen ▸ z.2⟩)
        ∈ Irr ↥(Subgroup.zpowers y0) := mem_Irr_comp_zpowers (hα i0') hy0gen
    have hmatch : ∀ j : ℕ, 1 ≤ j → j ≤ Nat.card ↥W₁ - 1 →
        η i0' j0' (y0 ^ j * x0)
          = (fun z : ↥(Subgroup.zpowers y0) => α i0' ⟨(z : G), hy0gen ▸ z.2⟩)
              (⟨y0, Subgroup.mem_zpowers _⟩ ^ j) := by
      intro j hj1 hj2
      obtain ⟨hmem, hne⟩ := hy0j j hj1 hj2
      rw [eta_apply_mul hW hω hα hβ hαinj hβinj hαsurj hβsurj hw hη i0' j0' hmem hne hx0W hx01]
      have hβval : β j0' ⟨x0, hx0W⟩ = 1 := by rw [hβ0]; rfl
      rw [hβval, mul_one]
      exact congrArg (α i0') (Subtype.ext (by push_cast; rfl))
    have horth : ∀ ξ, ∀ hξ : ξ ∈ indFamDetect (fittingRaw ↥M)
          ((hallCore ↥M).subgroupOf (fittingRaw ↥M)),
        cfInner (νh ⟨ξ, Submodule.subset_span hξ⟩ : G → ℂ) (η i0' j0') = 0 := by
      intro ξ hξ
      rw [hνhcoe]
      exact hcolorth i0' hi0' ξ (hTT ▸ hξ)
    have key := card_sub_one_le_sum_norm_sq_of_forall_cfInner_eq_zero (S := M)
      (H := fittingRaw ↥M) (P := hallCore ↥M) hPH νh hνh' hcard (χ := η i0' j0')
      (eta_mem_span_Irr hW hω hα hβ hαinj hβinj hαsurj hβsurj hw hη i0' j0')
      horth hqp hxP hx1 hyord hxy hΘ hmatch
    rw [hcardF]
    exact le_sumSqOn_sharp_map_subtype (K := fittingRaw ↥M) _ (fun a => by simp) key
  ·
    set ζ := Mrow (if e = 0 then j₀ else bar j₀) with hζdef
    have hζT : ζ ∈ indFamDetect (fittingRaw ↥M)
      ((hallCore ↥M).subgroupOf (fittingRaw ↥M)) := hTT ▸ hrowT
    obtain ⟨ε, hεpm, hεval⟩ := exists_intCast_eq_neg_one_pow_mul e hδ he
    have hζχ : cfInner (νh ⟨ζ, Submodule.subset_span hζT⟩ : G → ℂ) (η i0 j₀) = (ε : ℂ) := by
      rw [hνhcoe, hεval]
      exact hrowcoef
    have horth : ∀ ξ, ∀ hξ : ξ ∈ indFamDetect (fittingRaw ↥M)
          ((hallCore ↥M).subgroupOf (fittingRaw ↥M)), ξ ≠ ζ →
        cfInner (νh ⟨ξ, Submodule.subset_span hξ⟩ : G → ℂ) (η i0 j₀) = 0 := by
      intro ξ hξ hne
      rw [hνhcoe]
      exact hrowoth ξ (hTT ▸ hξ) hne
    have key := card_div_sub_sq_le_sum_erase_norm_sq (S := M) (H := fittingRaw ↥M)
      (P := hallCore ↥M) hPH νh hνh' hcard (q := Nat.card ↥W₁) (u := u)
      (by rw [hidx]; ring) hPu hζT (hnormrow j₀ hj₀) hεpm
      (eta_mem_span_Irr hW hω hα hβ hαinj hβinj hαsurj hβsurj hw hη i0 j₀) hζχ horth
    have hq0 : (0 : ℝ) < (Nat.card ↥W₁ : ℝ) := by exact_mod_cast hqp.pos
    have heq : (Nat.card ↥M : ℝ) / (Nat.card ↥W₁ : ℝ)
        = (Nat.card ↥(⁅M, M⁆ : Subgroup G) : ℝ) := by
      have h : (Nat.card ↥W₁ : ℝ) * (Nat.card ↥(⁅M, M⁆ : Subgroup G) : ℝ)
          = (Nat.card ↥M : ℝ) := by
        exact_mod_cast natCard_W₁_mul_natCard_commutator hcfg.config
      field_simp
      linarith
    rw [heq] at key
    exact le_sumSqOn_sharp_map_subtype (K := fittingRaw ↥M) _ (fun a => by simp) key
  ·
    intro lam hlam
    obtain ⟨hlamT, hlamIrr⟩ := hlam
    have hlamT' : lam ∈ indFamDetect (fittingRaw ↥M)
      ((hallCore ↥M).subgroupOf (fittingRaw ↥M)) := hTT ▸ hlamT
    have hlamS : lam ∈ Sfam := by
      rw [hSS]
      refine IsMinimalAbelianCore.mem_indFamDetect_of_mem_indFamDetect_coreProduct_of_mem_Irr
        hcyc hmac hσ' ?_ hlamIrr
      rw [hcp]; exact hlamT'
    obtain ⟨-, -, hνvanish, -⟩ := hSirr lam ⟨hlamS, hlamIrr⟩
    have hval : ∀ j : ℕ, 1 ≤ j → j ≤ Nat.card ↥W₁ - 1 →
        (νh ⟨lam, Submodule.subset_span hlamT'⟩ : G → ℂ)
            (((⟨y0, hcfg.config.le_M_W₁ hy0W⟩ : ↥M) ^ j
              * (⟨x0, hcfg.config.le_M_W₂ hx0W⟩ : ↥M) : ↥M) : G)
          = lam ((⟨y0, hcfg.config.le_M_W₁ hy0W⟩ : ↥M) ^ j
              * (⟨x0, hcfg.config.le_M_W₂ hx0W⟩ : ↥M)) := by
      intro j hj1 hj2
      obtain ⟨hmem, hne⟩ := hy0j j hj1 hj2
      have hcoe : (((⟨y0, hcfg.config.le_M_W₁ hy0W⟩ : ↥M) ^ j
          * (⟨x0, hcfg.config.le_M_W₂ hx0W⟩ : ↥M) : ↥M) : G) = y0 ^ j * x0 := by
        push_cast; rfl
      have hV : y0 ^ j * x0 ∈ cyclicTIset W₁ W₂ := by
        rw [← cyclicTIDiff_sup_eq_cyclicTIset]
        exact mul_mem_cyclicTIDiff hW.inf_eq_bot hmem hne hx0W hx01
      have hnotF : y0 ^ j * x0 ∉ Prep03.fittingIn M :=
        notMem_fittingIn_mul hcfg.config hmem hne hx0F
      rw [hcoe, hνhcoe, hνvanish _ hV]
      refine (eq_zero_of_mem_detectInd_fittingIn (H := Prep03.hallCoreIn M) ?_ ?_).symm
      · rw [← hT]; exact hlamT
      · rw [hcoe]; exact hnotF
    have key := card_sub_index_sq_le_sum_erase_norm_sq (S := M) (H := fittingRaw ↥M)
      (P := hallCore ↥M) hPH νh hνh' hνhiso hcard hlamT' hlamIrr (chi := _) rfl hu0 hqp
      (by rw [hidx]; ring)
      (by have h2 : ((2 * u + 1 : ℕ) : ℤ) ≤ (Nat.card ↥(hallCore ↥M) : ℤ) := by exact_mod_cast hPu
          push_cast at h2; linarith)
      hxP hx1 hyord hxy hval
    rw [hidx] at key
    have heq : ((Nat.card ↥W₁ * u : ℕ) : ℝ) = (Nat.card ↥W₁ : ℝ) * (u : ℝ) := by push_cast; ring
    rw [heq] at key
    have hνeq : (νh ⟨lam, Submodule.subset_span hlamT'⟩ : G → ℂ) = ν lam := hνhcoe _ _
    rw [← hνeq]
    exact le_sumSqOn_sharp_map_subtype (K := fittingRaw ↥M) _ (fun a => by simp) key

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

open Subgroup
open CFSG.FeitThompson
open CFSG.FeitThompson.Prep03

attribute [local instance] CFSG.FeitThompson.subgroupFintype

universe u

theorem FCH_type_p_three_fitting_norm_bounds
    (h₁ : Statements.FNI_type_p_elementary_core_structure.{u}) :
    Statements.FCH_type_p_three_fitting_norm_bounds.{u} :=
  CFSG.FeitThompson.threeFittingNormBounds_aux h₁

end CFSG.FeitThompson.Proofs

end
