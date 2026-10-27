module

public import CFSG.LieType.Chevalley.EvenRootCommutatorF4
public import CFSG.LieType.Ree.LargeReeRootInvolution

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Ree RootOps
open scoped commutatorElement

@[expose] def f4LayerPairs : List (ℕ × ℕ) :=
  [(33, 24), (27, 25), (34, 26), (30, 28), (37, 29), (40, 31), (32, 35), (39, 36), (42, 38),
    (45, 41), (46, 43), (47, 44)]

@[expose] def f4PairLong (i : Fin 12) : ℕ :=
  (f4LayerPairs.getD i (0, 0)).1

@[expose] def f4PairShort (i : Fin 12) : ℕ :=
  (f4LayerPairs.getD i (0, 0)).2

@[expose] def f4Layer (k : ℕ) : ℕ :=
  (f4LayerPairs.findIdx fun p => p.1 == k || p.2 == k) + 1

@[expose] def f4LayerRoots (j : ℕ) : Set (Fin ReeTag.F4.tag.rank → ℤ) :=
  {α | ∃ i : Fin 12, j ≤ i.val + 1 ∧
    (α = orbitCertRoot ReeTag.F4.tag (f4PairLong i) ∨
      α = orbitCertRoot ReeTag.F4.tag (f4PairShort i))}

@[expose] def f4LayerGroup
    (K : Type) [Field K] (j : ℕ) : Subgroup (ModGL ReeTag.F4.tag K) :=
  rootSpan ReeTag.F4.tag K (f4LayerRoots j)

theorem f4PairLong_mem (i : Fin 12) :
    orbitCertRoot ReeTag.F4.tag (f4PairLong i) ∈ f4LayerRoots (i.val + 1) :=
  ⟨i, le_rfl, Or.inl rfl⟩

theorem f4PairShort_mem (i : Fin 12) :
    orbitCertRoot ReeTag.F4.tag (f4PairShort i) ∈ f4LayerRoots (i.val + 1) :=
  ⟨i, le_rfl, Or.inr rfl⟩

@[expose] def f4LayerElt
    (K : Type) [Field K] (i : Fin 12) (a b : K) :
    f4LayerGroup K (i.val + 1) :=
  ⟨pinnedX ReeTag.F4.tag K (orbitCertRoot ReeTag.F4.tag (f4PairLong i)) a *
      pinnedX ReeTag.F4.tag K (orbitCertRoot ReeTag.F4.tag (f4PairShort i)) b,
    mul_mem (pinnedX_mem_rootSpan (f4PairLong_mem i) a)
      (pinnedX_mem_rootSpan (f4PairShort_mem i) b)⟩

theorem f4Layer_spec : ∀ k : Fin 48, 24 ≤ (k : ℕ) →
    1 ≤ f4Layer k ∧ f4Layer k ≤ 12 ∧ ∀ i : Fin 12,
      (f4PairLong i = k ∨ f4PairShort i = k) ↔ f4Layer k = i.val + 1 := by
  decide +kernel

theorem f4Pair_range : ∀ i : Fin 12, 24 ≤ f4PairLong i ∧ f4PairLong i ≤ 47 ∧
    24 ≤ f4PairShort i ∧ f4PairShort i ≤ 47 := by
  decide +kernel

theorem f4Pair_dual : ∀ i : Fin 12,
    ReeTag.F4.quadForm (orbitCertRoot ReeTag.F4.tag (f4PairLong i)) = 4 ∧
      ReeTag.F4.quadForm (orbitCertRoot ReeTag.F4.tag (f4PairShort i)) = 2 ∧
      List.ofFn (ReeTag.F4.dualRoot (orbitCertRoot ReeTag.F4.tag (f4PairLong i))) =
        List.ofFn (orbitCertRoot ReeTag.F4.tag (f4PairShort i)) ∧
      List.ofFn (ReeTag.F4.dualRoot (orbitCertRoot ReeTag.F4.tag (f4PairShort i))) =
        List.ofFn (orbitCertRoot ReeTag.F4.tag (f4PairLong i)) := by
  decide +kernel

theorem f4OddCommutatorFactors_layer : ∀ e ∈ f4OddCommutatorFactors, ∀ f ∈ e.2,
    f4Layer e.1.1 < f4Layer f.2.2 ∧ f4Layer e.1.2 < f4Layer f.2.2 := by
  decide +kernel

theorem f4_witnesses_length : Tag.F4.witnesses.roots.length = 48 :=
  rfl

theorem mem_f4LayerRoots_iff
    {k : ℕ} (hk : 24 ≤ k) (hk' : k ≤ 47) (j : ℕ) :
    orbitCertRoot ReeTag.F4.tag k ∈ f4LayerRoots j ↔ j ≤ f4Layer k := by
  have hk48 : k < 48 := by omega
  have h1 : 1 ≤ f4Layer k := (f4Layer_spec ⟨k, hk48⟩ hk).1
  have h12 : f4Layer k ≤ 12 := (f4Layer_spec ⟨k, hk48⟩ hk).2.1
  have hspec' : ∀ i : Fin 12, (f4PairLong i = k ∨ f4PairShort i = k) ↔ f4Layer k = i.val + 1 :=
    (f4Layer_spec ⟨k, hk48⟩ hk).2.2
  constructor
  · rintro ⟨i, hji, h⟩
    obtain ⟨hl, hl', hs, hs'⟩ := f4Pair_range i
    have hik : f4PairLong i = k ∨ f4PairShort i = k := by
      rcases h with h | h
      · exact Or.inl (orbitCertRoot_injOn (τ := .F4) (by rw [f4_witnesses_length]; omega)
          (by rw [f4_witnesses_length]; omega) h.symm)
      · exact Or.inr (orbitCertRoot_injOn (τ := .F4) (by rw [f4_witnesses_length]; omega)
          (by rw [f4_witnesses_length]; omega) h.symm)
    rw [(hspec' i).1 hik]
    exact hji
  · intro hj
    set i : Fin 12 := ⟨f4Layer k - 1, by omega⟩
    have hi : f4Layer k = i.val + 1 := by simp only [i]; omega
    refine ⟨i, by omega, ?_⟩
    rcases (hspec' i).2 hi with h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr (by rw [h])

theorem f4LayerRoots_anti {j j' : ℕ} (h : j ≤ j') : f4LayerRoots j' ⊆ f4LayerRoots j := by
  rintro α ⟨i, hi, hα⟩
  exact ⟨i, h.trans hi, hα⟩

theorem exists_pos_of_mem_f4LayerRoots
    {j : ℕ} {α : Fin ReeTag.F4.tag.rank → ℤ}
    (hα : α ∈ f4LayerRoots j) :
    ∃ k, 24 ≤ k ∧ k ≤ 47 ∧ j ≤ f4Layer k ∧ orbitCertRoot ReeTag.F4.tag k = α := by
  obtain ⟨i, hi, h⟩ := hα
  obtain ⟨hl, hl', hs, hs'⟩ := f4Pair_range i
  rcases h with rfl | rfl
  · exact ⟨_, hl, hl', (mem_f4LayerRoots_iff hl hl' j).1 ⟨i, hi, Or.inl rfl⟩, rfl⟩
  · exact ⟨_, hs, hs', (mem_f4LayerRoots_iff hs hs' j).1 ⟨i, hi, Or.inr rfl⟩, rfl⟩

theorem f4LayerRoots_subset_pos
    (j : ℕ) :
    f4LayerRoots j ⊆ {α | IsRoot ReeTag.F4.tag α ∧ 0 < height α} := by
  intro α hα
  obtain ⟨k, hk, hk', -, rfl⟩ := exists_pos_of_mem_f4LayerRoots hα
  exact (isRoot_pos_iff_f4 _).2 ⟨k, hk, hk', rfl⟩

theorem f4LayerRoots_one
    : f4LayerRoots 1 = {α | IsRoot ReeTag.F4.tag α ∧ 0 < height α} := by
  refine (f4LayerRoots_subset_pos 1).antisymm fun α hα => ?_
  obtain ⟨k, hk, hk', rfl⟩ := (isRoot_pos_iff_f4 α).1 hα
  have h1 : 1 ≤ f4Layer k := (f4Layer_spec ⟨k, by omega⟩ hk).1
  exact (mem_f4LayerRoots_iff hk hk' 1).2 h1

theorem f4LayerRoots_thirteen : f4LayerRoots 13 = ∅ := by
  ext α
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨i, hi, -⟩
  have := i.2
  omega

theorem f4LayerGroup_one
    (K : Type) [Field K] :
    f4LayerGroup K 1 = posUnipotent ReeTag.F4.tag K := by
  rw [f4LayerGroup, f4LayerRoots_one]
  rfl

theorem f4LayerGroup_thirteen
    (K : Type) [Field K] : f4LayerGroup K 13 = ⊥ := by
  rw [f4LayerGroup, f4LayerRoots_thirteen, rootSpan]
  simp

theorem f4LayerGroup_anti
    (K : Type) [Field K] {j j' : ℕ} (h : j ≤ j') :
    f4LayerGroup K j' ≤ f4LayerGroup K j :=
  rootSpan_mono (f4LayerRoots_anti h)

theorem f4LayerGroup_le_posUnipotent
    (K : Type) [Field K] (j : ℕ) :
    f4LayerGroup K j ≤ posUnipotent ReeTag.F4.tag K :=
  rootSpan_mono (f4LayerRoots_subset_pos j)

section Commutators

variable {K : Type} [Field K]

theorem f4_commutator_mem_layer
    [CharP K 2] {k₁ k₂ : ℕ} (hk₁ : 24 ≤ k₁) (hk₁' : k₁ ≤ 47)
    (hk₂ : 24 ≤ k₂) (hk₂' : k₂ ≤ 47) (c d : K) :
    ⁅pinnedX ReeTag.F4.tag K (orbitCertRoot ReeTag.F4.tag k₁) c,
        pinnedX ReeTag.F4.tag K (orbitCertRoot ReeTag.F4.tag k₂) d⁆ ∈
      f4LayerGroup K (max (f4Layer k₁) (f4Layer k₂) + 1) := by
  by_cases h : k₁ = k₂
  · subst h
    rw [commutatorElement_eq_one_iff_commute.2]
    · exact one_mem _
    · rw [Commute, SemiconjBy, ← pinnedX_add, ← pinnedX_add, add_comm]
  · obtain ⟨-, -, hkeys, hfac, hcomm⟩ := f4_even_positive_root_commutator_table
    obtain ⟨l, hl, hmem⟩ := lookup_spec (l := f4OddCommutatorFactors) (a := (k₁, k₂))
      ((hkeys k₁ k₂).2 ⟨hk₁, hk₁', hk₂, hk₂', h⟩)
    have hc := hcomm K k₁ k₂ hk₁ hk₁' hk₂ hk₂' h c d
    rw [hl, Option.getD_some] at hc
    change ⁅pinnedX Tag.F4 K (orbitCertRoot Tag.F4 k₁) c,
      pinnedX Tag.F4 K (orbitCertRoot Tag.F4 k₂) d⁆ ∈ _
    rw [hc]
    refine list_prod_mem fun x hx => ?_
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hx
    obtain ⟨hf1, hf2, -⟩ := (hfac _ hmem).2 f hf
    obtain ⟨hl1, hl2⟩ := f4OddCommutatorFactors_layer _ hmem f hf
    exact pinnedX_mem_rootSpan
      ((mem_f4LayerRoots_iff hf1 hf2 _).2 (by simp only at hl1 hl2; omega)) _

theorem f4_commutator_mem_succ
    [CharP K 2] {j : ℕ} {α β : Fin ReeTag.F4.tag.rank → ℤ}
    (hα : IsRoot ReeTag.F4.tag α ∧ 0 < height α) (hβ : β ∈ f4LayerRoots j) (c d : K) :
    ⁅pinnedX ReeTag.F4.tag K α c, pinnedX ReeTag.F4.tag K β d⁆ ∈ f4LayerGroup K (j + 1) := by
  obtain ⟨k₁, hk₁, hk₁', rfl⟩ := (isRoot_pos_iff_f4 α).1 hα
  obtain ⟨k₂, hk₂, hk₂', hj, rfl⟩ := exists_pos_of_mem_f4LayerRoots hβ
  exact f4LayerGroup_anti K (by omega) (f4_commutator_mem_layer hk₁ hk₁' hk₂ hk₂' c d)

theorem le_normalizer_of_commutator_le {G : Type*} [Group G] {U A B : Subgroup G} (hBA : B ≤ A)
    (hc : ⁅U, A⁆ ≤ B) : U ≤ Subgroup.normalizer (A : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have hm : ⁅g, h⁆ * h ∈ A :=
      mul_mem (hBA (hc (Subgroup.commutator_mem_commutator hg hh))) hh
    have e : ⁅g, h⁆ * h = g * h * g⁻¹ := by
      rw [commutatorElement_def]
      group
    rwa [e] at hm
  · intro hh
    have hm : ⁅g⁻¹, g * h * g⁻¹⁆ * (g * h * g⁻¹) ∈ A :=
      mul_mem (hBA (hc (Subgroup.commutator_mem_commutator (inv_mem hg) hh))) hh
    have e : ⁅g⁻¹, g * h * g⁻¹⁆ * (g * h * g⁻¹) = h := by
      rw [commutatorElement_def]
      group
    rwa [e] at hm

theorem f4_commutator_layer_le
    [CharP K 2] {j : ℕ}
    (hN : posUnipotent ReeTag.F4.tag K ≤
      Subgroup.normalizer (f4LayerGroup K (j + 1) : Set (ModGL ReeTag.F4.tag K))) :
    ⁅posUnipotent ReeTag.F4.tag K, f4LayerGroup K j⁆ ≤ f4LayerGroup K (j + 1) := by
  have hU : posUnipotent ReeTag.F4.tag K = Subgroup.closure {g | ∃ α ∈
      {α : Fin ReeTag.F4.tag.rank → ℤ | IsRoot ReeTag.F4.tag α ∧ 0 < height α},
        ∃ c : K, pinnedX ReeTag.F4.tag K α c = g} := rootSpan_eq_closure K _
  have hUj : f4LayerGroup K j = Subgroup.closure {g | ∃ α ∈ f4LayerRoots j,
      ∃ c : K, pinnedX ReeTag.F4.tag K α c = g} := rootSpan_eq_closure K _
  rw [hU, hUj]
  refine commutator_closure_le_of_le_normalizer (G₀ := posUnipotent ReeTag.F4.tag K)
    hU.ge (hUj.symm.le.trans (f4LayerGroup_le_posUnipotent K j)) hN ?_
  rintro _ ⟨α, hα, c, rfl⟩ _ ⟨β, hβ, d, rfl⟩
  exact f4_commutator_mem_succ hα hβ c d

theorem f4_le_normalizer_layer
    [CharP K 2] :
    ∀ m ≤ 12, posUnipotent ReeTag.F4.tag K ≤
      Subgroup.normalizer (f4LayerGroup K (13 - m) : Set (ModGL ReeTag.F4.tag K)) := by
  intro m hm
  induction m with
  | zero =>
    intro g _
    rw [Subgroup.mem_normalizer_iff]
    intro h
    simp only [Nat.sub_zero, f4LayerGroup_thirteen, Subgroup.mem_bot]
    constructor
    · rintro rfl
      group
    · intro hh
      have := congrArg (fun x => g⁻¹ * x * g) hh
      simpa [mul_assoc] using this
  | succ m ih =>
    have ih' := ih (by omega)
    have e : 13 - m = (13 - (m + 1)) + 1 := by omega
    rw [e] at ih'
    exact le_normalizer_of_commutator_le (f4LayerGroup_anti K (Nat.le_succ _))
      (f4_commutator_layer_le ih')

end Commutators

section Exceptional

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

omit [Finite K] [CharP K ReeTag.F4.prime] in
theorem f4LayerElt_mem_adjointGroup
    (i : Fin 12) (a b : K) :
    (f4LayerElt K i a b : ModGL ReeTag.F4.tag K) ∈ adjointGroup ReeTag.F4.tag K :=
  ReeTag.rootSpan_le_adjointGroup _ (f4LayerElt K i a b).2

theorem finiteReeAut_zero_F4 :
    ReeTag.F4.finiteReeAut K 0 = ReeTag.F4.finiteExceptionalAut K := by
  simp [ReeTag.finiteReeAut]

theorem finiteExceptionalAut_pinnedX_long
    {α : Fin ReeTag.F4.tag.rank → ℤ}
    (hα : α ∈ ReeTag.F4.longRoots) (c : K) :
    ReeTag.F4.finiteExceptionalAut K ⟨pinnedX ReeTag.F4.tag K α c, pinnedX_mem_adjointGroup α c⟩ =
      ⟨pinnedX ReeTag.F4.tag K (ReeTag.F4.dualRoot α) c, pinnedX_mem_adjointGroup _ _⟩ := by
  rw [← finiteReeAut_zero_F4, ReeTag.finiteReeAut_pinnedX_F4 hα.1,
    (ReeTag.relationExponent_pinnedData_F4 (a := 0) hα.1).1 hα, pow_zero, pow_one]

theorem finiteExceptionalAut_pinnedX_short
    {α : Fin ReeTag.F4.tag.rank → ℤ}
    (hα : α ∈ ReeTag.F4.shortRoots) (c : K) :
    ReeTag.F4.finiteExceptionalAut K ⟨pinnedX ReeTag.F4.tag K α c, pinnedX_mem_adjointGroup α c⟩ =
      ⟨pinnedX ReeTag.F4.tag K (ReeTag.F4.dualRoot α) (c ^ 2), pinnedX_mem_adjointGroup _ _⟩ := by
  rw [← finiteReeAut_zero_F4, ReeTag.finiteReeAut_pinnedX_F4 hα.1,
    (ReeTag.relationExponent_pinnedData_F4 (a := 0) hα.1).2 hα, pow_zero, mul_one]

theorem f4Pair_roots
    (i : Fin 12) :
    orbitCertRoot ReeTag.F4.tag (f4PairLong i) ∈ ReeTag.F4.longRoots ∧
      orbitCertRoot ReeTag.F4.tag (f4PairShort i) ∈ ReeTag.F4.shortRoots ∧
      ReeTag.F4.dualRoot (orbitCertRoot ReeTag.F4.tag (f4PairLong i)) =
        orbitCertRoot ReeTag.F4.tag (f4PairShort i) ∧
      ReeTag.F4.dualRoot (orbitCertRoot ReeTag.F4.tag (f4PairShort i)) =
        orbitCertRoot ReeTag.F4.tag (f4PairLong i) := by
  obtain ⟨h1, h2, h3, h4⟩ := f4Pair_dual i
  have hl := (f4LayerRoots_subset_pos _ (f4PairLong_mem i)).1
  have hs := (f4LayerRoots_subset_pos _ (f4PairShort_mem i)).1
  exact ⟨⟨hl, ReeTag.lengthParam_eq_prime_iff.2 h1⟩, ⟨hs, ReeTag.lengthParam_eq_one_iff.2 h2⟩,
    List.ofFn_injective h3, List.ofFn_injective h4⟩

theorem dualRoot_mem_f4LayerRoots
    {j : ℕ} {α : Fin ReeTag.F4.tag.rank → ℤ}
    (hα : α ∈ f4LayerRoots j) : IsRoot ReeTag.F4.tag α ∧ ReeTag.F4.dualRoot α ∈ f4LayerRoots j := by
  refine ⟨(f4LayerRoots_subset_pos j hα).1, ?_⟩
  obtain ⟨i, hi, h⟩ := hα
  obtain ⟨-, -, h3, h4⟩ := f4Pair_roots i
  rcases h with rfl | rfl
  · exact ⟨i, hi, Or.inr h3⟩
  · exact ⟨i, hi, Or.inl h4⟩

theorem map_finiteExceptionalAut_f4LayerGroup
    (j : ℕ) :
    ((f4LayerGroup K j).subgroupOf (adjointGroup ReeTag.F4.tag K)).map
        (ReeTag.F4.finiteExceptionalAut K).toMonoidHom =
      (f4LayerGroup K j).subgroupOf (adjointGroup ReeTag.F4.tag K) := by
  rw [← finiteReeAut_zero_F4]
  exact map_eq_of_map_le _ (ReeTag.map_finiteReeAut_rootSpan_le fun _ hα =>
    dualRoot_mem_f4LayerRoots hα)

end Exceptional

section Quotient

variable {K : Type} [Field K] [CharP K 2]

theorem f4LayerGroup_le_normalizer_succ
    (i : Fin 12) :
    posUnipotent ReeTag.F4.tag K ≤ Subgroup.normalizer
      (f4LayerGroup K (i.val + 2) : Set (ModGL ReeTag.F4.tag K)) := by
  have h := f4_le_normalizer_layer (K := K) (11 - i.val) (by omega)
  rwa [show 13 - (11 - i.val) = i.val + 2 by omega] at h

theorem f4Layer_normal_succ
    (i : Fin 12) :
    ((f4LayerGroup K (i.val + 2)).subgroupOf (f4LayerGroup K (i.val + 1))).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer
    ((f4LayerGroup_le_posUnipotent K _).trans (f4LayerGroup_le_normalizer_succ i))

omit [CharP K 2] in
theorem f4LayerElt_zero
    (i : Fin 12) : f4LayerElt K i 0 0 = 1 :=
  Subtype.ext (by simp [f4LayerElt, pinnedX_zero])

theorem f4LayerElt_add
    (i : Fin 12) (p p' : K × K) :
    (QuotientGroup.mk (f4LayerElt K i (p.1 + p'.1) (p.2 + p'.2)) : f4LayerGroup K (i.val + 1) ⧸
        (f4LayerGroup K (i.val + 2)).subgroupOf (f4LayerGroup K (i.val + 1))) =
      QuotientGroup.mk (f4LayerElt K i p.1 p.2 * f4LayerElt K i p'.1 p'.2) := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have hs := f4LayerRoots_subset_pos _ (f4PairShort_mem i)
  have hc := f4_commutator_mem_succ (K := K) hs (f4PairLong_mem i) (-p.2) (-p'.1)
  have hu : (pinnedX ReeTag.F4.tag K (orbitCertRoot ReeTag.F4.tag (f4PairShort i)) p'.2)⁻¹ ∈
      posUnipotent ReeTag.F4.tag K :=
    inv_mem (f4LayerGroup_le_posUnipotent K _ (pinnedX_mem_rootSpan (f4PairShort_mem i) _))
  have h := (Subgroup.mem_normalizer_iff.1 (f4LayerGroup_le_normalizer_succ i hu) _).1 hc
  convert h using 1
  simp only [f4LayerElt, Subgroup.coe_mul, Subgroup.coe_inv, pinnedX_add, ← pinnedX_neg,
    commutatorElement_def]
  group

theorem f4LayerElt_surjective
    (i : Fin 12) :
    Function.Surjective fun p : K × K => (QuotientGroup.mk (f4LayerElt K i p.1 p.2) :
      f4LayerGroup K (i.val + 1) ⧸
        (f4LayerGroup K (i.val + 2)).subgroupOf (f4LayerGroup K (i.val + 1))) := by
  have := f4Layer_normal_succ (K := K) i
  set N := (f4LayerGroup K (i.val + 2)).subgroupOf (f4LayerGroup K (i.val + 1))
  let Ψ : Multiplicative (K × K) →* f4LayerGroup K (i.val + 1) ⧸ N :=
    { toFun := fun p => QuotientGroup.mk (f4LayerElt K i p.toAdd.1 p.toAdd.2)
      map_one' := by simp [f4LayerElt_zero]
      map_mul' := fun p p' => by
        rw [toAdd_mul, Prod.fst_add, Prod.snd_add, f4LayerElt_add i p.toAdd p'.toAdd,
          QuotientGroup.mk_mul] }
  have hUj : f4LayerGroup K (i.val + 1) = Subgroup.closure {g | ∃ α ∈ f4LayerRoots (i.val + 1),
      ∃ c : K, pinnedX ReeTag.F4.tag K α c = g} := rootSpan_eq_closure K _
  have key : ∀ g (hg : g ∈ Subgroup.closure {g | ∃ α ∈ f4LayerRoots (i.val + 1),
      ∃ c : K, pinnedX ReeTag.F4.tag K α c = g}),
      (QuotientGroup.mk (⟨g, hUj ▸ hg⟩ : f4LayerGroup K (i.val + 1)) :
        f4LayerGroup K (i.val + 1) ⧸ N) ∈ Ψ.range := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨α, ⟨i', hi', hα⟩, c, rfl⟩ := hg
      by_cases hii : i' = i
      · subst hii
        rcases hα with rfl | rfl
        · refine ⟨Multiplicative.ofAdd (c, 0), congrArg QuotientGroup.mk (Subtype.ext ?_)⟩
          simp [f4LayerElt, pinnedX_zero]
        · refine ⟨Multiplicative.ofAdd (0, c), congrArg QuotientGroup.mk (Subtype.ext ?_)⟩
          simp [f4LayerElt, pinnedX_zero]
      · have hlt : i.val + 2 ≤ i'.val + 1 := by
          have : i.val ≠ i'.val := fun h => hii (Fin.ext h.symm)
          omega
        have hmem : pinnedX ReeTag.F4.tag K α c ∈ f4LayerGroup K (i.val + 2) :=
          pinnedX_mem_rootSpan (S := f4LayerRoots (i.val + 2)) ⟨i', hlt, hα⟩ c
        refine ⟨1, ?_⟩
        rw [map_one, eq_comm, QuotientGroup.eq_one_iff]
        exact Subgroup.mem_subgroupOf.2 hmem
    | one => exact ⟨1, by rw [map_one]; rfl⟩
    | mul x y hx hy ihx ihy =>
      obtain ⟨u, hu⟩ := ihx
      obtain ⟨v, hv⟩ := ihy
      refine ⟨u * v, ?_⟩
      rw [map_mul, hu, hv, ← QuotientGroup.mk_mul]
      rfl
    | inv x hx ihx =>
      obtain ⟨u, hu⟩ := ihx
      refine ⟨u⁻¹, ?_⟩
      rw [map_inv, hu, ← QuotientGroup.mk_inv]
      rfl
  intro y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨u, hu⟩ := key x (hUj ▸ x.2)
  exact ⟨u.toAdd, hu⟩

end Quotient

section Count

variable {K : Type} [Field K]

theorem f4Layer_card_eq (i : Fin 12) :
    Nat.card (f4LayerGroup K (i.val + 1)) =
      Nat.card (f4LayerGroup K (i.val + 1) ⧸
        (f4LayerGroup K (i.val + 2)).subgroupOf (f4LayerGroup K (i.val + 1))) *
        Nat.card (f4LayerGroup K (i.val + 2)) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
      ((f4LayerGroup K (i.val + 2)).subgroupOf (f4LayerGroup K (i.val + 1))),
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (f4LayerGroup_anti K (by omega))).toEquiv]

variable [Finite K] [CharP K 2]

theorem f4Layer_card_quot_le
    (i : Fin 12) :
    Nat.card (f4LayerGroup K (i.val + 1) ⧸
        (f4LayerGroup K (i.val + 2)).subgroupOf (f4LayerGroup K (i.val + 1))) ≤
      Nat.card K ^ 2 := by
  rw [sq, ← Nat.card_prod]
  exact Nat.card_le_card_of_surjective _ (f4LayerElt_surjective i)

theorem f4Layer_card_le
    : ∀ m ≤ 12, Nat.card (f4LayerGroup K (13 - m)) ≤ Nat.card K ^ (2 * m) := by
  intro m hm
  induction m with
  | zero => simp [f4LayerGroup_thirteen]
  | succ m ih =>
    have h := f4Layer_card_eq (K := K) ⟨11 - m, by omega⟩
    have hq := f4Layer_card_quot_le (K := K) ⟨11 - m, by omega⟩
    simp only at h hq
    rw [show 11 - m + 1 = 13 - (m + 1) by omega, show 11 - m + 2 = 13 - m by omega] at h hq
    rw [h, show 2 * (m + 1) = 2 + 2 * m by ring, pow_add]
    exact Nat.mul_le_mul hq (ih (by omega))

theorem f4Layer_card_ge :
    ∀ n ≤ 12, Nat.card K ^ (2 * (12 - n)) ≤ Nat.card (f4LayerGroup K (n + 1)) := by
  have hq : 0 < Nat.card K := Nat.card_pos
  intro n hn
  induction n with
  | zero =>
    have h24 : {α : Fin ReeTag.F4.tag.rank → ℤ | IsRoot ReeTag.F4.tag α ∧ 0 < height α}.ncard =
        24 := ncard_f4_posRoots
    rw [zero_add, f4LayerGroup_one, card_posUnipotent, h24]
  | succ n ih =>
    have h := f4Layer_card_eq (K := K) ⟨n, by omega⟩
    have hQ := f4Layer_card_quot_le (K := K) ⟨n, by omega⟩
    simp only at h hQ
    have key : Nat.card K ^ 2 * Nat.card K ^ (2 * (12 - (n + 1))) ≤
        Nat.card K ^ 2 * Nat.card (f4LayerGroup K (n + 1 + 1)) := by
      calc Nat.card K ^ 2 * Nat.card K ^ (2 * (12 - (n + 1))) = Nat.card K ^ (2 * (12 - n)) := by
            rw [← pow_add]
            congr 1
            omega
        _ ≤ Nat.card (f4LayerGroup K (n + 1)) := ih (by omega)
        _ = _ := h
        _ ≤ Nat.card K ^ 2 * Nat.card (f4LayerGroup K (n + 2)) := Nat.mul_le_mul_right _ hQ
    exact Nat.le_of_mul_le_mul_left key (by positivity)

theorem f4Layer_card_quot
    (i : Fin 12) :
    Nat.card (f4LayerGroup K (i.val + 1) ⧸
        (f4LayerGroup K (i.val + 2)).subgroupOf (f4LayerGroup K (i.val + 1))) =
      Nat.card K ^ 2 := by
  have hq : 0 < Nat.card K := Nat.card_pos
  have h := f4Layer_card_eq (K := K) i
  have hge := f4Layer_card_ge (K := K) i.val (by omega)
  have hle := f4Layer_card_le (K := K) (11 - i.val) (by omega)
  rw [show 13 - (11 - i.val) = i.val + 2 by omega] at hle
  refine le_antisymm (f4Layer_card_quot_le i) ?_
  have key : Nat.card K ^ 2 * Nat.card K ^ (2 * (11 - i.val)) ≤
      Nat.card (f4LayerGroup K (i.val + 1) ⧸
        (f4LayerGroup K (i.val + 2)).subgroupOf (f4LayerGroup K (i.val + 1))) *
        Nat.card K ^ (2 * (11 - i.val)) := by
    calc Nat.card K ^ 2 * Nat.card K ^ (2 * (11 - i.val)) = Nat.card K ^ (2 * (12 - i.val)) := by
          rw [← pow_add]
          congr 1
          omega
      _ ≤ Nat.card (f4LayerGroup K (i.val + 1)) := hge
      _ = _ := h
      _ ≤ _ := Nat.mul_le_mul_left _ hle
  exact Nat.le_of_mul_le_mul_right key (by positivity)

theorem f4LayerElt_bijective
    (i : Fin 12) :
    Function.Bijective fun p : K × K => (QuotientGroup.mk (f4LayerElt K i p.1 p.2) :
      f4LayerGroup K (i.val + 1) ⧸
        (f4LayerGroup K (i.val + 2)).subgroupOf (f4LayerGroup K (i.val + 1))) :=
  (f4LayerElt_surjective i).bijective_of_nat_card_le
    (le_of_eq (by rw [Nat.card_prod, f4Layer_card_quot, sq]))

end Count

section Main

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

instance f4Layer_normal_succ_of_F4
    (i : Fin 12) :
    ((f4LayerGroup K (i.val + 2)).subgroupOf (f4LayerGroup K (i.val + 1))).Normal :=
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  f4Layer_normal_succ i

theorem exists_f4Layer_mulEquiv
    (i : Fin 12) :
    ∃ e : Multiplicative (K × K) ≃* f4LayerGroup K (i.val + 1) ⧸
        (f4LayerGroup K (i.val + 2)).subgroupOf (f4LayerGroup K (i.val + 1)),
      ∀ a b : K, e (Multiplicative.ofAdd (a, b)) = QuotientGroup.mk (f4LayerElt K i a b) := by
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  let Ψ : Multiplicative (K × K) →* f4LayerGroup K (i.val + 1) ⧸
      (f4LayerGroup K (i.val + 2)).subgroupOf (f4LayerGroup K (i.val + 1)) :=
    { toFun := fun p => QuotientGroup.mk (f4LayerElt K i p.toAdd.1 p.toAdd.2)
      map_one' := by simp [f4LayerElt_zero]
      map_mul' := fun p p' => by
        rw [toAdd_mul, Prod.fst_add, Prod.snd_add, f4LayerElt_add i p.toAdd p'.toAdd,
          QuotientGroup.mk_mul] }
  have hΨ : Function.Bijective Ψ :=
    (f4LayerElt_bijective (K := K) i).comp (Multiplicative.toAdd.bijective)
  exact ⟨MulEquiv.ofBijective Ψ hΨ, fun a b => rfl⟩

theorem finiteExceptionalAut_f4LayerElt
    (i : Fin 12) (a b : K) :
    (ReeTag.F4.finiteExceptionalAut K ⟨f4LayerElt K i a b, f4LayerElt_mem_adjointGroup i a b⟩ :
        ModGL ReeTag.F4.tag K) =
      pinnedX ReeTag.F4.tag K (orbitCertRoot ReeTag.F4.tag (f4PairShort i)) a *
        pinnedX ReeTag.F4.tag K (orbitCertRoot ReeTag.F4.tag (f4PairLong i)) (b ^ 2) := by
  obtain ⟨hl, hs, hls, hsl⟩ := f4Pair_roots i
  have e : (⟨f4LayerElt K i a b, f4LayerElt_mem_adjointGroup i a b⟩ :
      adjointGroup ReeTag.F4.tag K) =
      ⟨_, pinnedX_mem_adjointGroup (orbitCertRoot ReeTag.F4.tag (f4PairLong i)) a⟩ *
        ⟨_, pinnedX_mem_adjointGroup (orbitCertRoot ReeTag.F4.tag (f4PairShort i)) b⟩ :=
    Subtype.ext rfl
  rw [e, map_mul, finiteExceptionalAut_pinnedX_long hl, finiteExceptionalAut_pinnedX_short hs]
  simp only [Subgroup.coe_mul, hls, hsl]

theorem finiteExceptionalAut_f4LayerElt_mem
    (i : Fin 12) (a b : K) :
    ((f4LayerElt K i (b ^ 2) a : ModGL ReeTag.F4.tag K))⁻¹ *
        (ReeTag.F4.finiteExceptionalAut K ⟨f4LayerElt K i a b, f4LayerElt_mem_adjointGroup i a b⟩ :
          ModGL ReeTag.F4.tag K) ∈ f4LayerGroup K (i.val + 2) := by
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  rw [finiteExceptionalAut_f4LayerElt]
  have hs := f4LayerRoots_subset_pos _ (f4PairShort_mem i)
  have hc := f4_commutator_mem_succ (K := K) hs (f4PairLong_mem i) (-a) (-(b ^ 2))
  convert hc using 1
  simp only [f4LayerElt, ← pinnedX_neg, commutatorElement_def, mul_inv_rev, inv_inv]
  group

end Main

theorem even_F4_exceptional_root_layers
    (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] :
    (∀ α ∈ ReeTag.F4.longRoots, ∀ c : K,
      ReeTag.F4.finiteExceptionalAut K
          ⟨pinnedX ReeTag.F4.tag K α c, pinnedX_mem_adjointGroup α c⟩ =
        ⟨pinnedX ReeTag.F4.tag K (ReeTag.F4.dualRoot α) c, pinnedX_mem_adjointGroup _ _⟩) ∧
    (∀ α ∈ ReeTag.F4.shortRoots, ∀ c : K,
      ReeTag.F4.finiteExceptionalAut K
          ⟨pinnedX ReeTag.F4.tag K α c, pinnedX_mem_adjointGroup α c⟩ =
        ⟨pinnedX ReeTag.F4.tag K (ReeTag.F4.dualRoot α) (c ^ 2), pinnedX_mem_adjointGroup _ _⟩) ∧
    ((posUnipotent ReeTag.F4.tag K).subgroupOf (adjointGroup ReeTag.F4.tag K)).map
        (ReeTag.F4.finiteExceptionalAut K).toMonoidHom =
      (posUnipotent ReeTag.F4.tag K).subgroupOf (adjointGroup ReeTag.F4.tag K) ∧
    ((negUnipotent ReeTag.F4.tag K).subgroupOf (adjointGroup ReeTag.F4.tag K)).map
        (ReeTag.F4.finiteExceptionalAut K).toMonoidHom =
      (negUnipotent ReeTag.F4.tag K).subgroupOf (adjointGroup ReeTag.F4.tag K) ∧
    (∀ i : Fin 12, orbitCertRoot ReeTag.F4.tag (f4PairLong i) ∈ ReeTag.F4.longRoots ∧
      orbitCertRoot ReeTag.F4.tag (f4PairShort i) ∈ ReeTag.F4.shortRoots ∧
      ReeTag.F4.dualRoot (orbitCertRoot ReeTag.F4.tag (f4PairLong i)) =
        orbitCertRoot ReeTag.F4.tag (f4PairShort i) ∧
      ReeTag.F4.dualRoot (orbitCertRoot ReeTag.F4.tag (f4PairShort i)) =
        orbitCertRoot ReeTag.F4.tag (f4PairLong i)) ∧
    f4LayerRoots 1 = {α | IsRoot ReeTag.F4.tag α ∧ 0 < height α} ∧
    f4LayerGroup K 1 = posUnipotent ReeTag.F4.tag K ∧ f4LayerGroup K 13 = ⊥ ∧
    (∀ j : ℕ, 1 ≤ j → j ≤ 13 →
      ((f4LayerGroup K j).subgroupOf (adjointGroup ReeTag.F4.tag K)).map
          (ReeTag.F4.finiteExceptionalAut K).toMonoidHom =
        (f4LayerGroup K j).subgroupOf (adjointGroup ReeTag.F4.tag K) ∧
      f4LayerGroup K j ≤ posUnipotent ReeTag.F4.tag K ∧
      ((f4LayerGroup K j).subgroupOf (posUnipotent ReeTag.F4.tag K)).Normal) ∧
    (∀ j : ℕ, 1 ≤ j → j ≤ 12 →
      ⁅posUnipotent ReeTag.F4.tag K, f4LayerGroup K j⁆ ≤ f4LayerGroup K (j + 1)) ∧
    ∀ i : Fin 12,
      (∃ e : Multiplicative (K × K) ≃* f4LayerGroup K (i.val + 1) ⧸
          (f4LayerGroup K (i.val + 2)).subgroupOf (f4LayerGroup K (i.val + 1)),
        ∀ a b : K, e (Multiplicative.ofAdd (a, b)) = QuotientGroup.mk (f4LayerElt K i a b)) ∧
      ∀ a b : K, ((f4LayerElt K i (b ^ 2) a : ModGL ReeTag.F4.tag K))⁻¹ *
          (ReeTag.F4.finiteExceptionalAut K
            ⟨f4LayerElt K i a b, f4LayerElt_mem_adjointGroup i a b⟩ : ModGL ReeTag.F4.tag K) ∈
        f4LayerGroup K (i.val + 2) := by
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  refine ⟨fun α hα c => finiteExceptionalAut_pinnedX_long hα c,
    fun α hα c => finiteExceptionalAut_pinnedX_short hα c, ?_, ?_, f4Pair_roots,
    f4LayerRoots_one, f4LayerGroup_one K, f4LayerGroup_thirteen K, fun j hj hj' => ?_,
    fun j hj hj' => ?_,
    fun i => ⟨exists_f4Layer_mulEquiv i, finiteExceptionalAut_f4LayerElt_mem i⟩⟩
  · rw [← finiteReeAut_zero_F4]
    exact ReeTag.map_finiteReeAut_posUnipotentSub
  · rw [← finiteReeAut_zero_F4]
    exact ReeTag.map_finiteReeAut_negUnipotentSub
  · refine ⟨map_finiteExceptionalAut_f4LayerGroup j, f4LayerGroup_le_posUnipotent K j, ?_⟩
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer (f4LayerGroup_le_posUnipotent K j)).2 ?_
    have h := f4_le_normalizer_layer (K := K) (13 - j) (by omega)
    rwa [show 13 - (13 - j) = j by omega] at h
  · have h := f4_le_normalizer_layer (K := K) (12 - j) (by omega)
    rw [show 13 - (12 - j) = j + 1 by omega] at h
    exact f4_commutator_layer_le h

end CFSG.LieType.Chevalley
