module

public import CFSG.LargeExtraspecial.S12TriC
public import CFSG.LargeExtraspecial.S12TriD3
public import CFSG.LargeExtraspecial.S12TriE
public import CFSG.LargeExtraspecial.S12TriF
public import CFSG.Fischer.Classification.Final
public import CFSG.Fischer.Classification.PartII.O2G.ThreeFinal
public import CFSG.LargeExtraspecial.S12TriQ

public section

namespace CFSG.LargeExtraspecial.S12Tri

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open Subgroup CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Fischer.Classification
open scoped commutatorElement

theorem triResult_of_hyp
    {G : Type} [Group G] {D : Set G} (hH : Hyp G D)
    (hna : ∃ a b : commutator G, a * b ≠ b * a) {t : G} (ht : t ∈ D)
    (htG : t ∉ commutator G) : TriResult G t := by
  rcases statement_of_twinFour o2TwinFourInput G D hH with h | ⟨k, hk⟩
  · rcases h with h1 | h2 | h3 | h4 | h5
    · exact triResult_sym hH hna ht htG h1
    · exact triResult_symp htG h2
    · exact triResult_orth hH hna ht htG h3
    · exact (false_unitary htG h4).elim
    · exact Or.inl (triGood_case5 hH hna ht htG h5)
  · exact Or.inl (triGood_hasType hH ht htG hk)

section X

variable {X : Type} [Group X] {E : Set X} (hP : Pair X E) (hZ : center X = ⊥)
  (h2 : ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥)
  (h3 : ∀ N : Subgroup X, N.Normal → IsPGroup 3 N → N = ⊥)
include hP hZ h2 h3

theorem commutator_fischerQ_eq_top : commutator (fischerQ E) = ⊤ := by
  have hs := isSimpleGroup_fischerQ hP hZ h2 h3
  have hns := not_isSolvable_fischerQ hP hZ h2 h3
  rcases hs.eq_bot_or_eq_top_of_normal (commutator (fischerQ E)) with h | h
  · exfalso
    apply hns
    refine Group.isSolvable_of_comm fun a b => ?_
    have hc : ⁅a, b⁆ ∈ commutator (fischerQ E) := by
      rw [_root_.commutator_def]
      exact commutator_mem_commutator (mem_top a) (mem_top b)
    rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
    exact hc
  · exact h

theorem eq_one_of_commute_fischerQ {y : X} (hy : ∀ q ∈ fischerQ E, y * q = q * y) : y = 1 := by
  have := Pair.finite hP
  have := fischerQ_normal hP
  set C := centralizer (fischerQ E : Set X)
  by_cases hC : C = ⊥
  · have hyC : y ∈ C := mem_centralizer_iff.2 fun q hq => (hy q hq).symm
    rw [hC, mem_bot] at hyC
    exact hyC
  · exfalso
    obtain ⟨N, hNn, hNC, hNbot, hmin⟩ := CFSG.exists_minimal_normal_le C inferInstance hC
    have hNQ := eq_fischerQ_of_minimal hP hZ h2 h3 hNn hNbot hmin
    have hQC : fischerQ E ≤ C := hNQ ▸ hNC
    refine not_isSolvable_fischerQ hP hZ h2 h3 (Group.isSolvable_of_comm fun a b => ?_)
    exact Subtype.ext (mem_centralizer_iff.1 (hQC a.2) b b.2).symm

omit hZ h2 h3 in
theorem not_mem_fischerQ (hcos : ∃ d ∈ E, ∃ e ∈ E, d * e ∉ fischerQ E) {d : X} (hd : d ∈ E) :
    d ∉ fischerQ E := by
  intro hdQ
  obtain ⟨d₀, hd₀, e₀, he₀, hde⟩ := hcos
  have hall : ∀ x ∈ E, x ∈ fischerQ E := fun x hx => by
    obtain ⟨g, rfl⟩ := isConj_iff.1 (Pair.isConj hP hd hx)
    exact (fischerQ_normal hP).conj_mem _ hdQ g
  exact hde (mul_mem (hall _ hd₀) (hall _ he₀))

omit hZ h2 h3 in
theorem exists_mul_not_mem_fischerQ (hcos : ∃ d ∈ E, ∃ e ∈ E, d * e ∉ fischerQ E) {d : X}
    (hd : d ∈ E) : ∃ e ∈ E, d * e ∉ fischerQ E := by
  obtain ⟨d₀, hd₀, e₀, he₀, hde⟩ := hcos
  obtain ⟨g, rfl⟩ := isConj_iff.1 (Pair.isConj hP hd₀ hd)
  refine ⟨g * e₀ * g⁻¹, Pair.conj_mem hP he₀ g, fun h => hde ?_⟩
  have := (fischerQ_normal hP).conj_mem _ h g⁻¹
  convert this using 1
  group

end X

variable {X : Type} [Group X]

@[expose] def dOne (E : Set X) (d : X) : (fischerQ E ⊔ zpowers d : Subgroup X) :=
  ⟨d, le_sup_right (a := fischerQ E) (mem_zpowers d)⟩

@[expose] def classOne (E : Set X) (d : X) : Set (fischerQ E ⊔ zpowers d : Subgroup X) :=
  {x | IsConj (dOne E d) x}

theorem commutator_X₁ {E : Set X} (hQ : commutator (fischerQ E) = ⊤) (hQn : (fischerQ E).Normal)
    (d : X) : commutator (fischerQ E ⊔ zpowers d : Subgroup X) =
      (fischerQ E).subgroupOf (fischerQ E ⊔ zpowers d) := by
  set X₁ := (fischerQ E ⊔ zpowers d : Subgroup X)
  have hle : ⁅X₁, X₁⁆ ≤ fischerQ E := by
    have hmap : X₁.map (QuotientGroup.mk' (fischerQ E)) =
        zpowers (QuotientGroup.mk' (fischerQ E) d) := by
      rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq, MonoidHom.map_zpowers]
    have hbot : ⁅X₁, X₁⁆.map (QuotientGroup.mk' (fischerQ E)) = ⊥ := by
      rw [map_commutator, hmap, commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [mem_centralizer_iff]
      intro y hy
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hx
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hy
      exact (Commute.zpow_zpow_self _ j i).eq
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
    exact hbot
  apply le_antisymm
  · intro x hx
    rw [mem_subgroupOf]
    have : (x : X) ∈ (commutator X₁).map X₁.subtype := ⟨x, hx, rfl⟩
    rw [map_subtype_commutator] at this
    exact hle this
  · intro x hx
    rw [mem_subgroupOf] at hx
    have h1 : (x : X) ∈ (commutator (fischerQ E)).map (fischerQ E).subtype :=
      ⟨⟨x, hx⟩, hQ ▸ mem_top _, rfl⟩
    rw [map_subtype_commutator] at h1
    have h2 : (x : X) ∈ (commutator X₁).map X₁.subtype := by
      rw [map_subtype_commutator]
      exact commutator_mono le_sup_left le_sup_left h1
    obtain ⟨y, hy, hyx⟩ := h2
    rwa [← Subtype.ext hyx]

section XOne

variable {E : Set X} (hP : Pair X E) {d : X} (hd : d ∈ E)
include hP hd

theorem coe_mem_of_mem_classOne {x : (fischerQ E ⊔ zpowers d : Subgroup X)}
    (hx : x ∈ classOne E d) : (x : X) ∈ E := by
  obtain ⟨g, rfl⟩ := isConj_iff.1 hx
  simpa [dOne] using Pair.conj_mem hP hd (g : X)

variable (hZ : center X = ⊥) (h2 : ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥)
  (h3 : ∀ N : Subgroup X, N.Normal → IsPGroup 3 N → N = ⊥) (hdQ : d ∉ fischerQ E)
include hZ h2 h3 hdQ

omit hdQ in
theorem hyp_X₁ : Hyp (fischerQ E ⊔ zpowers d : Subgroup X) (classOne E d) := by
  have := Pair.finite hP
  have hQn := fischerQ_normal hP
  set X₁ := (fischerQ E ⊔ zpowers d : Subgroup X) with hX₁
  have hQX₁ : fischerQ E ≤ X₁ := le_sup_left
  have hC := fun {y : X} (hy : ∀ q ∈ fischerQ E, y * q = q * y) =>
    eq_one_of_commute_fischerQ hP hZ h2 h3 hy
  have hconj : ∀ g : X₁, ∀ x ∈ classOne E d, g * x * g⁻¹ ∈ classOne E d := fun g x hx =>
    hx.trans (isConj_iff.2 ⟨g, rfl⟩)
  set N := closure (classOne E d)
  have hNn : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hle : N.map (MulAut.conj g).toMonoidHom ≤ N := by
      rw [MonoidHom.map_closure, closure_le]
      rintro _ ⟨x, hx, rfl⟩
      exact subset_closure (hconj g x hx)
    exact hle ⟨n, hn, rfl⟩
  set N' := N.map X₁.subtype
  have hN'conj : ∀ g ∈ X₁, ∀ n ∈ N', g * n * g⁻¹ ∈ N' := by
    rintro g hg _ ⟨m, hm, rfl⟩
    exact ⟨⟨g, hg⟩ * m * ⟨g, hg⟩⁻¹, hNn.conj_mem m hm _, by simp⟩
  have hdN' : d ∈ N' := ⟨dOne E d, subset_closure (IsConj.refl _), rfl⟩
  have hQN' : fischerQ E ≤ N' := by
    set K := N' ⊓ fischerQ E
    have hKn : (K.subgroupOf (fischerQ E)).Normal := by
      refine ⟨fun k hk q => ?_⟩
      rw [mem_subgroupOf] at hk ⊢
      exact ⟨hN'conj q (hQX₁ q.2) k hk.1, hQn.conj_mem _ hk.2 q⟩
    rcases (isSimpleGroup_fischerQ hP hZ h2 h3).eq_bot_or_eq_top_of_normal
      (K.subgroupOf (fischerQ E)) with hb | ht
    · exfalso
      apply Pair.ne_one hP hd
      refine hC fun q hq => ?_
      have hc : d * q * d⁻¹ * q⁻¹ ∈ K := by
        refine mem_inf.2 ⟨?_, (fischerQ E).mul_mem (hQn.conj_mem q hq d)
          ((fischerQ E).inv_mem hq)⟩
        have h1 : q * d⁻¹ * q⁻¹ ∈ N' := hN'conj q (hQX₁ hq) _ (N'.inv_mem hdN')
        have := N'.mul_mem hdN' h1
        simpa only [mul_assoc] using this
      have hc' : (⟨_, hc.2⟩ : fischerQ E) ∈ K.subgroupOf (fischerQ E) := hc
      rw [hb, mem_bot] at hc'
      have h1 : d * q * d⁻¹ * q⁻¹ = 1 := congrArg Subtype.val hc'
      calc d * q = d * q * d⁻¹ * q⁻¹ * (q * d) := by group
        _ = q * d := by rw [h1, one_mul]
    · intro q hq
      have : (⟨q, hq⟩ : fischerQ E) ∈ K.subgroupOf (fischerQ E) := by rw [ht]; exact mem_top _
      exact (mem_subgroupOf.1 this).1
  have hX₁N' : X₁ ≤ N' := sup_le hQN' (zpowers_le.2 hdN')
  have hcl : closure (classOne E d) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨m, hm, hmx⟩ := hX₁N' x.2
    rwa [← Subtype.ext hmx]
  have hP₁ : Pair X₁ (classOne E d) := by
    refine ⟨inferInstance, ⟨dOne E d, rfl⟩, fun x hx => ?_, fun x hx y hy => ?_, hcl⟩
    · rw [← orderOf_coe]
      exact Pair.orderOf_eq_two hP (coe_mem_of_mem_classOne hP hd hx)
    · rw [← orderOf_coe, coe_mul]
      exact Pair.orderOf_mul_mem hP (coe_mem_of_mem_classOne hP hd hx)
        (coe_mem_of_mem_classOne hP hd hy)
  refine ⟨hP₁, ?_, ?_⟩
  · rw [eq_bot_iff]
    intro z hz
    rw [mem_bot]
    refine Subtype.ext (hC fun q hq => ?_)
    exact (congrArg Subtype.val (mem_center_iff.1 hz ⟨q, hQX₁ hq⟩)).symm
  · rw [commutator_X₁ (commutator_fischerQ_eq_top hP hZ h2 h3) hQn]
    have := isSimpleGroup_fischerQ hP hZ h2 h3
    exact (subgroupOfEquivOfLe hQX₁).isSimpleGroup

omit hd hdQ in
noncomputable def commutatorX₁Equiv :
    commutator (fischerQ E ⊔ zpowers d : Subgroup X) ≃* fischerQ E :=
  (MulEquiv.subgroupCongr (commutator_X₁ (commutator_fischerQ_eq_top hP hZ h2 h3)
    (fischerQ_normal hP) d)).trans (subgroupOfEquivOfLe le_sup_left)

omit hd hdQ in
theorem nonabelian_X₁ :
    ∃ a b : commutator (fischerQ E ⊔ zpowers d : Subgroup X), a * b ≠ b * a := by
  by_contra! hc
  apply not_isSolvable_fischerQ hP hZ h2 h3
  refine Group.isSolvable_of_comm fun a b => ?_
  have := hc ((commutatorX₁Equiv hP hZ h2 h3).symm a) ((commutatorX₁Equiv hP hZ h2 h3).symm b)
  rw [← map_mul, ← map_mul] at this
  exact (commutatorX₁Equiv hP hZ h2 h3).symm.injective this

omit hd in
theorem dOne_not_mem : dOne E d ∉ commutator (fischerQ E ⊔ zpowers d : Subgroup X) := by
  rw [commutator_X₁ (commutator_fischerQ_eq_top hP hZ h2 h3) (fischerQ_normal hP), mem_subgroupOf]
  exact hdQ

theorem triResult_X₁ :
    TriResult (fischerQ E ⊔ zpowers d : Subgroup X) (dOne E d) :=
  triResult_of_hyp (hyp_X₁ hP hd hZ h2 h3) (nonabelian_X₁ hP hZ h2 h3) (IsConj.refl _)
    (dOne_not_mem hP hZ h2 h3 hdQ)

omit hd hdQ in
theorem map_commutator_inf_centralizer_X₁ :
    (commutator (fischerQ E ⊔ zpowers d : Subgroup X) ⊓ centralizer {dOne E d}).map
      (fischerQ E ⊔ zpowers d).subtype = fischerQ E ⊓ centralizer {d} := by
  rw [commutator_X₁ (commutator_fischerQ_eq_top hP hZ h2 h3) (fischerQ_normal hP)]
  ext x
  simp only [mem_map, mem_inf, mem_subgroupOf, mem_centralizer_singleton_iff, coe_subtype]
  constructor
  · rintro ⟨y, ⟨hyQ, hyd⟩, rfl⟩
    exact ⟨hyQ, congrArg Subtype.val hyd⟩
  · rintro ⟨hxQ, hxd⟩
    exact ⟨⟨x, le_sup_left (a := fischerQ E) hxQ⟩, ⟨hxQ, Subtype.ext hxd⟩, rfl⟩

end XOne

end CFSG.LargeExtraspecial.S12Tri
