module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitDihedral
public import CFSG.LocalAnalysis.ComponentClassification.GSLitReach

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X}

namespace Config

theorem isPerfect (h : Config t L) : Group.IsPerfect L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := CatalogueBHeldSmallCore.pComponent_perfect 2 _ h.isPComponent
  exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe h.le_centralizer).toMonoidHom)
    (subgroupOfEquivOfLe h.le_centralizer).surjective

theorem nontrivial (h : Config t L) : Nontrivial L :=
  (nontrivial_iff_ne_bot L).mpr h.ne_bot

theorem not_isSolvable (h : Config t L) : ¬ Group.IsSolvable L := by
  intro hs
  have := h.nontrivial
  have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial L
  rw [h.isPerfect.commutator_eq_top] at hlt
  exact lt_irrefl _ hlt

theorem false_of_isSolvable (h : Config t L)
    (hs : Group.IsSolvable (centralizer ({t} : Set X))) : False := by
  apply h.not_isSolvable
  have : Group.IsSolvable (L.subgroupOf (centralizer ({t} : Set X))) :=
    Group.isSolvable_of_isSolvable_injective (subtype_injective _)
  exact Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe h.le_centralizer).symm.toMonoidHom) (MulEquiv.injective _)

theorem false_of_twoConstrained (h : Config t L) {Q : Subgroup X}
    (hQC : Q ≤ centralizer ({t} : Set X)) (hQ : IsPGroup 2 Q)
    (hQn : centralizer ({t} : Set X) ≤ normalizer (Q : Set X))
    (hcon : centralizer ({t} : Set X) ⊓ centralizer (Q : Set X) ≤ Q) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({t} : Set X) with hC
  have hQn' : (Q.subgroupOf C).Normal := (normal_subgroupOf_iff_le_normalizer hQC).mpr hQn
  have hQ' : IsPGroup 2 (Q.subgroupOf C) := hQ.comap_of_injective C.subtype (subtype_injective C)
  have hcomm := CatalogueBPrimeJoin.p_component_normal_p_centralizer h.isPComponent hQn' hQ'
  have hLQ : L ≤ Q := by
    intro l hl
    refine hcon ⟨h.le_centralizer hl, ?_⟩
    show l ∈ centralizer (Q : Set X)
    rw [mem_centralizer_iff]
    intro q hq
    have hmem : ⁅(⟨l, h.le_centralizer hl⟩ : C), (⟨q, hQC hq⟩ : C)⁆ ∈
        ⁅L.subgroupOf C, Q.subgroupOf C⁆ :=
      commutator_mem_commutator (by rw [mem_subgroupOf]; exact hl)
        (by rw [mem_subgroupOf]; exact hq)
    rw [hcomm, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact (congrArg Subtype.val hmem).symm
  apply h.not_isSolvable
  have hL2 : IsPGroup 2 L := hQ.to_le hLQ
  have := hL2.isNilpotent
  infer_instance

theorem false_of_isQuasisimple (h : Config t L)
    (hq : Open.IsQuasisimple (centralizer ({t} : Set X))) : False := by
  set C := centralizer ({t} : Set X) with hC
  rcases h.isSubnormal.lt_normal with htop | ⟨K, hKn, hLK, hKlt⟩
  · apply h.not_mem
    have : (⟨t, mem_centralizer_singleton_iff.mpr rfl⟩ : C) ∈ L.subgroupOf C := by
      rw [htop]; exact mem_top _
    exact this
  · have hKc := Quasisimple.normal_le_center_of_ne_top hq K hKlt.ne
    apply h.not_isSolvable
    have hcomm : ∀ a b : L, a * b = b * a := by
      intro a b
      have ha : (⟨a, h.le_centralizer a.2⟩ : C) ∈ center C := hKc (hLK (by
        rw [mem_subgroupOf]; exact a.2))
      have := mem_center_iff.mp ha ⟨b, h.le_centralizer b.2⟩
      exact Subtype.ext (congrArg Subtype.val this).symm
    have : IsMulCommutative L := ⟨⟨hcomm⟩⟩
    infer_instance

omit [Finite X] in
theorem false_of_noncyclic (h : Config t L) {E : Subgroup X} (hE : IsPGroup 2 E)
    (hEc : ¬ IsCyclic E) (hEL : ∀ e ∈ E, L ≤ centralizer ({e} : Set X)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEK : E ≤ coreActionKernel L := fun e he =>
    GSLit.mem_coreActionKernel_of_le_centralizer (hEL e he)
  set E' := E.subgroupOf (coreActionKernel L) with hE'
  have hE'2 : IsPGroup 2 E' :=
    hE.comap_of_injective (coreActionKernel L).subtype (subtype_injective _)
  obtain ⟨P, hP⟩ := hE'2.exists_le_sylow
  have hPc := h.isCyclic P
  have : IsCyclic E' := Subgroup.isCyclic_of_le hP
  exact hEc ((subgroupOfEquivOfLe hEK).isCyclic.mp this)

theorem false_of_card (h : Config t L) (h7 : ¬ 7 ∣ Nat.card (centralizer ({t} : Set X)))
    (h9 : ¬ 9 ∣ Nat.card (centralizer ({t} : Set X)))
    (h2000 : Nat.card (centralizer ({t} : Set X)) ≤ 2000) : False := by
  have hd := h.card_quot_dvd_centralizer
  have hpos : 0 < Nat.card (centralizer ({t} : Set X)) := Nat.card_pos
  rcases h.card_quot_cases with h1 | h1 | h1
  · exact h7 (h1.trans hd)
  · exact h9 (h1.trans hd)
  · have := Nat.le_of_dvd hpos hd
    omega

end Config

@[expose] def Excluded {X : Type} [Group X] (t : X) : Prop :=
  Group.IsSolvable (centralizer ({t} : Set X)) ∨
    (∃ Q : Subgroup X, Q ≤ centralizer ({t} : Set X) ∧ IsPGroup 2 Q ∧
      centralizer ({t} : Set X) ≤ normalizer (Q : Set X) ∧
      centralizer ({t} : Set X) ⊓ centralizer (Q : Set X) ≤ Q) ∨
    Open.IsQuasisimple (centralizer ({t} : Set X)) ∨
    (¬ 7 ∣ Nat.card (centralizer ({t} : Set X)) ∧ ¬ 9 ∣ Nat.card (centralizer ({t} : Set X)) ∧
      Nat.card (centralizer ({t} : Set X)) ≤ 2000)

theorem Config.false_of_excluded (h : Config t L) (hex : Excluded t) : False := by
  rcases hex with hs | ⟨Q, hQC, hQ, hQn, hcon⟩ | hq | ⟨h7, h9, h2000⟩
  · exact h.false_of_isSolvable hs
  · exact h.false_of_twoConstrained hQC hQ hQn hcon
  · exact h.false_of_isQuasisimple hq
  · exact h.false_of_card h7 h9 h2000

omit [Finite X] in
theorem map_centralizer_singleton {Y : Type} [Group Y] (e : X ≃* Y) (x : X) :
    (centralizer ({x} : Set X)).map e.toMonoidHom = centralizer ({e x} : Set Y) := by
  ext y
  rw [mem_map_equiv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro hc
    have := congrArg e hc
    simpa using this
  · intro hc
    have := congrArg e.symm hc
    simpa using this

noncomputable def centralizerEquiv {Y : Type} [Group Y] (e : X ≃* Y) (x : X) :
    centralizer ({x} : Set X) ≃* centralizer ({e x} : Set Y) :=
  ((centralizer ({x} : Set X)).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr (map_centralizer_singleton e x))

omit [Finite X] in
theorem Excluded.of_mulEquiv {Y : Type} [Group Y] [Finite Y] (e : X ≃* Y) {x : X}
    (h : Excluded (e x)) : Excluded x := by
  have : Finite X := Finite.of_equiv Y e.symm.toEquiv
  set c := centralizerEquiv e x with hc
  rcases h with hs | ⟨Q, hQC, hQ, hQn, hcon⟩ | hq | ⟨h7, h9, h2000⟩
  · left
    exact Group.isSolvable_of_isSolvable_injective (f := c.toMonoidHom) c.injective
  · right; left
    refine ⟨Q.map e.symm.toMonoidHom, ?_, hQ.map _, ?_, ?_⟩
    · intro q hq
      obtain ⟨q', hq', rfl⟩ := mem_map.mp hq
      have h1 := hQC hq'
      rw [← map_centralizer_singleton e x] at h1
      obtain ⟨w, hw, hwq⟩ := mem_map.mp h1
      rw [← hwq]
      simpa using hw
    · intro g hg
      rw [mem_normalizer_iff]
      intro q
      have hg' : e g ∈ centralizer ({e x} : Set Y) := by
        rw [← map_centralizer_singleton e x]; exact mem_map_of_mem _ hg
      have hN := mem_normalizer_iff.mp (hQn hg') (e q)
      constructor
      · rintro ⟨q', hq', hqq⟩
        refine ⟨e (g * q * g⁻¹), ?_, by simp⟩
        rw [map_mul, map_mul, map_inv]
        apply hN.mp
        have : e q = q' := by rw [← hqq]; simp
        rw [this]; exact hq'
      · rintro ⟨q', hq', hqq⟩
        refine ⟨e q, ?_, by simp⟩
        apply hN.mpr
        have : e (g * q * g⁻¹) = q' := by rw [← hqq]; simp
        rw [map_mul, map_mul, map_inv] at this
        rw [this]; exact hq'
    · rintro g ⟨hg1, hg2⟩
      have hg1' : e g ∈ centralizer ({e x} : Set Y) := by
        rw [← map_centralizer_singleton e x]; exact mem_map_of_mem _ hg1
      have hg2' : e g ∈ centralizer (Q : Set Y) := by
        rw [mem_centralizer_iff]
        intro q hq
        have := mem_centralizer_iff.mp hg2 (e.symm q) ⟨q, hq, rfl⟩
        have := congrArg e this
        simpa using this
      exact ⟨e g, hcon ⟨hg1', hg2'⟩, by simp⟩
  · right; right; left
    exact Components.quasisimple_of_equiv c hq
  · right; right; right
    rw [Nat.card_congr c.toEquiv]
    exact ⟨h7, h9, h2000⟩

end CFSG.ComponentClassification.HSFLit
