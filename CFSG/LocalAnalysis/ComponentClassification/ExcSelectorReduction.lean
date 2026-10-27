module

public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorBasic
public import CFSG.LocalAnalysis.ComponentInitial.FixedComponentCorrespondence
import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI

public noncomputable section

namespace CFSG.ComponentClassification.ExcSelector

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.RestrictedStd
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def NoSmallComponent (C : Type) [Group C] : Prop :=
  ∀ α : MulAut C, α ^ 2 = 1 → α ≠ 1 → ∀ K : Subgroup C,
    Assembly.IsComponentOf K (fixedSubgroup α) → (K.subgroupOf (fixedSubgroup α)).Normal →
      ¬ SmallType K

section Transport

variable {C C' : Type} [Group C] [Group C']

theorem assembly_isQuasisimple_of_equiv (e : C ≃* C') (h : Assembly.IsQuasisimple C) :
    Assembly.IsQuasisimple C' :=
  h.of_mulEquiv e.symm

theorem fixedSubgroup_congr (e : C ≃* C') (α : MulAut C) :
    fixedSubgroup (MulAut.congr e α) = (fixedSubgroup α).map e.toMonoidHom := by
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  change e (α (e.symm (e x))) = e x ↔ e x ∈ (fixedSubgroup α).map e.toMonoidHom
  rw [MulEquiv.symm_apply_apply, Subgroup.mem_map]
  constructor
  · intro h
    exact ⟨x, e.injective h, rfl⟩
  · rintro ⟨x', hx', hxx'⟩
    have hx : x' = x := e.injective hxx'
    subst hx
    exact congrArg e hx'

theorem isComponentOf_map_of_equiv (e : C ≃* C') {K F : Subgroup C}
    (h : Assembly.IsComponentOf K F) :
    Assembly.IsComponentOf (K.map e.toMonoidHom) (F.map e.toMonoidHom) := by
  have hmap : ∀ H : Subgroup C, H.map e.toMonoidHom = H.comap e.symm.toMonoidHom := fun H =>
    Subgroup.map_equiv_eq_comap_symm e H
  refine ⟨Subgroup.map_mono h.1, ?_, ?_⟩
  · rw [hmap, hmap]
    exact LocalAnalysis.ComponentInitial.assembly_isSubnormal_comap _ h.2.1
  · exact assembly_isQuasisimple_of_equiv (e.subgroupMap K) h.2.2

theorem noSmallComponent_of_equiv (e : C ≃* C') (h : NoSmallComponent C') :
    NoSmallComponent C := by
  intro α hα hα1 K hK hKn
  set α' := MulAut.congr e α with hα'
  have hfix := fixedSubgroup_congr e α
  have hα'2 : α' ^ 2 = 1 := by rw [hα', ← map_pow, hα, map_one]
  have hα'1 : α' ≠ 1 := fun h1 => hα1 ((MulAut.congr e).injective (by rw [← hα', h1, map_one]))
  have hK' : Assembly.IsComponentOf (K.map e.toMonoidHom) (fixedSubgroup α') := by
    rw [hfix]
    exact isComponentOf_map_of_equiv e hK
  have hKn' : ((K.map e.toMonoidHom).subgroupOf (fixedSubgroup α')).Normal := by
    rw [hfix]
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, hk, hkn⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hn)
    obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.1 g.2
    have hkF : k ∈ fixedSubgroup α := hK.1 hk
    have h1 := hKn.conj_mem ⟨k, hkF⟩ (Subgroup.mem_subgroupOf.2 hk) ⟨y, hy⟩
    rw [Subgroup.mem_subgroupOf] at h1 ⊢
    refine ⟨y * k * y⁻¹, h1, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv] at hkn hyg ⊢
    rw [hkn, hyg]
    rfl
  intro hs
  exact h α' hα'2 hα'1 _ hK' hKn' ((smallType_congr (e.subgroupMap K)).1 hs)

end Transport

section Reduction

variable {A : Type} [Group A]

theorem mem_normalizer_of_standard {L : Subgroup A} (hL : IsStandardSubgroup L) {t : A}
    (ht : t ∈ centralizer (L : Set A)) (ht2 : orderOf t = 2) {g : A}
    (hg : g ∈ centralizer ({t} : Set A)) : g ∈ normalizer (L : Set A) :=
  hL.standardComponentIsStandard.mem_normalizer_of_commute ht ht2
    (mem_centralizer_singleton_iff.1 hg)

variable {W : Subgroup A} [W.Normal]

theorem fixedSubgroup_conjNormal (a : A) :
    fixedSubgroup (MulAut.conjNormal a : MulAut W) = (centralizer ({a} : Set A)).subgroupOf W := by
  ext w
  change MulAut.conjNormal a w = w ↔ (w : A) ∈ centralizer ({a} : Set A)
  rw [mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h1 : ((MulAut.conjNormal a w : W) : A) = w := congrArg Subtype.val h
    rw [MulAut.conjNormal_apply] at h1
    calc (w : A) * a = a * (w : A) * a⁻¹ * a := by rw [h1]
      _ = a * w := by group
  · intro h
    apply Subtype.ext
    rw [MulAut.conjNormal_apply, ← h]
    group

theorem not_smallSource_of_noSmallComponent (hCW : centralizer (W : Set A) = ⊥) {a : A}
    (ha : orderOf a = 2) {L : Subgroup A} (hLW : L ≤ W)
    (hL : Assembly.IsComponentOf L (centralizer ({a} : Set A))) (hstd : IsStandardSubgroup L)
    (h : NoSmallComponent W) : ¬ SmallSource L := by
  set α : MulAut W := MulAut.conjNormal a with hα
  have hfix := fixedSubgroup_conjNormal (W := W) a
  have hα2 : α ^ 2 = 1 := by
    rw [hα, ← map_pow, ← ha, pow_orderOf_eq_one, map_one]
  have hα1 : α ≠ 1 := by
    intro h1
    have haC : a ∈ centralizer (W : Set A) := by
      rw [mem_centralizer_iff]
      intro w hw
      have h2 := congrArg (fun φ : MulAut W => ((φ ⟨w, hw⟩ : W) : A)) h1
      simp only [hα, MulAut.conjNormal_apply, MulAut.one_apply] at h2
      calc w * a = a * w * a⁻¹ * a := by rw [h2]
        _ = a * w := by group
    rw [hCW, mem_bot] at haC
    rw [haC, orderOf_one] at ha
    exact absurd ha (by norm_num)
  set K := L.subgroupOf W with hK
  have hKL : K ≃* L := Subgroup.subgroupOfEquivOfLe hLW
  have hKc : Assembly.IsComponentOf K (fixedSubgroup α) := by
    rw [hfix]
    refine ⟨fun x hx => Subgroup.mem_subgroupOf.2 (hL.1 (Subgroup.mem_subgroupOf.1 hx)), ?_,
      assembly_isQuasisimple_of_equiv hKL.symm hL.2.2⟩
    exact LocalAnalysis.ComponentInitial.assembly_isSubnormal_comap W.subtype hL.2.1
  have hKn : (K.subgroupOf (fixedSubgroup α)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hg : ((g : W) : A) ∈ centralizer ({a} : Set A) := by
      have h1 : (g : W) ∈ (centralizer ({a} : Set A)).subgroupOf W := hfix ▸ g.2
      exact Subgroup.mem_subgroupOf.1 h1
    have haL : a ∈ centralizer (L : Set A) := by
      rw [mem_centralizer_iff]
      intro l hl
      exact mem_centralizer_singleton_iff.mp (hL.1 hl)
    have hgN := mem_normalizer_of_standard hstd haL ha hg
    have hn' : (((n : fixedSubgroup α) : W) : A) ∈ L :=
      Subgroup.mem_subgroupOf.1 (Subgroup.mem_subgroupOf.1 hn)
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact (mem_normalizer_iff.1 hgN _).1 hn'
  intro hs
  exact h α hα2 hα1 K hKc hKn ((smallType_congr hKL).2 hs)

end Reduction

end CFSG.ComponentClassification.ExcSelector
