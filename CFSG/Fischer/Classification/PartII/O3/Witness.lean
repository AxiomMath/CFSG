module

public import CFSG.Fischer.Classification.PartII.O3.Fibre
public import CFSG.Fischer.Uniq.Counting

public section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Fischer

namespace O3

variable {X : Type} [Group X] {E : Set X}

structure Setting (X : Type) [Group X] (E : Set X) : Prop where
  hyp : Hyp X E
  nab : ∃ a b : commutator X, a * b ≠ b * a
  move : ∃ d ∈ E, ∃ g ∈ core E d, ∃ x ∈ LocalClass E d, g * x * g⁻¹ ≠ x

@[expose] def IsWit (E : Set X) (e a b : X) : Prop := e ∈ muSet E a b ∧ a * b ∈ core E e

theorem mem_localClass_symm {e x : X} (he : e ∈ E) (hx : x ∈ LocalClass E e) :
    e ∈ LocalClass E x :=
  ⟨he, fun h => hx.2.1 h.symm, hx.2.2.symm⟩

namespace Setting

variable (hS : Setting X E)
include hS

theorem pair : Pair X E := hS.hyp.pair

theorem move_at {e : X} (he : e ∈ E) :
    ∃ g ∈ core E e, ∃ x ∈ LocalClass E e, g * x * g⁻¹ ≠ x := by
  obtain ⟨d, hd, g, hg, x, hx, hgx⟩ := hS.move
  obtain ⟨h, rfl⟩ := isConj_iff.1 (Pair.isConj hS.pair hd he)
  refine ⟨h * g * h⁻¹, Pair.conj_mem_core_conj hS.pair h hg, h * x * h⁻¹,
    (Pair.conj_mem_localClass_iff hS.pair h).2 hx, fun heq => hgx ?_⟩
  have h2 : h * (g * x * g⁻¹) * h⁻¹ = h * x * h⁻¹ := by rw [← heq]; group
  simpa using h2

theorem exists_fib_pair {e : X} (he : e ∈ E) :
    ∃ x ∈ LocalClass E e, ∃ y ∈ fib E e x, y ≠ x := by
  obtain ⟨g, hg, x, hx, hgx⟩ := hS.move_at he
  exact ⟨x, hx, g * x * g⁻¹, Pair.conj_mem_fib hS.pair hx hg, hgx⟩

theorem exists_isWit {a b : X} (ha : a ∈ E) (hb : b ∈ E) (hab : a * b ≠ b * a) :
    ∃ e, IsWit E e a b := by
  obtain ⟨d, hd, -⟩ := hS.move
  obtain ⟨x, hx, y, hy, hyx⟩ := hS.exists_fib_pair hd
  have hP := hS.pair
  have hxy := Pair.not_commute_of_mem_fib hP hx.1 hy hyx
  obtain ⟨h, rfl, rfl⟩ := Pair.exists_conj_pair_of_not_commute hP hS.hyp.center hS.hyp.simple
    hS.nab hx.1 hy.1 ha hb hxy hab
  have hyd : y ∈ LocalClass E d := Pair.mem_localClass_of_mem_fib hP hx hy
  refine ⟨h * d * h⁻¹, ⟨?_, ?_⟩, ?_⟩
  · exact (Pair.conj_mem_localClass_iff hP h).2 (mem_localClass_symm hd hx)
  · exact (Pair.conj_mem_localClass_iff hP h).2 (mem_localClass_symm hd hyd)
  · have h' := Pair.conj_mem_core_conj hP h hy.2
    rwa [show h * (x * y) * h⁻¹ = h * x * h⁻¹ * (h * y * h⁻¹) by group] at h'

end Setting

section Closure

variable (hP : Pair X E)
include hP

theorem Pair.mem_core_of_commute_of_not_commute {a c u : X} (ha : a ∈ E) (hc : c ∈ E)
    (hac : a * c ≠ c * a) (hu : u ∈ core E a) (huc : u * c = c * u) : u ∈ core E c := by
  have hua : u * a = a * u :=
    Subgroup.mem_centralizer_singleton_iff.1 (core_le_centralizer E a hu)
  have hbr : a * c * a = c * a * c := Pair.mul_mul_eq hP ha hc hac
  have hta : c * a * c * a * (c * a * c)⁻¹ = c := by
    rw [mul_inv_rev, mul_inv_rev, Pair.inv_eq hP ha, Pair.inv_eq hP hc]
    calc c * a * c * a * (c * (a * c)) = c * (a * c * a) * c * a * c := by group
      _ = c * (c * a * c) * c * a * c := by rw [hbr]
      _ = c * c * a * (c * c) * a * c := by group
      _ = c := by rw [Pair.mul_self hP hc, one_mul, mul_one, Pair.mul_self hP ha, one_mul]
  have hut : Commute u (c * a * c) :=
    ((show Commute u c from huc).mul_right (show Commute u a from hua)).mul_right huc
  have h := Pair.conj_mem_core_conj hP (c * a * c) hu
  rwa [hta, ← hut.eq, mul_inv_cancel_right] at h

theorem Pair.isWit_of_not_commute {w c a b : X} (hw : IsWit E w a b) (hc : c ∈ muSet E a b)
    (hwc : w * c ≠ c * w) : IsWit E c a b := by
  refine ⟨hc, Pair.mem_core_of_commute_of_not_commute hP hw.1.1.1 hc.1.1 hwc hw.2 ?_⟩
  rw [mul_assoc, ← hc.2.2.2, ← mul_assoc, ← hc.1.2.2, mul_assoc]

theorem Pair.commute_of_isWit {w c a b : X} (hw : IsWit E w a b) (hc : c ∈ muSet E a b)
    (hnc : ¬ IsWit E c a b) : w * c = c * w := by
  by_contra h
  exact hnc (Pair.isWit_of_not_commute hP hw hc h)

theorem Pair.fib_subset_of_commute {a c f : X} (ha : a ∈ E) (hc : c ∈ E)
    (hac : a * c ≠ c * a) (hfc : ∀ y ∈ fib E a f, y * c = c * y) (hf : f ∈ E) :
    fib E a f ⊆ fib E c f := by
  intro y hy
  have hf' := hfc f (Pair.mem_fib_self hP hf)
  refine ⟨hy.1, Pair.mem_core_of_commute_of_not_commute hP ha hc hac hy.2 ?_⟩
  rw [mul_assoc, hfc y hy, ← mul_assoc, hf', mul_assoc]

theorem Pair.isWit_conj (g : X) {e a b : X} (h : IsWit E e a b) :
    IsWit E (g * e * g⁻¹) (g * a * g⁻¹) (g * b * g⁻¹) := by
  refine ⟨⟨(Pair.conj_mem_localClass_iff hP g).2 h.1.1,
    (Pair.conj_mem_localClass_iff hP g).2 h.1.2⟩, ?_⟩
  have h' := Pair.conj_mem_core_conj hP g h.2
  rwa [show g * (a * b) * g⁻¹ = g * a * g⁻¹ * (g * b * g⁻¹) by group] at h'

end Closure

namespace Setting

variable (hS : Setting X E)
include hS

theorem ncard_wit_eq {a b a' b' : X} (ha : a ∈ E) (hb : b ∈ E) (hab : a * b ≠ b * a)
    (ha' : a' ∈ E) (hb' : b' ∈ E) (hab' : a' * b' ≠ b' * a') :
    {e | IsWit E e a' b'}.ncard = {e | IsWit E e a b}.ncard := by
  have hP := hS.pair
  obtain ⟨g, rfl, rfl⟩ := Pair.exists_conj_pair_of_not_commute hP hS.hyp.center hS.hyp.simple
    hS.nab ha hb ha' hb' hab hab'
  have himg : {e | IsWit E e (g * a * g⁻¹) (g * b * g⁻¹)} =
      (fun y => g * y * g⁻¹) '' {e | IsWit E e a b} := by
    ext e
    constructor
    · intro h
      refine ⟨g⁻¹ * e * g⁻¹⁻¹, ?_, by group⟩
      have h' := Pair.isWit_conj hP g⁻¹ h
      rwa [show g⁻¹ * (g * a * g⁻¹) * g⁻¹⁻¹ = a by group,
        show g⁻¹ * (g * b * g⁻¹) * g⁻¹⁻¹ = b by group] at h'
    · rintro ⟨e, he, rfl⟩
      exact Pair.isWit_conj hP g he
  rw [himg, Set.ncard_image_of_injective _ (conj_injective g)]

theorem ncard_far_mul_ncard_wit {x a b e₀ x₀ : X} (hx : x ∈ E) (ha : a ∈ E) (hb : b ∈ E)
    (hab : a * b ≠ b * a) (he₀ : e₀ ∈ E) (hx₀ : x₀ ∈ LocalClass E e₀) :
    {c | c ∈ E ∧ c * x ≠ x * c}.ncard * {e | IsWit E e a b}.ncard =
      (LocalClass E x).ncard * ((fib E e₀ x₀).ncard - 1) := by
  have hP := hS.pair
  have := Pair.finite hP
  refine ncard_mul_eq_ncard_mul (fun c e => IsWit E e x c) (fun c hc => ?_) (fun e he => ?_)
  · have hxc : x * c ≠ c * x := fun h => hc.2 h.symm
    rw [← hS.ncard_wit_eq ha hb hab hx hc.1 hxc]
    congr 1
    ext e
    exact ⟨fun h => h.2, fun h => ⟨h.1.1, h⟩⟩
  · have hxe : x ∈ LocalClass E e := mem_localClass_symm hx he
    have hset : {c | c ∈ {c | c ∈ E ∧ c * x ≠ x * c} ∧ IsWit E e x c} = fib E e x \ {x} := by
      ext c
      constructor
      · rintro ⟨⟨hc, hcx⟩, hw⟩
        exact ⟨⟨hc, hw.2⟩, fun h => hcx (by rw [Set.mem_singleton_iff.1 h])⟩
      · rintro ⟨hc, hcx⟩
        have hcx' : c ≠ x := hcx
        have hnc := Pair.not_commute_of_mem_fib hP hx hc hcx'
        have hce : c ∈ LocalClass E e := Pair.mem_localClass_of_mem_fib hP hxe hc
        exact ⟨⟨hc.1, fun h => hnc h.symm⟩, ⟨he, mem_localClass_symm he.1 hce⟩, hc.2⟩
    rw [hset, Set.ncard_sdiff_singleton_of_mem (Pair.mem_fib_self hP hx),
      Pair.ncard_fib_eq hP hS.hyp.center hS.hyp.simple he₀ hx₀ he.1 hxe]

theorem ncard_muSet_eq {a b a' b' : X} (ha : a ∈ E) (hb : b ∈ E) (hab : a * b ≠ b * a)
    (ha' : a' ∈ E) (hb' : b' ∈ E) (hab' : a' * b' ≠ b' * a') :
    (muSet E a' b').ncard = (muSet E a b).ncard := by
  obtain ⟨g, rfl, rfl⟩ := Pair.exists_conj_pair_of_not_commute hS.pair hS.hyp.center
    hS.hyp.simple hS.nab ha hb ha' hb' hab hab'
  rw [← Pair.image_conj_muSet hS.pair, Set.ncard_image_of_injective _ (conj_injective g)]

theorem ncard_inter_eq {a b a' b' : X} (ha : a ∈ E) (hb : b ∈ LocalClass E a) (ha' : a' ∈ E)
    (hb' : b' ∈ LocalClass E a') :
    (muSet E a' b').ncard = (muSet E a b).ncard := by
  obtain ⟨g, rfl, rfl⟩ := Pair.exists_conj_pair_of_commute hS.pair hS.hyp.center
    hS.hyp.simple ha hb.1 ha' hb'.1 hb.2.1.symm hb.2.2.symm hb'.2.1.symm hb'.2.2.symm
  rw [← Pair.image_conj_muSet hS.pair, Set.ncard_image_of_injective _ (conj_injective g)]

end Setting

end O3

end CFSG.Fischer.Classification
