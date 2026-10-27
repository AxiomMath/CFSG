module

public import CFSG.Fischer.Classification.PartII.O3.Core
public import CFSG.Fischer.Classification.Basic.Transitivity

public section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Fischer

namespace O3

variable {X : Type} [Group X] {E : Set X}

@[expose] def fib (E : Set X) (e x : X) : Set X := {y | y ∈ E ∧ x * y ∈ core E e}

section Basic

variable (hP : Pair X E)
include hP

theorem Pair.mem_fib_self {e x : X} (hx : x ∈ E) : x ∈ fib E e x :=
  ⟨hx, by rw [Pair.mul_self hP hx]; exact one_mem _⟩

theorem Pair.fib_symm {e x y : X} (hx : x ∈ E) (hy : y ∈ fib E e x) : x ∈ fib E e y := by
  refine ⟨hx, ?_⟩
  have h := inv_mem hy.2
  rwa [mul_inv_rev, Pair.inv_eq hP hy.1, Pair.inv_eq hP hx] at h

theorem Pair.fib_trans {e x y z : X} (hy : y ∈ fib E e x) (hz : z ∈ fib E e y) :
    z ∈ fib E e x := by
  refine ⟨hz.1, ?_⟩
  have h := mul_mem hy.2 hz.2
  rwa [show x * y * (y * z) = x * (y * y) * z by group, Pair.mul_self hP hy.1, mul_one] at h

theorem Pair.fib_eq {e x y : X} (hx : x ∈ E) (hy : y ∈ fib E e x) : fib E e y = fib E e x :=
  Set.ext fun _ => ⟨fun h => Pair.fib_trans hP hy h,
    fun h => Pair.fib_trans hP (Pair.fib_symm hP hx hy) h⟩

theorem Pair.not_commute_of_mem_fib {e x y : X} (hx : x ∈ E) (hy : y ∈ fib E e x)
    (hxy : y ≠ x) : x * y ≠ y * x := by
  intro hc
  have h2 : x * y * (x * y) = 1 := by
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * x * (y * y) := by rw [← hc]; group
      _ = 1 := by rw [Pair.mul_self hP hx, Pair.mul_self hP hy.1, one_mul]
  have h1 := eq_one_of_isPGroup_three (isPGroup_core E e) hy.2 h2
  apply hxy
  rw [← Pair.inv_eq hP hx]
  exact (inv_eq_of_mul_eq_one_right h1).symm

theorem Pair.mem_localClass_of_mem_fib {e x y : X} (hx : x ∈ LocalClass E e)
    (hy : y ∈ fib E e x) : y ∈ LocalClass E e := by
  have hyx : y = x * (x * y) := by rw [← mul_assoc, Pair.mul_self hP hx.1, one_mul]
  have hc : x * y * e = e * (x * y) :=
    Subgroup.mem_centralizer_singleton_iff.1 (core_le_centralizer E e hy.2)
  have hye : y * e = e * y := by
    rw [hyx, mul_assoc, hc, ← mul_assoc, hx.2.2, mul_assoc]
  refine ⟨hy.1, fun h => ?_, hye⟩
  subst h
  exact Pair.not_commute_of_mem_fib hP hx.1 hy (fun h => hx.2.1 h.symm) hx.2.2

theorem Pair.conj_mem_fib {e x r : X} (hx : x ∈ LocalClass E e) (hr : r ∈ core E e) :
    r * x * r⁻¹ ∈ fib E e x := by
  refine ⟨Pair.conj_mem hP hx.1 r, ?_⟩
  have h := mul_mem (conj_mem_core (mem_localGroup hx) hr) (inv_mem hr)
  rwa [Pair.inv_eq hP hx.1, show x * r * x * r⁻¹ = x * (r * x * r⁻¹) by group] at h

theorem Pair.exists_conj_of_mem_fib {e x y : X} (hx : x ∈ E) (hy : y ∈ fib E e x) :
    ∃ r ∈ core E e, r * x * r⁻¹ = y := by
  by_cases hxy : y = x
  · exact ⟨1, one_mem _, by rw [hxy]; group⟩
  refine ⟨x * y, hy.2, ?_⟩
  have h3 : (x * y) ^ 3 = 1 := by
    rw [← Pair.orderOf_mul_eq_three hP hx hy.1 (Pair.not_commute_of_mem_fib hP hx hy hxy),
      pow_orderOf_eq_one]
  have h3' : x * y * x * y * x * y = 1 := by rw [← h3]; simp only [pow_three, mul_assoc]
  rw [mul_inv_rev, Pair.inv_eq hP hx, Pair.inv_eq hP hy.1,
    show x * y * x * (y * x) = x * y * x * y * x * y * y⁻¹ by group, h3', one_mul,
    Pair.inv_eq hP hy.1]

theorem Pair.tau_mem_fib {e x y z : X} (hx : x ∈ E) (hy : y ∈ fib E e x) (hz : z ∈ fib E e x) :
    z * y * z ∈ fib E e x := by
  have hzy : z ∈ fib E e y := Pair.fib_trans hP (Pair.fib_symm hP hx hy) hz
  refine ⟨Pair.mul_mul_mem hP hz.1 hy.1, ?_⟩
  have h := mul_mem hz.2 hzy.2
  rwa [show x * z * (y * z) = x * (z * y * z) by group] at h

theorem Pair.conj_mem_fib_conj (g : X) {e x y : X} (hy : y ∈ fib E e x) :
    g * y * g⁻¹ ∈ fib E (g * e * g⁻¹) (g * x * g⁻¹) := by
  refine ⟨Pair.conj_mem hP hy.1 g, ?_⟩
  have h := Pair.conj_mem_core_conj hP g hy.2
  rwa [show g * (x * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) by group] at h

end Basic

section Propagation

variable (hP : Pair X E)
include hP

theorem Pair.commute_of_mem_fib {e f x y : X} (hf : f ∈ LocalClass E e)
    (hx : x ∈ LocalClass E e) (hfx : f ≠ x) (hc : f * x = x * f) (hy : y ∈ fib E e x) :
    f * y = y * f := by
  obtain ⟨r, hr, rfl⟩ := Pair.exists_conj_of_mem_fib hP hx.1 hy
  refine Pair.commute_conj_of_commute hP (N := core E e) (fun g hg n hn => ?_)
    (fun u hu hu2 g _ => ?_) hx hf hfx hc hr (Pair.mem_localClass_of_mem_fib hP hx hy)
  · have h := conj_mem_core (mem_localGroup hg) hn
    rw [Pair.inv_eq hP hg.1] at h ⊢
    exact h
  · rw [eq_one_of_isPGroup_three (isPGroup_core E e) hu hu2, one_mul, mul_one]

theorem Pair.mem_localClass_of_mem_fib_of_mem {e x f f' : X} (hx : x ∈ LocalClass E e)
    (hfe : f ∈ LocalClass E e) (hfx : f ∈ LocalClass E x) (hf' : f' ∈ fib E e f) :
    f' ∈ LocalClass E x := by
  have hxf : x * f' = f' * x :=
    Pair.commute_of_mem_fib hP hx hfe (fun h => hfx.2.1 h.symm) hfx.2.2.symm hf'
  refine ⟨hf'.1, fun h => ?_, hxf.symm⟩
  subst h
  exact Pair.not_commute_of_mem_fib hP hfe.1 hf' (fun h => hfx.2.1 h.symm) hfx.2.2

end Propagation

theorem Pair.fib_conj (hP : Pair X E) (g e x : X) :
    fib E (g * e * g⁻¹) (g * x * g⁻¹) = (fun y => g * y * g⁻¹) '' fib E e x := by
  ext y
  constructor
  · intro hy
    refine ⟨g⁻¹ * y * g⁻¹⁻¹, ?_, by group⟩
    have h := Pair.conj_mem_fib_conj hP g⁻¹ hy
    rwa [show g⁻¹ * (g * e * g⁻¹) * g⁻¹⁻¹ = e by group,
      show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at h
  · rintro ⟨y, hy, rfl⟩
    exact Pair.conj_mem_fib_conj hP g hy

theorem Pair.ncard_fib_eq (hP : Pair X E) (hZ : Subgroup.center X = ⊥)
    (hS : IsSimpleGroup (commutator X)) {e x e' x' : X} (he : e ∈ E) (hx : x ∈ LocalClass E e)
    (he' : e' ∈ E) (hx' : x' ∈ LocalClass E e') :
    (fib E e' x').ncard = (fib E e x).ncard := by
  obtain ⟨g, hge, hgx⟩ := Pair.exists_conj_pair_of_commute hP hZ hS he hx.1 he' hx'.1
    hx.2.1.symm hx.2.2.symm hx'.2.1.symm hx'.2.2.symm
  rw [← hge, ← hgx, Pair.fib_conj hP]
  exact Set.ncard_image_of_injective _ (conj_injective g)

end O3

end CFSG.Fischer.Classification
