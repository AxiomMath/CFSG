module

public import CFSG.Fischer.Classification.PartII.O3.Witness

public section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Fischer

namespace O3

variable {X : Type} [Group X] {E : Set X}

namespace Setting

variable (hS : Setting X E)
include hS

theorem pairwise_of_forall_isWit
    (hall : ∀ a ∈ E, ∀ b ∈ E, a * b ≠ b * a → ∀ e ∈ muSet E a b, IsWit E e a b)
    {d : X} (hd : d ∈ E) :
    ∀ y ∈ LocalClass E d, ∀ z ∈ LocalClass E d, y ≠ z → y * z ≠ z * y := by
  have hP := hS.pair
  intro y hy z hz hyz hc
  have hsame : ∀ w ∈ LocalClass E d, ∀ g ∈ LocalClass E d, w * g ≠ g * w → g ∈ fib E d w :=
    fun w hw g hg hwg => ⟨hg.1, (hall w hw.1 g hg.1 hwg d
      ⟨mem_localClass_symm hd hw, mem_localClass_symm hd hg⟩).2⟩
  have hnorm : LocalGroup E d ≤ Subgroup.normalizer (fib E d y) := by
    rw [LocalGroup, Subgroup.closure_le]
    intro g hg
    have hfwd : ∀ w ∈ fib E d y, g * w * g⁻¹ ∈ fib E d y := by
      intro w hw
      have hwD : w ∈ LocalClass E d := Pair.mem_localClass_of_mem_fib hP hy hw
      by_cases hgw : g * w = w * g
      · rw [hgw, mul_inv_cancel_right]
        exact hw
      · have hgF : g ∈ fib E d y :=
          (Pair.fib_eq hP hy.1 hw) ▸ hsame w hwD g hg fun h => hgw h.symm
        rw [Pair.inv_eq hP hg.1]
        exact Pair.tau_mem_fib hP hy.1 hw hgF
    refine Subgroup.mem_set_normalizer_iff.2 fun w => ⟨hfwd w, fun h => ?_⟩
    have h' := hfwd _ h
    rwa [show g * (g * w * g⁻¹) * g⁻¹ = g * g * w * (g * g)⁻¹ by group,
      Pair.mul_self hP hg.1, one_mul, inv_one, mul_one] at h'
  obtain ⟨h, hh, rfl⟩ := Pair.exists_localGroup_conj hP hS.hyp.center hS.hyp.simple hd hy hz
  have hzF : h * y * h⁻¹ ∈ fib E d y :=
    (Subgroup.mem_set_normalizer_iff.1 (hnorm hh) y).1 (Pair.mem_fib_self hP hy.1)
  exact Pair.not_commute_of_mem_fib hP hy.1 hzF (Ne.symm hyz) hc

theorem exists_nonwit {d y z : X} (hd : d ∈ E) (hy : y ∈ LocalClass E d)
    (hz : z ∈ LocalClass E d) (hyz : y ≠ z) (hc : y * z = z * y) :
    ∃ a ∈ E, ∃ b ∈ E, a * b ≠ b * a ∧ ∃ w, IsWit E w a b ∧
      ∃ v ∈ muSet E a b, ¬ IsWit E v a b := by
  by_contra! hall
  refine hS.pairwise_of_forall_isWit (fun a ha b hb hab e he => ?_) hd y hy z hz hyz hc
  obtain ⟨w, hw⟩ := hS.exists_isWit ha hb hab
  exact hall a ha b hb hab w hw e he

theorem exists_affine {a b w v : X} (ha : a ∈ E) (hb : b ∈ E) (hw : IsWit E w a b)
    (hv : v ∈ muSet E a b) (hnv : ¬ IsWit E v a b) :
    ∃ y ∈ fib E v a, y ∉ fib E w a ∧ y ∈ LocalClass E w ∧ a * y ≠ y * a ∧ b * y ≠ y * b ∧
      y * (a * b * a) ≠ a * b * a * y := by
  have hP := hS.pair
  have := Pair.finite hP
  have hwv : w * v = v * w := Pair.commute_of_isWit hP hw hv hnv
  have hwne : w ≠ v := fun h => hnv (h ▸ hw)
  have hwV : w ∈ LocalClass E v := ⟨hw.1.1.1, hwne, hwv⟩
  have haw : a ∈ LocalClass E w := mem_localClass_symm ha hw.1.1
  have hav : a ∈ LocalClass E v := mem_localClass_symm ha hv.1
  have hbw : b ∈ fib E w a := ⟨hb, hw.2⟩
  have hnsub : ¬ fib E v a ⊆ fib E w a := by
    intro hsub
    have heq : fib E v a = fib E w a := Set.eq_of_subset_of_ncard_le hsub
      (Pair.ncard_fib_eq hP hS.hyp.center hS.hyp.simple hv.1.1 hav hw.1.1.1 haw).le
    exact hnv ⟨hv, (heq ▸ hbw : b ∈ fib E v a).2⟩
  obtain ⟨y, hy, hyw⟩ := Set.not_subset.1 hnsub
  have hyW : y ∈ LocalClass E w := Pair.mem_localClass_of_mem_fib_of_mem hP hwV hav haw hy
  have hya : y ≠ a := by
    rintro rfl
    exact hyw (Pair.mem_fib_self hP ha)
  have hay : a * y ≠ y * a := Pair.not_commute_of_mem_fib hP ha hy hya
  have hnot : ∀ x ∈ fib E w a, y * x ≠ x * y := by
    intro x hx hc
    have hxW : x ∈ LocalClass E w := Pair.mem_localClass_of_mem_fib hP haw hx
    have hyx : y ≠ x := by
      rintro rfl
      exact hyw hx
    have hax : a ∈ fib E w x := Pair.fib_symm hP ha hx
    exact hay (Pair.commute_of_mem_fib hP hyW hxW hyx hc hax).symm
  refine ⟨y, hy, hyw, hyW, hay, fun h => hnot b hbw h.symm, hnot _ ?_⟩
  exact Pair.tau_mem_fib hP ha hbw (Pair.mem_fib_self hP ha)

end Setting

end O3

end CFSG.Fischer.Classification
