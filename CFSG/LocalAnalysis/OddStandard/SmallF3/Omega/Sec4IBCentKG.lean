module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IBMono
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IBPow7

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private def sec4ICanon (j : Fin 7) : Fin 7 → ZMod 2 := fun k => if k = j then 0 else 1

private theorem sec4I_weight_six_form :
    ∀ v : Fin 7 → ZMod 2, IsEvenVec v → vecWeight v = 6 → ∃ j, v = sec4ICanon j := by
  unfold IsEvenVec vecWeight
  decide +kernel

private theorem sec4I_class_card_le_canon :
    ∀ (j : Fin 7) (w : Fin 7 → ZMod 2), IsEvenVec w → w ≠ 0 → w ≠ sec4ICanon j →
      ∀ i : Fin 7,
        (Finset.univ.filter fun k : Fin 7 =>
          sec4ICanon j k = sec4ICanon j i ∧ w k = w i).card ≤ 5 := by
  unfold IsEvenVec
  decide +kernel

theorem sec4I_class_card_le {v w : Fin 7 → ZMod 2} (hv : IsEvenVec v) (hv6 : vecWeight v = 6)
    (hw : IsEvenVec w) (hw0 : w ≠ 0) (hwv : w ≠ v) (i : Fin 7) :
    (Finset.univ.filter fun k : Fin 7 => v k = v i ∧ w k = w i).card ≤ 5 := by
  obtain ⟨j, hj⟩ := sec4I_weight_six_form v hv hv6
  rw [hj] at hwv ⊢
  exact sec4I_class_card_le_canon j w hw hw0 hwv i

private theorem sec4I_repr_eq_zero_of_comm_T {fr : Sec4IFrame Q} {g : OGroup Q}
    {s : Fin 7 → ZMod 2} (hgs : g * sec4IT fr s = sec4IT fr s * g) {k m : Fin 7}
    (h : s m ≠ s k) : fr.b.repr ((g : V ≃ₗ[ZMod 3] V) (fr.b k)) m = 0 := by
  have hG : (g : V ≃ₗ[ZMod 3] V) * (sec4IT fr s : V ≃ₗ[ZMod 3] V) =
      (sec4IT fr s : V ≃ₗ[ZMod 3] V) * (g : V ≃ₗ[ZMod 3] V) := by
    simpa using congrArg (fun x : OGroup Q => (x : V ≃ₗ[ZMod 3] V)) hgs
  have hcomm : ∀ x, (g : V ≃ₗ[ZMod 3] V) ((sec4IT fr s : V ≃ₗ[ZMod 3] V) x) =
      (sec4IT fr s : V ≃ₗ[ZMod 3] V) ((g : V ≃ₗ[ZMod 3] V) x) := by
    intro x
    have h := congrArg (fun e : V ≃ₗ[ZMod 3] V => e x) hG
    simpa only [LinearEquiv.mul_apply] using h
  have hT : (sec4IT fr s : V ≃ₗ[ZMod 3] V) ((g : V ≃ₗ[ZMod 3] V) (fr.b k)) =
      ((sec4ISgn (s k) : (ZMod 3)ˣ) : ZMod 3) • (g : V ≃ₗ[ZMod 3] V) (fr.b k) := by
    rw [← hcomm (fr.b k), sec4IT_apply_basis, map_smul]
  have key := congrArg (fun y => fr.b.repr y m) hT
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at key
  rw [sec4IT_repr] at key
  have hsne : ((sec4ISgn (s m) : (ZMod 3)ˣ) : ZMod 3) ≠
      ((sec4ISgn (s k) : (ZMod 3)ˣ) : ZMod 3) := by
    intro hh
    exact h (sec4ISgn_injective (Units.ext hh))
  have hzero : (((sec4ISgn (s m) : (ZMod 3)ˣ) : ZMod 3) -
      ((sec4ISgn (s k) : (ZMod 3)ˣ) : ZMod 3)) *
      fr.b.repr ((g : V ≃ₗ[ZMod 3] V) (fr.b k)) m = 0 := by
    rw [sub_mul, key, sub_self]
  exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hsne)

theorem sec4I_eq_one_of_pow_seven (fr : Sec4IFrame Q) {v w : Fin 7 → ZMod 2}
    (hv : IsEvenVec v) (hv6 : vecWeight v = 6) (hw : IsEvenVec w) (hw0 : w ≠ 0) (hwv : w ≠ v)
    {g : OGroup Q} (hg7 : g ^ 7 = 1) (hgv : g * sec4IT fr v = sec4IT fr v * g)
    (hgw : g * sec4IT fr w = sec4IT fr w * g) : g = 1 := by
  have hG7 : (g : V ≃ₗ[ZMod 3] V) ^ 7 = 1 := by
    simpa using congrArg (fun x : OGroup Q => (x : V ≃ₗ[ZMod 3] V)) hg7
  refine sec4I_ogroup_ext fr fun i => ?_
  let S : Finset (Fin 7) := Finset.univ.filter fun k : Fin 7 => v k = v i ∧ w k = w i
  let p : Submodule (ZMod 3) V :=
    Submodule.span (ZMod 3) (Set.range fun k : {k : Fin 7 // k ∈ S} => fr.b k)
  have hd : Module.finrank (ZMod 3) p ≤ 5 := by
    have h1 : Module.finrank (ZMod 3) p ≤ S.card := by
      have h := finrank_range_le_card (R := ZMod 3) (fun k : {k : Fin 7 // k ∈ S} => fr.b k)
      rwa [Fintype.card_coe] at h
    have h3 : S.card ≤ 5 := by
      simpa only [S] using sec4I_class_card_le hv hv6 hw hw0 hwv i
    omega
  have hGb : ∀ k ∈ S, (g : V ≃ₗ[ZMod 3] V) (fr.b k) ∈ p := by
    intro k hk
    rw [← fr.b.sum_repr ((g : V ≃ₗ[ZMod 3] V) (fr.b k))]
    refine Submodule.sum_mem p fun m _ => ?_
    by_cases hm : m ∈ S
    · exact Submodule.smul_mem p _ (Submodule.subset_span
        (show fr.b m ∈ Set.range (fun k : {k : Fin 7 // k ∈ S} => fr.b k) from
          ⟨⟨m, hm⟩, rfl⟩))
    · have hvk : v k = v i := by
        have h := hk
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at h
        exact h.1
      have hwk : w k = w i := by
        have h := hk
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at h
        exact h.2
      have hne : v m ≠ v k ∨ w m ≠ w k := by
        by_contra hcon
        push Not at hcon
        exact hm (by
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hcon.1.trans hvk, hcon.2.trans hwk⟩)
      have hcoef : fr.b.repr ((g : V ≃ₗ[ZMod 3] V) (fr.b k)) m = 0 := by
        rcases hne with hne | hne
        · exact sec4I_repr_eq_zero_of_comm_T hgv hne
        · exact sec4I_repr_eq_zero_of_comm_T hgw hne
      rw [hcoef, zero_smul]
      exact p.zero_mem
  have hp : ∀ x ∈ p, (g : V ≃ₗ[ZMod 3] V) x ∈ p := by
    have hmono : Submodule.span (ZMod 3) (Set.range fun k : {k : Fin 7 // k ∈ S} => fr.b k) ≤
        Submodule.comap ((g : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V) p := by
      rw [Submodule.span_le]
      intro y hy
      rw [Set.mem_range] at hy
      obtain ⟨k, rfl⟩ := hy
      exact hGb k.1 k.2
    intro x hx
    exact hmono hx
  have hiS : i ∈ S := by simp [S]
  have hbi : fr.b i ∈ p := Submodule.subset_span ⟨⟨i, hiS⟩, rfl⟩
  have hfix : (g : V ≃ₗ[ZMod 3] V) (fr.b i) = fr.b i :=
    sec4I_fixed_of_pow_seven (h := (g : V ≃ₗ[ZMod 3] V)) hG7 p hp hd (fr.b i) hbi
  have hone : ((1 : OGroup Q) : V ≃ₗ[ZMod 3] V) (fr.b i) = fr.b i := rfl
  rw [hone]
  exact hfix

end CFSG.OddStandard.SmallF3.Omega
