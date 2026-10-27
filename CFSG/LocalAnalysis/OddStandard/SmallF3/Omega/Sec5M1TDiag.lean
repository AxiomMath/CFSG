module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5Mono1
public import CFSG.Assembly.ComponentTypeDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

@[expose] def sec5m1tC012 : Equiv.Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 1 2

@[expose] def sec5m1tC123 : Equiv.Perm (Fin 6) := Equiv.swap 1 2 * Equiv.swap 2 3

private def sec5m1t_aux_comm {c : ZMod 3} (fr : NFrame Q (Fin 6) c) (y : V ≃ₗ[ZMod 3] V) : Prop :=
  ∀ i j : Fin 6, (i : ℕ) < 4 → (j : ℕ) < 4 → i ≠ j →
    y * ((fr.signChange {i, j} : OGroup Q) : V ≃ₗ[ZMod 3] V) =
      ((fr.signChange {i, j} : OGroup Q) : V ≃ₗ[ZMod 3] V) * y

private lemma sec5m1t_aux_coord_zero {c : ZMod 3} (fr : NFrame Q (Fin 6) c)
    {y : V ≃ₗ[ZMod 3] V} (ht : sec5m1t_aux_comm fr y) {l : Fin 6} (hl : (l : ℕ) < 4)
    {k : Fin 6} (hk : k ≠ l) : fr.b.repr (y (fr.b l)) k = 0 := by
  obtain ⟨j, hj4, hjl, hjk⟩ :=
    (by decide : ∀ l k : Fin 6, (l : ℕ) < 4 → k ≠ l →
      ∃ j : Fin 6, (j : ℕ) < 4 ∧ j ≠ l ∧ j ≠ k) l k hl hk
  have hcomm := ht l j hl hj4 (Ne.symm hjl)
  have h1 : y (((fr.signChange {l, j} : OGroup Q) : V ≃ₗ[ZMod 3] V) (fr.b l)) =
      ((fr.signChange {l, j} : OGroup Q) : V ≃ₗ[ZMod 3] V) (y (fr.b l)) := by
    have := congrArg (fun e : V ≃ₗ[ZMod 3] V => e (fr.b l)) hcomm
    simpa [LinearEquiv.mul_apply] using this
  have htl : ((fr.signChange {l, j} : OGroup Q) : V ≃ₗ[ZMod 3] V) (fr.b l) = -fr.b l := by
    rw [fr.signChange_basis {l, j} l, if_pos (by simp)]
  have h2 : ((fr.signChange {l, j} : OGroup Q) : V ≃ₗ[ZMod 3] V) (y (fr.b l)) =
      -y (fr.b l) := by
    rw [← h1, htl, map_neg]
  have h3 : fr.b.repr (((fr.signChange {l, j} : OGroup Q) : V ≃ₗ[ZMod 3] V)
        (y (fr.b l))) k = fr.b.repr (-y (fr.b l)) k := by rw [h2]
  rw [fr.repr_signChange {l, j} (y (fr.b l)) k] at h3
  have hknot : k ∉ ({l, j} : Finset (Fin 6)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hk, Ne.symm hjk⟩
  rw [if_neg hknot] at h3
  have hneg : fr.b.repr (-y (fr.b l)) k = -fr.b.repr (y (fr.b l)) k := by simp
  rw [hneg] at h3
  exact (by decide : ∀ r : ZMod 3, r = -r → r = 0) _ h3

private lemma sec5m1t_aux_eigen {c : ZMod 3} (fr : NFrame Q (Fin 6) c)
    {y : V ≃ₗ[ZMod 3] V} (ht : sec5m1t_aux_comm fr y) {l : Fin 6} (hl : (l : ℕ) < 4) :
    y (fr.b l) = (fr.b.repr (y (fr.b l)) l) • fr.b l := by
  conv_lhs => rw [← fr.b.sum_repr (y (fr.b l))]
  refine Finset.sum_eq_single l ?_ ?_
  · intro i _ hi
    rw [sec5m1t_aux_coord_zero fr ht hl hi, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ l) h

private lemma sec5m1t_aux_scalar_eq {c : ZMod 3} (fr : NFrame Q (Fin 6) c)
    {y : V ≃ₗ[ZMod 3] V} {σ : Equiv.Perm (Fin 6)}
    (hp : y * ((fr.permOrth σ : OGroup Q) : V ≃ₗ[ZMod 3] V) =
      ((fr.permOrth σ : OGroup Q) : V ≃ₗ[ZMod 3] V) * y)
    {l : Fin 6} (hl' : y (fr.b l) = (fr.b.repr (y (fr.b l)) l) • fr.b l)
    (hσl' : y (fr.b (σ l)) = (fr.b.repr (y (fr.b (σ l))) (σ l)) • fr.b (σ l)) :
    fr.b.repr (y (fr.b (σ l))) (σ l) = fr.b.repr (y (fr.b l)) l := by
  have h1 : y (((fr.permOrth σ : OGroup Q) : V ≃ₗ[ZMod 3] V) (fr.b l)) =
      ((fr.permOrth σ : OGroup Q) : V ≃ₗ[ZMod 3] V) (y (fr.b l)) := by
    have := congrArg (fun e : V ≃ₗ[ZMod 3] V => e (fr.b l)) hp
    simpa [LinearEquiv.mul_apply] using this
  rw [fr.permOrth_basis σ l, hl', map_smul, fr.permOrth_basis σ l, hσl'] at h1
  have hsub : (fr.b.repr (y (fr.b l)) l - fr.b.repr (y (fr.b (σ l))) (σ l)) •
      fr.b (σ l) = 0 := by
    rw [sub_smul, h1, sub_self]
  rcases smul_eq_zero.mp hsub with hz | hb
  · exact (sub_eq_zero.mp hz).symm
  · exact absurd hb (fr.b.ne_zero (σ l))

theorem sec5m1t_diag {c : ZMod 3} (fr : NFrame Q (Fin 6) c) {y : V ≃ₗ[ZMod 3] V}
    (ht : ∀ i j : Fin 6, (i : ℕ) < 4 → (j : ℕ) < 4 → i ≠ j →
      y * ((fr.signChange {i, j} : OGroup Q) : V ≃ₗ[ZMod 3] V) =
        ((fr.signChange {i, j} : OGroup Q) : V ≃ₗ[ZMod 3] V) * y)
    (hp₁ : y * ((fr.permOrth sec5m1tC012 : OGroup Q) : V ≃ₗ[ZMod 3] V) =
      ((fr.permOrth sec5m1tC012 : OGroup Q) : V ≃ₗ[ZMod 3] V) * y)
    (hp₂ : y * ((fr.permOrth sec5m1tC123 : OGroup Q) : V ≃ₗ[ZMod 3] V) =
      ((fr.permOrth sec5m1tC123 : OGroup Q) : V ≃ₗ[ZMod 3] V) * y) :
    ∃ a : ZMod 3, a ≠ 0 ∧ ∀ l : Fin 6, (l : ℕ) < 4 → y (fr.b l) = a • fr.b l := by
  have heig : ∀ l : Fin 6, (l : ℕ) < 4 → y (fr.b l) =
      (fr.b.repr (y (fr.b l)) l) • fr.b l := fun l hl => sec5m1t_aux_eigen fr ht hl
  have hC012_0 : sec5m1tC012 0 = 1 := by decide
  have hC012_1 : sec5m1tC012 1 = 2 := by decide
  have hC123_2 : sec5m1tC123 2 = 3 := by decide
  have h01 : fr.b.repr (y (fr.b 1)) 1 = fr.b.repr (y (fr.b 0)) 0 := by
    have h := sec5m1t_aux_scalar_eq fr hp₁ (heig 0 (by decide)) (heig 1 (by decide))
    rwa [hC012_0] at h
  have h12 : fr.b.repr (y (fr.b 2)) 2 = fr.b.repr (y (fr.b 1)) 1 := by
    have h := sec5m1t_aux_scalar_eq fr hp₁ (heig 1 (by decide)) (heig 2 (by decide))
    rwa [hC012_1] at h
  have h23 : fr.b.repr (y (fr.b 3)) 3 = fr.b.repr (y (fr.b 2)) 2 := by
    have h := sec5m1t_aux_scalar_eq fr hp₂ (heig 2 (by decide)) (heig 3 (by decide))
    rwa [hC123_2] at h
  have haeq : ∀ l : Fin 6, (l : ℕ) < 4 →
      fr.b.repr (y (fr.b l)) l = fr.b.repr (y (fr.b 0)) 0 := by
    intro l hl
    fin_cases l
    · rfl
    · exact h01
    · exact h12.trans h01
    · exact h23.trans (h12.trans h01)
    · exact absurd hl (by decide)
    · exact absurd hl (by decide)
  have hne : fr.b.repr (y (fr.b 0)) 0 ≠ 0 := by
    intro hzero
    have h0 : y (fr.b 0) = 0 := by rw [heig 0 (by decide), hzero, zero_smul]
    have hb0 : fr.b 0 = 0 := y.injective (by rw [h0, map_zero])
    exact fr.b.ne_zero 0 hb0
  refine ⟨fr.b.repr (y (fr.b 0)) 0, hne, fun l hl => ?_⟩
  rw [heig l hl, haeq l hl]

end CFSG.OddStandard.SmallF3.Omega
