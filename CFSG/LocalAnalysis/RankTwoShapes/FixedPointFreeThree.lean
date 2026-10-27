module

public import Mathlib.GroupTheory.FixedPointFree

public section

namespace CFSG.RankTwoShapes

open scoped commutatorElement

universe u

variable {Q : Type u} [Group Q]

@[expose] def rcomm (x y : Q) : Q := x⁻¹ * y⁻¹ * x * y

theorem rcomm_def (x y : Q) : rcomm x y = x⁻¹ * y⁻¹ * x * y := rfl

private theorem rcomm_mul_left (x y z : Q) :
    rcomm (x * y) z = y⁻¹ * rcomm x z * y * rcomm y z := by
  simp only [rcomm]
  group

private theorem rcomm_balanced_of_commutes (phi : MulAut Q)
    (hcomm : ∀ q : Q, Commute q (phi q)) (x y : Q) :
    rcomm (phi x) y = rcomm x (phi y) := by
  have hp := (hcomm (x * y⁻¹)).eq
  simp only [map_mul, map_inv] at hp
  have hp' := congrArg (fun t : Q => (phi x)⁻¹ * x⁻¹ * t * y * phi y) hp
  group at hp'
  have hba_inv : Commute (phi x) x⁻¹ := Commute.inv_right_iff.mpr (hcomm x).symm
  have hp'' : (phi x)⁻¹ * y⁻¹ * phi x * (phi y)⁻¹ * y = x⁻¹ * (phi y)⁻¹ * x := by
    simpa [hba_inv.inv_mul_cancel] using hp'
  calc
    rcomm (phi x) y = ((phi x)⁻¹ * y⁻¹ * phi x * (phi y)⁻¹ * y) * phi y := by
      simp [rcomm, mul_assoc, (hcomm y).symm.inv_mul_cancel]
    _ = (x⁻¹ * (phi y)⁻¹ * x) * phi y := congrArg (fun t : Q => t * phi y) hp''
    _ = rcomm x (phi y) := by simp [rcomm, mul_assoc]

private theorem rcomm_conj_eq_of_balanced (phi : MulAut Q)
    (hbal : ∀ x y : Q, rcomm (phi x) y = rcomm x (phi y)) (x z y : Q) :
    (phi y)⁻¹ * rcomm x (phi z) * phi y = y⁻¹ * rcomm x (phi z) * y := by
  have h := hbal (x * y) z
  simp only [map_mul, rcomm_mul_left] at h
  rw [hbal x z, hbal y z] at h
  exact mul_right_cancel h

private theorem rcomm_delta_commute_of_conj_eq (phi : MulAut Q)
    (hconj : ∀ x z y : Q, (phi y)⁻¹ * rcomm x (phi z) * phi y = y⁻¹ * rcomm x (phi z) * y)
    (x z y : Q) :
    Commute (rcomm x (phi z)) (phi y * y⁻¹) := by
  rw [commute_iff_eq]
  have h := congrArg (fun t : Q => phi y * t * y⁻¹) (hconj x z y)
  group at h
  simpa [mul_assoc] using h

theorem fpfThree_cube (α : MulAut Q) (hα : α ^ 3 = 1) (x : Q) : α (α (α x)) = x := by
  have hq := congrArg (fun g : MulAut Q => g x) hα
  simpa [pow_succ] using hq

private theorem rcomm_mul_left_of_central (hcen : ∀ x w g : Q, Commute (rcomm x w) g)
    (x y z : Q) : rcomm (x * y) z = rcomm x z * rcomm y z := by
  rw [rcomm_mul_left]
  have h := (hcen x z y).eq
  calc y⁻¹ * rcomm x z * y * rcomm y z = y⁻¹ * (rcomm x z * y) * rcomm y z := by group
    _ = y⁻¹ * (y * rcomm x z) * rcomm y z := by rw [h]
    _ = rcomm x z * rcomm y z := by group

variable [Finite Q]

theorem fpfThree_norm (α : MulAut Q) (hα : α ^ 3 = 1) (hfpf : ∀ x : Q, α x = x → x = 1)
    (x : Q) : x * α x * α (α x) = 1 := by
  have hFPF : MonoidHom.FixedPointFree (fun q : Q => α q) := fun q hq => hfpf q hq
  have hperiod : (fun q : Q => α q)^[3] = id := by
    ext q
    have hq := congrArg (fun g : MulAut Q => g q) hα
    simpa [pow_succ, Function.iterate_succ_apply] using hq
  have hnorm := MonoidHom.FixedPointFree.prod_pow_eq_one hFPF hperiod x
  simpa [Function.iterate_succ_apply, mul_assoc, Finset.prod_range_succ] using hnorm

theorem fpfThree_commute (α : MulAut Q) (hα : α ^ 3 = 1) (hfpf : ∀ x : Q, α x = x → x = 1)
    (q : Q) : Commute q (α q) := by
  have hq := fpfThree_norm α hα hfpf q
  have hqq := fpfThree_norm α hα hfpf (q * α q)
  simp only [map_mul] at hqq
  rw [fpfThree_cube α hα] at hqq
  have hc : α (α q) = (q * α q)⁻¹ := eq_inv_of_mul_eq_one_right hq
  rw [hc] at hqq
  group at hqq
  rw [commute_iff_eq]
  have hconj : q * α q * q⁻¹ = α q := by
    apply mul_inv_eq_one.mp
    simpa [mul_assoc] using hqq
  exact mul_inv_eq_iff_eq_mul.mp hconj

theorem fpfThree_rcomm_balanced (α : MulAut Q) (hα : α ^ 3 = 1)
    (hfpf : ∀ x : Q, α x = x → x = 1) (x y : Q) : rcomm (α x) y = rcomm x (α y) :=
  rcomm_balanced_of_commutes α (fpfThree_commute α hα hfpf) x y

theorem fpfThree_rcomm_central (α : MulAut Q) (hα : α ^ 3 = 1)
    (hfpf : ∀ x : Q, α x = x → x = 1) (x w g : Q) : Commute (rcomm x w) g := by
  have hbal := fpfThree_rcomm_balanced α hα hfpf
  have hconj := rcomm_conj_eq_of_balanced α hbal
  have hdelta := rcomm_delta_commute_of_conj_eq α hconj
  have hFPF : MonoidHom.FixedPointFree (fun q : Q => α q) := fun q hq => hfpf q hq
  have hsurj : Function.Surjective (MonoidHom.commutatorMap (fun q : Q => α q)) :=
    MonoidHom.FixedPointFree.commutatorMap_surjective hFPF
  obtain ⟨y, hy⟩ := hsurj g⁻¹
  have hy' : α y * y⁻¹ = g := by
    have hi := congrArg (fun t : Q => t⁻¹) hy
    simpa [MonoidHom.commutatorMap_apply, div_eq_mul_inv] using hi
  have h := hdelta x (α.symm w) y
  simpa [hy'] using h

theorem fpfThree_commutatorElement_central (α : MulAut Q) (hα : α ^ 3 = 1)
    (hfpf : ∀ x : Q, α x = x → x = 1) (x y g : Q) : Commute ⁅x, y⁆ g := by
  have h := fpfThree_rcomm_central α hα hfpf x⁻¹ y⁻¹ g
  simpa [rcomm, commutatorElement_def] using h

theorem fpfThree_commutator_le_center (α : MulAut Q) (hα : α ^ 3 = 1)
    (hfpf : ∀ x : Q, α x = x → x = 1) :
    ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ ≤ Subgroup.center Q := by
  rw [Subgroup.commutator_def, Subgroup.closure_le]
  rintro c ⟨x, -, y, -, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_center_iff]
  intro g
  exact (fpfThree_commutatorElement_central α hα hfpf x y g).symm.eq

theorem fpfThree_rcomm_alpha_left (α : MulAut Q) (hα : α ^ 3 = 1)
    (hfpf : ∀ x : Q, α x = x → x = 1) (x y : Q) :
    rcomm (α x) y = α (α (rcomm x y)) := by
  have hcen := fpfThree_rcomm_central α hα hfpf
  have hbal := fpfThree_rcomm_balanced α hα hfpf
  have hnorm := fpfThree_norm α hα hfpf
  have hexp : rcomm x y * rcomm (α x) y * rcomm (α (α x)) y = 1 := by
    rw [← rcomm_mul_left_of_central hcen, ← rcomm_mul_left_of_central hcen, hnorm x]
    simp [rcomm]
  have h2 : rcomm (α (α x)) y = α (rcomm x y) := by
    rw [hbal (α x) y]
    simp [rcomm]
  rw [h2] at hexp
  have hc := hnorm (rcomm x y)
  have hcomm1 : Commute (rcomm x y) (rcomm (α x) y) := hcen x y _
  have : rcomm (α x) y = (rcomm x y)⁻¹ * (α (rcomm x y))⁻¹ := by
    have h' : rcomm x y * rcomm (α x) y = (α (rcomm x y))⁻¹ :=
      eq_inv_of_mul_eq_one_left hexp
    rw [← h']
    group
  rw [this]
  have hc' : α (α (rcomm x y)) = (rcomm x y * α (rcomm x y))⁻¹ :=
    eq_inv_of_mul_eq_one_right hc
  rw [hc', mul_inv_rev]
  exact (Commute.inv_left (hcen x y (α (rcomm x y))⁻¹)).eq

theorem fixedPointFree_three_class_two (α : MulAut Q) (hα : α ^ 3 = 1)
    (hfpf : ∀ x : Q, α x = x → x = 1) :
    ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ ≤ Subgroup.center Q ∧
      (∀ x y : Q, rcomm x (α y) = rcomm (α x) y) ∧
      (∀ x y : Q, rcomm (α x) y = α (α (rcomm x y))) ∧
      (∀ x : Q, rcomm x (α x) = 1) ∧
      (∀ x : Q, x * α x * α (α x) = 1) :=
  ⟨fpfThree_commutator_le_center α hα hfpf,
    fun x y => (fpfThree_rcomm_balanced α hα hfpf x y).symm,
    fpfThree_rcomm_alpha_left α hα hfpf,
    fun x => by
      have h := (fpfThree_commute α hα hfpf x).eq
      have h' : (α x)⁻¹ * x * α x = x := by
        rw [mul_assoc, h]
        group
      calc rcomm x (α x) = x⁻¹ * ((α x)⁻¹ * x * α x) := by simp only [rcomm]; group
        _ = 1 := by rw [h']; group,
    fpfThree_norm α hα hfpf⟩

end CFSG.RankTwoShapes
