module

public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.Goldschmidt.Sec89

@[expose] def neumannKappa {Q : Type*} [Group Q] (x y : Q) : Q :=
  x⁻¹ * y⁻¹ * x * y

theorem neumannKappa_mul_left {Q : Type*} [Group Q] (x y z : Q) :
    neumannKappa (x * y) z = y⁻¹ * neumannKappa x z * y * neumannKappa y z := by
  simp [neumannKappa]
  group

theorem neumannKappa_balanced_of_commutes {Q : Type*} [Group Q] (phi : MulAut Q)
    (hcomm : ∀ q : Q, Commute q (phi q)) (x y : Q) :
    neumannKappa (phi x) y = neumannKappa x (phi y) := by
  have hp := (hcomm (x * y⁻¹)).eq
  simp only [map_mul, map_inv] at hp
  have hp' := congrArg (fun t : Q => (phi x)⁻¹ * x⁻¹ * t * y * phi y) hp
  group at hp'
  have hba_inv : Commute (phi x) x⁻¹ := Commute.inv_right_iff.mpr (hcomm x).symm
  have hp'' : (phi x)⁻¹ * y⁻¹ * phi x * (phi y)⁻¹ * y = x⁻¹ * (phi y)⁻¹ * x := by
    simpa [hba_inv.inv_mul_cancel] using hp'
  calc neumannKappa (phi x) y = ((phi x)⁻¹ * y⁻¹ * phi x * (phi y)⁻¹ * y) * phi y := by
        simp [neumannKappa, mul_assoc, (hcomm y).symm.inv_mul_cancel]
    _ = (x⁻¹ * (phi y)⁻¹ * x) * phi y := congrArg (fun t : Q => t * phi y) hp''
    _ = neumannKappa x (phi y) := by simp [neumannKappa, mul_assoc]

theorem neumannKappa_conj_eq_of_balanced {Q : Type*} [Group Q] (phi : MulAut Q)
    (hbal : ∀ x y : Q, neumannKappa (phi x) y = neumannKappa x (phi y)) (x z y : Q) :
    (phi y)⁻¹ * neumannKappa x (phi z) * phi y = y⁻¹ * neumannKappa x (phi z) * y := by
  have h := hbal (x * y) z
  simp only [map_mul, neumannKappa_mul_left] at h
  rw [hbal x z, hbal y z] at h
  exact mul_right_cancel h

theorem neumannKappa_delta_commute_of_conj_eq {Q : Type*} [Group Q] (phi : MulAut Q)
    (hconj : ∀ x z y : Q,
      (phi y)⁻¹ * neumannKappa x (phi z) * phi y = y⁻¹ * neumannKappa x (phi z) * y)
    (x z y : Q) : Commute (neumannKappa x (phi z)) (phi y * y⁻¹) := by
  rw [commute_iff_eq]
  have h := congrArg (fun t : Q => phi y * t * y⁻¹) (hconj x z y)
  group at h
  simpa [mul_assoc] using h

theorem commute_kappa_of_fixedPointFree {Q : Type*} [Group Q] [Finite Q] (phi : MulAut Q)
    (hfpf : ∀ q : Q, phi q = q → q = 1) (hthird : ∀ q : Q, phi (phi (phi q)) = q)
    (x w g : Q) : Commute (x⁻¹ * w⁻¹ * x * w) g := by
  have hFPF : MonoidHom.FixedPointFree (fun q : Q => phi q) := fun q hq => hfpf q hq
  have hphi_period : (fun q : Q => phi q)^[3] = id := by
    ext q
    simpa [Function.iterate_succ_apply] using hthird q
  have hphi_product (q : Q) : q * phi q * phi (phi q) = 1 := by
    have hnorm := MonoidHom.FixedPointFree.prod_pow_eq_one hFPF hphi_period q
    simpa [Function.iterate_succ_apply, mul_assoc] using hnorm
  have hcomm (q : Q) : Commute q (phi q) := by
    have hq := hphi_product q
    have hqq := hphi_product (q * phi q)
    simp only [map_mul] at hqq
    rw [hthird] at hqq
    have hc : phi (phi q) = (q * phi q)⁻¹ := eq_inv_of_mul_eq_one_right hq
    rw [hc] at hqq
    group at hqq
    rw [commute_iff_eq]
    have hconj : q * phi q * q⁻¹ = phi q := by
      apply mul_inv_eq_one.mp
      simpa [mul_assoc] using hqq
    exact mul_inv_eq_iff_eq_mul.mp hconj
  have hbal := neumannKappa_balanced_of_commutes phi hcomm
  have hconj := neumannKappa_conj_eq_of_balanced phi hbal
  have hdelta := neumannKappa_delta_commute_of_conj_eq phi hconj
  have hsurj : Function.Surjective (MonoidHom.commutatorMap (fun q : Q => phi q)) :=
    MonoidHom.FixedPointFree.commutatorMap_surjective hFPF
  obtain ⟨y, hy⟩ := hsurj g⁻¹
  have hy' : phi y * y⁻¹ = g := by
    have hi := congrArg (fun t : Q => t⁻¹) hy
    simpa [MonoidHom.commutatorMap_apply, div_eq_mul_inv] using hi
  have h := hdelta x (phi.symm w) y
  simpa [hy', neumannKappa] using h

end CFSG.Goldschmidt.Sec89
