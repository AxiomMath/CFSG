module

public import CFSG.ClassicalInvolution.Phan.PhanDn.StdFamily
public import CFSG.ClassicalInvolution.Phan.PhanDn.DiagTorus
public import CFSG.LocalAnalysis.StandardType.PhanEBridgeDefs
public import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutBlocks
public import CFSG.GroupTheory.LocalCores.MinimalNormal

public section

namespace CFSG.ClassicalInvolution.PhanDn

open CFSG.ClassicalInvolution.Phan
open CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.ClassicalInvolution.Phan.PhanE
open CFSG.ClassicalInvolution.ModelFacts.UnitaryAut
open CFSG.ClassicalGroups.Unitary
open CFSG.LieType.Universal.Unitary
open CFSG.LieType.Steinberg
open CFSG.LieType.BorelTits
open QuadraticMap

variable {F K : Type} [Field F] [Field K] [Finite K] [Algebra F K] {f : ℕ} [CharP K 2]

private noncomputable abbrev mu := normOne (unitaryInvolution K 2 f)

private noncomputable def nodeTuple (m : ℕ) (hm : 3 ≤ m) (i : Fin (m + 1)) :
    mu (f := f) (K := K) →* (Fin (m + 1) → mu (f := f) (K := K)) :=
  Fin.lastCases
    (motive := fun _ => mu (f := f) (K := K) →* (Fin (m + 1) → mu (f := f) (K := K)))
    ((MonoidHom.mulSingle (fun _ : Fin (m + 1) => mu (f := f) (K := K))
        ⟨m - 1, by omega⟩) *
      (MonoidHom.mulSingle (fun _ : Fin (m + 1) => mu (f := f) (K := K))
        (Fin.last m)))
    (fun k =>
      (MonoidHom.mulSingle (fun _ : Fin (m + 1) => mu (f := f) (K := K))
          (Fin.castSucc k)) *
        ((MonoidHom.mulSingle (fun _ : Fin (m + 1) => mu (f := f) (K := K))
          k.succ).comp invMonoidHom))
    i

private theorem nodeTuple_castSucc (m : ℕ) (hm : 3 ≤ m) (k : Fin m) :
    nodeTuple (K := K) (f := f) m hm (Fin.castSucc k) =
      (MonoidHom.mulSingle (fun _ : Fin (m + 1) => mu (f := f) (K := K))
          (Fin.castSucc k)) *
        ((MonoidHom.mulSingle (fun _ : Fin (m + 1) => mu (f := f) (K := K))
          k.succ).comp invMonoidHom) := by
  rw [nodeTuple, Fin.lastCases_castSucc]

private theorem nodeTuple_last (m : ℕ) (hm : 3 ≤ m) :
    nodeTuple (K := K) (f := f) m hm (Fin.last m) =
      (MonoidHom.mulSingle (fun _ : Fin (m + 1) => mu (f := f) (K := K))
          ⟨m - 1, by omega⟩) *
        (MonoidHom.mulSingle (fun _ : Fin (m + 1) => mu (f := f) (K := K))
          (Fin.last m)) := by
  rw [nodeTuple, Fin.lastCases_last]

private theorem nodeTuple_apply_castSucc (m : ℕ) (hm : 3 ≤ m) (k : Fin m)
    (u : mu (f := f) (K := K)) (j : Fin (m + 1)) :
    nodeTuple (K := K) (f := f) m hm (Fin.castSucc k) u j =
      (if j = Fin.castSucc k then u else 1) *
        (if j = k.succ then u⁻¹ else 1) := by
  rw [nodeTuple_castSucc, MonoidHom.mul_apply, MonoidHom.comp_apply, invMonoidHom_apply,
    MonoidHom.mulSingle_apply, MonoidHom.mulSingle_apply, Pi.mul_apply, Pi.mulSingle_apply,
    Pi.mulSingle_apply]

private theorem nodeTuple_apply_last (m : ℕ) (hm : 3 ≤ m)
    (u : mu (f := f) (K := K)) (j : Fin (m + 1)) :
    nodeTuple (K := K) (f := f) m hm (Fin.last m) u j =
      (if j = (⟨m - 1, by omega⟩ : Fin (m + 1)) then u else 1) *
        (if j = Fin.last m then u else 1) := by
  rw [nodeTuple_last, MonoidHom.mul_apply, MonoidHom.mulSingle_apply,
    MonoidHom.mulSingle_apply, Pi.mul_apply, Pi.mulSingle_apply, Pi.mulSingle_apply]

private noncomputable def paramMap (m : ℕ) (hm : 3 ≤ m) :
    (Fin (m + 1) → mu (f := f) (K := K)) →*
      (Fin (m + 1) → mu (f := f) (K := K)) where
  toFun t := ∏ i, nodeTuple (K := K) (f := f) m hm i (t i)
  map_one' := by simp
  map_mul' t s := by
    simp only [Pi.mul_apply]
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => map_mul (nodeTuple (K := K) (f := f) m hm i) _ _

private theorem paramMap_apply (m : ℕ) (hm : 3 ≤ m)
    (t : Fin (m + 1) → mu (f := f) (K := K)) :
    paramMap (K := K) (f := f) m hm t =
      ∏ i, nodeTuple (K := K) (f := f) m hm i (t i) := rfl

private theorem paramMap_mulSingle (m : ℕ) (hm : 3 ≤ m) (i : Fin (m + 1))
    (u : mu (f := f) (K := K)) :
    paramMap (K := K) (f := f) m hm (Pi.mulSingle i u) =
      nodeTuple (K := K) (f := f) m hm i u := by
  let t : Fin (m + 1) → mu (f := f) (K := K) := Pi.mulSingle i u
  change paramMap (K := K) (f := f) m hm t = nodeTuple (K := K) (f := f) m hm i u
  rw [paramMap_apply]
  change (∏ j, nodeTuple (K := K) (f := f) m hm j (t j)) =
    nodeTuple (K := K) (f := f) m hm i u
  rw [Fintype.prod_eq_single (f := fun j => nodeTuple (K := K) (f := f) m hm j (t j)) i]
  · rw [show t i = u by rw [show t = Pi.mulSingle i u from rfl, Pi.mulSingle_eq_same]]
  · intro j hj
    rw [show t j = 1 by
      rw [show t = Pi.mulSingle i u from rfl, Pi.mulSingle_apply, if_neg hj]]
    exact map_one _

private theorem prod_nodeTuple_apply_zero (m : ℕ) (hm : 3 ≤ m)
    (t : Fin (m + 1) → mu (f := f) (K := K)) :
    (∏ i, nodeTuple (K := K) (f := f) m hm i (t i)) (⟨0, by omega⟩ : Fin (m + 1)) =
      t ⟨0, by omega⟩ := by
  rw [Fin.prod_univ_castSucc, Pi.mul_apply]
  have hjlast : (⟨0, by omega⟩ : Fin (m + 1)) ≠ Fin.last m := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_last] at this
    omega
  have hja : (⟨0, by omega⟩ : Fin (m + 1)) ≠ (⟨m - 1, by omega⟩ : Fin (m + 1)) := by
    intro h
    have := congrArg Fin.val h
    simp only at this
    omega
  rw [nodeTuple_apply_last, if_neg hja, if_neg hjlast, one_mul, Finset.prod_apply]
  have hfirst : (∏ k : Fin m,
      (if (⟨0, by omega⟩ : Fin (m + 1)) = Fin.castSucc k then t (Fin.castSucc k) else 1)) =
      t ⟨0, by omega⟩ := by
    let k0 : Fin m := ⟨0, by omega⟩
    have hjk0 : (⟨0, by omega⟩ : Fin (m + 1)) = Fin.castSucc k0 := Fin.ext rfl
    rw [Fintype.prod_eq_single (f := fun k : Fin m =>
      (if (⟨0, by omega⟩ : Fin (m + 1)) = Fin.castSucc k then t (Fin.castSucc k) else 1)) k0]
    · rw [if_pos hjk0, ← hjk0]
    · intro k hk
      rw [if_neg]
      intro h
      apply hk
      exact Fin.ext (by simpa [k0] using (congrArg Fin.val h).symm)
  have hsecond : (∏ k : Fin m,
      (if (⟨0, by omega⟩ : Fin (m + 1)) = k.succ then (t (Fin.castSucc k))⁻¹ else 1)) = 1 := by
    refine Finset.prod_eq_one ?_
    intro k _
    rw [if_neg]
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_succ] at this
    omega
  have hprod : (∏ i : Fin m,
      nodeTuple (K := K) (f := f) m hm (Fin.castSucc i) (t (Fin.castSucc i))
        (⟨0, by omega⟩ : Fin (m + 1))) =
      ((∏ k : Fin m,
        ((if (⟨0, by omega⟩ : Fin (m + 1)) = Fin.castSucc k then t (Fin.castSucc k) else 1) *
          (if (⟨0, by omega⟩ : Fin (m + 1)) = k.succ then (t (Fin.castSucc k))⁻¹ else 1))) :
        mu (f := f) (K := K)) := by
    refine Finset.prod_congr (M := mu (f := f) (K := K)) rfl ?_
    intro k _
    exact nodeTuple_apply_castSucc m hm k (t (Fin.castSucc k)) ⟨0, by omega⟩
  rw [mul_one, hprod, Finset.prod_mul_distrib, hfirst, hsecond, mul_one]

private theorem prod_nodeTuple_apply_succ (m : ℕ) (hm : 3 ≤ m)
    (t : Fin (m + 1) → mu (f := f) (K := K)) (j : ℕ) (hj : j + 1 < m - 1) :
    (∏ i, nodeTuple (K := K) (f := f) m hm i (t i))
        (⟨j + 1, by omega⟩ : Fin (m + 1)) =
      t ⟨j + 1, by omega⟩ * (t ⟨j, by omega⟩)⁻¹ := by
  rw [Fin.prod_univ_castSucc, Pi.mul_apply]
  have hjlast : (⟨j + 1, by omega⟩ : Fin (m + 1)) ≠ Fin.last m := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_last] at this
    omega
  have hja : (⟨j + 1, by omega⟩ : Fin (m + 1)) ≠
      (⟨m - 1, by omega⟩ : Fin (m + 1)) := by
    intro h
    have := congrArg Fin.val h
    simp only at this
    omega
  rw [nodeTuple_apply_last, if_neg hja, if_neg hjlast, one_mul, Finset.prod_apply]
  have hfirst : (∏ k : Fin m,
      (if (⟨j + 1, by omega⟩ : Fin (m + 1)) = Fin.castSucc k then t (Fin.castSucc k) else 1)) =
      t ⟨j + 1, by omega⟩ := by
    let k0 : Fin m := ⟨j + 1, by omega⟩
    have hjk0 : (⟨j + 1, by omega⟩ : Fin (m + 1)) = Fin.castSucc k0 := Fin.ext rfl
    rw [Fintype.prod_eq_single (f := fun k : Fin m =>
      (if (⟨j + 1, by omega⟩ : Fin (m + 1)) = Fin.castSucc k then t (Fin.castSucc k) else 1)) k0]
    · rw [if_pos hjk0, ← hjk0]
    · intro k hk
      rw [if_neg]
      intro h
      apply hk
      exact Fin.ext (by simpa [k0] using (congrArg Fin.val h).symm)
  have hsecond : (∏ k : Fin m,
      (if (⟨j + 1, by omega⟩ : Fin (m + 1)) = k.succ then (t (Fin.castSucc k))⁻¹ else 1)) =
      (t ⟨j, by omega⟩)⁻¹ := by
    let k0 : Fin m := ⟨j, by omega⟩
    have hjk0 : (⟨j + 1, by omega⟩ : Fin (m + 1)) = k0.succ := Fin.ext (by simp [k0])
    rw [Fintype.prod_eq_single (f := fun k : Fin m =>
      (if (⟨j + 1, by omega⟩ : Fin (m + 1)) = k.succ then (t (Fin.castSucc k))⁻¹ else 1)) k0]
    · rw [if_pos hjk0]
      congr 1
    · intro k hk
      rw [if_neg]
      intro h
      apply hk
      have := congrArg Fin.val h
      simp only [Fin.val_succ] at this
      exact Fin.ext (by
        show k.val = j
        omega)
  have hprod : (∏ i : Fin m,
      nodeTuple (K := K) (f := f) m hm (Fin.castSucc i) (t (Fin.castSucc i))
        (⟨j + 1, by omega⟩ : Fin (m + 1))) =
      ((∏ k : Fin m,
        ((if (⟨j + 1, by omega⟩ : Fin (m + 1)) = Fin.castSucc k then t (Fin.castSucc k) else 1) *
          (if (⟨j + 1, by omega⟩ : Fin (m + 1)) = k.succ then (t (Fin.castSucc k))⁻¹ else 1))) :
        mu (f := f) (K := K)) := by
    refine Finset.prod_congr (M := mu (f := f) (K := K)) rfl ?_
    intro k _
    exact nodeTuple_apply_castSucc m hm k (t (Fin.castSucc k)) ⟨j + 1, by omega⟩
  rw [mul_one, hprod, Finset.prod_mul_distrib, hfirst, hsecond]

private theorem prod_nodeTuple_apply_pred (m : ℕ) (hm : 3 ≤ m)
    (t : Fin (m + 1) → mu (f := f) (K := K)) :
    (∏ i, nodeTuple (K := K) (f := f) m hm i (t i))
        (⟨m - 1, by omega⟩ : Fin (m + 1)) =
      t ⟨m - 1, by omega⟩ * (t ⟨m - 2, by omega⟩)⁻¹ * t (Fin.last m) := by
  rw [Fin.prod_univ_castSucc, Pi.mul_apply]
  have hja : (⟨m - 1, by omega⟩ : Fin (m + 1)) =
      (⟨m - 1, by omega⟩ : Fin (m + 1)) := rfl
  have hjl : (⟨m - 1, by omega⟩ : Fin (m + 1)) ≠ Fin.last m := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_last] at this
    omega
  rw [nodeTuple_apply_last, if_pos hja, if_neg hjl, Finset.prod_apply]
  have hfirst : (∏ k : Fin m,
      (if (⟨m - 1, by omega⟩ : Fin (m + 1)) = Fin.castSucc k then t (Fin.castSucc k) else 1)) =
      t ⟨m - 1, by omega⟩ := by
    let k0 : Fin m := ⟨m - 1, by omega⟩
    have hjk0 : (⟨m - 1, by omega⟩ : Fin (m + 1)) = Fin.castSucc k0 := Fin.ext rfl
    rw [Fintype.prod_eq_single (f := fun k : Fin m =>
      (if (⟨m - 1, by omega⟩ : Fin (m + 1)) = Fin.castSucc k then t (Fin.castSucc k) else 1)) k0]
    · rw [if_pos hjk0, ← hjk0]
    · intro k hk
      rw [if_neg]
      intro h
      apply hk
      exact Fin.ext (by simpa [k0] using (congrArg Fin.val h).symm)
  have hsecond : (∏ k : Fin m,
      (if (⟨m - 1, by omega⟩ : Fin (m + 1)) = k.succ then (t (Fin.castSucc k))⁻¹ else 1)) =
      (t ⟨m - 2, by omega⟩)⁻¹ := by
    let k0 : Fin m := ⟨m - 2, by omega⟩
    have hjk0 : (⟨m - 1, by omega⟩ : Fin (m + 1)) = k0.succ := Fin.ext (by simp [k0]; omega)
    rw [Fintype.prod_eq_single (f := fun k : Fin m =>
      (if (⟨m - 1, by omega⟩ : Fin (m + 1)) = k.succ then (t (Fin.castSucc k))⁻¹ else 1)) k0]
    · rw [if_pos hjk0]
      congr 1
    · intro k hk
      rw [if_neg]
      intro h
      apply hk
      have := congrArg Fin.val h
      simp only [Fin.val_succ] at this
      exact Fin.ext (by
        show k.val = m - 2
        omega)
  have hprod : (∏ i : Fin m,
      nodeTuple (K := K) (f := f) m hm (Fin.castSucc i) (t (Fin.castSucc i))
        (⟨m - 1, by omega⟩ : Fin (m + 1))) =
      ((∏ k : Fin m,
        ((if (⟨m - 1, by omega⟩ : Fin (m + 1)) = Fin.castSucc k then t (Fin.castSucc k) else 1) *
          (if (⟨m - 1, by omega⟩ : Fin (m + 1)) = k.succ then (t (Fin.castSucc k))⁻¹ else 1))) :
        mu (f := f) (K := K)) := by
    refine Finset.prod_congr (M := mu (f := f) (K := K)) rfl ?_
    intro k _
    exact nodeTuple_apply_castSucc m hm k (t (Fin.castSucc k)) ⟨m - 1, by omega⟩
  rw [hprod, Finset.prod_mul_distrib, hfirst, hsecond, mul_one]

private theorem prod_nodeTuple_apply_last (m : ℕ) (hm : 3 ≤ m)
    (t : Fin (m + 1) → mu (f := f) (K := K)) :
    (∏ i, nodeTuple (K := K) (f := f) m hm i (t i)) (Fin.last m) =
      (t ⟨m - 1, by omega⟩)⁻¹ * t (Fin.last m) := by
  rw [Fin.prod_univ_castSucc, Pi.mul_apply]
  have hla : (Fin.last m) ≠ (⟨m - 1, by omega⟩ : Fin (m + 1)) := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_last] at this
    omega
  rw [nodeTuple_apply_last, if_neg hla, if_pos rfl, one_mul, Finset.prod_apply]
  have hfirst : (∏ k : Fin m,
      (if (Fin.last m) = Fin.castSucc k then t (Fin.castSucc k) else 1)) = 1 := by
    refine Finset.prod_eq_one ?_
    intro k _
    rw [if_neg]
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_last, Fin.val_castSucc] at this
    omega
  have hsecond : (∏ k : Fin m,
      (if (Fin.last m) = k.succ then (t (Fin.castSucc k))⁻¹ else 1)) =
      (t ⟨m - 1, by omega⟩)⁻¹ := by
    let k0 : Fin m := ⟨m - 1, by omega⟩
    have hjk0 : (Fin.last m : Fin (m + 1)) = k0.succ := Fin.ext (by simp [k0]; omega)
    rw [Fintype.prod_eq_single (f := fun k : Fin m =>
      (if (Fin.last m) = k.succ then (t (Fin.castSucc k))⁻¹ else 1)) k0]
    · rw [if_pos hjk0]
      congr 1
    · intro k hk
      rw [if_neg]
      intro h
      apply hk
      have := congrArg Fin.val h
      simp only [Fin.val_last, Fin.val_succ] at this
      exact Fin.ext (by
        show k.val = m - 1
        omega)
  have hprod : (∏ i : Fin m,
      nodeTuple (K := K) (f := f) m hm (Fin.castSucc i) (t (Fin.castSucc i))
        (Fin.last m)) =
      ((∏ k : Fin m,
        ((if (Fin.last m) = Fin.castSucc k then t (Fin.castSucc k) else 1) *
          (if (Fin.last m) = k.succ then (t (Fin.castSucc k))⁻¹ else 1))) :
        mu (f := f) (K := K)) := by
    refine Finset.prod_congr (M := mu (f := f) (K := K)) rfl ?_
    intro k _
    exact nodeTuple_apply_castSucc m hm k (t (Fin.castSucc k)) (Fin.last m)
  rw [hprod, Finset.prod_mul_distrib, hfirst, hsecond, one_mul]

theorem odd_card_normOne_unitaryInvolution (hK : Nat.card K = (2 ^ f) ^ 2) :
    Odd (Nat.card (normOne (unitaryInvolution K 2 f))) := by
  have hcard : Nat.card (mu (f := f) (K := K)) = 2 ^ f + 1 := by
    simpa using CFSG.ClassicalInvolution.Phan.card_normOne (K := K) (p := 2) (f := f) hK
  have hf : f ≠ 0 := by
    intro hf0
    have h1 : Nat.card K = 1 := by simpa [hf0] using hK
    have h2 : 1 < Nat.card K := Finite.one_lt_card
    omega
  rw [hcard]
  exact (Nat.even_pow.mpr ⟨⟨1, by norm_num⟩, hf⟩).add_one

theorem eq_one_of_mul_self_eq_one_normOne (hK : Nat.card K = (2 ^ f) ^ 2)
    {u : normOne (unitaryInvolution K 2 f)} (hu : u * u = 1) : u = 1 := by
  by_contra hne
  have hord : orderOf u = 2 :=
    (orderOf_eq_prime_iff (p := 2)).mpr ⟨by simpa [pow_two] using hu, hne⟩
  have hdvd : 2 ∣ Nat.card (mu (f := f) (K := K)) := by
    rw [← hord]
    exact orderOf_dvd_natCard u
  exact (odd_card_normOne_unitaryInvolution (K := K) (f := f) hK).not_two_dvd_nat hdvd

private theorem paramMap_eq_one (m : ℕ) (hm : 3 ≤ m)
    (hK : Nat.card K = (2 ^ f) ^ 2)
    (t : Fin (m + 1) → mu (f := f) (K := K))
    (h : paramMap (K := K) (f := f) m hm t = 1) : t = 1 := by
  have hprod : (∏ i, nodeTuple (K := K) (f := f) m hm i (t i)) = 1 := by
    rwa [← paramMap_apply]
  have h0 : t (⟨0, by omega⟩ : Fin (m + 1)) = 1 := by
    have := congrFun hprod (⟨0, by omega⟩ : Fin (m + 1))
    rwa [prod_nodeTuple_apply_zero m hm t] at this
  have ht : ∀ j : ℕ, j ≤ m - 2 → ∀ hj : j < m + 1,
      t (⟨j, hj⟩ : Fin (m + 1)) = 1 := by
    intro j
    induction j with
    | zero =>
        intro _ hj
        simpa using h0
    | succ j ih =>
        intro hjle hjlt
        have hj' : j ≤ m - 2 := by omega
        have hcoord := congrFun hprod (⟨j + 1, hjlt⟩ : Fin (m + 1))
        rw [prod_nodeTuple_apply_succ m hm t j (by omega)] at hcoord
        rw [ih hj' (by omega), inv_one, mul_one] at hcoord
        exact hcoord
  have hpred : t (⟨m - 2, by omega⟩ : Fin (m + 1)) = 1 :=
    ht (m - 2) (by omega) (by omega)
  have ha' := congrFun hprod (⟨m - 1, by omega⟩ : Fin (m + 1))
  rw [prod_nodeTuple_apply_pred m hm t, hpred, inv_one, mul_one] at ha'
  have hl' := congrFun hprod (Fin.last m)
  rw [prod_nodeTuple_apply_last m hm t] at hl'
  have hta : t (⟨m - 1, by omega⟩ : Fin (m + 1)) = 1 := by
    have h1 : t (⟨m - 1, by omega⟩ : Fin (m + 1)) * t (Fin.last m) = 1 := ha'
    have h2 : (t (⟨m - 1, by omega⟩ : Fin (m + 1)))⁻¹ * t (Fin.last m) = 1 := hl'
    have h3 : t (⟨m - 1, by omega⟩ : Fin (m + 1)) =
        (t (⟨m - 1, by omega⟩ : Fin (m + 1)))⁻¹ := by
      exact mul_right_cancel (h1.trans h2.symm)
    have hs : t (⟨m - 1, by omega⟩ : Fin (m + 1)) *
        t (⟨m - 1, by omega⟩ : Fin (m + 1)) = 1 := by
      have hcongr := congrArg
        (fun x : mu (f := f) (K := K) =>
          x * t (⟨m - 1, by omega⟩ : Fin (m + 1))) h3
      rwa [inv_mul_cancel] at hcongr
    exact eq_one_of_mul_self_eq_one_normOne hK hs
  have htl : t (Fin.last m) = 1 := by
    have h1 : t (⟨m - 1, by omega⟩ : Fin (m + 1)) * t (Fin.last m) = 1 := ha'
    rwa [hta, one_mul] at h1
  funext i
  rcases Fin.eq_castSucc_or_eq_last (n := m) i with ⟨j, rfl⟩ | rfl
  · by_cases hj : j.val ≤ m - 2
    · have hcast : (Fin.castSucc j : Fin (m + 1)) = ⟨j.val, by omega⟩ := Fin.ext rfl
      rw [hcast]
      exact ht j.val hj (by omega)
    · have hj' : j.val = m - 1 := by
        have := j.isLt
        omega
      have hjeq : j = (⟨m - 1, by omega⟩ : Fin m) := Fin.ext hj'
      rw [hjeq]
      exact hta
  · exact htl

private theorem paramMap_injective (m : ℕ) (hm : 3 ≤ m)
    (hK : Nat.card K = (2 ^ f) ^ 2) :
    Function.Injective (paramMap (K := K) (f := f) m hm) := by
  intro s t hst
  have h1 : paramMap (K := K) (f := f) m hm (s * t⁻¹) = 1 := by
    rw [map_mul, map_inv, hst, mul_inv_cancel]
  have h2 : s * t⁻¹ = 1 := paramMap_eq_one m hm hK (s * t⁻¹) h1
  exact mul_inv_eq_one.mp h2

variable (E : QuadExt F K (unitaryInvolution K 2 f))

private theorem nodeTor_apply_castSucc (m : ℕ) (hm : 3 ≤ m) (k : Fin m)
    (u : mu (f := f) (K := K)) :
    (stdFamilyV E m hm).nodeTor (Fin.castSucc k) u =
      diagHom F (unitaryInvolution K 2 f) (m + 1)
        (nodeTuple (K := K) (f := f) m hm (Fin.castSucc k) u) := by
  rw [PhanFamilyE.nodeTor, MonoidHom.comp_apply, stdFamilyV_ι_castSucc]
  unfold stdChainIota
  rw [MonoidHom.comp_apply]
  apply LinearEquiv.ext
  intro v
  funext j
  rw [suEndN_apply, CFSG.ClassicalGroups.Unitary.smul_def,
    coe_coe_blockEmb2_torusTwo, Matrix.mulVec_diagonal, diagHom_apply,
    nodeTuple_apply_castSucc]
  congr 1
  have hne1 : (Fin.castSucc k : Fin (m + 1)) ≠ k.succ := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_castSucc, Fin.val_succ] at this
    omega
  have hne2 : (k.succ : Fin (m + 1)) ≠ Fin.castSucc k := hne1.symm
  by_cases h1 : j = Fin.castSucc k
  · subst h1
    simp [hne1]
  · by_cases h2 : j = k.succ
    · subst h2
      simp [hne2]
    · have hv1 : j.val ≠ k.val := by
        intro h
        exact h1 (Fin.ext h)
      have hv2 : j.val ≠ k.val + 1 := by
        intro h
        exact h2 (Fin.ext (by simpa using h))
      simp [h1, h2, hv1, hv2]

private theorem stdTau_conj_diag_last (m : ℕ) (hm : 3 ≤ m)
    (u : mu (f := f) (K := K)) :
    stdTau (K := K) (f := f) E m *
        diagHom F (unitaryInvolution K 2 f) (m + 1)
          (Pi.mulSingle (⟨m - 1, by omega⟩ : Fin (m + 1)) u *
            Pi.mulSingle (Fin.last m) u⁻¹) *
        (stdTau (K := K) (f := f) E m)⁻¹ =
      diagHom F (unitaryInvolution K 2 f) (m + 1)
        (Pi.mulSingle (⟨m - 1, by omega⟩ : Fin (m + 1)) u *
          Pi.mulSingle (Fin.last m) u) := by
  have hsig : unitaryInvolution K 2 f (((u⁻¹ : mu (f := f) (K := K)) : Kˣ) : K) =
      (((u : mu (f := f) (K := K)) : Kˣ) : K) := by
    have h := (mem_normOne (unitaryInvolution K 2 f)).1
      ((normOne (unitaryInvolution K 2 f)).inv_mem u.2)
    have h2 := eq_inv_of_mul_eq_one_left h
    simpa [Subgroup.coe_inv, Units.val_inv_eq_inv_val] using h2
  have hinvol : ∀ x : K, (iterateFrobenius K 2 f)
      ((iterateFrobenius K 2 f) x) = x := fun x => E.isUnitary.invol x
  have hsig' : ((iterateFrobenius K 2 f)
      (((u : mu (f := f) (K := K)) : Kˣ) : K))⁻¹ =
      (((u : mu (f := f) (K := K)) : Kˣ) : K) := by
    have hu : (iterateFrobenius K 2 f) (((u : mu (f := f) (K := K)) : Kˣ) : K) =
        ((((u : mu (f := f) (K := K)) : Kˣ) : K))⁻¹ :=
      eq_inv_of_mul_eq_one_left ((mem_normOne (unitaryInvolution K 2 f)).1 u.2)
    rw [hu, inv_inv]
  apply LinearEquiv.ext
  intro v
  funext j
  rw [stdTau]
  rw [show (tauAt E (Fin.last m))⁻¹ = tauAt E (Fin.last m) from
    inv_eq_of_mul_eq_one_right (tauAt_mul_self E (Fin.last m))]
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  simp only [diagHom_apply, tauAt_apply]
  have hne : (⟨m - 1, by omega⟩ : Fin (m + 1)) ≠ Fin.last m := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_last] at this
    omega
  by_cases hja : j = (⟨m - 1, by omega⟩ : Fin (m + 1))
  · subst hja
    simp [hne]
  · by_cases hjl : j = Fin.last m
    · subst hjl
      simp [hja, hsig', hinvol]
    · simp [hja, hjl]

private theorem nodeTor_apply_last (m : ℕ) (hm : 3 ≤ m)
    (u : mu (f := f) (K := K)) :
    (stdFamilyV E m hm).nodeTor (Fin.last m) u =
      diagHom F (unitaryInvolution K 2 f) (m + 1)
        (nodeTuple (K := K) (f := f) m hm (Fin.last m) u) := by
  have hchain := nodeTor_apply_castSucc (E := E) m hm
    (⟨m - 1, by omega⟩ : Fin m) u
  have h1 : stdChainIota (F := F) (f := f) m (⟨m - 1, by omega⟩ : Fin m)
      (torusTwo (unitaryInvolution K 2 f) u) =
      (stdFamilyV E m hm).nodeTor
        (Fin.castSucc (⟨m - 1, by omega⟩ : Fin m)) u := by
    rw [PhanFamilyE.nodeTor, MonoidHom.comp_apply, stdFamilyV_ι_castSucc]
  rw [PhanFamilyE.nodeTor, MonoidHom.comp_apply, stdFamilyV_ι_last]
  unfold stdForkIota stdConj
  rw [MonoidHom.comp_apply]
  change stdTau (K := K) (f := f) E m *
      stdChainIota (F := F) (f := f) m (⟨m - 1, by omega⟩ : Fin m)
        (torusTwo (unitaryInvolution K 2 f) u) *
      (stdTau (K := K) (f := f) E m)⁻¹ =
    diagHom F (unitaryInvolution K 2 f) (m + 1)
      (nodeTuple (K := K) (f := f) m hm (Fin.last m) u)
  rw [h1, hchain, nodeTuple_castSucc, nodeTuple_last]
  have hsucc : (⟨m - 1, by omega⟩ : Fin m).succ = Fin.last m := Fin.ext (by simp; omega)
  rw [hsucc]
  exact stdTau_conj_diag_last (E := E) m hm u

private theorem nodeTuple_eq_comp (m : ℕ) (hm : 3 ≤ m) (i : Fin (m + 1)) :
    nodeTuple (K := K) (f := f) m hm i =
      (paramMap (K := K) (f := f) m hm).comp
        (MonoidHom.mulSingle (fun _ : Fin (m + 1) => mu (f := f) (K := K)) i) := by
  ext u
  rw [MonoidHom.comp_apply, MonoidHom.mulSingle_apply, paramMap_mulSingle]

private theorem nodeTor_eq_comp (m : ℕ) (hm : 3 ≤ m) (i : Fin (m + 1)) :
    (stdFamilyV E m hm).nodeTor i =
      (diagHom F (unitaryInvolution K 2 f) (m + 1)).comp
        (nodeTuple (K := K) (f := f) m hm i) := by
  refine MonoidHom.ext fun u => ?_
  rw [MonoidHom.comp_apply]
  rcases Fin.eq_castSucc_or_eq_last (n := m) i with ⟨k, rfl⟩ | rfl
  · exact nodeTor_apply_castSucc (E := E) m hm k u
  · exact nodeTor_apply_last (E := E) m hm u

private theorem nodeTor_apply (m : ℕ) (hm : 3 ≤ m) (i : Fin (m + 1))
    (u : mu (f := f) (K := K)) :
    (stdFamilyV E m hm).nodeTor i u =
      diagHom F (unitaryInvolution K 2 f) (m + 1)
        (nodeTuple (K := K) (f := f) m hm i u) := by
  rcases Fin.eq_castSucc_or_eq_last (n := m) i with ⟨k, rfl⟩ | rfl
  · exact nodeTor_apply_castSucc (E := E) m hm k u
  · exact nodeTor_apply_last (E := E) m hm u

theorem stdFamilyV_nodeTor_castSucc (m : ℕ) (hm : 3 ≤ m) (k : Fin m)
    (u : normOne (unitaryInvolution K 2 f)) :
    (stdFamilyV E m hm).nodeTor (Fin.castSucc k) u =
      diagHom F (unitaryInvolution K 2 f) (m + 1)
        (Pi.mulSingle (Fin.castSucc k) u * Pi.mulSingle k.succ u⁻¹) := by
  rw [nodeTor_apply_castSucc, nodeTuple_castSucc]
  congr 1

theorem stdFamilyV_nodeTor_last (m : ℕ) (hm : 3 ≤ m)
    (u : normOne (unitaryInvolution K 2 f)) :
    (stdFamilyV E m hm).nodeTor (Fin.last m) u =
      diagHom F (unitaryInvolution K 2 f) (m + 1)
        (Pi.mulSingle (⟨m - 1, by omega⟩ : Fin (m + 1)) u *
          Pi.mulSingle (Fin.last m) u) := by
  rw [nodeTor_apply_last, nodeTuple_last]
  congr 1

theorem nodeTor_mem_diagTorusV (m : ℕ) (hm : 3 ≤ m) (i : Fin (m + 1))
    (u : normOne (unitaryInvolution K 2 f)) :
    (stdFamilyV E m hm).nodeTor i u ∈ diagTorusV F (unitaryInvolution K 2 f) (m + 1) := by
  rw [nodeTor_apply]
  exact ⟨nodeTuple (K := K) (f := f) m hm i u, rfl⟩

private theorem iSupIndep_mulSingle (m : ℕ) :
    iSupIndep fun i : Fin (m + 1) =>
      (MonoidHom.mulSingle (fun _ : Fin (m + 1) => mu (f := f) (K := K)) i).range := by
  rw [iSupIndep_def]
  intro i
  rw [disjoint_iff]
  refine le_bot_iff.mp ?_
  intro x hx
  rcases hx with ⟨hxi, hxrest⟩
  let E : Subgroup (Fin (m + 1) → normOne (unitaryInvolution K 2 f)) :=
    (Pi.evalMonoidHom (fun _ : Fin (m + 1) => normOne (unitaryInvolution K 2 f)) i).ker
  have hle : (⨆ j, ⨆ (_ : j ≠ i),
      (MonoidHom.mulSingle
        (fun _ : Fin (m + 1) => normOne (unitaryInvolution K 2 f)) j).range) ≤ E := by
    refine iSup₂_le fun j hj => ?_
    rintro x ⟨u, rfl⟩
    rw [MonoidHom.mem_ker, Pi.evalMonoidHom_apply, MonoidHom.mulSingle_apply,
      Pi.mulSingle_apply, if_neg (Ne.symm hj)]
  have hxE : x ∈ E := hle hxrest
  rcases hxi with ⟨u, rfl⟩
  rw [MonoidHom.mem_ker, Pi.evalMonoidHom_apply, MonoidHom.mulSingle_apply,
    Pi.mulSingle_apply, if_pos rfl] at hxE
  rw [hxE]
  exact Subgroup.mem_bot.mpr (map_one _)

private theorem nodeTuple_injective (m : ℕ) (hm : 3 ≤ m) (i : Fin (m + 1)) :
    Function.Injective (nodeTuple (K := K) (f := f) m hm i) := by
  intro u v h
  rcases Fin.eq_castSucc_or_eq_last (n := m) i with ⟨k, rfl⟩ | rfl
  · have hne : (Fin.castSucc k : Fin (m + 1)) ≠ k.succ := by
      intro h'
      have := congrArg Fin.val h'
      simp only [Fin.val_castSucc, Fin.val_succ] at this
      omega
    have h1 := congrFun h (Fin.castSucc k)
    rw [nodeTuple_apply_castSucc, nodeTuple_apply_castSucc] at h1
    simpa [hne] using h1
  · have hne : (⟨m - 1, by omega⟩ : Fin (m + 1)) ≠ Fin.last m := by
      intro h'
      have := congrArg Fin.val h'
      simp only [Fin.val_last] at this
      omega
    have h1 := congrFun h (⟨m - 1, by omega⟩ : Fin (m + 1))
    rw [nodeTuple_apply_last, nodeTuple_apply_last] at h1
    simpa [hne] using h1

theorem stdFamilyV_nodeTor_injective (m : ℕ) (hm : 3 ≤ m) (i : Fin (m + 1)) :
    Function.Injective ((stdFamilyV E m hm).nodeTor i) := by
  rw [nodeTor_eq_comp]
  exact (diagHom_injective (F := F) (σ := unitaryInvolution K 2 f) (m + 1)).comp
    (nodeTuple_injective m hm i)

private theorem paramMap_surjective (m : ℕ) (hm : 3 ≤ m)
    (hK : Nat.card K = (2 ^ f) ^ 2) :
    Function.Surjective (paramMap (K := K) (f := f) m hm) :=
  Finite.surjective_of_injective (paramMap_injective m hm hK)

theorem torus_stdFamilyV (m : ℕ) (hm : 3 ≤ m)
    (hK : Nat.card K = (2 ^ f) ^ 2) :
    (stdFamilyV E m hm).torus =
      diagTorusV F (unitaryInvolution K 2 f) (m + 1) := by
  rw [PhanFamilyE.torus]
  apply le_antisymm
  · refine iSup_le fun i => ?_
    rintro x ⟨u, rfl⟩
    exact nodeTor_mem_diagTorusV E m hm i u
  · rintro x ⟨t, rfl⟩
    obtain ⟨s, rfl⟩ := paramMap_surjective m hm hK t
    let g : Fin (m + 1) → (Fin (m + 1) → normOne (unitaryInvolution K 2 f)) :=
      fun i => nodeTuple (K := K) (f := f) m hm i (s i)
    let comm : Set.Pairwise (↑(Finset.univ : Finset (Fin (m + 1))) : Set (Fin (m + 1)))
        (Function.onFun Commute g) := fun _ _ _ _ _ => Commute.all _ _
    have hP : paramMap (K := K) (f := f) m hm s =
        Finset.univ.noncommProd g comm := by
      rw [paramMap_apply, Finset.noncommProd_eq_prod]
    rw [hP, Finset.map_noncommProd (s := Finset.univ) (f := g) (comm := comm)]
    refine Subgroup.noncommProd_mem _ _ fun i _ => ?_
    refine Subgroup.mem_iSup_of_mem i ?_
    refine ⟨s i, ?_⟩
    rw [nodeTor_apply (E := E) m hm i (s i)]

theorem stdFamilyV_indep (m : ℕ) (hm : 3 ≤ m)
    (hK : Nat.card K = (2 ^ f) ^ 2) :
    iSupIndep fun i => ((stdFamilyV E m hm).nodeTor i).range := by
  have hcoord := iSupIndep_mulSingle (K := K) (f := f) m
  have hnode : iSupIndep fun i => (nodeTuple (K := K) (f := f) m hm i).range := by
    have hmap := CFSG.LocalCores.iSupIndep_map_of_injective
      (paramMap_injective m hm hK) hcoord
    simpa [nodeTuple_eq_comp, MonoidHom.range_comp] using hmap
  have hfin := CFSG.LocalCores.iSupIndep_map_of_injective
    (diagHom_injective (F := F) (σ := unitaryInvolution K 2 f) (m + 1)) hnode
  simpa [nodeTor_eq_comp, MonoidHom.range_comp] using hfin

private theorem prod_le_succ_fin (m : ℕ) (t : Fin (m + 1) → mu (f := f) (K := K))
    (j : Fin (m + 1)) (hj : 0 < j.val) :
    (∏ c ∈ Finset.univ.filter (fun c : Fin (m + 1) => c.val ≤ j.val), t c) =
      t j *
        (∏ c ∈ Finset.univ.filter (fun c : Fin (m + 1) => c.val ≤ j.val - 1), t c) := by
  classical
  have hi : j ∈ Finset.univ.filter (fun c : Fin (m + 1) => c.val ≤ j.val) := by
    simp
  have hset : Finset.univ.filter (fun c : Fin (m + 1) => c.val ≤ j.val) \ {j} =
      Finset.univ.filter (fun c : Fin (m + 1) => c.val ≤ j.val - 1) := by
    ext c
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · rintro ⟨hle, hne⟩
      have hlt : c.val < j.val := by
        rcases Nat.lt_or_ge c.val j.val with hlt | hge
        · exact hlt
        · exfalso
          exact hne (Fin.ext (by omega))
      omega
    · intro hle
      refine ⟨by omega, ?_⟩
      intro hc
      rw [hc] at hle
      omega
  rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem hi t, hset]

private theorem prod_le_eq (m : ℕ) (hm : 3 ≤ m)
    (s t : Fin (m + 1) → mu (f := f) (K := K))
    (hst : t = paramMap (K := K) (f := f) m hm s) :
    ∀ k : ℕ, k ≤ m - 2 → ∀ hk : k < m + 1,
      (∏ c ∈ Finset.univ.filter (fun c : Fin (m + 1) => c.val ≤ k), t c) =
        s ⟨k, hk⟩ := by
  intro k
  induction k with
  | zero =>
      intro _ hk
      have h0 : t ⟨0, by omega⟩ = s ⟨0, by omega⟩ := by
        have h := congrFun hst (⟨0, by omega⟩ : Fin (m + 1))
        rw [paramMap_apply, prod_nodeTuple_apply_zero m hm s] at h
        exact h
      have hset : Finset.univ.filter (fun c : Fin (m + 1) => c.val ≤ 0) =
          {⟨0, by omega⟩} := by
        ext c
        constructor
        · intro hc
          have hle : c.val ≤ 0 := (Finset.mem_filter.mp hc).2
          exact Finset.mem_singleton.mpr (Fin.ext (Nat.eq_zero_of_le_zero hle))
        · intro hc
          rw [Finset.mem_singleton] at hc
          rw [hc]
          simp
      rw [hset, Finset.prod_singleton]
      exact h0
  | succ k ih =>
      intro hk hk1
      have hk2 : k ≤ m - 2 := by omega
      have hklt : k < m + 1 := by omega
      have hkm : k < m := by omega
      have hcoord : t ⟨k + 1, hk1⟩ =
          s ⟨k + 1, hk1⟩ * (s ⟨k, by omega⟩)⁻¹ := by
        have h := congrFun hst (⟨k + 1, hk1⟩ : Fin (m + 1))
        rw [paramMap_apply, prod_nodeTuple_apply_succ m hm s k (by omega)] at h
        exact h
      have hstep := prod_le_succ_fin m t (⟨k + 1, hk1⟩ : Fin (m + 1)) (by simp)
      have hval : (⟨k + 1, hk1⟩ : Fin (m + 1)).val - 1 = k := by
        simp
      rw [hval] at hstep
      rw [hstep, ih hk2 hklt, hcoord, mul_assoc, inv_mul_cancel, mul_one]

theorem diagHom_mem_iSup_nodeTor_of_prod (m : ℕ) (hm : 3 ≤ m)
    (hK : Nat.card K = (2 ^ f) ^ 2)
    (C : Set (Fin (m + 1))) (t : Fin (m + 1) → normOne (unitaryInvolution K 2 f))
    (hpre : ∀ k : Fin (m + 1), k ∉ C → k.val + 2 ≤ m →
      ∏ c, (if c.val ≤ k.val then t c else 1) = 1)
    (htot : Fin.last m ∉ C → ∏ c, t c = 1)
    (htw : (⟨m - 1, by omega⟩ : Fin (m + 1)) ∉ C →
      ∏ c, Function.update t (Fin.last m) (t (Fin.last m))⁻¹ c = 1) :
    diagHom F (unitaryInvolution K 2 f) (m + 1) t ∈
      ⨆ i ∈ C, ((stdFamilyV E m hm).nodeTor i).range := by
  classical
  obtain ⟨s, hs⟩ := paramMap_surjective (K := K) (f := f) m hm hK t
  have hst : t = paramMap (K := K) (f := f) m hm s := hs.symm
  have hP2 : (∏ c ∈ Finset.univ.filter (fun c : Fin (m + 1) => c.val ≤ m - 2), t c) =
      s ⟨m - 2, by omega⟩ :=
    prod_le_eq m hm s t hst (m - 2) (by omega) (by omega)
  have hP1 : (∏ c ∈ Finset.univ.filter (fun c : Fin (m + 1) => c.val ≤ m - 1),
        t c) =
      t ⟨m - 1, by omega⟩ *
        (∏ c ∈ Finset.univ.filter (fun c : Fin (m + 1) => c.val ≤ m - 2), t c) := by
    have h := prod_le_succ_fin m t (⟨m - 1, by omega⟩ : Fin (m + 1))
      (by simpa using (show 0 < m - 1 by omega))
    have hval : (⟨m - 1, by omega⟩ : Fin (m + 1)).val - 1 = m - 2 := by
      simpa using (show m - 1 - 1 = m - 2 by omega)
    rw [hval] at h
    exact h
  have hPlast : (∏ c ∈ Finset.univ.filter (fun c : Fin (m + 1) => c.val ≤ m),
        t c) =
      t (Fin.last m) *
        (∏ c ∈ Finset.univ.filter (fun c : Fin (m + 1) => c.val ≤ m - 1), t c) := by
    have h := prod_le_succ_fin m t (Fin.last m)
      (by simpa using (show 0 < m by omega))
    have hval : (Fin.last m : Fin (m + 1)).val - 1 = m - 1 := by
      simp
    rw [hval] at h
    exact h
  have hpred : t ⟨m - 1, by omega⟩ =
      s ⟨m - 1, by omega⟩ * (s ⟨m - 2, by omega⟩)⁻¹ * s (Fin.last m) := by
    have h := congrFun hst (⟨m - 1, by omega⟩ : Fin (m + 1))
    rw [paramMap_apply, prod_nodeTuple_apply_pred m hm s] at h
    exact h
  have hlast : t (Fin.last m) =
      (s ⟨m - 1, by omega⟩)⁻¹ * s (Fin.last m) := by
    have h := congrFun hst (Fin.last m)
    rw [paramMap_apply, prod_nodeTuple_apply_last m hm s] at h
    exact h
  have hP1_ab : (∏ c ∈ Finset.univ.filter (fun c : Fin (m + 1) => c.val ≤ m - 1),
        t c) =
      s ⟨m - 1, by omega⟩ * s (Fin.last m) := by
    rw [hP1, hP2, hpred]
    simp [mul_comm, mul_left_comm]
  have htotal : (∏ c, t c) = s (Fin.last m) * s (Fin.last m) := by
    have huniv : (∏ c ∈ Finset.univ.filter (fun c : Fin (m + 1) => c.val ≤ m),
        t c) = ∏ c, t c := by
      refine Finset.prod_congr ?_ (fun _ _ => rfl)
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact iff_true_intro (Nat.le_of_lt_succ c.isLt)
    rw [← huniv, hPlast, hP1_ab, hlast]
    simp [mul_comm, mul_left_comm]
  have hsq_last : Fin.last m ∉ C → s (Fin.last m) * s (Fin.last m) = 1 := by
    intro hnot
    rw [← htotal]
    exact htot hnot
  have htw_eq : (⟨m - 1, by omega⟩ : Fin (m + 1)) ∉ C →
      (t (Fin.last m))⁻¹ *
        (∏ c ∈ Finset.univ.filter (fun c : Fin (m + 1) => c.val ≤ m - 1),
          t c) = 1 := by
    intro hnot
    have h := htw hnot
    have hset : Finset.univ \ {Fin.last m} =
        Finset.univ.filter (fun c : Fin (m + 1) => c.val ≤ m - 1) := by
      ext c
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_singleton,
        Finset.mem_filter]
      constructor
      · intro hne
        have hval : c.val ≠ m := by
          intro hv
          exact hne (Fin.ext (by simpa [Fin.val_last] using hv))
        have := c.isLt
        omega
      · intro hle hc
        rw [hc] at hle
        simp only [Fin.val_last] at hle
        omega
    rw [Finset.prod_update_of_mem (s := Finset.univ) (i := Fin.last m)
      (h := Finset.mem_univ _) (f := t) (b := (t (Fin.last m))⁻¹)] at h
    rwa [hset] at h
  have hP_eq_t : (⟨m - 1, by omega⟩ : Fin (m + 1)) ∉ C →
      (∏ c ∈ Finset.univ.filter (fun c : Fin (m + 1) => c.val ≤ m - 1),
        t c) = t (Fin.last m) := by
    intro hnot
    have h := htw_eq hnot
    calc
      (∏ c ∈ Finset.univ.filter (fun c : Fin (m + 1) => c.val ≤ m - 1), t c) =
          t (Fin.last m) *
            ((t (Fin.last m))⁻¹ *
              (∏ c ∈ Finset.univ.filter (fun c : Fin (m + 1) => c.val ≤ m - 1),
                t c)) := by group
      _ = t (Fin.last m) * 1 := by rw [h]
      _ = t (Fin.last m) := mul_one _
  have hsq_pred : (⟨m - 1, by omega⟩ : Fin (m + 1)) ∉ C →
      s ⟨m - 1, by omega⟩ * s ⟨m - 1, by omega⟩ = 1 := by
    intro hnot
    have hPt := hP_eq_t hnot
    have hb : s (Fin.last m) = s ⟨m - 1, by omega⟩ * t (Fin.last m) := by
      rw [hlast]
      group
    have ha : s ⟨m - 1, by omega⟩ *
        (s ⟨m - 1, by omega⟩ * t (Fin.last m)) = t (Fin.last m) := by
      calc
        s ⟨m - 1, by omega⟩ * (s ⟨m - 1, by omega⟩ * t (Fin.last m)) =
            s ⟨m - 1, by omega⟩ * s (Fin.last m) := by rw [hb]
        _ = (∏ c ∈ Finset.univ.filter (fun c : Fin (m + 1) => c.val ≤ m - 1),
              t c) := hP1_ab.symm
        _ = t (Fin.last m) := hPt
    have h : (s ⟨m - 1, by omega⟩ * s ⟨m - 1, by omega⟩) * t (Fin.last m) =
        t (Fin.last m) := by
      rw [mul_assoc]
      exact ha
    refine mul_right_cancel (b := t (Fin.last m)) ?_
    rw [one_mul]
    exact h
  have hs_one : ∀ i : Fin (m + 1), i ∉ C → s i = 1 := by
    intro i hi
    by_cases hle : i.val ≤ m - 2
    · have hP := prod_le_eq m hm s t hst i.val hle i.isLt
      have hpre_i : (∏ c ∈ Finset.univ.filter (fun c : Fin (m + 1) =>
          c.val ≤ i.val), t c) = 1 := by
        rw [Finset.prod_filter]
        exact hpre i hi (by omega)
      exact hP.symm.trans hpre_i
    · have hcases : i.val = m - 1 ∨ i.val = m := by
        have := i.isLt
        omega
      rcases hcases with hval | hval
      · have hi_eq : i = (⟨m - 1, by omega⟩ : Fin (m + 1)) := Fin.ext hval
        have hnot : (⟨m - 1, by omega⟩ : Fin (m + 1)) ∉ C := by
          rwa [← hi_eq]
        have hone := eq_one_of_mul_self_eq_one_normOne (K := K) (f := f) hK
          (hsq_pred hnot)
        rw [hi_eq]
        exact hone
      · have hi_eq : i = Fin.last m := Fin.ext (by simpa [Fin.val_last] using hval)
        have hnot : Fin.last m ∉ C := by rwa [← hi_eq]
        have hone := eq_one_of_mul_self_eq_one_normOne (K := K) (f := f) hK
          (hsq_last hnot)
        rw [hi_eq]
        exact hone
  let g : Fin (m + 1) → (Fin (m + 1) → mu (f := f) (K := K)) :=
    fun i => nodeTuple (K := K) (f := f) m hm i (s i)
  let comm : Set.Pairwise (↑(Finset.univ : Finset (Fin (m + 1))) : Set (Fin (m + 1)))
      (Function.onFun Commute g) := fun _ _ _ _ _ => Commute.all _ _
  have hP : paramMap (K := K) (f := f) m hm s =
      Finset.univ.noncommProd g comm := by
    rw [paramMap_apply, Finset.noncommProd_eq_prod]
  rw [← hs, hP, Finset.map_noncommProd (s := Finset.univ) (f := g) (comm := comm)]
  refine Subgroup.noncommProd_mem _ _ fun i _ => ?_
  dsimp only [g]
  rw [← nodeTor_apply (E := E) m hm i (s i)]
  by_cases hi : i ∈ C
  · exact Subgroup.mem_iSup_of_mem i
      (Subgroup.mem_iSup_of_mem hi ⟨s i, rfl⟩)
  · rw [hs_one i hi, map_one]
    exact Subgroup.one_mem _

end CFSG.ClassicalInvolution.PhanDn
