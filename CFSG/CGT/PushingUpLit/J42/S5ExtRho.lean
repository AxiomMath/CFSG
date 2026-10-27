module

public import CFSG.CGT.PushingUpLit.J42.S5ExtIface

public section

namespace CFSG.CGT.PushingUpLit.SolK

theorem s5rho_zero_zero : extraMulFin 0 0 = 0 := by decide +kernel

theorem s5rho_four_four : extraMulFin 4 4 = 0 := by decide +kernel

theorem s5rho_four_comm : ∀ i : Fin 32, extraMulFin 4 i = extraMulFin i 4 := by decide +kernel

theorem s5rho_center :
    ∀ j : Fin 32, (∀ i : Fin 32, extraMulFin j i = extraMulFin i j) → j = 0 ∨ j = 4 := by
  decide +kernel

section Pk

variable {K : Type*} [Group K]

noncomputable def s5rho_pk (D : ExtraData K) (k : K) (i : Fin 32) : Fin 32 :=
  (D.nf_conj k i).choose

theorem s5rho_pk_spec (D : ExtraData K) (k : K) (i : Fin 32) :
    D.nf (s5rho_pk D k i) = k * D.nf i * k⁻¹ :=
  (D.nf_conj k i).choose_spec.symm

theorem s5rho_nf_zero (D : ExtraData K) : D.nf 0 = 1 := by
  have h := D.nf_mul 0 0
  rw [s5rho_zero_zero] at h
  exact mul_left_cancel (h.trans (mul_one _).symm)

theorem s5rho_pk_mul (D : ExtraData K) (k : K) (i j : Fin 32) :
    s5rho_pk D k (extraMulFin i j) = extraMulFin (s5rho_pk D k i) (s5rho_pk D k j) := by
  apply D.nf_inj
  rw [← D.nf_mul, s5rho_pk_spec, s5rho_pk_spec, s5rho_pk_spec, ← D.nf_mul]
  simp only [mul_assoc, inv_mul_cancel_left]

theorem s5rho_pk_injective (D : ExtraData K) (k : K) : Function.Injective (s5rho_pk D k) := by
  intro i j h
  have h' := congrArg D.nf h
  rw [s5rho_pk_spec, s5rho_pk_spec] at h'
  exact D.nf_inj (mul_left_cancel (mul_right_cancel h'))

theorem s5rho_pk_surjective (D : ExtraData K) (k : K) : Function.Surjective (s5rho_pk D k) :=
  Finite.surjective_of_injective (s5rho_pk_injective D k)

theorem s5rho_pk_comp (D : ExtraData K) (k k' : K) (i : Fin 32) :
    s5rho_pk D (k * k') i = s5rho_pk D k (s5rho_pk D k' i) := by
  apply D.nf_inj
  rw [s5rho_pk_spec, s5rho_pk_spec, s5rho_pk_spec]
  simp only [mul_inv_rev, mul_assoc]

theorem s5rho_pk_one (D : ExtraData K) (i : Fin 32) : s5rho_pk D 1 i = i := by
  apply D.nf_inj
  rw [s5rho_pk_spec, one_mul, inv_one, mul_one]

theorem s5rho_pk_zero (D : ExtraData K) (k : K) : s5rho_pk D k 0 = 0 := by
  apply D.nf_inj
  rw [s5rho_pk_spec, s5rho_nf_zero, mul_one, mul_inv_cancel]

theorem s5rho_pk_four (D : ExtraData K) (k : K) : s5rho_pk D k 4 = 4 := by
  have hc : ∀ i, extraMulFin (s5rho_pk D k 4) i = extraMulFin i (s5rho_pk D k 4) := by
    intro i
    obtain ⟨x, rfl⟩ := s5rho_pk_surjective D k i
    rw [← s5rho_pk_mul, ← s5rho_pk_mul, s5rho_four_comm]
  rcases s5rho_center _ hc with h | h
  · exact absurd (s5rho_pk_injective D k (h.trans (s5rho_pk_zero D k).symm)) (by decide)
  · exact h

theorem s5rho_z_conj (D : ExtraData K) (k : K) : k * D.nf 4 = D.nf 4 * k := by
  have h := s5rho_pk_spec D k 4
  rw [s5rho_pk_four] at h
  exact (eq_mul_inv_iff_mul_eq.mp h).symm

theorem s5rho_z_sq (D : ExtraData K) : D.nf 4 * D.nf 4 = 1 := by
  rw [D.nf_mul, s5rho_four_four, s5rho_nf_zero]

theorem s5rho_mul_right_cancel (D : ExtraData K) {a b i : Fin 32}
    (h : extraMulFin a i = extraMulFin b i) : a = b := by
  have h' := congrArg D.nf h
  rw [← D.nf_mul, ← D.nf_mul] at h'
  exact D.nf_inj (mul_right_cancel h')

theorem s5rho_exists (I : S5Iface) (D : ExtraData K) (k : K) :
    ∃ e, e < I.N ∧ I.tab e = s5rho_pk D k :=
  I.complete _ (s5rho_pk_mul D k) (s5rho_pk_injective D k)

noncomputable def s5rho_idx (I : S5Iface) (D : ExtraData K) (k : K) : ℕ :=
  (s5rho_exists I D k).choose

theorem s5rho_idx_lt (I : S5Iface) (D : ExtraData K) (k : K) : s5rho_idx I D k < I.N :=
  (s5rho_exists I D k).choose_spec.1

theorem s5rho_idx_tab (I : S5Iface) (D : ExtraData K) (k : K) :
    I.tab (s5rho_idx I D k) = s5rho_pk D k :=
  (s5rho_exists I D k).choose_spec.2

theorem s5rho_idx_mul (I : S5Iface) (D : ExtraData K) (k k' : K) :
    s5rho_idx I D (k * k') = I.cm (s5rho_idx I D k) (s5rho_idx I D k') := by
  have hk := s5rho_idx_lt I D k
  have hk' := s5rho_idx_lt I D k'
  refine I.tab_inj _ _ (s5rho_idx_lt I D _) (I.cm_lt _ _ hk hk') (funext fun x => ?_)
  rw [I.cm_tab _ _ hk hk', s5rho_idx_tab, s5rho_idx_tab, s5rho_idx_tab, s5rho_pk_comp]

theorem s5rho_idx_one (I : S5Iface) (D : ExtraData K) : s5rho_idx I D 1 = I.ide :=
  I.tab_inj _ _ (s5rho_idx_lt I D 1) I.ide_lt (funext fun x => by
    rw [s5rho_idx_tab, s5rho_pk_one, I.ide_tab])

theorem s5rho_idx_inv (I : S5Iface) (D : ExtraData K) (k : K) :
    I.inv (s5rho_idx I D k) = s5rho_idx I D k⁻¹ := by
  have hk := s5rho_idx_lt I D k
  refine I.tab_inj _ _ (I.inv_lt _ hk) (s5rho_idx_lt I D _) (funext fun x => ?_)
  apply s5rho_pk_injective D k
  have h1 : I.tab (I.cm (s5rho_idx I D k) (I.inv (s5rho_idx I D k))) x = x := by
    rw [I.cm_inv _ hk, I.ide_tab]
  rw [I.cm_tab _ _ hk (I.inv_lt _ hk), s5rho_idx_tab] at h1
  rw [h1, s5rho_idx_tab, ← s5rho_pk_comp, mul_inv_cancel, s5rho_pk_one]

theorem s5rho_idx_ker (I : S5Iface) (D : ExtraData K) (k k' : K)
    (h : s5rho_idx I D k = s5rho_idx I D k') : k' = k ∨ k' = k * D.nf 4 := by
  have hp : ∀ i, s5rho_pk D k i = s5rho_pk D k' i := fun i => by
    rw [← s5rho_idx_tab I D k, ← s5rho_idx_tab I D k', h]
  have hc : ∀ i, k⁻¹ * k' * D.nf i = D.nf i * (k⁻¹ * k') := by
    intro i
    have h1 : s5rho_pk D (k⁻¹ * k') i = i := by
      rw [s5rho_pk_comp, ← hp, ← s5rho_pk_comp, inv_mul_cancel, s5rho_pk_one]
    have h2 := s5rho_pk_spec D (k⁻¹ * k') i
    rw [h1] at h2
    exact (eq_mul_inv_iff_mul_eq.mp h2).symm
  obtain ⟨j, hj⟩ := D.nf_cent _ hc
  have hjc : ∀ i, extraMulFin j i = extraMulFin i j := fun i =>
    D.nf_inj (by rw [← D.nf_mul, ← D.nf_mul, ← hj, hc i])
  rcases s5rho_center j hjc with rfl | rfl
  · left
    rw [s5rho_nf_zero] at hj
    exact (inv_mul_eq_one.mp hj).symm
  · right
    exact inv_mul_eq_iff_eq_mul.mp hj

theorem s5rho_idx_nf (I : S5Iface) (D : ExtraData K) (i : Fin 32) :
    s5rho_idx I D (D.nf i) = I.ci i := by
  refine I.tab_inj _ _ (s5rho_idx_lt I D _) (I.ci_lt i) (funext fun x => ?_)
  rw [s5rho_idx_tab]
  apply s5rho_mul_right_cancel D (i := i)
  rw [I.ci_tab]
  apply D.nf_inj
  rw [← D.nf_mul, ← D.nf_mul, s5rho_pk_spec, inv_mul_cancel_right]

theorem s5rho_idx_z (I : S5Iface) (D : ExtraData K) : s5rho_idx I D (D.nf 4) = I.ide := by
  refine I.tab_inj _ _ (s5rho_idx_lt I D _) I.ide_lt (funext fun x => ?_)
  rw [s5rho_idx_tab, I.ide_tab]
  apply D.nf_inj
  rw [s5rho_pk_spec, ← s5rho_z_conj D (D.nf x), mul_inv_cancel_right]

end Pk

noncomputable def s5Rho (I : S5Iface) {K : Type*} [Group K] (D : ExtraData K) : S5Rho D I where
  rho := s5rho_idx I D
  rho_lt := s5rho_idx_lt I D
  rho_conj k i := by rw [s5rho_idx_tab]; exact s5rho_pk_spec D k i
  rho_mul := s5rho_idx_mul I D
  rho_one := s5rho_idx_one I D
  rho_inv := s5rho_idx_inv I D
  rho_ker := s5rho_idx_ker I D
  rho_nf := s5rho_idx_nf I D
  rho_z := s5rho_idx_z I D
  z_central := s5rho_z_conj D
  z_sq := s5rho_z_sq D

end CFSG.CGT.PushingUpLit.SolK
