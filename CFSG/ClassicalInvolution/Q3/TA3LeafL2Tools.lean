module

public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2KleinFourSelfCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourOfCommutingInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearTwoMatrixCentralizer

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open Matrix QuaternionGroup

theorem quaternionGroup_exists_ker_sq_ne_one {n : ℕ} [NeZero n] (hn : Even n) {C : Type*}
    [Group C] [Finite C] [IsCyclic C] (f : QuaternionGroup n →* C) :
    ∃ w : QuaternionGroup n, f w = 1 ∧ w ^ 2 ≠ 1 ∧ w ^ 4 = 1 := by
  obtain ⟨m, hm⟩ := hn
  have hn2 : n = 2 * m := by omega
  have hcomm : ∀ u v : C, u * v = v * u := fun u v =>
    (IsCyclic.isMulCommutative (α := C)).is_comm.comm u v
  have h2 : f (a 2) = 1 := by
    have h1 : f (xa (-1)) = f (xa 1) := by
      have := hcomm (f (a 1)) (f (xa 0))
      rwa [← map_mul, ← map_mul, a_mul_xa, xa_mul_a, zero_sub, zero_add] at this
    have h3 : f (xa (-1)) * f (a 2) = f (xa (-1)) := by
      rw [← map_mul, xa_mul_a, h1]
      congr 2
      ring
    exact mul_eq_left.mp h3
  have ha1sq : f (a 1) ^ 2 = 1 := by
    rw [← map_pow, a_one_pow]
    exact_mod_cast h2
  have han : f (a 1 ^ n) = 1 := by
    rw [map_pow]
    calc f (a 1) ^ n = f (a 1) ^ (2 * m) := congrArg (fun k => f (a 1) ^ k) hn2
      _ = 1 := by rw [pow_mul, ha1sq, one_pow]
  have hxa0sq : f (xa 0) ^ 2 = 1 := by
    rw [← map_pow, xa_sq, ← a_one_pow, han]
  have hne : (a 1 : QuaternionGroup n) ^ n ≠ 1 :=
    pow_ne_one_of_lt_orderOf (NeZero.ne n) (by rw [orderOf_a_one]; have := NeZero.ne n; omega)
  by_cases hfa : f (a 1) = 1
  · refine ⟨a 1 ^ m, by rw [map_pow, hfa, one_pow], ?_, ?_⟩
    · rw [← pow_mul, show m * 2 = n by omega]
      exact hne
    · rw [← pow_mul, show m * 4 = orderOf (a 1 : QuaternionGroup n) by rw [orderOf_a_one]; omega]
      exact pow_orderOf_eq_one _
  by_cases hfx : f (xa 0) = 1
  · exact ⟨xa 0, hfx, by rw [xa_sq, ← a_one_pow]; exact hne, xa_pow_four 0⟩
  · refine ⟨xa 1, ?_, by rw [xa_sq, ← a_one_pow]; exact hne, xa_pow_four 1⟩
    have heq : f (xa 0) = f (a 1) := by
      classical
      have hox : orderOf (f (xa 0)) = 2 := orderOf_eq_prime hxa0sq hfx
      have hz : Subgroup.zpowers (f (xa 0)) = Subgroup.zpowers (f (a 1)) := by
        rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers, hox,
          orderOf_eq_prime ha1sq hfa]
      have hyx : f (a 1) ∈ Subgroup.zpowers (f (xa 0)) := hz ▸ Subgroup.mem_zpowers _
      rw [mem_zpowers_iff_mem_range_orderOf, hox] at hyx
      simp only [Finset.mem_image, Finset.mem_range] at hyx
      obtain ⟨k, hk, hkx⟩ := hyx
      interval_cases k
      · rw [pow_zero] at hkx
        exact absurd hkx.symm hfa
      · rw [pow_one] at hkx
        exact hkx
    have : xa (1 : ZMod (2 * n)) = xa 0 * a 1 := by rw [xa_mul_a, zero_add]
    rw [this, map_mul, ← heq, ← pow_two, hxa0sq]

theorem exists_mem_ker_sq_ne_one {G : Type*} [Group G] {P : Subgroup G} {n : ℕ} [NeZero n]
    (hn : Even n) (e : P ≃* QuaternionGroup n) {C : Type*} [Group C] [Finite C] [IsCyclic C]
    (ρ : G →* C) : ∃ w ∈ P, ρ w = 1 ∧ w ^ 2 ≠ 1 ∧ w ^ 4 = 1 := by
  obtain ⟨w, hf, h2, h4⟩ :=
    quaternionGroup_exists_ker_sq_ne_one hn (ρ.comp (P.subtype.comp e.symm.toMonoidHom))
  refine ⟨(e.symm w : G), (e.symm w).2, hf, fun h => h2 ?_, ?_⟩
  · apply e.symm.injective
    apply Subtype.ext
    rw [map_pow, Subgroup.coe_pow, h, map_one, Subgroup.coe_one]
  · rw [← Subgroup.coe_pow, ← map_pow, h4, map_one, Subgroup.coe_one]

theorem gl_commute_of_mk_commute_of_odd {K : Type*} [Field K] {A X : GL (Fin 2) K}
    (hc : ProjGenLinGroup.mk X * ProjGenLinGroup.mk A =
      ProjGenLinGroup.mk A * ProjGenLinGroup.mk X)
    (hx : Odd (orderOf (ProjGenLinGroup.mk X))) : X * A = A * X := by
  rw [← map_mul, ← map_mul, ProjGenLinGroup.mk_eq_mk_iff] at hc
  obtain ⟨u, hu⟩ := hc
  set s : GL (Fin 2) K := GeneralLinearGroup.scalar (Fin 2) u with hs
  have hcen : ∀ g : GL (Fin 2) K, g * s = s * g := by
    intro g
    have hv : s ∈ Subgroup.center (GL (Fin 2) K) := by
      rw [GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨u, rfl⟩
    exact Subgroup.mem_center_iff.mp hv g
  have hu2 : u ^ 2 = 1 := by
    have h := congrArg GeneralLinearGroup.det hu
    rw [map_mul, map_mul, map_mul, hs, GeneralLinearGroup.det_scalar, Fintype.card_fin,
      mul_comm (GeneralLinearGroup.det A) (GeneralLinearGroup.det X)] at h
    exact mul_eq_left.mp h
  have key : ∀ k : ℕ, X ^ k * A * s ^ k = A * X ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc X ^ (k + 1) * A * s ^ (k + 1) = X * (X ^ k * A * s ^ k) * s := by
            rw [pow_succ', pow_succ]; group
        _ = X * A * (X ^ k * s) := by rw [ih]; group
        _ = (X * A * s) * X ^ k := by rw [hcen]; group
        _ = A * X ^ (k + 1) := by rw [hu, pow_succ']; group
  set m := orderOf (ProjGenLinGroup.mk X) with hm
  have hXm : X ^ m ∈ Subgroup.center (GL (Fin 2) K) := by
    rw [← ProjGenLinGroup.mk_eq_one, map_pow, hm]
    exact pow_orderOf_eq_one _
  have hsm : s ^ m = 1 := by
    have h1 := key m
    rw [← Subgroup.mem_center_iff.mp hXm A] at h1
    exact mul_eq_left.mp h1
  have hum : u ^ m = 1 := by
    rw [hs, ← map_pow] at hsm
    have h1 := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) hsm
    simp [Matrix.diagonal_pow] at h1
    exact Units.ext (by simpa using h1)
  have hu1 : u = 1 := by
    obtain ⟨j, hj⟩ := hx
    rw [hj, pow_succ, pow_mul, hu2, one_pow, one_mul] at hum
    exact hum
  rw [hs, hu1, map_one, mul_one] at hu
  exact hu

theorem pgl2_commute_of_odd_of_commute {K : Type*} [Field K]
    {a x y : ProjGenLinGroup (Fin 2) K} (ha : a ≠ 1) (hxa : x * a = a * x)
    (hya : y * a = a * y) (hx : Odd (orderOf x)) (hy : Odd (orderOf y)) : x * y = y * x := by
  obtain ⟨A, rfl⟩ := ProjGenLinGroup.mk_surjective a
  obtain ⟨X, rfl⟩ := ProjGenLinGroup.mk_surjective x
  obtain ⟨Y, rfl⟩ := ProjGenLinGroup.mk_surjective y
  have hXA := gl_commute_of_mk_commute_of_odd hxa hx
  have hYA := gl_commute_of_mk_commute_of_odd hya hy
  have hA : ¬ ∃ c : K, (A : Matrix (Fin 2) (Fin 2) K) = Matrix.scalar (Fin 2) c := by
    rintro ⟨c, hc⟩
    apply ha
    have hc0 : c ≠ 0 := by
      rintro rfl
      apply (GeneralLinearGroup.det A).ne_zero
      change (A : Matrix (Fin 2) (Fin 2) K).det = 0
      rw [hc]
      simp
    rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨Units.mk0 c hc0, Units.ext (by rw [GeneralLinearGroup.coe_scalar, hc]; rfl)⟩
  have hm := ComponentClassification.CatalogueBLinearTwo.nonscalar_matrix_centralizer_commutative
    (A : Matrix (Fin 2) (Fin 2) K) X Y hA
    (by rw [← Units.val_mul, ← Units.val_mul, hXA])
    (by rw [← Units.val_mul, ← Units.val_mul, hYA])
  rw [← map_mul, ← map_mul]
  congr 1
  exact Units.ext (by rw [Units.val_mul, Units.val_mul, hm])

theorem pgl2_sq_eq_of_commute_of_pow_four {K : Type} [Field K] [Finite K]
    (hK : GorensteinWalter.IsOddPrimePower (Nat.card K)) {a b : ProjGenLinGroup (Fin 2) K}
    (ha : a * a = 1) (ha1 : a ≠ 1) (hab : a * b = b * a) (hb4 : b ^ 4 = 1) (hb2 : b ^ 2 ≠ 1) :
    b ^ 2 = a := by
  by_contra hne
  have hcc : b ^ 2 * b ^ 2 = 1 := by rw [← pow_add]; exact hb4
  have hac : Commute a (b ^ 2) := Commute.pow_right hab 2
  have hV := GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions a (b ^ 2) ha hcc ha1
    hb2 (Ne.symm hne) hac
  have hcent := GorensteinWalter.pgl2_kleinFour_centralizer_eq_self K hK _ hV
  have hbV : b ∈ GorensteinWalter.kleinFourOfCommutingInvolutions a (b ^ 2) ha hcc hac := by
    rw [← hcent, Subgroup.mem_centralizer_iff]
    intro v hv
    have hv' : v ∈ ({a * b ^ 2, a, b ^ 2, 1} : Set (ProjGenLinGroup (Fin 2) K)) := hv
    have hbb : b ^ 2 * b = b * b ^ 2 := (Commute.self_pow b 2).eq.symm
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv'
    rcases hv' with rfl | rfl | rfl | rfl
    · rw [mul_assoc, hbb, ← mul_assoc, hab, mul_assoc]
    · exact hab
    · exact hbb
    · rw [one_mul, mul_one]
  have hsq := @IsKleinFour.mul_self _ _ hV ⟨b, hbV⟩
  apply hb2
  rw [pow_two]
  exact congrArg Subtype.val hsq

end CFSG.ClassicalInvolution.Q3.TA3
