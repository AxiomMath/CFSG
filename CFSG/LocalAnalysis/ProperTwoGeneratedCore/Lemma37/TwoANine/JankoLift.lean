module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.Elementary

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

open Subgroup

variable {J : Type*} [Group J]

@[expose] noncomputable def someLift (e : J ⧸ center J ≃* alternatingGroup (Fin 9))
    (g : alternatingGroup (Fin 9)) : J :=
  (proj_surjective e g).choose

@[simp] theorem proj_someLift (e : J ⧸ center J ≃* alternatingGroup (Fin 9))
    (g : alternatingGroup (Fin 9)) : proj e (someLift e g) = g :=
  (proj_surjective e g).choose_spec

@[expose] noncomputable def liftOdd (e : J ⧸ center J ≃* alternatingGroup (Fin 9))
    (g : alternatingGroup (Fin 9)) : J :=
  Classical.epsilon fun x => proj e x = g ∧ Odd (orderOf x)

private theorem orderOf_conj' {X : Type*} [Group X] (g a : X) :
    orderOf (g * a * g⁻¹) = orderOf a := by
  simpa only [MulAut.conj_apply] using (MulAut.conj g).orderOf_eq a

namespace IsTwoANine

variable (hJ : IsTwoANine J) (e : J ⧸ center J ≃* alternatingGroup (Fin 9))
include hJ

theorem zbar_pow_of_odd {n : ℕ} (hn : Odd n) : zbar J ^ n = zbar J := by
  obtain ⟨k, rfl⟩ := hn
  rw [pow_succ, pow_mul, hJ.zbar_sq, one_pow, one_mul]

theorem eq_one_of_mem_center_of_odd {c : J} (hc : c ∈ center J) (hco : Odd (orderOf c)) :
    c = 1 := by
  rcases hJ.mem_center_iff.mp hc with h | h
  · exact h
  · rw [h, hJ.orderOf_zbar] at hco
    exact absurd hco (Nat.not_odd_iff_even.mpr even_two)

theorem eq_of_proj_eq_of_odd {x y : J} (hx : Odd (orderOf x)) (hy : Odd (orderOf y))
    (h : proj e x = proj e y) : x = y := by
  rcases (hJ.proj_eq_proj_iff' e).mp h with h' | h'
  · exact h'.symm
  · exfalso
    obtain ⟨n, hn, hxn, hyn⟩ : ∃ n, Odd n ∧ x ^ n = 1 ∧ y ^ n = 1 :=
      ⟨orderOf x * orderOf y, hx.mul hy, by rw [pow_mul, pow_orderOf_eq_one, one_pow],
        by rw [mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]⟩
    rw [h', (hJ.commute_zbar x).mul_pow, hxn, one_mul, hJ.zbar_pow_of_odd hn] at hyn
    exact hJ.zbar_ne_one hyn

theorem exists_lift_odd {g : alternatingGroup (Fin 9)} (hg : Odd (orderOf g)) :
    ∃ x : J, proj e x = g ∧ Odd (orderOf x) := by
  obtain ⟨y, rfl⟩ := proj_surjective e g
  have hc : y ^ orderOf (proj e y) ∈ center J :=
    (proj_eq_one_iff e).mp (by rw [map_pow, pow_orderOf_eq_one])
  rcases hJ.mem_center_iff.mp hc with h | h
  · exact ⟨y, rfl, hg.of_dvd_nat (orderOf_dvd_of_pow_eq_one h)⟩
  · refine ⟨y * zbar J, proj_mul_of_mem_center e hJ.zbar_mem_center,
      hg.of_dvd_nat (orderOf_dvd_of_pow_eq_one ?_)⟩
    rw [(hJ.commute_zbar y).mul_pow, h, hJ.zbar_pow_of_odd hg, hJ.zbar_mul_zbar]

variable {g : alternatingGroup (Fin 9)} (hg : Odd (orderOf g))
include hg

theorem proj_liftOdd : proj e (liftOdd e g) = g :=
  (Classical.epsilon_spec (hJ.exists_lift_odd e hg)).1

theorem odd_orderOf_liftOdd : Odd (orderOf (liftOdd e g)) :=
  (Classical.epsilon_spec (hJ.exists_lift_odd e hg)).2

theorem orderOf_liftOdd : orderOf (liftOdd e g) = orderOf g := by
  have hx := hJ.proj_liftOdd e hg
  have h2 := orderOf_map_dvd (proj e) (liftOdd e g)
  rw [hx] at h2
  refine Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one ?_) h2
  exact hJ.eq_one_of_mem_center_of_odd ((proj_eq_one_iff e).mp
    (by rw [map_pow, hx, pow_orderOf_eq_one]))
    ((hJ.odd_orderOf_liftOdd e hg).of_dvd_nat (orderOf_pow_dvd _))

omit hg in
theorem eq_liftOdd {x : J} (hx : Odd (orderOf x)) : x = liftOdd e (proj e x) :=
  hJ.eq_of_proj_eq_of_odd e hx (hJ.odd_orderOf_liftOdd e (hx.of_dvd_nat (orderOf_map_dvd _ x)))
    (hJ.proj_liftOdd e (hx.of_dvd_nat (orderOf_map_dvd _ x))).symm

theorem eq_liftOdd_of_proj_eq {x : J} (hx : Odd (orderOf x)) (hxg : proj e x = g) :
    x = liftOdd e g :=
  hJ.eq_of_proj_eq_of_odd e hx (hJ.odd_orderOf_liftOdd e hg)
    (hxg.trans (hJ.proj_liftOdd e hg).symm)

theorem conj_liftOdd (u : J) :
    u * liftOdd e g * u⁻¹ = liftOdd e (proj e u * g * (proj e u)⁻¹) :=
  hJ.eq_liftOdd_of_proj_eq e (by rw [orderOf_conj']; exact hg)
    (by rw [orderOf_conj']; exact hJ.odd_orderOf_liftOdd e hg)
    (by rw [map_mul, map_mul, map_inv, hJ.proj_liftOdd e hg])

theorem liftOdd_inv : liftOdd e g⁻¹ = (liftOdd e g)⁻¹ :=
  (hJ.eq_liftOdd_of_proj_eq e (by rw [orderOf_inv]; exact hg)
    (by rw [orderOf_inv]; exact hJ.odd_orderOf_liftOdd e hg)
    (by rw [map_inv, hJ.proj_liftOdd e hg])).symm

theorem conj_liftOdd_eq_inv {u : J} (hu : proj e u * g * (proj e u)⁻¹ = g⁻¹) :
    u * liftOdd e g * u⁻¹ = (liftOdd e g)⁻¹ := by
  rw [hJ.conj_liftOdd e hg, hu, hJ.liftOdd_inv e hg]

omit hg

theorem commute_of_odd_orderOf {u x : J} (hx : Odd (orderOf x))
    (h : Commute (proj e u) (proj e x)) : Commute u x := by
  have h1 : u * x * u⁻¹ = x := hJ.eq_of_proj_eq_of_odd e (by rw [orderOf_conj']; exact hx) hx
    (by rw [map_mul, map_mul, map_inv, h.eq, mul_inv_cancel_right])
  calc u * x = u * x * u⁻¹ * u := by rw [inv_mul_cancel_right]
    _ = x * u := by rw [h1]

theorem centralizer_eq_comap_of_odd {x : J} (hx : Odd (orderOf x)) :
    centralizer ({x} : Set J) =
      (centralizer ({proj e x} : Set (alternatingGroup (Fin 9)))).comap (proj e) := by
  ext u
  rw [mem_comap, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  exact ⟨fun h => by rw [← map_mul, h, map_mul], fun h => hJ.commute_of_odd_orderOf e hx h⟩

theorem card_centralizer_of_odd {x : J} (hx : Odd (orderOf x)) :
    Nat.card (centralizer ({x} : Set J)) =
      2 * Nat.card (centralizer ({proj e x} : Set (alternatingGroup (Fin 9)))) := by
  rw [hJ.centralizer_eq_comap_of_odd e hx, hJ.card_comap_proj e]

theorem exists_conj_eq_liftOdd {x : J} {g : alternatingGroup (Fin 9)} (hx : Odd (orderOf x))
    (hg : Odd (orderOf g)) (hxg : IsConj (proj e x) g) : ∃ h : J, h * x * h⁻¹ = liftOdd e g := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hxg
  refine ⟨someLift e c, hJ.eq_liftOdd_of_proj_eq e hg (by rw [orderOf_conj']; exact hx) ?_⟩
  rw [map_mul, map_mul, map_inv, proj_someLift, hc]

end IsTwoANine

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine
