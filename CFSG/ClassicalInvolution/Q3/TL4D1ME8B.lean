module

public import CFSG.ClassicalInvolution.Q3.TL4D1ME8
import CFSG.ClassicalInvolution.Q3.TL4VecAddSelfEng

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open Matrix

variable {G : Type} [Group G] {E : Subgroup G} {e : Fin 3 → G}

theorem eq_of_mul_eq_one_of_mem (hsq : ∀ x ∈ E, x * x = 1) {x y : G} (hy : y ∈ E)
    (h : x * y = 1) : x = y := by
  have := eq_inv_of_mul_eq_one_left h
  rwa [inv_eq_of_mul_eq_one_right (hsq y hy)] at this

theorem eq_zero_of_e8Coord_eq_one (he : E8Basis E e) {v : Fin 3 → ZMod 2}
    (hv : e8Coord e v = 1) : v = 0 := by
  obtain ⟨h1a, h1b⟩ := he.ne1
  obtain ⟨h2a, h2b, h2c, h2d⟩ := he.ne2
  have m := he.mem
  unfold e8Coord at hv
  rcases zmod_two_cases (v 0) with h0 | h0 <;> rcases zmod_two_cases (v 1) with h1 | h1 <;>
    rcases zmod_two_cases (v 2) with h2 | h2 <;>
    rw [h0, h1, h2] at hv <;>
    simp only [ZMod.val_zero, ZMod.val_one, pow_zero, pow_one, one_mul, mul_one] at hv
  · funext i
    fin_cases i
    exacts [h0, h1, h2]
  · exact absurd hv h2a
  · exact absurd hv h1a
  · exact absurd (eq_of_mul_eq_one_of_mem he.sq (m 2) hv).symm h2c
  · exact absurd hv he.ne0
  · exact absurd (eq_of_mul_eq_one_of_mem he.sq (m 2) hv).symm h2b
  · exact absurd (eq_of_mul_eq_one_of_mem he.sq (m 1) hv).symm h1b
  · exact absurd (eq_of_mul_eq_one_of_mem he.sq (m 2) hv).symm h2d

theorem vec_add_self (v : Fin 3 → ZMod 2) : v + v = 0 :=
  CFSG.ClassicalInvolution.Q3.TL4.vec_add_self_gen v

theorem e8Coord_injective (he : E8Basis E e) : Function.Injective (e8Coord e) := by
  intro u v huv
  have h : e8Coord e (u + v) = 1 := by
    rw [e8Coord_add he, huv]
    exact he.sq _ (e8Coord_mem he v)
  have h0 := eq_zero_of_e8Coord_eq_one he h
  calc u = u + v + v := by rw [add_assoc, vec_add_self, add_zero]
    _ = v := by rw [h0, zero_add]

theorem exists_e8Coord_eq [Finite G] (he : E8Basis E e) {x : G} (hx : x ∈ E) :
    ∃ v, e8Coord e v = x := by
  let f : (Fin 3 → ZMod 2) → ↥E := fun v => ⟨e8Coord e v, e8Coord_mem he v⟩
  have hf : Function.Injective f := fun u v h => e8Coord_injective he (congrArg Subtype.val h)
  have hcard : Nat.card ↥E ≤ Nat.card (Fin 3 → ZMod 2) := by
    rw [he.card, Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]
    norm_num
  obtain ⟨v, hv⟩ := (hf.bijective_of_nat_card_le hcard).2 ⟨x, hx⟩
  exact ⟨v, congrArg Subtype.val hv⟩

open Classical in
noncomputable def e8Inv [Finite G] (he : E8Basis E e) (x : G) : Fin 3 → ZMod 2 :=
  if hx : x ∈ E then (exists_e8Coord_eq he hx).choose else 0

theorem e8Coord_e8Inv [Finite G] (he : E8Basis E e) {x : G} (hx : x ∈ E) :
    e8Coord e (e8Inv he x) = x := by
  have h := (exists_e8Coord_eq he hx).choose_spec
  unfold e8Inv
  split_ifs
  exact h

theorem e8Inv_e8Coord [Finite G] (he : E8Basis E e) (v : Fin 3 → ZMod 2) :
    e8Inv he (e8Coord e v) = v :=
  e8Coord_injective he (e8Coord_e8Inv he (e8Coord_mem he v))

theorem e8Coord_single (k : Fin 3) : e8Coord e (Pi.single k 1) = e k := by
  fin_cases k <;> simp [e8Coord, ZMod.val_one]

noncomputable def conjMat [Finite G] (he : E8Basis E e) (x : G) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  Matrix.of fun r k => e8Inv he (x * e k * x⁻¹) r

theorem e8Coord_smul (a : ZMod 2) (v : Fin 3 → ZMod 2) :
    e8Coord e (a • v) = e8Coord e v ^ a.val := by
  rcases zmod_two_cases a with rfl | rfl
  · rw [zero_smul, ZMod.val_zero, pow_zero, e8Coord_zero]
  · rw [one_smul, ZMod.val_one, pow_one]

theorem mulVec_three (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) (v : Fin 3 → ZMod 2) :
    M *ᵥ v = v 0 • (fun r => M r 0) + v 1 • (fun r => M r 1) + v 2 • (fun r => M r 2) := by
  funext r
  simp only [mulVec, dotProduct, Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem conj_e8Coord [Finite G] (he : E8Basis E e) {x : G}
    (hx : ∀ y ∈ E, x * y * x⁻¹ ∈ E) (v : Fin 3 → ZMod 2) :
    x * e8Coord e v * x⁻¹ = e8Coord e (conjMat he x *ᵥ v) := by
  have hcol : ∀ k, x * e k * x⁻¹ = e8Coord e (fun r => conjMat he x r k) := fun k =>
    (e8Coord_e8Inv he (hx _ (he.mem k))).symm
  rw [mulVec_three, e8Coord_add he, e8Coord_add he, e8Coord_smul, e8Coord_smul, e8Coord_smul,
    ← hcol, ← hcol, ← hcol]
  unfold e8Coord
  rw [conj_pow, conj_pow, conj_pow]
  group

end CFSG.ClassicalInvolution.Q3.TL4
