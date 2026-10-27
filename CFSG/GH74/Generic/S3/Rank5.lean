module

public import CFSG.GH74.Filter.ClassicalOdd.Basic
public import CFSG.GH74.Generic.Certificates
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.Filter.ClassicalOdd Subgroup
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem sl2_center_scalar {A : SL(2, F)} (hA : A ∈ center SL(2, F)) :
    ∃ r : F, r ^ 2 = 1 ∧ (A : Matrix (Fin 2) (Fin 2) F) = Matrix.scalar (Fin 2) r := by
  obtain ⟨r, hr, hA'⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  exact ⟨r, by simpa using hr, hA'.symm⟩

theorem sl2_scalar_eq {A : SL(2, F)} {r : F} (hr : r ^ 2 = 1)
    (hA : (A : Matrix (Fin 2) (Fin 2) F) = Matrix.scalar (Fin 2) r) : A = 1 ∨ A = -1 := by
  have h : r * r = 1 := by rw [← sq]; exact hr
  rcases mul_self_eq_one_iff.1 h with rfl | rfl
  · left
    apply Subtype.ext
    rw [hA]
    ext i j
    simp [Matrix.scalar_apply, Matrix.one_apply, Matrix.diagonal_apply]
  · right
    apply Subtype.ext
    rw [hA]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]

theorem sl2_center_eq {A : SL(2, F)} (hA : A ∈ center SL(2, F)) : A = 1 ∨ A = -1 := by
  obtain ⟨r, hr, hA'⟩ := sl2_center_scalar hA
  exact sl2_scalar_eq hr hA'

theorem sl2_sq_eq_one (hF : ringChar F ≠ 2) {A : SL(2, F)} (hA : A * A = 1) : A = 1 ∨ A = -1 := by
  have h := congrArg (fun B : SL(2, F) => (B : Matrix (Fin 2) (Fin 2) F)) hA
  have hdet := A.2
  rw [Matrix.det_fin_two] at hdet
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at h
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  have h10 := congrFun (congrFun h 1) 0
  have h11 := congrFun (congrFun h 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  by_cases hs : (A : Matrix (Fin 2) (Fin 2) F) 0 0 + (A : Matrix (Fin 2) (Fin 2) F) 1 1 = 0
  · exfalso
    have hd : (A : Matrix (Fin 2) (Fin 2) F) 1 1 = -(A : Matrix (Fin 2) (Fin 2) F) 0 0 := by
      linear_combination hs
    apply h2
    rw [hd] at hdet h11
    linear_combination -(hdet + h00)
  · have hb : (A : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
      have : (A : Matrix (Fin 2) (Fin 2) F) 0 1 * ((A : Matrix (Fin 2) (Fin 2) F) 0 0 + (A : Matrix (Fin 2) (Fin 2) F) 1 1) = 0 := by
        linear_combination h01
      exact (mul_eq_zero.1 this).resolve_right hs
    have hc : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
      have : (A : Matrix (Fin 2) (Fin 2) F) 1 0 * ((A : Matrix (Fin 2) (Fin 2) F) 0 0 + (A : Matrix (Fin 2) (Fin 2) F) 1 1) = 0 := by
        linear_combination h10
      exact (mul_eq_zero.1 this).resolve_right hs
    rw [hb, hc] at h00 h11 hdet
    have ha2 : (A : Matrix (Fin 2) (Fin 2) F) 0 0 * (A : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by linear_combination h00
    have hd2 : (A : Matrix (Fin 2) (Fin 2) F) 0 0 * (A : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by linear_combination hdet
    have hd : (A : Matrix (Fin 2) (Fin 2) F) 1 1 = (A : Matrix (Fin 2) (Fin 2) F) 0 0 := by
      have h0 : (A : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := by
        intro h0; rw [h0] at ha2; simp at ha2
      apply mul_left_cancel₀ h0
      rw [hd2, ha2]
    apply sl2_scalar_eq (r := (A : Matrix (Fin 2) (Fin 2) F) 0 0) (by linear_combination ha2)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, hb, hc, hd]

variable {G : Type} [Group G]

theorem sl2_img_eq_z (hF : ringChar F ≠ 2) {Y : Subgroup G}
    (e : SL(2, F) ≃* Y) {z : G} (hzY : z ∈ Y) (hzc : ∀ a ∈ Y, a * z = z * a) (hz1 : z ≠ 1) :
    (∀ a ∈ Y, (∀ b ∈ Y, a * b = b * a) → a = 1 ∨ a = z) ∧
      (∀ a ∈ Y, a * a = 1 → a = 1 ∨ a = z) := by
  have hcent : ∀ A : SL(2, F), (∀ C : SL(2, F), A * C = C * A) → A = 1 ∨ A = -1 :=
    fun A hA => sl2_center_eq (Subgroup.mem_center_iff.2 fun C => (hA C).symm)
  have hZe : e (e.symm ⟨z, hzY⟩) = ⟨z, hzY⟩ := e.apply_symm_apply _
  have hZc : ∀ C : SL(2, F), e.symm ⟨z, hzY⟩ * C = C * e.symm ⟨z, hzY⟩ := by
    intro C
    apply e.injective
    rw [map_mul, map_mul, hZe]
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact (hzc _ (e C).2).symm
  have hZneg : e.symm ⟨z, hzY⟩ = -1 := by
    rcases hcent _ hZc with h | h
    · exfalso
      apply hz1
      have : (⟨z, hzY⟩ : Y) = 1 := by rw [← hZe, h, map_one]
      exact congrArg Subtype.val this
    · exact h
  have hz_eq : ((e (-1) : Y) : G) = z := by
    rw [← hZneg, hZe]
  have hfin : ∀ A : SL(2, F), (A = 1 ∨ A = -1) → ((e A : Y) : G) = 1 ∨ ((e A : Y) : G) = z := by
    rintro A (rfl | rfl)
    · left; simp
    · right; exact hz_eq
  constructor
  · intro a ha hac
    have hA : ∀ C : SL(2, F), e.symm ⟨a, ha⟩ * C = C * e.symm ⟨a, ha⟩ := by
      intro C
      apply e.injective
      rw [map_mul, map_mul, e.apply_symm_apply]
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      exact hac _ (e C).2
    have := hfin _ (hcent _ hA)
    rwa [e.apply_symm_apply] at this
  · intro a ha haa
    have hA : e.symm ⟨a, ha⟩ * e.symm ⟨a, ha⟩ = 1 := by
      apply e.injective
      rw [map_mul, e.apply_symm_apply, map_one]
      apply Subtype.ext
      simpa using haa
    have := hfin _ (sl2_sq_eq_one hF hA)
    rwa [e.apply_symm_apply] at this

@[expose] def zPow4 (w : G) (hw : w ^ 4 = 1) : Multiplicative (ZMod 4) →* G where
  toFun k := w ^ (Multiplicative.toAdd k).val
  map_one' := by simp
  map_mul' a b := by
    rw [toAdd_mul, ZMod.val_add, ← pow_eq_pow_mod _ hw, pow_add]

theorem zPow4_apply (w : G) (hw : w ^ 4 = 1) (k : Multiplicative (ZMod 4)) :
    zPow4 w hw k = w ^ (Multiplicative.toAdd k).val := rfl

@[expose] def quatSL (Q : QuatRep F) : Q8 →* SL(2, F) where
  toFun g := ⟨Q.ρ g, Q.det_eq g⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul Q.ρ a b)

theorem coe_quatSL (Q : QuatRep F) (g : Q8) : ((quatSL Q g : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = Q.ρ g := rfl

@[expose] def pairHom (Q : QuatRep F) {Y : Subgroup G} (e : SL(2, F) ≃* Y) : Q8 →* G :=
  Y.subtype.comp (e.toMonoidHom.comp (quatSL Q))

theorem pairHom_mem (Q : QuatRep F) {Y : Subgroup G} (e : SL(2, F) ≃* Y) (g : Q8) :
    pairHom Q e g ∈ Y := (e (quatSL Q g)).2

theorem q8Frattini_of_pairHom (Q : QuatRep F) {Y Y' : Subgroup G} (e : SL(2, F) ≃* Y)
    (hcomm : ∀ a ∈ Y, ∀ b ∈ Y', a * b = b * a) (g : Q8) (hg : pairHom Q e g ∈ Y') :
    q8Frattini g = 1 := by
  have hc : quatSL Q g ∈ center SL(2, F) := by
    rw [Subgroup.mem_center_iff]
    intro C
    apply e.injective
    rw [map_mul, map_mul]
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact (hcomm _ (e C).2 _ hg)
  obtain ⟨r, -, hr⟩ := sl2_center_scalar hc
  exact (Q.scalar_eq g r (by rw [← coe_quatSL]; exact hr)).1

@[expose] def rk5Hom (φ0 φ2 : Q8 →* G) (w : G) (hw : w ^ 4 = 1)
    (h02 : ∀ a b, Commute (φ0 a) (φ2 b)) (hw0 : ∀ a, Commute (φ0 a) w)
    (hw2 : ∀ b, Commute (φ2 b) w) : (Q8 × Q8) × Multiplicative (ZMod 4) →* G :=
  MonoidHom.noncommCoprod (MonoidHom.noncommCoprod φ0 φ2 h02) (zPow4 w hw) (fun ab k => by
    rw [MonoidHom.noncommCoprod_apply, zPow4_apply]
    exact ((hw0 ab.1).mul_left (hw2 ab.2)).pow_right _)

theorem rk5Hom_apply (φ0 φ2 : Q8 →* G) (w : G) (hw : w ^ 4 = 1)
    (h02 : ∀ a b, Commute (φ0 a) (φ2 b)) (hw0 : ∀ a, Commute (φ0 a) w)
    (hw2 : ∀ b, Commute (φ2 b) w) (a b : Q8) (k : Multiplicative (ZMod 4)) :
    rk5Hom φ0 φ2 w hw h02 hw0 hw2 ((a, b), k) = φ0 a * φ2 b * w ^ (Multiplicative.toAdd k).val :=
  rfl

theorem not_gen4_of_sl2_pair [Finite G] [Finite F] (hF : ringChar F ≠ 2)
    {Y0 Y2 : Subgroup G} (e0 : SL(2, F) ≃* Y0) (e2 : SL(2, F) ≃* Y2)
    (hcomm : ∀ a ∈ Y0, ∀ b ∈ Y2, a * b = b * a) {z w : G} (hz0 : z ∈ Y0) (hz2 : z ∈ Y2)
    (hzz : z * z = 1) (hw0 : ∀ a ∈ Y0, a * w = w * a) (hw2 : ∀ b ∈ Y2, b * w = w * b)
    (hww : w * w = z) (hind : ∀ a ∈ Y0, ∀ b ∈ Y2, w ≠ a * b) : ¬ Gen4 G := by
  obtain ⟨Q⟩ := exists_quatRep hF
  have hw4 : w ^ 4 = 1 := by
    calc w ^ 4 = (w * w) * (w * w) := by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
      _ = 1 := by rw [hww, hzz]
  have h02 : ∀ a b, Commute (pairHom Q e0 a) (pairHom Q e2 b) := fun a b =>
    hcomm _ (pairHom_mem Q e0 a) _ (pairHom_mem Q e2 b)
  have hw0' : ∀ a, Commute (pairHom Q e0 a) w := fun a => hw0 _ (pairHom_mem Q e0 a)
  have hw2' : ∀ b, Commute (pairHom Q e2 b) w := fun b => hw2 _ (pairHom_mem Q e2 b)
  let β : (Q8 × Q8) × Multiplicative (ZMod 4) →* (V4 × V4) × Multiplicative (ZMod 2) :=
    (q8Frattini.prodMap q8Frattini).prodMap (zRed 4 (by decide))
  have hβ : Function.Surjective β :=
    (q8Frattini_surjective.prodMap q8Frattini_surjective).prodMap (zRed_surjective 4 (by decide))
  intro hG
  refine not_sectionalTwoRankLE_of_surjection 4
    (rk5Hom (pairHom Q e0) (pairHom Q e2) w hw4 h02 hw0' hw2') β hβ
    (fun a b => mul_comm a b) (by decide) (by rw [card_V4_sq_V2]; norm_num) ?_ hG
  rintro ⟨⟨a, b⟩, k⟩ hk
  rw [MonoidHom.mem_ker, rk5Hom_apply] at hk
  rw [MonoidHom.mem_ker]
  have hn4 : (Multiplicative.toAdd k).val < 4 := ZMod.val_lt _
  set n := (Multiplicative.toAdd k).val with hn
  have hw2z : w ^ 2 = z := by rw [pow_two]; exact hww
  have hz_inv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  by_cases hev : 2 ∣ n
  · have hwn : w ^ n ∈ Y0 ∧ w ^ n ∈ Y2 := by
      have : n = 0 ∨ n = 2 := by omega
      rcases this with h | h
      · rw [h, pow_zero]; exact ⟨one_mem _, one_mem _⟩
      · rw [h, hw2z]; exact ⟨hz0, hz2⟩
    have hfa : q8Frattini a = 1 := by
      refine q8Frattini_of_pairHom Q e0 hcomm a ?_
      have h1 : pairHom Q e0 a = (pairHom Q e2 b * w ^ n)⁻¹ := by
        apply eq_inv_of_mul_eq_one_left
        rw [← mul_assoc]; exact hk
      rw [h1]
      exact inv_mem (mul_mem (pairHom_mem Q e2 b) hwn.2)
    have hfb : q8Frattini b = 1 := by
      refine q8Frattini_of_pairHom Q e2 (fun x hx y hy => (hcomm y hy x hx).symm) b ?_
      have h1 : pairHom Q e2 b = (pairHom Q e0 a)⁻¹ * (w ^ n)⁻¹ := by
        calc pairHom Q e2 b = (pairHom Q e0 a)⁻¹ * (pairHom Q e0 a * pairHom Q e2 b * w ^ n) *
              (w ^ n)⁻¹ := by group
          _ = (pairHom Q e0 a)⁻¹ * (w ^ n)⁻¹ := by rw [hk]; group
      rw [h1]
      exact mul_mem (inv_mem (pairHom_mem Q e0 a)) (inv_mem hwn.1)
    have hfk : zRed 4 (by decide) k = 1 := (zRed_eq_one_iff 4 _ k).2 hev
    exact Prod.ext (Prod.ext hfa hfb) hfk
  · exfalso
    have hnn : n = 1 ∨ n = 3 := by omega
    have hprod : w ^ n = (pairHom Q e0 a)⁻¹ * (pairHom Q e2 b)⁻¹ := by
      have h1 : w ^ n = (pairHom Q e0 a * pairHom Q e2 b)⁻¹ := by
        apply eq_inv_of_mul_eq_one_right
        exact hk
      rw [h1, _root_.mul_inv_rev]
      exact ((h02 a b).inv_inv).eq.symm
    have h0 : (pairHom Q e0 a)⁻¹ ∈ Y0 := inv_mem (pairHom_mem Q e0 a)
    have h2 : (pairHom Q e2 b)⁻¹ ∈ Y2 := inv_mem (pairHom_mem Q e2 b)
    rcases hnn with h | h
    · rw [h, pow_one] at hprod
      exact hind _ h0 _ h2 hprod
    · have hw3 : w ^ 3 = z * w := by
        rw [pow_succ, hw2z]
      rw [h, hw3] at hprod
      apply hind (z * (pairHom Q e0 a)⁻¹) (mul_mem hz0 h0) _ h2
      calc w = z⁻¹ * (z * w) := by group
        _ = z * ((pairHom Q e0 a)⁻¹ * (pairHom Q e2 b)⁻¹) := by rw [hprod, hz_inv]
        _ = z * (pairHom Q e0 a)⁻¹ * (pairHom Q e2 b)⁻¹ := by group

theorem refl_ind (hF : ringChar F ≠ 2) {Y0 Y1 Y2 : Subgroup G} (e0 : SL(2, F) ≃* Y0)
    (e2 : SL(2, F) ≃* Y2) (hcomm : ∀ a ∈ Y0, ∀ b ∈ Y2, a * b = b * a) {z x j : G}
    (hz0 : z ∈ Y0) (hz2 : z ∈ Y2) (hzc0 : ∀ a ∈ Y0, a * z = z * a)
    (hzc2 : ∀ a ∈ Y2, a * z = z * a) (hz1 : z ≠ 1) (hzz : z * z = 1)
    (hxx : x * x = 1) (hx1 : x ≠ 1) (hx0 : ∀ a ∈ Y0, a * x = x * a)
    (hxY1 : ∀ g ∈ Y1, g * x = x * g) (hnc : ∃ g ∈ Y1, g * z ≠ z * g) (hj : j ∈ Y2) :
    ∀ a ∈ Y0, ∀ b ∈ Y2, x * j⁻¹ ≠ a * b := by
  intro a ha b hb hab
  have hb'Y : b * j ∈ Y2 := mul_mem hb hj
  have hx : x = a * (b * j) := by
    calc x = (x * j⁻¹) * j := by group
      _ = (a * b) * j := by rw [hab]
      _ = a * (b * j) := by rw [mul_assoc]
  have hacent : ∀ y ∈ Y0, a * y = y * a := by
    intro y hy
    have h1 := hx0 y hy
    rw [hx] at h1
    have h2 : (b * j) * y = y * (b * j) := (hcomm y hy _ hb'Y).symm
    have h3 : y * a * (b * j) = a * y * (b * j) := by
      calc y * a * (b * j) = y * (a * (b * j)) := by rw [mul_assoc]
        _ = a * (b * j) * y := h1
        _ = a * ((b * j) * y) := by rw [mul_assoc]
        _ = a * (y * (b * j)) := by rw [h2]
        _ = a * y * (b * j) := by rw [mul_assoc]
    exact (mul_right_cancel h3).symm
  obtain ⟨hA1, -⟩ := sl2_img_eq_z hF e0 hz0 hzc0 hz1
  obtain ⟨-, hB2⟩ := sl2_img_eq_z hF e2 hz2 hzc2 hz1
  have haz : a = 1 ∨ a = z := hA1 a ha hacent
  have haa : a * a = 1 := by
    rcases haz with rfl | rfl
    · simp
    · exact hzz
  have hbb : (b * j) * (b * j) = 1 := by
    have h1 : x * x = (a * a) * ((b * j) * (b * j)) := by
      rw [hx]
      calc a * (b * j) * (a * (b * j)) = a * ((b * j) * a) * (b * j) := by group
        _ = a * (a * (b * j)) * (b * j) := by rw [← hcomm a ha _ hb'Y]
        _ = (a * a) * ((b * j) * (b * j)) := by group
    rw [hxx, haa, one_mul] at h1
    exact h1.symm
  have hbz : b * j = 1 ∨ b * j = z := hB2 _ hb'Y hbb
  have hxz : x = 1 ∨ x = z := by
    rw [hx]
    rcases haz with rfl | rfl <;> rcases hbz with h | h <;> rw [h]
    · left; simp
    · right; simp
    · right; simp
    · left; exact hzz
  rcases hxz with h | h
  · exact hx1 h
  · obtain ⟨g, hg, hgz⟩ := hnc
    apply hgz
    have := hxY1 g hg
    rwa [h] at this

theorem not_gen4_of_reflection [Finite G] [Finite F] (hF : ringChar F ≠ 2) {Y0 Y1 Y2 : Subgroup G}
    (e0 : SL(2, F) ≃* Y0) (e2 : SL(2, F) ≃* Y2) (hcomm : ∀ a ∈ Y0, ∀ b ∈ Y2, a * b = b * a)
    {z u x j : G} (hz0 : z ∈ Y0) (hz2 : z ∈ Y2) (hzc0 : ∀ a ∈ Y0, a * z = z * a)
    (hzc2 : ∀ a ∈ Y2, a * z = z * a) (hz1 : z ≠ 1) (hzz : z * z = 1) (huu : u * u = 1)
    (hxx : x * x = 1) (hx1 : x ≠ 1) (hx0 : ∀ a ∈ Y0, a * x = x * a)
    (hxY1 : ∀ g ∈ Y1, g * x = x * g) (hxu : ∀ g ∈ Y2, g * (x * u) = (x * u) * g)
    (hnc : ∃ g ∈ Y1, g * z ≠ z * g) (hj : j ∈ Y2) (hjj : j * j = z)
    (hconj : ∀ g ∈ Y2, u * g * u⁻¹ = j * g * j⁻¹) : ¬ Gen4 G := by
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
  have hw0 : ∀ a ∈ Y0, a * (x * j⁻¹) = (x * j⁻¹) * a := by
    intro a ha
    calc a * (x * j⁻¹) = (a * x) * j⁻¹ := by rw [mul_assoc]
      _ = (x * a) * j⁻¹ := by rw [hx0 a ha]
      _ = x * (a * j⁻¹) := by rw [mul_assoc]
      _ = x * (j⁻¹ * a) := by rw [hcomm a ha j⁻¹ (inv_mem hj)]
      _ = (x * j⁻¹) * a := by rw [mul_assoc]
  have hw2 : ∀ g ∈ Y2, g * (x * j⁻¹) = (x * j⁻¹) * g := by
    intro g hg
    have hg' : j⁻¹ * g * j ∈ Y2 := mul_mem (mul_mem (inv_mem hj) hg) hj
    have h1 := hconj _ hg'
    have hjg : j * (j⁻¹ * g * j) * j⁻¹ = g := by group
    have h2 : u * (j⁻¹ * g * j) * u = g := by
      rw [hui] at h1
      exact h1.trans hjg
    have hg'eq : j⁻¹ * g * j = u * g * u := by
      calc j⁻¹ * g * j = (u * u) * (j⁻¹ * g * j) * (u * u) := by rw [huu]; simp
        _ = u * (u * (j⁻¹ * g * j) * u) * u := by group
        _ = u * g * u := by rw [h2]
    have hxug := hxu g hg
    symm
    calc (x * j⁻¹) * g = x * ((j⁻¹ * g * j) * j⁻¹) := by group
      _ = x * ((u * g * u) * j⁻¹) := by rw [hg'eq]
      _ = ((x * u) * g) * u * j⁻¹ := by group
      _ = (g * (x * u)) * u * j⁻¹ := by rw [← hxug]
      _ = g * (x * (u * u)) * j⁻¹ := by group
      _ = g * (x * j⁻¹) := by rw [huu]; group
  have hxj : x * j = j * x := by
    calc x * j = ((x * j⁻¹) * j) * j := by group
      _ = (j * (x * j⁻¹)) * j := by rw [hw2 j hj]
      _ = j * x := by group
  have hjx : j⁻¹ * x = x * j⁻¹ := by
    calc j⁻¹ * x = j⁻¹ * (x * j) * j⁻¹ := by group
      _ = j⁻¹ * (j * x) * j⁻¹ := by rw [hxj]
      _ = x * j⁻¹ := by group
  have hww : (x * j⁻¹) * (x * j⁻¹) = z := by
    calc (x * j⁻¹) * (x * j⁻¹) = x * (j⁻¹ * x) * j⁻¹ := by group
      _ = x * (x * j⁻¹) * j⁻¹ := by rw [hjx]
      _ = (x * x) * (j * j)⁻¹ := by group
      _ = z := by rw [hxx, hjj, one_mul, inv_eq_of_mul_eq_one_right hzz]
  exact not_gen4_of_sl2_pair hF e0 e2 hcomm hz0 hz2 hzz hw0 hw2 hww
    (refl_ind hF e0 e2 hcomm hz0 hz2 hzc0 hzc2 hz1 hzz hxx hx1 hx0 hxY1 hnc hj)

end CFSG.GH74.Generic.S3
