module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsFourCubeAction
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixFusionOrbits
public import Certificates.Certificate22216

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts.FourCube

open Matrix Subgroup

@[expose] noncomputable def redHom :
    Matrix (Fin 3) (Fin 3) (ZMod 4) →+* Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  RingHom.mapMatrix (ZMod.castHom (show 2 ∣ 4 by norm_num) (ZMod 2))

theorem redHom_apply (A : Mat4) (i j : Fin 3) :
    redHom A i j = ZMod.castHom (show 2 ∣ 4 by norm_num) (ZMod 2) (A i j) := rfl

theorem cast_sq_zero : ∀ x y : ZMod 4, ZMod.castHom (show 2 ∣ 4 by norm_num) (ZMod 2) x = 0 →
    ZMod.castHom (show 2 ∣ 4 by norm_num) (ZMod 2) y = 0 → x * y = 0 ∧ x + x = 0 := by
  decide

theorem cast_lift : ∀ a b : ZMod 4, ZMod.castHom (show 2 ∣ 4 by norm_num) (ZMod 2) a =
    ZMod.castHom (show 2 ∣ 4 by norm_num) (ZMod 2) b → a = b + if decide (a ≠ b) then 2 else 0 := by
  decide

theorem mul_self_of_red_eq_one {A : Mat4} (hA : redHom A = 1) : A * A = 1 := by
  set E := A - 1 with hE
  have hE0 : ∀ i j, ZMod.castHom (show 2 ∣ 4 by norm_num) (ZMod 2) (E i j) = 0 := by
    intro i j
    have : redHom E = 0 := by
      rw [hE, map_sub, hA, map_one]
      exact sub_self _
    have := congrFun (congrFun this i) j
    rwa [redHom_apply] at this
  have hA' : A = 1 + E := by rw [hE]; abel
  have hEE : E * E = 0 := by
    ext i j
    rw [mul_apply, Fin.sum_univ_three]
    simp only [Matrix.zero_apply]
    rw [(cast_sq_zero _ _ (hE0 i 0) (hE0 0 j)).1, (cast_sq_zero _ _ (hE0 i 1) (hE0 1 j)).1,
      (cast_sq_zero _ _ (hE0 i 2) (hE0 2 j)).1]
    simp
  have h2E : E + E = 0 := by
    ext i j
    rw [Matrix.add_apply, Matrix.zero_apply]
    exact (cast_sq_zero _ _ (hE0 i j) (hE0 i j)).2
  rw [hA', mul_add, add_mul, add_mul, one_mul, mul_one, one_mul, hEE, add_zero, add_assoc, h2E,
    add_zero]

theorem eq_add_twoM {A B : Mat4} (h : redHom A = redHom B) :
    A = B + twoM fun i j => decide (A i j ≠ B i j) := by
  ext i j
  have hij := congrFun (congrFun h i) j
  rw [redHom_apply, redHom_apply] at hij
  rw [Matrix.add_apply, twoM, Matrix.of_apply]
  exact cast_lift _ _ hij

theorem twoM_mul_self (m : Fin 3 → Fin 3 → Bool) : (1 + twoM m) * (1 + twoM m) = 1 := by
  have hEE : twoM m * twoM m = 0 := by
    ext i j
    simp only [twoM, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_three, Matrix.zero_apply]
    split_ifs <;> decide
  have h2 : twoM m + twoM m = 0 := by
    ext i j
    simp only [twoM, Matrix.add_apply, Matrix.of_apply, Matrix.zero_apply]
    split_ifs <;> decide
  rw [mul_add, add_mul, add_mul, one_mul, mul_one, one_mul, hEE, add_zero, add_assoc, h2,
    add_zero]

theorem X0_rel : X0 * X0 = 1 := by decide

theorem Y0_rel : Y0 * Y0 * Y0 = 1 := by decide

theorem XY0_rel : (X0 * Y0) ^ 7 = 1 := by decide

theorem C0_rel : (X0 * Y0 * X0 * (Y0 * Y0)) ^ 4 = 1 := by decide

theorem redY0_sq : redHom (Y0 * Y0) ≠ 1 := by
  intro h
  have := congrFun (congrFun h 0) 2
  rw [redHom_apply] at this
  revert this
  decide

@[expose] noncomputable def x2 : GL (Fin 3) (ZMod 2) :=
  ⟨redHom X0, redHom X0, by rw [← map_mul, X0_rel, map_one], by rw [← map_mul, X0_rel, map_one]⟩

@[expose] noncomputable def y2 : GL (Fin 3) (ZMod 2) :=
  ⟨redHom Y0, redHom (Y0 * Y0), by rw [← map_mul, ← mul_assoc, Y0_rel, map_one],
    by rw [← map_mul, Y0_rel, map_one]⟩

theorem y2_sq_ne_one : y2 ^ 2 ≠ 1 := by
  intro h
  have := congrArg Units.val h
  rw [Units.val_pow_eq_pow_val, sq, Units.val_one] at this
  exact redY0_sq (by rw [map_mul]; exact this)

variable {L : Type*} [Group L] {T : Subgroup L} [hT : T.Normal]
  (ι : T ≃* Multiplicative V4)

@[expose] noncomputable def redMat : L →* GL (Fin 3) (ZMod 2) :=
  ((redHom : Mat4 →* Matrix (Fin 3) (Fin 3) (ZMod 2)).comp (matHom ι)).toHomUnits

theorem redMat_val (g : L) : (redMat ι g : Matrix (Fin 3) (Fin 3) (ZMod 2)) = redHom (mat ι g) :=
  rfl

theorem mem_of_mat_eq_one (hC : centralizer (T : Set L) = T) {g : L} (hg : mat ι g = 1) :
    g ∈ T := by
  rw [← hC]
  exact (mat_eq_one_iff ι g).1 hg

variable [Finite L] {φ : L →* GL (Fin 3) (ZMod 2)}

omit [Finite L] in
theorem ker_redMat (hC : centralizer (T : Set L) = T) (hφs : Function.Surjective φ)
    (hφk : φ.ker = T) : (redMat ι).ker = T := by
  apply le_antisymm
  · intro n hn
    have hsq : ∀ m ∈ (redMat ι).ker, φ m ^ 2 = 1 := by
      intro m hm
      have h1 : redHom (mat ι m) = 1 := by
        have := congrArg Units.val (MonoidHom.mem_ker.1 hm)
        rwa [redMat_val, Units.val_one] at this
      have h2 : mat ι (m * m) = 1 := by rw [mat_mul]; exact mul_self_of_red_eq_one h1
      have h3 : m * m ∈ φ.ker := hφk ▸ mem_of_mat_eq_one ι hC h2
      rw [sq, ← map_mul]
      exact h3
    have hnorm : ((redMat ι).ker.map φ).Normal := (MonoidHom.normal_ker _).map φ hφs
    have hsimp := open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix in
      FusionOrbits.isSimpleGroup_GL_three_two
    rcases hsimp.eq_bot_or_eq_top_of_normal ((redMat ι).ker.map φ) with hb | ht
    · rw [← hφk]
      have : φ n ∈ (redMat ι).ker.map φ := ⟨n, hn, rfl⟩
      rw [hb, mem_bot] at this
      exact this
    · exfalso
      have : y2 ∈ (redMat ι).ker.map φ := by rw [ht]; trivial
      obtain ⟨m, hm, hmy⟩ := this
      exact y2_sq_ne_one (hmy ▸ hsq m hm)
  · intro t ht
    rw [MonoidHom.mem_ker]
    apply Units.ext
    rw [redMat_val, mat_of_mem ι ht, map_one, Units.val_one]

omit [Finite L] in
theorem redMat_surjective (hC : centralizer (T : Set L) = T) (hφs : Function.Surjective φ)
    (hφk : φ.ker = T) : Function.Surjective (redMat ι) := by
  have h1 : Nat.card (redMat ι).range = Nat.card (GL (Fin 3) (ZMod 2)) := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange (redMat ι)).toEquiv,
      ker_redMat ι hC hφs hφk, ← hφk,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφs).toEquiv]
  have h2 : (redMat ι).range = ⊤ := Subgroup.eq_top_of_card_eq _ h1
  exact MonoidHom.range_eq_top.1 h2

@[expose] noncomputable def kEquiv (k k' : Mat4) (h1 : k * k' = 1) (h2 : k' * k = 1) :
    Multiplicative V4 ≃* Multiplicative V4 where
  toFun v := Multiplicative.ofAdd (k *ᵥ Multiplicative.toAdd v)
  invFun v := Multiplicative.ofAdd (k' *ᵥ Multiplicative.toAdd v)
  left_inv v := by simp [mulVec_mulVec, h2]
  right_inv v := by simp [mulVec_mulVec, h1]
  map_mul' v w := by simp [mulVec_add]

omit hT [Finite L] in
theorem vec_trans (k k' : Mat4) (h1 : k * k' = 1) (h2 : k' * k = 1) (t : T) :
    vec (ι.trans (kEquiv k k' h1 h2)) t = k *ᵥ vec ι t := rfl

omit hT [Finite L] in
theorem elt_trans (k k' : Mat4) (h1 : k * k' = 1) (h2 : k' * k = 1) (v : V4) :
    elt (ι.trans (kEquiv k k' h1 h2)) v = elt ι (k' *ᵥ v) := rfl

omit [Finite L] in
theorem mat_trans (k k' : Mat4) (h1 : k * k' = 1) (h2 : k' * k = 1) (g : L) :
    mat (ι.trans (kEquiv k k' h1 h2)) g = k * mat ι g * k' := by
  rw [mat, ← LinearMap.toMatrix'_toLin' (k * mat ι g * k')]
  congr 1
  apply LinearMap.ext
  intro v
  rw [Matrix.toLin'_apply]
  show vec (ι.trans (kEquiv k k' h1 h2)) (conjT g (elt (ι.trans (kEquiv k k' h1 h2)) v)) = _
  rw [vec_trans, elt_trans, vec_conj, vec_elt, mulVec_mulVec, mulVec_mulVec, mul_assoc]

theorem complementA_holds : complementA := by
  have h := Certificates.certificate22216
  simp only [complementOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem complementB_holds : complementB := by
  have h := Certificates.certificate22216
  simp only [complementOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

theorem redHom_k (m : Fin 3 → Fin 3 → Bool) : redHom (1 + twoM m) = 1 := by
  ext i j
  rw [redHom_apply, Matrix.add_apply, map_add, twoM, Matrix.of_apply]
  have h2 : ZMod.castHom (show 2 ∣ 4 by norm_num) (ZMod 2) (if m i j = true then 2 else 0) = 0 := by
    split_ifs <;> decide
  rw [h2, add_zero]
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.one_apply_eq, map_one]
  · simp only [Matrix.one_apply_ne hij, map_zero]

theorem conj_pow' (k k' M : Mat4) (h1 : k * k' = 1) (h2 : k' * k = 1) (n : ℕ) :
    (k * M * k') ^ n = k * M ^ n * k' := by
  induction n with
  | zero => rw [pow_zero, pow_zero, mul_one, h1]
  | succ n ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [mul_assoc]
    rw [← mul_assoc k' k, h2, one_mul]

omit [Finite L] in
include ι in
theorem exists_std_lifts (hC : centralizer (T : Set L) = T)
    (hφs : Function.Surjective φ) (hφk : φ.ker = T) :
    ∃ ι' : T ≃* Multiplicative V4, ∃ x y : L, mat ι' x = X0 ∧ mat ι' y = Y0 := by
  obtain ⟨x, hx⟩ := redMat_surjective ι hC hφs hφk x2
  obtain ⟨y, hy⟩ := redMat_surjective ι hC hφs hφk y2
  have hxr : redHom (mat ι x) = redHom X0 := by rw [← redMat_val, hx]; rfl
  have hyr : redHom (mat ι y) = redHom Y0 := by rw [← redMat_val, hy]; rfl
  have hrel : ∀ g : L, redHom (mat ι g) = 1 → mat ι g = 1 := fun g hg => by
    refine mat_of_mem ι ?_
    rw [← ker_redMat ι hC hφs hφk, MonoidHom.mem_ker]
    exact Units.ext (by rw [redMat_val, hg]; rfl)
  have hX2 : mat ι x * mat ι x = 1 := by
    rw [← mat_mul]
    apply hrel
    rw [mat_mul, map_mul, hxr, ← map_mul, X0_rel, map_one]
  have hY3 : mat ι y * mat ι y * mat ι y = 1 := by
    rw [← mat_mul, ← mat_mul]
    apply hrel
    rw [mat_mul, mat_mul, map_mul, map_mul, hyr, ← map_mul, ← map_mul, Y0_rel, map_one]
  have hXY : (mat ι x * mat ι y) ^ 7 = 1 := by
    rw [← mat_mul, ← mat_pow]
    apply hrel
    rw [mat_pow, mat_mul, map_pow, map_mul, hxr, hyr, ← map_mul, ← map_pow, XY0_rel, map_one]
  have hCC : (mat ι x * mat ι y * mat ι x * (mat ι y * mat ι y)) ^ 4 = 1 := by
    rw [← mat_mul, ← mat_mul, ← mat_mul, ← mat_mul, ← mat_pow]
    apply hrel
    rw [mat_pow, mat_mul, mat_mul, mat_mul, mat_mul, map_pow, map_mul, map_mul, map_mul, map_mul,
      hxr, hyr, ← map_mul, ← map_mul, ← map_mul, ← map_mul, ← map_pow, C0_rel, map_one]
  have hYe := eq_add_twoM hyr
  obtain ⟨m1, hm1⟩ := complementA_holds _ (by rw [← hYe]; exact hY3)
  rw [← hYe] at hm1
  set k1 := 1 + twoM m1 with hk1
  have hk11 := twoM_mul_self m1
  have hY0 : k1 * mat ι y * k1 = Y0 := by rw [hm1, mul_assoc, hk11, mul_one]
  set X' := k1 * mat ι x * k1 with hX'
  have hX'r : redHom X' = redHom X0 := by
    rw [hX', map_mul, map_mul, redHom_k, hxr, one_mul, mul_one]
  have hX'e := eq_add_twoM hX'r
  have hrelX : GenRel X' Y0 := by
    refine ⟨?_, Y0_rel, ?_, ?_⟩
    · rw [hX', show k1 * mat ι x * k1 * (k1 * mat ι x * k1) = k1 * (mat ι x * mat ι x) * k1 by
        simp only [mul_assoc]; rw [← mul_assoc k1 k1, hk11, one_mul], hX2, mul_one, hk11]
    · rw [← hY0, hX',
        show k1 * mat ι x * k1 * (k1 * mat ι y * k1) = k1 * (mat ι x * mat ι y) * k1 by
          simp only [mul_assoc]; rw [← mul_assoc k1 k1, hk11, one_mul],
        conj_pow' k1 k1 _ hk11 hk11, hXY, mul_one, hk11]
    · rw [← hY0, hX']
      have e : k1 * mat ι x * k1 * (k1 * mat ι y * k1) * (k1 * mat ι x * k1) *
          ((k1 * mat ι y * k1) * (k1 * mat ι y * k1)) =
          k1 * (mat ι x * mat ι y * mat ι x * (mat ι y * mat ι y)) * k1 := by
        simp only [mul_assoc]
        rw [← mul_assoc k1 k1, hk11, one_mul, ← mul_assoc k1 k1, hk11, one_mul,
          ← mul_assoc k1 k1, hk11, one_mul, ← mul_assoc k1 k1, hk11, one_mul]
      rw [e, conj_pow' k1 k1 _ hk11 hk11, hCC, mul_one, hk11]
  rw [hX'e] at hrelX
  obtain ⟨m2, hm2Y, hm2X⟩ := complementB_holds _ hrelX
  rw [← hX'e] at hm2X
  set k2 := 1 + twoM m2 with hk2
  have hk22 := twoM_mul_self m2
  have h1 : k2 * k1 * (k1 * k2) = 1 := by rw [mul_assoc, ← mul_assoc k1 k1, hk11, one_mul, hk22]
  have h2 : k1 * k2 * (k2 * k1) = 1 := by rw [mul_assoc, ← mul_assoc k2 k2, hk22, one_mul, hk11]
  refine ⟨ι.trans (kEquiv (k2 * k1) (k1 * k2) h1 h2), x, y, ?_, ?_⟩
  · rw [mat_trans]
    calc k2 * k1 * mat ι x * (k1 * k2) = k2 * X' * k2 := by rw [hX']; simp only [mul_assoc]
      _ = X0 := by rw [hm2X, mul_assoc, hk22, mul_one]
  · rw [mat_trans]
    calc k2 * k1 * mat ι y * (k1 * k2) = k2 * (k1 * mat ι y * k1) * k2 := by simp only [mul_assoc]
      _ = Y0 := by rw [hY0, hm2Y, mul_assoc, hk22, mul_one]

end CFSG.ComponentClassification.GrSLit.L34Facts.FourCube
