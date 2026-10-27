module

public import CFSG.GH74.Generic.ClassicalCerts

public section

namespace CFSG.GH74.E2

open CFSG.GH74.Generic CFSG.Assembly.LowTwoRank CFSG.GH74.Filter.ClassicalOdd CFSG.GH74.L5U5
  CFSG.SectionRank.ClassicalOdd Matrix

section U42

variable {F : Type} [Field F]

@[expose] def u42N (a d b b' : F) : Matrix (Fin 4) (Fin 4) F :=
  !![a, a, b, b; a, a, b, b; b', b', d, d; b', b', d, d]

theorem u42N_mul_u42N (h2 : (2 : F) = 0) (a d b b' a' d' c c' : F) :
    u42N a d b b' * u42N a' d' c c' = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u42N, Matrix.mul_apply, Fin.sum_univ_four] <;>
    ring_nf <;> simp [h2]

theorem u42N_add (a d b b' a' d' c c' : F) :
    u42N a d b b' + u42N a' d' c c' = u42N (a + a') (d + d') (b + c) (b' + c') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u42N]

theorem u42N_zero : u42N (0 : F) 0 0 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u42N]

theorem one_add_u42N_mul (h2 : (2 : F) = 0) (a d b b' a' d' c c' : F) :
    (1 + u42N a d b b') * (1 + u42N a' d' c c') = 1 + u42N (a + a') (d + d') (b + c) (b' + c') := by
  rw [← u42N_add, add_mul, mul_add, mul_add, u42N_mul_u42N h2]
  simp only [Matrix.one_mul, Matrix.mul_one, add_zero]
  abel

theorem hstar_u42N (σ : F →+* F) (a d b b' : F) :
    hstar σ (u42N a d b b') = u42N (σ a) (σ d) (σ b') (σ b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hstar, u42N]

@[expose] def u42Mat (ι : ZMod 2 →+* F) (σ : F →+* F) (v : ZMod 2 × ZMod 2 × F) :
    Matrix (Fin 4) (Fin 4) F :=
  1 + u42N (ι v.1) (ι v.2.1) v.2.2 (σ v.2.2)

variable {ι : ZMod 2 →+* F} {σ : F →+* F}

theorem u42Mat_zero : u42Mat ι σ 0 = 1 := by
  simp [u42Mat, u42N_zero]

theorem u42Mat_add (h2 : (2 : F) = 0) (v w : ZMod 2 × ZMod 2 × F) :
    u42Mat ι σ (v + w) = u42Mat ι σ v * u42Mat ι σ w := by
  simp only [u42Mat]
  rw [one_add_u42N_mul h2]
  simp [map_add]

theorem u42Mat_self (h2 : (2 : F) = 0) (hι : ∀ a : ZMod 2, a + a = 0)
    (v : ZMod 2 × ZMod 2 × F) : u42Mat ι σ v * u42Mat ι σ v = 1 := by
  have h : v + v = 0 := Prod.ext (hι _) (Prod.ext (hι _) (by
    change v.2.2 + v.2.2 = 0
    rw [← two_mul, h2, zero_mul]))
  rw [← u42Mat_add h2, h, u42Mat_zero]

theorem hstar_u42Mat (hσι : ∀ a : ZMod 2, σ (ι a) = ι a) (hσσ : ∀ x, σ (σ x) = x)
    (v : ZMod 2 × ZMod 2 × F) : hstar σ (u42Mat ι σ v) = u42Mat ι σ v := by
  unfold u42Mat
  rw [hstar_add, hstar_one, hstar_u42N, hσι, hσι, hσσ]

theorem u42Mat_injective (hι : Function.Injective ι) : Function.Injective (u42Mat ι σ) := by
  intro v w h
  have h00 := congrFun (congrFun h 0) 1
  have h02 := congrFun (congrFun h 0) 2
  have h23 := congrFun (congrFun h 2) 3
  simp [u42Mat, u42N] at h00 h02 h23
  exact Prod.ext (hι h00) (Prod.ext (hι h23) h02)

end U42

theorem rankCertified_SU4_two {F : Type} [Field F] [Finite F] {q : ℕ} (hq : q = 2)
    (hF : Nat.card F = q ^ 2) : RankCertified (StatedProj (StatedSU 4 q F)) 3 := by
  subst hq
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := CFSG.SectionRank.ClassicalOdd.charP_of_card (p := 2) (f := 2) hF
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  let σ : F →+* F := iterateFrobenius F 2 1
  have hσ : ∀ x, σ x = x ^ 2 := fun x => by
    rw [CFSG.SectionRank.ClassicalOdd.frob_apply]
    norm_num
  have hσσ : ∀ x, σ (σ x) = x := fun x =>
    CFSG.SectionRank.ClassicalOdd.frob_frob (by simpa using hF) x
  let ι : ZMod 2 →+* F := ZMod.castHom (dvd_refl 2) F
  have hι : Function.Injective ι := ι.injective
  have hσι : ∀ a : ZMod 2, σ (ι a) = ι a := fun a =>
    RingHom.congr_fun (RingHom.ext_zmod (σ.comp ι) ι) a
  have hι2 : ∀ a : ZMod 2, a + a = 0 := fun a => CharTwo.add_self_eq_zero a
  let α : Multiplicative (ZMod 2 × ZMod 2 × F) →* GL (Fin 4) F :=
    glOfAdd (u42Mat ι σ) u42Mat_zero (u42Mat_add h2)
  have hαv : ∀ k, (α k : Matrix (Fin 4) (Fin 4) F) = u42Mat ι σ (Multiplicative.toAdd k) :=
    fun k => rfl
  refine rankCertified_statedProj (A := Multiplicative (ZMod 2 × ZMod 2 × F)) α (fun k => ?_)
    (MonoidHom.id _) Function.surjective_id (fun a b => mul_comm a b) (fun a => ?_) ?_ ?_
  · refine mem_statedSU_of_isUni hσ (α k) ?_ ?_
    · rw [hαv]
      exact det_eq_one_of_pow_char (p := 2) (by rw [sq]; exact u42Mat_self h2 hι2 _)
    · change hstar σ (α k : Matrix (Fin 4) (Fin 4) F) * (α k : Matrix (Fin 4) (Fin 4) F) = 1
      rw [hαv, hstar_u42Mat hσι hσσ]
      exact u42Mat_self h2 hι2 _
  · apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, two_nsmul]
    exact Prod.ext (hι2 _) (Prod.ext (hι2 _) (by
      change (Multiplicative.toAdd a).2.2 + (Multiplicative.toAdd a).2.2 = 0
      rw [← two_mul, h2, zero_mul]))
  · rw [Nat.card_congr Multiplicative.toAdd, Nat.card_prod, Nat.card_prod, Nat.card_zmod, hF]
    norm_num
  · intro k c h
    have h' : u42Mat ι σ (Multiplicative.toAdd k) = scalar (Fin 4) c := by rw [← hαv]; exact h
    have h01 := congrFun (congrFun h' 0) 1
    have h02 := congrFun (congrFun h' 0) 2
    have h23 := congrFun (congrFun h' 2) 3
    simp [u42Mat, u42N, scalar_apply] at h01 h02 h23
    apply Multiplicative.toAdd.injective
    exact Prod.ext (hι (by simpa using h01)) (Prod.ext (hι (by simpa using h23)) h02)

end CFSG.GH74.E2
