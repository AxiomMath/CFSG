module

public import Certificates.Data.Kernel.ThFive.Check
public import CFSG.Certificates.Kernel.ThCent.ListSound

public section

namespace CFSG.KC.ThFive

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.Th.Spec CFSG.KC.Th.Spec.FwdRel CFSG.KC.ThCent
  CFSG.SectionRank.Native

local notation "𝕄" g:max =>
  ((Subtype.val g : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2))

theorem runK_eq {α : Sort*} (c rm ONE : ℕ) (k : (ℕ → ℕ) → α) :
    ∀ (prog : List Op) (R : ℕ → ℕ), runK c rm ONE prog k R = k (runPk c rm ONE prog R)
  | [], _ => rfl
  | op :: prog, R => by
    cases op with
    | mul i j k' =>
      change strictF (mulB c rm (R i) (R j)) (fun v => runK c rm ONE prog k (updN R k' v)) =
        k (strictF (mulB c rm (R i) (R j)) fun v => runPk c rm ONE prog (updN R k' v))
      rw [strictF_eq, strictF_eq, runK_eq]
    | pow e i k' =>
      change strictF (powB c rm ONE (R i) e 6) (fun v => runK c rm ONE prog k (updN R k' v)) =
        k (strictF (powB c rm ONE (R i) e 6) fun v => runPk c rm ONE prog (updN R k' v))
      rw [strictF_eq, strictF_eq, runK_eq]

theorem foldl_opG_mem {G : Type*} [Group G] (H : Subgroup G) :
    ∀ (prog : List Op) (R : ℕ → G), (∀ r, R r ∈ H) → ∀ r, prog.foldl opG R r ∈ H
  | [], _, hR, r => hR r
  | op :: prog, R, hR, r => by
    rw [List.foldl_cons]
    refine foldl_opG_mem H prog _ (fun s => ?_) r
    cases op with
    | mul i j k =>
      change Function.update R k (R i * R j) s ∈ H
      by_cases hs : s = k
      · rw [hs, Function.update_self]
        exact H.mul_mem (hR i) (hR j)
      · rw [Function.update_of_ne hs]
        exact hR s
    | pow e i k =>
      change Function.update R k (R i ^ e) s ∈ H
      by_cases hs : s = k
      · rw [hs, Function.update_self]
        exact H.pow_mem (hR i) e
      · rw [Function.update_of_ne hs]
        exact hR s

variable {J : Subgroup (GL (Fin 248) (ZMod 2))}

theorem pkMat_updN {R : ℕ → ℕ} {RJ : ℕ → J} (hR : ∀ r, pkMat (R r) = 𝕄 (RJ r)) {k v : ℕ} {x : J}
    (hv : pkMat v = 𝕄 x) : ∀ r, pkMat (updN R k v r) = 𝕄 (Function.update RJ k x r) := by
  intro r
  unfold updN
  by_cases hrk : r = k
  · subst hrk
    rw [Nat.beq_refl, Function.update_self]
    exact hv
  · rw [beq_false' hrk, Function.update_of_ne hrk]
    exact hR r

variable {c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE : ℕ}
  (hk : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
include hk

theorem eqB_sound {X Y : ℕ} (h : eqB c rm ONE X Y = true) : pkMat X = pkMat Y := by
  have e := congrArg pkMat (Nat.eq_of_beq_eq_true h)
  rwa [pkMat_mulB hk, pkMat_mulB hk, pkMat_one hk, Matrix.mul_one, Matrix.mul_one] at e

theorem mul_sound {X Y Z W : ℕ} {x y z w : J} (hX : pkMat X = 𝕄 x) (hY : pkMat Y = 𝕄 y)
    (hZ : pkMat Z = 𝕄 z) (hW : pkMat W = 𝕄 w)
    (h : Nat.beq (mulB c rm X Y) (mulB c rm Z W) = true) : x * y = z * w := by
  have e := congrArg pkMat (Nat.eq_of_beq_eq_true h)
  rw [pkMat_mulB hk, pkMat_mulB hk, hX, hY, hZ, hW, ← mat_mul, ← mat_mul] at e
  exact mat_injective e

theorem chk_sound (a b : J) {A B : ℕ} (hA : 𝕄 a = pkMat A) (hB : 𝕄 b = pkMat B)
    {P1 P2 P3 : List (List ℕ)} {O1 O2 O3 : List ℕ} (h : chk c rm ONE A B P1 P2 P3 O1 O2 O3 = true) :
    ∃ q₁ q₂ r g c₁ z y₁ y₂ w : J,
      q₁ ^ 5 = 1 ∧ q₂ ^ 5 = 1 ∧
      q₁ * q₂ * q₁ ^ 4 * q₂ ^ 4 * q₁ = q₁ * (q₁ * q₂ * q₁ ^ 4 * q₂ ^ 4) ∧
      q₁ * q₂ * q₁ ^ 4 * q₂ ^ 4 * q₂ = q₂ * (q₁ * q₂ * q₁ ^ 4 * q₂ ^ 4) ∧
      (q₁ * q₂ * q₁ ^ 4 * q₂ ^ 4) ^ 5 = 1 ∧
      r ≠ 1 ∧ r = y₁ ∧ a * r = r * a ∧ c₁ * r = r * c₁ ∧ r * g = g * y₂ ∧ z * y₂ = y₂ * z ∧
      w = b ∧ y₁ ∈ Subgroup.closure {q₁, q₂} ∧ y₂ ∈ Subgroup.closure {q₁, q₂} ∧
      w ∈ Subgroup.closure {q₁, q₂, a, c₁, z} := by
  unfold chk at h
  obtain ⟨hp1, h⟩ := andB_tt h
  obtain ⟨hp2, h⟩ := andB_tt h
  obtain ⟨hp3, h⟩ := andB_tt h
  simp only [runK_eq, strictF_eq] at h
  have hR := pkMat_runPk hk _ hp1 _ _ (pkMat_initPk hk a b hA hB)
  generalize runPk c rm ONE (P1.map opOf) (initPk A B ONE) = R at h hR
  generalize (P1.map opOf).foldl opG (initG a b) = RJ at hR
  obtain ⟨hpg, h⟩ := andB_tt h
  set q₁ := RJ (O1.getD 0 0)
  set q₂ := RJ (O1.getD 1 0)
  set c₁ := RJ (O1.getD 4 0)
  set z := RJ (O1.getD 5 0)
  have hR2 := pkMat_runPk hk _ hp2 _ _ (pkMat_initPk hk q₁ q₂ (hR _).symm (hR _).symm)
  have hR3 : ∀ r, pkMat (runPk c rm ONE (P3.map opOf) (file5 ONE (R (O1.getD 0 0)) (R (O1.getD 1 0)) A
      (R (O1.getD 4 0)) (R (O1.getD 5 0))) r) = 𝕄 ((P3.map opOf).foldl opG (Function.update
      (Function.update (Function.update (initG q₁ q₂) 2 a) 3 c₁) 4 z) r) :=
    pkMat_runPk hk _ hp3 _ _ (pkMat_updN (pkMat_updN (pkMat_updN
      (pkMat_initPk hk q₁ q₂ (hR _).symm (hR _).symm) hA.symm) (hR (O1.getD 4 0))) (hR (O1.getD 5 0)))
  have hinit : ∀ (H : Subgroup J), q₁ ∈ H → q₂ ∈ H → ∀ r, initG q₁ q₂ r ∈ H := by
    intro H h1 h2 r
    unfold initG
    split_ifs
    · exact h1
    · exact h2
    · exact H.one_mem
  have hm2 : ∀ r, (P2.map opOf).foldl opG (initG q₁ q₂) r ∈ Subgroup.closure {q₁, q₂} :=
    foldl_opG_mem _ _ _ (hinit _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp)))
  have hm3 : ∀ r, (P3.map opOf).foldl opG (Function.update (Function.update (Function.update
      (initG q₁ q₂) 2 a) 3 c₁) 4 z) r ∈ Subgroup.closure {q₁, q₂, a, c₁, z} := by
    refine foldl_opG_mem _ _ _ fun r => ?_
    by_cases h4 : r = 4
    · rw [h4, Function.update_self]
      exact Subgroup.subset_closure (by simp)
    rw [Function.update_of_ne h4]
    by_cases h3 : r = 3
    · rw [h3, Function.update_self]
      exact Subgroup.subset_closure (by simp)
    rw [Function.update_of_ne h3]
    by_cases h2 : r = 2
    · rw [h2, Function.update_self]
      exact Subgroup.subset_closure (by simp)
    rw [Function.update_of_ne h2]
    exact hinit _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)) r
  generalize runPk c rm ONE (P2.map opOf) (initPk (R (O1.getD 0 0)) (R (O1.getD 1 0)) ONE) = S
    at h hR2
  generalize (P2.map opOf).foldl opG (initG q₁ q₂) = SJ at hR2 hm2
  generalize runPk c rm ONE (P3.map opOf) (file5 ONE (R (O1.getD 0 0)) (R (O1.getD 1 0)) A
    (R (O1.getD 4 0)) (R (O1.getD 5 0))) = T at h hR3
  generalize (P3.map opOf).foldl opG (Function.update (Function.update (Function.update
    (initG q₁ q₂) 2 a) 3 c₁) 4 z) = TJ at hR3 hm3
  unfold pgOK at hpg
  rw [strictF_eq] at hpg
  obtain ⟨hcube, hC5⟩ := andB_tt hpg
  obtain ⟨h1, h2, h3, h4⟩ := cubeOK5_sound hk hcube
  have hC : pkMat (mulB c rm (mulB c rm (mulB c rm (R (O1.getD 0 0)) (R (O1.getD 1 0)))
      (powB c rm ONE (R (O1.getD 0 0)) 4 (nat_lit 3))) (powB c rm ONE (R (O1.getD 1 0)) 4 (nat_lit 3))) =
      𝕄 (q₁ * q₂ * q₁ ^ 4 * q₂ ^ 4) := by
    rw [pkMat_mulB hk, pkMat_mulB hk, pkMat_mulB hk, pkMat_powB hk _ _ 3 (by norm_num),
      pkMat_powB hk _ _ 3 (by norm_num), hR, hR, mat_mul, mat_mul, mat_mul, mat_pow, mat_pow]
  rw [hC, hR] at h3
  rw [hC, hR] at h4
  rw [hR] at h1
  rw [hR] at h2
  have inj : ∀ {x y : J}, 𝕄 x = 𝕄 y → x = y := fun e => mat_injective e
  have hC5' : 𝕄 ((q₁ * q₂ * q₁ ^ 4 * q₂ ^ 4) ^ 5) = 1 := by
    rw [mat_pow, ← hC, ← pkMat_powB hk _ _ 3 (by norm_num), Nat.eq_of_beq_eq_true hC5, pkMat_one hk]
  unfold entOK at h
  obtain ⟨e1, h⟩ := andB_tt h
  obtain ⟨e2, h⟩ := andB_tt h
  obtain ⟨e3, h⟩ := andB_tt h
  obtain ⟨e4, h⟩ := andB_tt h
  obtain ⟨e5, h⟩ := andB_tt h
  obtain ⟨e6, e7⟩ := andB_tt h
  refine ⟨q₁, q₂, RJ (O1.getD 2 0), RJ (O1.getD 3 0), c₁, z, SJ (O2.getD 0 0), SJ (O2.getD 1 0),
    TJ (O3.getD 0 0), inj (by rw [mat_pow, mat_one]; exact h1),
    inj (by rw [mat_pow, mat_one]; exact h2),
    inj (by rw [mat_mul, mat_mul]; exact h3),
    inj (by rw [mat_mul, mat_mul]; exact h4),
    inj (by rw [hC5', mat_one]), ?_,
    inj (by rw [← hR, ← hR2]; exact eqB_sound hk e2),
    mul_sound hk hA.symm (hR _) (hR _) hA.symm e3, mul_sound hk (hR _) (hR _) (hR _) (hR _) e4,
    mul_sound hk (hR _) (hR _) (hR _) (hR2 _) e5, mul_sound hk (hR _) (hR2 _) (hR2 _) (hR _) e6,
    inj (by rw [← hR3, hB]; exact eqB_sound hk e7), hm2 _, hm2 _, hm3 _⟩
  intro e
  apply neB_sound hk e1
  rw [hR, e, mat_one, pkMat_one hk]

end CFSG.KC.ThFive

end
