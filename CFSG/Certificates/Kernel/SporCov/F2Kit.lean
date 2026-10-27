module

public import Certificates.Data.Kernel.SporCov.F2Kit
public import CFSG.Certificates.Kernel.SporCov.Words
public import CFSG.Certificates.Kernel.TabMatGrpSound
public import CFSG.Sporadic.HS.Group

public section

namespace CFSG.KD.SporCov

open CFSG.KC.SporCov CFSG.KC.TabMatGrp CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KC.Co1F2
  CFSG.KC.F2W

private theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

private theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

private theorem andB_eq (a b : Bool) : andB a b = (a && b) := by
  cases a <;> rfl

variable {G : Type} [Group G]

@[expose] def fF (a b : G) (c : ℕ) : G :=
  if c = 0 then a else if c = 1 then a⁻¹ else if c = 2 then b else b⁻¹

theorem fF_zero (a b : G) : fF a b 0 = a := rfl

theorem fF_two (a b : G) : fF a b 2 = b := rfl

section Kit

variable {d : ℕ} {φ : G →* GL (Fin d) (ZMod 2)} {a b : G} {MA MAi MB MBi : ℕ}

theorem MatP_letF (hA : MatP d MA = matOf φ a) (hAi : MatP d MAi = matOf φ a⁻¹)
    (hB : MatP d MB = matOf φ b) (hBi : MatP d MBi = matOf φ b⁻¹) (c : ℕ) :
    MatP d (letF MA MAi MB MBi c) = matOf φ (fF a b c) := by
  unfold letF fF
  rcases c with _ | _ | _ | c
  · exact hA
  · exact hAi
  · exact hB
  · have e0 : Nat.beq (c + 3) 0 = false := rfl
    have e1 : Nat.beq (c + 3) 1 = false := rfl
    have e2 : Nat.beq (c + 3) 2 = false := rfl
    rw [e0, e1, e2]
    simpa using hBi

theorem MatP_mwF (hA : MatP d MA = matOf φ a) (hAi : MatP d MAi = matOf φ a⁻¹)
    (hB : MatP d MB = matOf φ b) (hBi : MatP d MBi = matOf φ b⁻¹) :
    ∀ (w : List ℕ) (acc : ℕ),
      MatP d (mwF d MA MAi MB MBi w acc) = matOf φ (wE (fF a b) w) * MatP d acc
  | [], acc => by
    change MatP d acc = _
    rw [wE_nil, matOf_one, one_mul]
  | c :: w, acc => by
    change MatP d (strictN (mulW d (letF MA MAi MB MBi c) acc) (mwF d MA MAi MB MBi w)) = _
    rw [strictN_eq, MatP_mwF hA hAi hB hBi w, mulW_eq, MatP_mul, MatP_letF hA hAi hB hBi,
      wE_cons, matOf_mul, mul_assoc]

theorem mwF_lt (MA MAi MB MBi : ℕ) :
    ∀ (w : List ℕ) (acc : ℕ), acc < 2 ^ (d * d) → mwF d MA MAi MB MBi w acc < 2 ^ (d * d)
  | [], _, h => h
  | c :: w, acc, _ => by
    change strictN (mulW d (letF MA MAi MB MBi c) acc) (mwF d MA MAi MB MBi w) < _
    rw [strictN_eq]
    exact mwF_lt MA MAi MB MBi w _ (mulW_eq d _ acc ▸ mulF_lt d _ _)

theorem eqF_model (hφ : Function.Injective φ) (hA : MatP d MA = matOf φ a)
    (hAi : MatP d MAi = matOf φ a⁻¹) (hB : MatP d MB = matOf φ b)
    (hBi : MatP d MBi = matOf φ b⁻¹) :
    Model letL (eqF d MA MAi MB MBi) (wE (fF a b)) ∧
      ∀ u, chW letL u = true → wE (fF a b) u = 1 → eqF d MA MAi MB MBi u [] = true := by
  have key : ∀ u, MatP d (mwF d MA MAi MB MBi u (idF d)) = matOf φ (wE (fF a b) u) := fun u => by
    rw [MatP_mwF hA hAi hB hBi, MatP_id, mul_one]
  refine ⟨Model.of_wE _ fun u v _ _ h => ?_, fun u _ h => ?_⟩
  · have e := congrArg (MatP d) (Nat.eq_of_beq_eq_true h)
    rw [key, key] at e
    exact hφ (Units.ext e)
  · have e : MatP d (mwF d MA MAi MB MBi u (idF d)) = MatP d (idF d) := by
      rw [key, h, matOf_one, MatP_id]
    have e' := MatP_inj e (mwF_lt MA MAi MB MBi u _ (idF_lt d)) (idF_lt d)
    unfold eqF
    rw [e']
    exact Nat.beq_refl _

end Kit

theorem kitF_sound {d : ℕ} {φ : G →* GL (Fin d) (ZMod 2)} (hφ : Function.Injective φ) {a b : G}
    {MA MB eA eB : ℕ} (hA : MatP d MA = matOf φ a) (hB : MatP d MB = matOf φ b)
    {k : (List ℕ → List ℕ → Bool) → Bool} (h : kitF d MA MB eA eB k = true) :
    ∃ E, k E = true ∧ Model letL E (wE (fF a b)) ∧
      ∀ u, chW letL u = true → wE (fF a b) u = 1 → E u [] = true := by
  unfold kitF at h
  rw [strictB_eq, strictB_eq, andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨h1, h2, hk⟩ := h
  have e1 : MatP d MA * MatP d (powK d MA (Nat.pred eA)) = 1 := by
    rw [← MatP_mul, Nat.eq_of_beq_eq_true h1, MatP_id]
  have e2 : MatP d MB * MatP d (powK d MB (Nat.pred eB)) = 1 := by
    rw [← MatP_mul, Nat.eq_of_beq_eq_true h2, MatP_id]
  obtain ⟨hM, hc⟩ := eqF_model hφ hA (MatP_inv_of hA e1) hB (MatP_inv_of hB e2)
  exact ⟨_, hk, hM, hc⟩

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native

theorem MatP_seedA {D : VecData} {cs : List Char} {M : ℕ} (hs : D.seedA = String.ofList cs)
    (h : m1Bind cs D.d M = true) : MatP D.d M = mA D := by
  unfold MatP
  rw [← bind_sound h, ← hs]
  exact rowsMatrix_rowsOfPayload _ _

theorem MatP_seedB {D : VecData} {cs : List Char} {M : ℕ} (hs : D.seedB = String.ofList cs)
    (h : m1Bind cs D.d M = true) : MatP D.d M = mB D := by
  unfold MatP
  rw [← bind_sound h, ← hs]
  exact rowsMatrix_rowsOfPayload _ _

private theorem det_ne_of_mul {d : ℕ} {X Y : Matrix (Fin d) (Fin d) (ZMod 2)} (h : X * Y = 1) :
    X.det ≠ 0 := by
  intro h0
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

theorem kitF_J (D : VecData) {csA csB : List Char} {MA MB eA eB : ℕ}
    (hsA : D.seedA = String.ofList csA) (hsB : D.seedB = String.ofList csB)
    (hbA : m1Bind csA D.d MA = true) (hbB : m1Bind csB D.d MB = true)
    {k : (List ℕ → List ℕ → Bool) → Bool} (h : kitF D.d MA MB eA eB k = true) :
    ∃ E, k E = true ∧ Model letL E (wE (fF (a D) (b D))) ∧
      ∀ u, chW letL u = true → wE (fF (a D) (b D)) u = 1 → E u [] = true := by
  have hMA := MatP_seedA hsA hbA
  have hMB := MatP_seedB hsB hbB
  have hdet : (mA D).det ≠ 0 ∧ (mB D).det ≠ 0 := by
    unfold kitF at h
    rw [strictB_eq, strictB_eq, andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true] at h
    refine ⟨det_ne_of_mul (Y := MatP D.d (powK D.d MA (Nat.pred eA))) ?_,
      det_ne_of_mul (Y := MatP D.d (powK D.d MB (Nat.pred eB))) ?_⟩
    · rw [← hMA, ← MatP_mul, Nat.eq_of_beq_eq_true h.1, MatP_id]
    · rw [← hMB, ← MatP_mul, Nat.eq_of_beq_eq_true h.2.1, MatP_id]
  have hA : MatP D.d MA = matOf (J D).subtype (a D) := by
    rw [matOf, Subgroup.subtype_apply, a, Subtype.coe_mk, gA, dif_pos hdet.1,
      Matrix.GeneralLinearGroup.val_mkOfDetNeZero, hMA]
  have hB : MatP D.d MB = matOf (J D).subtype (b D) := by
    rw [matOf, Subgroup.subtype_apply, b, Subtype.coe_mk, gB, dif_pos hdet.2,
      Matrix.GeneralLinearGroup.val_mkOfDetNeZero, hMB]
  exact kitF_sound Subtype.val_injective hA hB h

end CFSG.KD.SporCov

end
