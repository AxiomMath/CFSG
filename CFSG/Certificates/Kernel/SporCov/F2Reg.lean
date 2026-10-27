module

public import Certificates.Data.Kernel.SporCov.F2Reg
public import CFSG.Certificates.Kernel.SporCov.F2Kit
public import CFSG.Certificates.Kernel.SporCov.PCl

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

theorem letRL_iff (n c : ℕ) : letRL n c = true ↔ c < 4 + n := by
  unfold letRL
  rw [Nat.blt_eq]
  rfl

theorem letR_of_lt {MA MAi MB MBi : ℕ} (Ms : List ℕ) {c : ℕ} (hc : c < 4) :
    letR MA MAi MB MBi Ms c = letF MA MAi MB MBi c := by
  unfold letR
  have e : Nat.blt c 4 = true := by
    rw [Nat.blt_eq]
    exact hc
  rw [e]

theorem letR_of_ge {MA MAi MB MBi : ℕ} (Ms : List ℕ) {c : ℕ} (hc : 4 ≤ c) :
    letR MA MAi MB MBi Ms c = nthN Ms (c - 4) := by
  unfold letR
  have e : Nat.blt c 4 = false := by
    rw [Bool.eq_false_iff, ne_eq, Nat.blt_eq]
    omega
  rw [e]
  rfl

variable {G : Type} [Group G]

section Kit

variable {d : ℕ} {φ : G →* GL (Fin d) (ZMod 2)} {MA MAi MB MBi : ℕ} {Ms : List ℕ}

theorem MatP_mwR {f : ℕ → G} {L : ℕ → Bool}
    (hf : ∀ c, L c = true → MatP d (letR MA MAi MB MBi Ms c) = matOf φ (f c)) :
    ∀ (w : List ℕ) (acc : ℕ), chW L w = true →
      MatP d (mwR d MA MAi MB MBi Ms w acc) = matOf φ (wE f w) * MatP d acc
  | [], acc, _ => by
    change MatP d acc = _
    rw [wE_nil, matOf_one, one_mul]
  | c :: w, acc, h => by
    rw [chW_cons, Bool.and_eq_true] at h
    change MatP d (strictN (mulW d (letR MA MAi MB MBi Ms c) acc) (mwR d MA MAi MB MBi Ms w)) = _
    rw [strictN_eq, MatP_mwR hf w _ h.2, mulW_eq, MatP_mul, hf c h.1, wE_cons, matOf_mul,
      mul_assoc]

theorem mwR_lt : ∀ (w : List ℕ) (acc : ℕ), acc < 2 ^ (d * d) →
    mwR d MA MAi MB MBi Ms w acc < 2 ^ (d * d)
  | [], _, h => h
  | c :: w, acc, _ => by
    change strictN (mulW d (letR MA MAi MB MBi Ms c) acc) (mwR d MA MAi MB MBi Ms w) < _
    rw [strictN_eq]
    exact mwR_lt w _ (mulW_eq d _ acc ▸ mulF_lt d _ _)

@[expose] noncomputable def fR (a b : G) (g : ℕ → G) (c : ℕ) : G :=
  if c < 4 then fF a b c else g (c - 4)

theorem MatP_letR {a b : G} (hA : MatP d MA = matOf φ a) (hAi : MatP d MAi = matOf φ a⁻¹)
    (hB : MatP d MB = matOf φ b) (hBi : MatP d MBi = matOf φ b⁻¹) {g : ℕ → G} {i : ℕ}
    (hg : ∀ j < i, MatP d (nthN Ms j) = matOf φ (g j)) :
    ∀ c, letRL i c = true → MatP d (letR MA MAi MB MBi Ms c) = matOf φ (fR a b g c) := by
  intro c hc
  rw [letRL_iff] at hc
  unfold fR
  by_cases h4 : c < 4
  · rw [if_pos h4, letR_of_lt Ms h4]
    exact MatP_letF hA hAi hB hBi c
  · rw [if_neg h4, letR_of_ge Ms (by omega)]
    exact hg _ (by omega)

theorem exists_regs {a b : G} (hA : MatP d MA = matOf φ a) (hAi : MatP d MAi = matOf φ a⁻¹)
    (hB : MatP d MB = matOf φ b) (hBi : MatP d MBi = matOf φ b⁻¹) {Rg : List (List ℕ)} {n : ℕ}
    (hR : ∀ i < n, regOK d MA MAi MB MBi Ms Rg i = true) :
    ∀ i ≤ n, ∃ g : ℕ → G, ∀ j < i, MatP d (nthN Ms j) = matOf φ (g j)
  | 0, _ => ⟨fun _ => 1, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | i + 1, hi => by
    obtain ⟨g, hg⟩ := exists_regs hA hAi hB hBi hR i (by omega)
    have h := hR i (by omega)
    unfold regOK at h
    rw [Bool.and_eq_true] at h
    have e := MatP_mwR (MatP_letR hA hAi hB hBi hg) (nthW Rg i) (idF d) h.1
    rw [MatP_id, mul_one] at e
    refine ⟨fun j => if j < i then g j else wE (fR a b g) (nthW Rg i), fun j hj => ?_⟩
    beta_reduce
    by_cases hji : j < i
    · rw [if_pos hji]
      exact hg j hji
    · have ej : j = i := by omega
      subst ej
      rw [if_neg (lt_irrefl j), ← Nat.eq_of_beq_eq_true h.2]
      exact e

end Kit

theorem kitR_sound {d : ℕ} {φ : G →* GL (Fin d) (ZMod 2)} (hφ : Function.Injective φ) {a b : G}
    {MA MB eA eB : ℕ} (hA : MatP d MA = matOf φ a) (hB : MatP d MB = matOf φ b) {Ms : List ℕ}
    {Rg : List (List ℕ)} {n : ℕ} {k : (List ℕ → List ℕ → Bool) → (List ℕ → ℕ) → Bool}
    (h : kitR d MA MB eA eB Ms Rg n k = true) :
    ∃ (E : List ℕ → List ℕ → Bool) (K : List ℕ → ℕ) (f : ℕ → G), k E K = true ∧
      Model (letRL n) E (wE f) ∧
      (∀ u, chW (letRL n) u = true → wE f u = 1 → E u [] = true) ∧
      (∀ u v, chW (letRL n) u = true → chW (letRL n) v = true → wE f u = wE f v → K u = K v) ∧
      ∀ c < 4, f c = fF a b c := by
  unfold kitR at h
  rw [strictB_eq, strictB_eq, andB_eq, andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true] at h
  obtain ⟨h1, h2, hR, hk⟩ := h
  set MAi := powK d MA (Nat.pred eA)
  set MBi := powK d MB (Nat.pred eB)
  have e1 : MatP d MA * MatP d MAi = 1 := by
    rw [← MatP_mul, Nat.eq_of_beq_eq_true h1, MatP_id]
  have e2 : MatP d MB * MatP d MBi = 1 := by
    rw [← MatP_mul, Nat.eq_of_beq_eq_true h2, MatP_id]
  have hAi := MatP_inv_of hA e1
  have hBi := MatP_inv_of hB e2
  have hR' := (allLt_iff _ n).1 hR
  obtain ⟨g, hg⟩ := exists_regs hA hAi hB hBi hR' n le_rfl
  have key : ∀ u, chW (letRL n) u = true →
      MatP d (keyR d MA MAi MB MBi Ms u) = matOf φ (wE (fR a b g) u) := fun u hu => by
    unfold keyR
    rw [MatP_mwR (MatP_letR hA hAi hB hBi hg) u _ hu, MatP_id, mul_one]
  have hK : ∀ u v, chW (letRL n) u = true → chW (letRL n) v = true →
      wE (fR a b g) u = wE (fR a b g) v → keyR d MA MAi MB MBi Ms u = keyR d MA MAi MB MBi Ms v :=
    fun u v hu hv e => MatP_inj (by rw [key u hu, key v hv, e]) (mwR_lt u _ (idF_lt d))
      (mwR_lt v _ (idF_lt d))
  refine ⟨_, _, fR a b g, hk, Model.of_wE _ fun u v hu hv h => ?_, fun u hu h => ?_, hK,
    fun c hc => if_pos hc⟩
  · have e := congrArg (MatP d) (Nat.eq_of_beq_eq_true h)
    rw [key u hu, key v hv] at e
    exact hφ (Units.ext e)
  · unfold eqR
    rw [hK u [] hu (chW_nil _) (by rw [h, wE_nil])]
    exact Nat.beq_refl _

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native

private theorem det_ne_of_mul {d : ℕ} {X Y : Matrix (Fin d) (Fin d) (ZMod 2)} (h : X * Y = 1) :
    X.det ≠ 0 := by
  intro h0
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

theorem kitR_J (D : VecData) {csA csB : List Char} {MA MB eA eB : ℕ}
    (hsA : D.seedA = String.ofList csA) (hsB : D.seedB = String.ofList csB)
    (hbA : m1Bind csA D.d MA = true) (hbB : m1Bind csB D.d MB = true) {Ms : List ℕ}
    {Rg : List (List ℕ)} {n : ℕ} {k : (List ℕ → List ℕ → Bool) → (List ℕ → ℕ) → Bool}
    (h : kitR D.d MA MB eA eB Ms Rg n k = true) :
    ∃ (E : List ℕ → List ℕ → Bool) (K : List ℕ → ℕ) (f : ℕ → ↥(J D)), k E K = true ∧
      Model (letRL n) E (wE f) ∧
      (∀ u, chW (letRL n) u = true → wE f u = 1 → E u [] = true) ∧
      (∀ u v, chW (letRL n) u = true → chW (letRL n) v = true → wE f u = wE f v → K u = K v) ∧
      ∀ c < 4, f c = fF (a D) (b D) c := by
  have hMA := MatP_seedA hsA hbA
  have hMB := MatP_seedB hsB hbB
  have hdet : (mA D).det ≠ 0 ∧ (mB D).det ≠ 0 := by
    unfold kitR at h
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
  exact kitR_sound Subtype.val_injective hA hB h

end CFSG.KD.SporCov

end
