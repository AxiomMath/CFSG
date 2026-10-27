module

public import CFSG.Certificates.Kernel.Misc.GL52MatCode
import CFSG.Certificates.Kernel.Misc.GL52MatProved
import CFSG.Certificates.Kernel.Misc.GL52MatElimProved
public import CFSG.Certificates.Kernel.Misc.KGrpSound
public import Mathlib.LinearAlgebra.Matrix.Rank

public section

namespace CFSG.KC.Misc.GLM

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.Clos

theorem mmulK_mcode (A B : Mat) : mmulK (mcode A) (mcode B) = mcode (A * B) :=
  mmulK_mcode_proved A B

theorem mcode_one : mcode 1 = idK := by
  decide +kernel

theorem mcode_add (A B : Mat) : Nat.xor (mcode A) (mcode B) = mcode (A + B) :=
  mcode_add_proved A B

theorem mcode_inj : Function.Injective mcode :=
  mcode_inj_proved

theorem rankK_mcode (A : Mat) : rankK (mcode A) = A.rank :=
  rankK_mcode_proved A

theorem solCnt_sound (ps : List (Mat × Mat)) :
    Nat.card {g : GL (Fin 5) (ZMod 2) // ∀ p ∈ ps, (g : Mat) * p.1 = p.2 * (g : Mat)} =
      unitCntK (elimK (ps.map fun p => (mcode p.1, mcode p.2)) (25 * ps.length) 25).2 :=
  solCnt_sound_proved ps

theorem mcode_zero : mcode 0 = 0 := by
  simp [mcode]

@[expose] def peval (A : Mat) (cs : List (ZMod 2)) : Mat :=
  cs.foldr (fun c acc => acc * A + c • 1) 0

@[expose] def bitZ (b : Bool) : ZMod 2 := if b then 1 else 0

theorem pevalK_mcode (A : Mat) (bs : List Bool) :
    pevalK (mcode A) bs = mcode (peval A (bs.map bitZ)) := by
  induction bs with
  | nil => exact mcode_zero.symm
  | cons b bs ih =>
    change Nat.xor (mmulK (pevalK (mcode A) bs) (mcode A))
      (Bool.rec (motive := fun _ => ℕ) 0 idK b) = _
    rw [ih, mmulK_mcode]
    cases b
    · change Nat.xor _ 0 = _
      rw [show ∀ x : ℕ, Nat.xor x 0 = x from fun x => Nat.xor_zero x]
      simp [peval, bitZ]
    · change Nat.xor _ idK = _
      rw [← mcode_one, mcode_add]
      simp [peval, bitZ]

@[expose] noncomputable def invS (A : Mat) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0
    (fun m acc => acc * 8 + (peval A ((polyBits (m + 1)).map bitZ)).rank) 63

theorem invK_mcode (A : Mat) : invK (mcode A) = invS A := by
  have key : ∀ k, (Nat.rec (motive := fun _ => ℕ) 0
      (fun m acc => Nat.add (Nat.mul acc 8) (rankK (pevalK (mcode A) (polyBits (Nat.succ m)))))
      k : ℕ) = Nat.rec (motive := fun _ => ℕ) 0
      (fun m acc => acc * 8 + (peval A ((polyBits (m + 1)).map bitZ)).rank) k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      change Nat.add (Nat.mul _ 8) (rankK (pevalK (mcode A) (polyBits (Nat.succ k)))) =
        _ * 8 + _
      rw [ih, pevalK_mcode, rankK_mcode]
      rfl
  exact key 63

theorem ordGoK_iff (g : GL (Fin 5) (ZMod 2)) (k j : ℕ) :
    ordGoK (mcode (g : Mat)) k (mcode ((g ^ j : GL (Fin 5) (ZMod 2)) : Mat)) = true ↔
      (∀ i < k, g ^ (j + i) ≠ 1) ∧ g ^ (j + k) = 1 := by
  have hc : ∀ h : GL (Fin 5) (ZMod 2), Nat.beq (mcode (h : Mat)) idK = true ↔ h = 1 := by
    intro h
    rw [← mcode_one, beq_iff_eq']
    constructor
    · intro e
      exact Units.ext (by simpa using mcode_inj e)
    · rintro rfl
      simp
  induction k generalizing j with
  | zero =>
    change Nat.beq (mcode ((g ^ j : GL (Fin 5) (ZMod 2)) : Mat)) idK = true ↔ _
    rw [hc]
    simp
  | succ k ih =>
    change letB (mcode ((g ^ j : GL (Fin 5) (ZMod 2)) : Mat)) (fun a => andB (notB (Nat.beq a idK))
      (ordGoK (mcode (g : Mat)) k (mmulK a (mcode (g : Mat))))) = true ↔ _
    rw [letB_eq, mmulK_mcode, ← Units.val_mul, ← pow_succ, KG.andB_iff, KG.notB_iff, hc]
    refine (and_congr_right fun _ => ih (j + 1)).trans ?_
    constructor
    · rintro ⟨h0, h1, h2⟩
      refine ⟨fun i hi => ?_, by rwa [show j + (k + 1) = j + 1 + k by omega]⟩
      rcases i with _ | i
      · simpa using h0
      · have := h1 i (by omega)
        rwa [show j + 1 + i = j + (i + 1) by omega] at this
    · rintro ⟨h1, h2⟩
      refine ⟨by simpa using h1 0 (by omega), fun i hi => ?_, by
        rwa [show j + 1 + k = j + (k + 1) by omega]⟩
      have := h1 (i + 1) (by omega)
      rwa [show j + (i + 1) = j + 1 + i by omega] at this
where
  beq_iff_eq' {a b : ℕ} : Nat.beq a b = true ↔ a = b :=
    ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl a⟩

theorem ordK_iff (g : GL (Fin 5) (ZMod 2)) {m : ℕ} (hm : 0 < m) :
    ordK (mcode (g : Mat)) m = true ↔ orderOf g = m := by
  have h := ordGoK_iff g (m - 1) 1
  rw [pow_one] at h
  rw [ordK, Nat.sub_eq, h, orderOf_eq_iff hm, show 1 + (m - 1) = m by omega]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h2, fun i hi hi0 => ?_⟩
    have := h1 (i - 1) (by omega)
    rwa [show 1 + (i - 1) = i by omega] at this
  · rintro ⟨h2, h1⟩
    exact ⟨fun i hi => h1 (1 + i) (by omega) (by omega), h2⟩

theorem unitCntR_add (L : List ℕ) (lo a b : ℕ) :
    unitCntR L lo (a + b) = unitCntR L lo a + unitCntR L (lo + a) b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    change Nat.add (unitCntR L lo (a + b)) _ = unitCntR L lo a + Nat.add (unitCntR L (lo + a) b) _
    have e : Nat.add lo (Nat.add a b) = Nat.add (lo + a) b := by
      simp only [Nat.add_eq]
      omega
    rw [ih, e]
    simp only [Nat.add_eq]
    omega

end CFSG.KC.Misc.GLM

end
