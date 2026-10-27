module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84B0ModBits
public import Certificates.Data.Asc82NormA6

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace T84Mod

open Matrix Certificates.Asc82NormA6
open Certificates.A5GL42 (Mat4)

@[expose] def mS : Mat4 := Matrix.of ![![0, 0, 1, 0], ![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 0, 1]]

@[expose] def mT : Mat4 := Matrix.of ![![1, 0, 0, 1], ![1, 1, 1, 0], ![0, 1, 0, 1], ![0, 0, 1, 1]]

theorem rho_sigma_eq : rho sigma = mS := by
  decide +kernel

theorem rho_tau_eq : rho tau = mT := by
  decide +kernel

@[expose] def relBase : Fin 6 → List Bool := ![
  [true], [false], [true, false, false, false, false, true, true, false],
  [true, true, false, false, false, false], [true, false, true, false, false, false, false],
  [false, true, true, false, false, false, false, true, true, false]]

@[expose] def relExp : Fin 6 → ℕ := ![3, 5, 2, 4, 3, 3]

@[expose] def relWords (i : Fin 6) : List Bool :=
  List.flatten (List.replicate (relExp i) (relBase i))

theorem rel_words {M : Type*} [Monoid M] {x y : M} (h : Rel x y) (i : Fin 6) :
    ((relWords i).map fun c => if c then x else y).prod = 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  fin_cases i
  · simpa [relWords, relBase, relExp, pow_succ, mul_assoc] using h1
  · simpa [relWords, relBase, relExp, pow_succ, mul_assoc] using h2
  · simpa [relWords, relBase, relExp, pow_succ, mul_assoc] using h3
  · simpa [relWords, relBase, relExp, pow_succ, mul_assoc] using h4
  · simpa [relWords, relBase, relExp, pow_succ, mul_assoc] using h5
  · simpa [relWords, relBase, relExp, pow_succ, mul_assoc] using h6

theorem cocycle_eq {U V : Mat4} (h : Rel (blk (rho sigma) U) (blk (rho tau) V)) (i : Fin 6) :
    wfox (rho sigma) (rho tau) U V (relWords i) = 0 := by
  have h1 := rel_words h i
  rw [blk_word, ← blk_one] at h1
  exact (blk_inj h1).2

abbrev UIdx := Fin 2 × Fin 4 × Fin 4

abbrev EIdx := Fin 6 × Fin 4 × Fin 4

@[expose] def pk (p : Mat4 × Mat4) : UIdx → ZMod 2 := fun i =>
  if i.1 = 0 then p.1 i.2.1 i.2.2 else p.2 i.2.1 i.2.2

@[expose] def upk (x : UIdx → ZMod 2) : Mat4 × Mat4 :=
  (Matrix.of fun k l => x (0, k, l), Matrix.of fun k l => x (1, k, l))

theorem upk_pk (p : Mat4 × Mat4) : upk (pk p) = p := by
  refine Prod.ext ?_ ?_ <;> ext k l <;> simp [upk, pk]

@[expose] def uflat (i : UIdx) : ℕ := (i.1 : ℕ) * 16 + (i.2.1 : ℕ) * 4 + (i.2.2 : ℕ)

@[expose] def eflat (r : EIdx) : ℕ := (r.1 : ℕ) * 16 + (r.2.1 : ℕ) * 4 + (r.2.2 : ℕ)

@[expose] def foxVec (x : UIdx → ZMod 2) : EIdx → ZMod 2 := fun r =>
  wfox mS mT (upk x).1 (upk x).2 (relWords r.1) r.2.1 r.2.2

@[expose] def cob (m : Mat4) : Mat4 × Mat4 := (m * mS + mS * m, m * mT + mT * m)

@[expose] def mOf (v : Fin 4 × Fin 4 → ZMod 2) : Mat4 := Matrix.of fun k l => v (k, l)

@[expose] def Pcols : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 29599, 0, 9501, 6362, 0,
   0, 0, 0, 0, 1, 2, 4, 8,
   24, 37, 78, 29467, 29186, 625, 30522, 2242]

@[expose] def Qcols : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0,
   0, 85, 0, 0, 0, 0, 0, 33300,
   0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0,
   0, 771, 0, 1334, 0, 0, 0, 5242,
   0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 71333, 0,
   524305, 0, 0, 66732, 0, 0, 0, 0,
   0, 0, 0, 0, 66060, 656885, 791037, 591529,
   0, 0, 0, 0, 0, 853950, 0, 0,
   0, 463865, 857592, 0, 0, 0, 463921, 67162]

@[expose] def Pm : Matrix (Fin 4 × Fin 4) UIdx (ZMod 2) := Matrix.of fun k i =>
  if (Pcols.getD (uflat i) 0).testBit (4 * (k.1 : ℕ) + (k.2 : ℕ)) then 1 else 0

@[expose] def Qm : Matrix UIdx EIdx (ZMod 2) := Matrix.of fun u r =>
  if (Qcols.getD (eflat r) 0).testBit (uflat u) then 1 else 0

theorem pk_add (p q : Mat4 × Mat4) : pk (p + q) = pk p + pk q := by
  ext i
  simp only [pk, Pi.add_apply, Prod.fst_add, Prod.snd_add, Matrix.add_apply]
  split_ifs <;> rfl

theorem upk_add (x y : UIdx → ZMod 2) : upk (x + y) = upk x + upk y := by
  refine Prod.ext ?_ ?_ <;> ext k l <;> simp [upk]

theorem cob_add (m n : Mat4) : cob (m + n) = cob m + cob n := by
  refine Prod.ext ?_ ?_ <;> simp only [cob, Prod.fst_add, Prod.snd_add, add_mul, mul_add] <;> abel

theorem mOf_add (v w : Fin 4 × Fin 4 → ZMod 2) : mOf (v + w) = mOf v + mOf w := by
  ext k l
  simp [mOf]

theorem foxVec_add (x y : UIdx → ZMod 2) : foxVec (x + y) = foxVec x + foxVec y := by
  ext r
  simp only [foxVec, upk_add, Prod.fst_add, Prod.snd_add, wfox_add, Pi.add_apply, Matrix.add_apply]

theorem bmat_mS : bmat 33300 = mS := by
  decide +kernel

theorem bmat_mT : bmat 51833 = mT := by
  decide +kernel

@[expose] def foxCode (x : UIdx → ZMod 2) (i : Fin 6) : ℕ :=
  (wpairB 33300 51833 (codeOf (upk x).1) (codeOf (upk x).2) (relWords i)).2

@[expose] def foxVecB (x : UIdx → ZMod 2) : EIdx → ZMod 2 := fun r =>
  if (foxCode x r.1).testBit (4 * (r.2.1 : ℕ) + (r.2.2 : ℕ)) then 1 else 0

theorem foxVec_eq_B (x : UIdx → ZMod 2) : foxVec x = foxVecB x := by
  funext r
  have h := (wpairB_spec 33300 51833 (codeOf (upk x).1) (codeOf (upk x).2) (relWords r.1)).2
  rw [bmat_codeOf, bmat_codeOf, bmat_mS, bmat_mT] at h
  have e := congrFun (congrFun h r.2.1) r.2.2
  simp only [bmat, Matrix.of_apply] at e
  simp only [foxVec, foxVecB, foxCode]
  exact e.symm

theorem mOf_Pm_single (i : UIdx) :
    mOf (Pm *ᵥ (Pi.single i (1 : ZMod 2) : UIdx → ZMod 2)) = bmat (Pcols.getD (uflat i) 0) := by
  rw [Matrix.mulVec_single_one]
  ext k l
  simp [mOf, Matrix.col, Pm, bmat]

theorem key_unit_U : ∀ k l : Fin 4,
    (Pi.single ((0 : Fin 2), k, l) (1 : ZMod 2) : UIdx → ZMod 2) +
      pk (cob (bmat (Pcols.getD (uflat ((0 : Fin 2), k, l)) 0))) =
        Qm *ᵥ foxVecB (Pi.single ((0 : Fin 2), k, l) (1 : ZMod 2)) := by
  decide +kernel

theorem key_unit_V : ∀ k l : Fin 4,
    (Pi.single ((1 : Fin 2), k, l) (1 : ZMod 2) : UIdx → ZMod 2) +
      pk (cob (bmat (Pcols.getD (uflat ((1 : Fin 2), k, l)) 0))) =
        Qm *ᵥ foxVecB (Pi.single ((1 : Fin 2), k, l) (1 : ZMod 2)) := by
  decide +kernel

theorem key_unit : ∀ i : UIdx, (Pi.single i (1 : ZMod 2) : UIdx → ZMod 2) +
    pk (cob (mOf (Pm *ᵥ (Pi.single i (1 : ZMod 2) : UIdx → ZMod 2)))) =
      Qm *ᵥ foxVec (Pi.single i (1 : ZMod 2)) := by
  rintro ⟨i, k, l⟩
  rw [foxVec_eq_B, mOf_Pm_single]
  fin_cases i
  · exact key_unit_U k l
  · exact key_unit_V k l

theorem key (x : UIdx → ZMod 2) : x + pk (cob (mOf (Pm *ᵥ x))) = Qm *ᵥ foxVec x := by
  let L₁ : (UIdx → ZMod 2) →+ (UIdx → ZMod 2) :=
    AddMonoidHom.mk' (fun x => x + pk (cob (mOf (Pm *ᵥ x)))) (by
      intro x y
      simp only [Matrix.mulVec_add, mOf_add, cob_add, pk_add]
      abel)
  let L₂ : (UIdx → ZMod 2) →+ (UIdx → ZMod 2) :=
    AddMonoidHom.mk' (fun x => Qm *ᵥ foxVec x) (by
      intro x y
      simp only [foxVec_add, Matrix.mulVec_add])
  have hL : L₁ = L₂ := by
    refine AddMonoidHom.functions_ext _ L₁ L₂ (fun i a => ?_)
    rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a with rfl | rfl
    · rw [Pi.single_zero, map_zero, map_zero]
    · exact key_unit i
  exact DFunLike.congr_fun hL x

theorem h1_vanish {U V : Mat4} (h : Rel (blk (rho sigma) U) (blk (rho tau) V)) :
    ∃ m : Mat4, U = m * rho sigma + rho sigma * m ∧ V = m * rho tau + rho tau * m := by
  rw [rho_sigma_eq, rho_tau_eq] at h ⊢
  have hfox : foxVec (pk (U, V)) = 0 := by
    ext r
    have := cocycle_eq (U := U) (V := V) (by rw [rho_sigma_eq, rho_tau_eq]; exact h) r.1
    rw [rho_sigma_eq, rho_tau_eq] at this
    simp only [foxVec, upk_pk, this, Matrix.zero_apply, Pi.zero_apply]
  have hk := key (pk (U, V))
  rw [hfox, Matrix.mulVec_zero] at hk
  refine ⟨mOf (Pm *ᵥ pk (U, V)), ?_⟩
  have hcob : pk (U, V) = pk (cob (mOf (Pm *ᵥ pk (U, V)))) := by
    funext i
    have hi := congrFun hk i
    simp only [Pi.add_apply, Pi.zero_apply] at hi
    exact (by decide : ∀ a b : ZMod 2, a + b = 0 → a = b) _ _ hi
  have := congrArg upk hcob
  rw [upk_pk, upk_pk] at this
  exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩

end T84Mod

end CFSG.OddStandard.SmallF3.Omega
