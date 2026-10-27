module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434G28Check

set_option linter.unusedSectionVars false

public section

namespace CFSG.AGLEmbedding.KFactProofs.G28

open CFSG.Quasithin CFSG.RankThree.PartTwo.Sec4.Item434G28

@[expose] def frobGF8 : GF8 →+* GF8 where
  toFun a := a ^ 2
  map_one' := by decide
  map_mul' := by decide
  map_zero' := by decide
  map_add' := by decide

@[expose] def frobM (A : Matrix (Fin 6) (Fin 6) GF8) : Matrix (Fin 6) (Fin 6) GF8 :=
  A.map frobGF8

theorem frobM_mul (A B : Matrix (Fin 6) (Fin 6) GF8) : frobM (A * B) = frobM A * frobM B :=
  Matrix.map_mul (f := frobGF8)

theorem frobM_one : frobM (1 : Matrix (Fin 6) (Fin 6) GF8) = 1 :=
  Matrix.map_one _ (map_zero frobGF8) (map_one frobGF8)

@[expose] def frobCode (A : Array ℕ) : Array ℕ := A.map fun a => GF8.mulNat a a

theorem getElem!_frobCode (A : Array ℕ) {i : ℕ} (hi : i < A.size) :
    (frobCode A)[i]! = GF8.mulNat A[i]! A[i]! := by
  unfold frobCode
  rw [getElem!_pos _ i (by simpa using hi), getElem!_pos A i hi, Array.getElem_map]

theorem valid_frobCode {A : Array ℕ} (hA : Valid A) : Valid (frobCode A) := by
  refine ⟨by simp [frobCode, hA.1], fun i hi => ?_⟩
  rw [getElem!_frobCode A (by rw [hA.1]; exact hi)]
  exact mulNat_lt' (hA.2 i hi) (hA.2 i hi)

theorem decode_frobCode {A : Array ℕ} (hA : Valid A) :
    decode (frobCode A) = frobM (decode A) := by
  ext i j
  have hi := i.2
  have hj := j.2
  have hlt : 6 * i.val + j.val < 36 := by omega
  simp only [frobM, decode, Matrix.of_apply, Matrix.map_apply]
  rw [getElem!_frobCode A (by rw [hA.1]; exact hlt), ofNat'_mulNat' (hA.2 _ hlt) (hA.2 _ hlt)]
  show _ = GF8.ofNat' A[6 * i.val + j.val]! ^ 2
  rw [sq]

theorem frobCode_mulCode {A B : Array ℕ} (hA : Valid A) (hB : Valid B) :
    frobCode (mulCode A B) = mulCode (frobCode A) (frobCode B) := by
  apply eq_of_decode_eq (valid_frobCode (valid_mulCode hA hB))
    (valid_mulCode (valid_frobCode hA) (valid_frobCode hB))
  rw [decode_frobCode (valid_mulCode hA hB), decode_mulCode hA hB, frobM_mul,
    decode_mulCode (valid_frobCode hA) (valid_frobCode hB), decode_frobCode hA,
    decode_frobCode hB]

theorem frobCode_idCode : frobCode idCode = idCode := by
  apply eq_of_decode_eq (valid_frobCode valid_idCode) valid_idCode
  rw [decode_frobCode valid_idCode, decode_idCode, frobM_one]

theorem frobCode_rootCode : ∀ r : Fin 12, ∀ t : Fin 8,
    frobCode (rootCode r t) = rootCode r (GF8.mulNat t t) := by
  decide +kernel

theorem frobCode_letterCode (n : ℕ) :
    frobCode (letterCode n) = letterCode (8 * (n / 8) + GF8.mulNat (n % 8) (n % 8)) := by
  have h8 : n % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have hm : GF8.mulNat (n % 8) (n % 8) < 8 := mulNat_lt' h8 h8
  have e1 : (8 * (n / 8) + GF8.mulNat (n % 8) (n % 8)) / 8 = n / 8 := by omega
  have e2 : (8 * (n / 8) + GF8.mulNat (n % 8) (n % 8)) % 8 = GF8.mulNat (n % 8) (n % 8) := by
    omega
  have hr : (n / 8) % 12 < 12 := Nat.mod_lt _ (by norm_num)
  rw [letterCode, letterCode, e1, e2]
  exact frobCode_rootCode ⟨(n / 8) % 12, hr⟩ ⟨n % 8, h8⟩



@[expose] def frobk : ℕ → Array ℕ → Array ℕ
  | 0, A => A
  | k + 1, A => frobCode (frobk k A)

theorem valid_frobk {A : Array ℕ} (hA : Valid A) : ∀ k, Valid (frobk k A)
  | 0 => hA
  | k + 1 => valid_frobCode (valid_frobk hA k)

theorem decode_frobk {A : Array ℕ} (hA : Valid A) :
    ∀ k, decode (frobk k A) = frobM^[k] (decode A)
  | 0 => rfl
  | k + 1 => by
    rw [frobk, decode_frobCode (valid_frobk hA k), decode_frobk hA k,
      Function.iterate_succ_apply']


@[expose] def semi (a b : Array ℕ × ℕ) : Array ℕ × ℕ :=
  (mulCode a.1 (frobk a.2 b.1), (a.2 + b.2) % 3)

@[expose] def semiOne : Array ℕ × ℕ := (idCode, 0)

end CFSG.AGLEmbedding.KFactProofs.G28
