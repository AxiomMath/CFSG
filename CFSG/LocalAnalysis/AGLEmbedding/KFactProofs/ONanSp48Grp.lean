module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSp48Rep
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherAutomorphismData

public section

namespace CFSG.AGLEmbedding.KFactProofs.Sp48

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

instance instCharPGF8 : CharP GF8 2 := by
  refine ⟨fun x => ?_⟩
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' x
  · have h2 : (2 : GF8) = 0 := by decide
    simp [h2]
  · have h2 : (2 : GF8) = 0 := by decide
    simp [h2, Nat.cast_add, Nat.cast_mul]

abbrev Sp8 : Type := StatedSp 2 GF8

@[expose] def matOf (x : Sp8) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) GF8 :=
  ((x : GL (Fin 2 ⊕ Fin 2) GF8) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) GF8)

theorem matOf_mul (x y : Sp8) : matOf (x * y) = matOf x * matOf y := rfl

theorem matOf_injective : Function.Injective matOf := fun _ _ h => Subtype.ext (Units.ext h)

@[expose] noncomputable def frobE : GF8 ≃+* GF8 := frobeniusEquiv GF8 2

theorem frobE_apply (a : GF8) : frobE a = a * a := by
  simp [frobE, frobeniusEquiv_apply, frobenius_def, sq]

@[expose] def sqM (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) GF8) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) GF8 := M.map fun a => a * a

@[expose] noncomputable def fr : MulAut Sp8 := fieldSp 2 GF8 frobE

theorem matOf_fr (x : Sp8) : matOf (fr x) = sqM (matOf x) := by
  show (matOf x).map frobE = _
  simp only [sqM]
  congr 1
  funext a
  exact frobE_apply a

theorem matOf_fr_pow (n : ℕ) (x : Sp8) : matOf ((fr ^ n) x) = sqM^[n] (matOf x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', MulAut.mul_apply, matOf_fr, ih, Function.iterate_succ_apply']

theorem sqM_iter_three (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) GF8) : sqM^[3] M = M := by
  ext i j
  have h : ∀ a : GF8, (a * a) * (a * a) * ((a * a) * (a * a)) = a := by decide
  simp only [Function.iterate_succ_apply, Function.iterate_zero, id_eq, sqM, Matrix.map_apply]
  exact h _

theorem fr_pow_three : fr ^ 3 = 1 := by
  refine MulEquiv.ext fun x => ?_
  apply matOf_injective
  rw [matOf_fr_pow, sqM_iter_three]
  rfl

@[expose] noncomputable def phi : Multiplicative (ZMod 3) →* MulAut Sp8 where
  toFun j := fr ^ (Multiplicative.toAdd j).val
  map_one' := by simp
  map_mul' a b := by
    simp only [toAdd_mul, ZMod.val_add]
    rw [← pow_add, ← pow_eq_pow_mod _ fr_pow_three]

abbrev Hh : Type := Sp8 ⋊[phi] Multiplicative (ZMod 3)

instance instFiniteHh : Finite Hh := Finite.of_equiv _ SemidirectProduct.equivProd.symm

theorem matOf_phi (j : Multiplicative (ZMod 3)) (x : Sp8) :
    matOf (phi j x) = sqM^[(Multiplicative.toAdd j).val] (matOf x) :=
  matOf_fr_pow _ x

theorem decode_frobPow {n : ℕ} {A : Array ℕ} (hA : Valid A) :
    decode (frobPow n A) = sqM^[n] (decode A) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [frobPow, decode_frobCode (valid_frobPow n hA), ih, Function.iterate_succ_apply']
    rfl

structure RepP (p : Pc) (x : Hh) : Prop where
  valid : Valid p.m
  mat : decode p.m = matOf x.left
  exp : p.j = (Multiplicative.toAdd x.right).val

theorem RepP.one : RepP oneP 1 :=
  ⟨valid_idCode, by rw [show oneP.m = idCode from rfl, decode_idCode]; rfl, by simp [oneP]⟩

theorem RepP.mul {p q : Pc} {x y : Hh} (hp : RepP p x) (hq : RepP q y) :
    RepP (mulP p q) (x * y) := by
  have hfq := valid_frobPow p.j hq.valid
  refine ⟨valid_mulCode hp.valid hfq, ?_, ?_⟩
  · show decode (mulCode p.m (frobPow p.j q.m)) = matOf (x.left * (phi x.right) y.left)
    rw [decode_mulCode hp.valid hq.valid |> fun _ => decode_mulCode hp.valid hfq,
      decode_frobPow hq.valid, hp.mat, hq.mat, hp.exp, matOf_mul, matOf_phi]
  · show (p.j + q.j) % 3 = (Multiplicative.toAdd (x.right * y.right)).val
    rw [toAdd_mul, ZMod.val_add, hp.exp, hq.exp]

theorem RepP.eq {p : Pc} {x y : Hh} (hx : RepP p x) (hy : RepP p y) : x = y := by
  have h1 : x.left = y.left := matOf_injective (hx.mat.symm.trans hy.mat)
  have h2 : x.right = y.right := by
    apply Multiplicative.toAdd.injective
    apply ZMod.val_injective
    rw [← hx.exp, ← hy.exp]
  exact SemidirectProduct.ext h1 h2

theorem RepP.code_eq {p q : Pc} {x : Hh} (hp : RepP p x) (hq : RepP q x) : p = q := by
  have h1 : p.m = q.m := decode_inj hp.valid hq.valid (hp.mat.trans hq.mat.symm)
  have h2 : p.j = q.j := hp.exp.trans hq.exp.symm
  cases p; cases q
  simp only at h1 h2
  rw [h1, h2]

theorem RepP.pow {p : Pc} {x : Hh} (hp : RepP p x) (n : ℕ) : RepP (powP p n) (x ^ n) := by
  induction n with
  | zero => exact RepP.one
  | succ n ih => rw [pow_succ]; exact ih.mul hp

end CFSG.AGLEmbedding.KFactProofs.Sp48
