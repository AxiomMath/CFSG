module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThreeBAct
public import Certificates.Data.CFSGNative.Timmesfeld.M3B

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF

open _root_.Timmesfeld.M3B (F3 Vec Mat E AD fsum vget vofFn zeroV mget beta aget)

@[expose] def toZ (a : F3) : ZMod 3 := a

@[simp] theorem toZ_add (a b : F3) : toZ (a + b) = toZ a + toZ b := rfl

@[simp] theorem toZ_mul (a b : F3) : toZ (a * b) = toZ a * toZ b := rfl

@[simp] theorem toZ_zero : toZ 0 = 0 := rfl

@[simp] theorem toZ_one : toZ 1 = 1 := rfl

theorem toZ_val (a : F3) : (toZ a).val = a.val := rfl

theorem toZ_injective : Function.Injective toZ := fun _ _ h => h

theorem fsum_eq : ∀ (n : ℕ) (f : Fin n → F3), toZ (fsum n f) = ∑ i : Fin n, toZ (f i)
  | 0, f => by simp [fsum]
  | n + 1, f => by
    have h := fsum_eq n (fun i => f i.castSucc)
    rw [fsum, Fin.foldl_succ_last, Fin.sum_univ_castSucc, toZ_add, ← h, fsum]

@[expose] def betaC (n : ℕ) (B : Fin n → Fin n → ZMod 3) (v w : Fin n → ZMod 3) : ZMod 3 :=
  ∑ i : Fin n, ∑ j : Fin n, if j < i then v i * w j * B i j else 0

theorem betaN3_eq : ∀ (n : ℕ) (B : Fin n → Fin n → ZMod 3) (v w : Fin n → ZMod 3),
    betaN3 n B v w = betaC n B v w
  | 0, _, _, _ => by simp [betaN3, betaC]
  | n + 1, B, v, w => by
    rw [betaN3, betaN3_eq n]
    simp only [betaC, Fin.sum_univ_succ, Fin.succ_lt_succ_iff, Fin.not_lt_zero, ite_false,
      Finset.sum_const_zero, zero_add, Fin.succ_pos, ite_true, Finset.sum_add_distrib]

@[expose] def vfun (a : Vec) : Fin 12 → ZMod 3 := fun i => toZ (vget a i)

@[expose] def toE (x : E) : Elt 12 := (vfun x.1, toZ x.2)

@[expose] def toMat (A : Mat) : Fin 12 → Fin 12 → ZMod 3 := fun i j => toZ (mget A i j)

@[expose] def toD (D : AD) : ActD 12 := (fun i => toE (aget D i), toZ D.2)

theorem ofFn_get! {α : Type} [Inhabited α] (f : Fin 12 → α) (i : Fin 12) :
    (Array.ofFn f)[i.val]! = f i := by
  simp

theorem vget_vofFn (f : Fin 12 → F3) (i : Fin 12) : vget (vofFn f) i = f i :=
  ofFn_get! f i

theorem vfun_vofFn (f : Fin 12 → F3) : vfun (vofFn f) = fun i => toZ (f i) := by
  funext i; exact congrArg toZ (vget_vofFn f i)

theorem vfun_zeroV : vfun zeroV = 0 := by
  funext i; exact congrArg toZ (vget_vofFn _ i)

theorem beta_eq (B : Mat) (a b : Vec) :
    toZ (beta B a b) = betaN3 12 (toMat B) (vfun a) (vfun b) := by
  rw [betaN3_eq, beta, fsum_eq, betaC]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fsum_eq]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : j < i
  · simp only [h, ite_true, toZ_mul]; rfl
  · simp only [h, ite_false, toZ_zero]

theorem toE_emul (B : Mat) (x y : E) :
    toE (_root_.Timmesfeld.M3B.emul B x y) = ThreeBNF.emul (toMat B) (toE x) (toE y) := by
  simp only [toE, _root_.Timmesfeld.M3B.emul, ThreeBNF.emul, vfun_vofFn, toZ_add, beta_eq]
  rfl

theorem toE_eone : toE _root_.Timmesfeld.M3B.eone = ThreeBNF.eone := by
  unfold toE _root_.Timmesfeld.M3B.eone ThreeBNF.eone
  rw [vfun_zeroV]
  rfl

theorem toE_epow (B : Mat) (x : E) :
    ∀ k, toE (_root_.Timmesfeld.M3B.epow B x k) = ThreeBNF.epow (toMat B) (toE x) k
  | 0 => toE_eone
  | k + 1 => by rw [_root_.Timmesfeld.M3B.epow, ThreeBNF.epow, toE_emul, toE_epow B x k]

theorem toE_foldl (B : Mat) : ∀ (l : List E) (a : E),
    toE (l.foldl (_root_.Timmesfeld.M3B.emul B) a) =
      (l.map toE).foldl (ThreeBNF.emul (toMat B)) (toE a)
  | [], _ => rfl
  | x :: l, a => by
    rw [List.foldl_cons, toE_foldl B l, List.map_cons, List.foldl_cons, toE_emul]

theorem toE_eprod (B : Mat) (l : List E) :
    toE (_root_.Timmesfeld.M3B.eprod B l) = ThreeBNF.eprod (toMat B) (l.map toE) := by
  rw [_root_.Timmesfeld.M3B.eprod, toE_foldl, toE_eone]; rfl

theorem toE_zero_pair (a : F3) : toE (zeroV, a) = ((0 : Fin 12 → ZMod 3), toZ a) := by
  unfold toE
  rw [vfun_zeroV]

theorem toE_subst (B : Mat) (D : AD) (x : E) :
    toE (_root_.Timmesfeld.M3B.subst B D x) = ThreeBNF.subst (toMat B) (toD D) (toE x) := by
  unfold _root_.Timmesfeld.M3B.subst ThreeBNF.subst
  rw [toE_emul, toE_eprod, List.map_ofFn, toE_zero_pair, toZ_mul]
  have h : (toE ∘ fun i => _root_.Timmesfeld.M3B.epow B (aget D i) (vget x.1 i).val) =
      fun i => ThreeBNF.epow (toMat B) ((toD D).1 i) ((toE x).1 i).val := by
    funext i
    exact toE_epow B (aget D i) (vget x.1 i).val
  rw [h]
  rfl

theorem toD_comp (B : Mat) (D D' : AD) :
    toD (_root_.Timmesfeld.M3B.comp B D D') = ThreeBNF.comp (toMat B) (toD D) (toD D') := by
  refine Prod.ext (funext fun i => ?_) rfl
  show toE (aget (_root_.Timmesfeld.M3B.comp B D D') i) =
    ThreeBNF.subst (toMat B) (toD D') (toE (aget D i))
  rw [← toE_subst]
  unfold _root_.Timmesfeld.M3B.comp aget
  rw [ofFn_get!]

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF
