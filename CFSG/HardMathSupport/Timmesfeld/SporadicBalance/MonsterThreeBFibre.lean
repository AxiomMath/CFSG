module

public import CFSG.Assembly.Defs
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThreeBBridge
public import CFSG.Monster.Generated.Data

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF

open CFSG.Monster.Generated
open _root_.Timmesfeld.M3B (F3 Vec Mat E AD vget vofFn zeroV mget aget mofFn pack unpack fpt
  affOf affApply fibreCheck nPts adMat fimg0 fibreGenOK B0)

section Shift

variable {n : ℕ} (B : Fin n → Fin n → ZMod 3)

@[expose] def eshift (x : Elt n) (s : ZMod 3) : Elt n := (x.1, x.2 + s)

theorem emul_eshift_left (x y : Elt n) (s : ZMod 3) :
    emul B (eshift x s) y = eshift (emul B x y) s := by
  simp only [emul, eshift]
  refine Prod.ext rfl ?_
  simp only
  ring

theorem emul_eshift_right (x y : Elt n) (s : ZMod 3) :
    emul B x (eshift y s) = eshift (emul B x y) s := by
  simp only [emul, eshift]
  refine Prod.ext rfl ?_
  simp only
  ring

theorem eshift_eshift (x : Elt n) (s t : ZMod 3) : eshift (eshift x s) t = eshift x (s + t) := by
  simp only [eshift, add_assoc]

theorem epow_eshift (x : Elt n) (s : ZMod 3) :
    ∀ k : ℕ, epow B (eshift x s) k = eshift (epow B x k) (k * s)
  | 0 => by simp [epow, eshift, eone]
  | k + 1 => by
    rw [epow, epow, epow_eshift x s k, emul_eshift_left, emul_eshift_right, eshift_eshift]
    congr 1
    push_cast
    ring

theorem foldl_eshift : ∀ (l : List (Elt n × ZMod 3)) (a : Elt n) (t : ZMod 3),
    (l.map fun p => eshift p.1 p.2).foldl (emul B) (eshift a t) =
      eshift ((l.map Prod.fst).foldl (emul B) a) (t + (l.map Prod.snd).sum)
  | [], a, t => by simp
  | p :: l, a, t => by
    simp only [List.map_cons, List.foldl_cons, List.sum_cons]
    rw [emul_eshift_left, emul_eshift_right, eshift_eshift, foldl_eshift l]
    congr 1
    ring

theorem subst_eshift (D : ActD n) (x : Elt n) (s : ZMod 3) :
    subst B D (eshift x s) = eshift (subst B D x) (D.2 * s) := by
  unfold subst eshift emul
  refine Prod.ext rfl ?_
  simp only
  ring

@[expose] def fptM (T : Fin n → Fin n → ZMod 3) (lam : ZMod 3) (c : Fin n → ZMod 3) : ActD n :=
  (fun i => (T i, c i), lam)

theorem subst_fptM (T : Fin n → Fin n → ZMod 3) (lam : ZMod 3) (c : Fin n → ZMod 3) (x : Elt n) :
    subst B (fptM T lam c) x = eshift (subst B (fptM T lam 0) x) (∑ i, x.1 i * c i) := by
  unfold subst
  have hl : (List.ofFn fun i => epow B ((fptM T lam c).1 i) (x.1 i).val) =
      (List.ofFn fun i => (epow B ((fptM T lam 0).1 i) (x.1 i).val,
        ((x.1 i).val : ZMod 3) * c i)).map fun p => eshift p.1 p.2 := by
    rw [List.map_ofFn]
    refine congrArg List.ofFn (funext fun i => ?_)
    simp only [Function.comp_apply, fptM]
    rw [← epow_eshift]
    simp [eshift]
  have he : (eone : Elt n) = eshift eone 0 := by simp [eshift]
  rw [hl, eprod, he, foldl_eshift, List.map_ofFn, List.map_ofFn, emul_eshift_left, zero_add]
  congr 1
  rw [List.sum_ofFn]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

end Shift

section Conj

variable {n : ℕ} (B : Fin n → Fin n → ZMod 3)

theorem comp_fptM (T : Fin n → Fin n → ZMod 3) (lam : ZMod 3) (G Gi : ActD n)
    (hT : ∀ i, ((comp B (comp B Gi (fptM T lam 0)) G).1 i).1 = T i)
    (hl : (comp B (comp B Gi (fptM T lam 0)) G).2 = lam) (c : Fin n → ZMod 3) :
    comp B (comp B Gi (fptM T lam c)) G = fptM T lam (fun i =>
      ((comp B (comp B Gi (fptM T lam 0)) G).1 i).2 + G.2 * ∑ j, (Gi.1 i).1 j * c j) := by
  refine Prod.ext (funext fun i => ?_) ?_
  · show subst B G (subst B (fptM T lam c) (Gi.1 i)) = (T i, _)
    rw [subst_fptM, subst_eshift]
    refine Prod.ext (hT i) ?_
    rfl
  · exact hl

end Conj

section Pack

theorem ofDigits3_digit : ∀ (ds : List ℕ), (∀ d ∈ ds, d < 3) → ∀ i < ds.length,
    _root_.Timmesfeld.M3B.ofDigits3 ds / 3 ^ i % 3 = ds[i]!
  | [], _, i, h => by simp at h
  | d :: ds, hd, i, hi => by
    have hd0 : d < 3 := hd d List.mem_cons_self
    rcases i with _ | i
    · simp only [_root_.Timmesfeld.M3B.ofDigits3, List.foldr_cons, pow_zero, Nat.div_one]
      simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd0]
    · have ih := ofDigits3_digit ds (fun x hx => hd x (List.mem_cons_of_mem _ hx)) i
        (by simpa using hi)
      simp only [_root_.Timmesfeld.M3B.ofDigits3, List.foldr_cons] at ih ⊢
      rw [pow_succ', ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (by norm_num : 0 < 3),
        Nat.div_eq_of_lt hd0, zero_add]
      simpa using ih

theorem vget_unpack_pack (c : Vec) (i : Fin 12) : vget (unpack (pack c)) i = vget c i := by
  unfold unpack pack
  rw [vget_vofFn]
  apply Fin.ext
  rw [Fin.val_ofNat, ofDigits3_digit (List.ofFn fun i : Fin 12 => (vget c i).val)
    (fun d hd => by
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hd
      exact (vget c j).isLt) i.val (by simp)]
  rw [getElem!_pos (List.ofFn fun i : Fin 12 => (vget c i).val) i.val (by simp),
    List.getElem_ofFn]

theorem vfun_unpack_pack (c : Vec) : vfun (unpack (pack c)) = vfun c := by
  funext i
  exact congrArg toZ (vget_unpack_pack c i)

end Pack

section Compiled

theorem toD_fpt (T : Mat) (lam : F3) (c : Vec) :
    toD (fpt T lam c) = fptM (toMat T) (toZ lam) (vfun c) := by
  refine Prod.ext (funext fun i => ?_) rfl
  show toE (aget (fpt T lam c) i) = (toMat T i, vfun c i)
  unfold fpt aget
  rw [ofFn_get!]
  rfl

theorem meq_sound {A A' : Mat} (h : _root_.Timmesfeld.M3B.meq A A' = true) :
    toMat A = toMat A' := by
  unfold _root_.Timmesfeld.M3B.meq at h
  simp only [List.all_eq_true, beq_iff_eq] at h
  funext i j
  exact congrArg toZ (h i (List.mem_finRange i) j (List.mem_finRange j))

theorem toMat_adMat_row (D : AD) (i : Fin 12) : toMat (adMat D) i = ((toD D).1 i).1 := by
  funext j
  show toZ (mget (adMat D) i j) = toZ (vget (aget D i).1 j)
  unfold adMat mget
  rw [ofFn_get!]

end Compiled

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF
