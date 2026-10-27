module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThreeBNF

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF

variable {G : Type*} [Group G] {n : ℕ}

structure Sys (G : Type*) [Group G] (n : ℕ) where
  s : Fin n → G
  z : G
  B : Fin n → Fin n → ZMod 3

structure Sys.Good (S : Sys G n) : Prop where
  z3 : S.z ^ 3 = 1
  zs : ∀ i, Commute S.z (S.s i)
  s3 : ∀ i, S.s i ^ 3 = 1
  comm : ∀ i j, S.s i * S.s j = S.s j * S.s i * S.z ^ (S.B i j).val

abbrev Elt (n : ℕ) := (Fin n → ZMod 3) × ZMod 3

@[expose] def Sys.nf (S : Sys G n) (x : Elt n) : G := secN3 n S.s x.1 * S.z ^ x.2.val

@[expose] def emul (B : Fin n → Fin n → ZMod 3) (x y : Elt n) : Elt n :=
  (x.1 + y.1, x.2 + y.2 + betaN3 n B x.1 y.1)

@[expose] def eone : Elt n := (0, 0)

@[expose] def epow (B : Fin n → Fin n → ZMod 3) (x : Elt n) : ℕ → Elt n
  | 0 => eone
  | k + 1 => emul B (epow B x k) x

@[expose] def eprod (B : Fin n → Fin n → ZMod 3) (l : List (Elt n)) : Elt n :=
  l.foldl (emul B) eone

theorem secN3_zero : ∀ (n : ℕ) (s : Fin n → G), secN3 n s 0 = 1
  | 0, _ => rfl
  | n + 1, s => by
    rw [secN3]
    have : (fun i : Fin n => (0 : Fin (n + 1) → ZMod 3) i.succ) = 0 := rfl
    rw [this, secN3_zero n]
    simp

theorem Sys.nf_eone (S : Sys G n) : S.nf eone = 1 := by
  simp [Sys.nf, eone, secN3_zero]

theorem Sys.nf_mul {S : Sys G n} (hS : S.Good) (x y : Elt n) :
    S.nf x * S.nf y = S.nf (emul S.B x y) := by
  have hc : Commute (S.z ^ x.2.val) (secN3 n S.s y.1) :=
    (commute_secN3 n S.s y.1 hS.zs).pow_left _
  have hm := secN3_mul_secN3 hS.z3 n S.s S.B hS.zs hS.s3 hS.comm x.1 y.1
  have hz : S.z ^ (betaN3 n S.B x.1 y.1).val * (S.z ^ x.2.val * S.z ^ y.2.val) =
      S.z ^ (x.2 + y.2 + betaN3 n S.B x.1 y.1).val := by
    rw [pow_val_add hS.z3, pow_val_add hS.z3, ← pow_add, ← pow_add, ← pow_add]
    congr 1
    ring
  calc S.nf x * S.nf y = secN3 n S.s x.1 * (S.z ^ x.2.val * secN3 n S.s y.1) * S.z ^ y.2.val := by
        simp only [Sys.nf, mul_assoc]
    _ = secN3 n S.s x.1 * secN3 n S.s y.1 * (S.z ^ x.2.val * S.z ^ y.2.val) := by
        rw [hc.eq]; simp only [mul_assoc]
    _ = S.nf (emul S.B x y) := by
        rw [hm, mul_assoc, hz]; rfl

theorem Sys.nf_epow {S : Sys G n} (hS : S.Good) (x : Elt n) :
    ∀ k, S.nf (epow S.B x k) = S.nf x ^ k
  | 0 => by rw [epow, Sys.nf_eone, pow_zero]
  | k + 1 => by rw [epow, ← Sys.nf_mul hS, Sys.nf_epow hS x k, pow_succ]

theorem Sys.nf_foldl {S : Sys G n} (hS : S.Good) :
    ∀ (l : List (Elt n)) (a : Elt n),
      S.nf (l.foldl (emul S.B) a) = S.nf a * (l.map S.nf).prod
  | [], a => by simp
  | x :: l, a => by
    rw [List.foldl_cons, Sys.nf_foldl hS l, ← Sys.nf_mul hS, List.map_cons, List.prod_cons,
      mul_assoc]

theorem Sys.nf_eprod {S : Sys G n} (hS : S.Good) (l : List (Elt n)) :
    S.nf (eprod S.B l) = (l.map S.nf).prod := by
  rw [eprod, Sys.nf_foldl hS, Sys.nf_eone, one_mul]

abbrev ActD (n : ℕ) := (Fin n → Elt n) × ZMod 3

@[expose] def subst (B : Fin n → Fin n → ZMod 3) (D : ActD n) (x : Elt n) : Elt n :=
  emul B (eprod B (List.ofFn fun i => epow B (D.1 i) (x.1 i).val)) (0, D.2 * x.2)

@[expose] def IsAct (S : Sys G n) (g : G) (D : ActD n) : Prop :=
  (∀ i, g⁻¹ * S.s i * g = S.nf (D.1 i)) ∧ g⁻¹ * S.z * g = S.z ^ D.2.val

@[expose] def comp (B : Fin n → Fin n → ZMod 3) (D D' : ActD n) : ActD n :=
  (fun i => subst B D' (D.1 i), D.2 * D'.2)

theorem conj_pow_inv (g x : G) (k : ℕ) : (g⁻¹ * x * g) ^ k = g⁻¹ * x ^ k * g := by
  have h := conj_pow (i := k) (a := g⁻¹) (b := x)
  simpa only [inv_inv] using h

theorem conj_secN3 (g : G) : ∀ (n : ℕ) (s : Fin n → G) (v : Fin n → ZMod 3),
    g⁻¹ * secN3 n s v * g = (List.ofFn fun i => (g⁻¹ * s i * g) ^ (v i).val).prod
  | 0, _, _ => by simp [secN3]
  | n + 1, s, v => by
    rw [secN3, List.ofFn_succ, List.prod_cons, ← conj_secN3 g n, conj_pow_inv]
    group

theorem Sys.nf_zpow_val (S : Sys G n) (hS : S.Good) (a e : ZMod 3) :
    (S.z ^ a.val) ^ e.val = S.nf (0, a * e) := by
  rw [Sys.nf, secN3_zero, one_mul, ← pow_mul, ZMod.val_mul, pow_mod_three hS.z3]

theorem IsAct.conj_nf {S : Sys G n} (hS : S.Good) {g : G} {D : ActD n} (h : IsAct S g D)
    (x : Elt n) : g⁻¹ * S.nf x * g = S.nf (subst S.B D x) := by
  have e1 : g⁻¹ * S.nf x * g = (g⁻¹ * secN3 n S.s x.1 * g) * (g⁻¹ * S.z * g) ^ x.2.val := by
    rw [conj_pow_inv, Sys.nf]; group
  rw [e1, conj_secN3, h.2, Sys.nf_zpow_val S hS, subst, ← Sys.nf_mul hS, Sys.nf_eprod hS,
    List.map_ofFn]
  congr 2
  refine congrArg List.ofFn (funext fun i => ?_)
  simp only [Function.comp_apply, Sys.nf_epow hS, h.1 i]

theorem IsAct.mul {S : Sys G n} (hS : S.Good) {g h : G} {D D' : ActD n} (hg : IsAct S g D)
    (hh : IsAct S h D') : IsAct S (g * h) (comp S.B D D') := by
  refine ⟨fun i => ?_, ?_⟩
  · have e : (g * h)⁻¹ * S.s i * (g * h) = h⁻¹ * (g⁻¹ * S.s i * g) * h := by group
    rw [e, hg.1 i, hh.conj_nf hS]
    rfl
  · have e : (g * h)⁻¹ * S.z * (g * h) = h⁻¹ * (g⁻¹ * S.z * g) * h := by group
    rw [e, hg.2, ← conj_pow_inv, hh.2, ← pow_mul, comp, ZMod.val_mul, pow_mod_three hS.z3,
      mul_comm]

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF
