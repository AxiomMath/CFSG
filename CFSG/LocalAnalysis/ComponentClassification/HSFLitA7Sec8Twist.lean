module

public import Mathlib.Data.Fintype.Prod

public section

namespace CFSG.ComponentClassification.HSFLit.Sec8

@[expose] def tget (T b i : ℕ) : ℕ := T / 2 ^ (b * i) % 2 ^ b

theorem tget_lt (T b i : ℕ) : tget T b i < 2 ^ b := Nat.mod_lt _ (Nat.two_pow_pos b)

@[expose] def xorTab : ℕ :=
  93147360564760955560836986139376948966093980313303332972466539282436661195280 + 2 ^ 256 *
  (62270412405532766427640066322909459187133297767310466390939146540591751394900 + 2 ^ 256 *
  (31391579666949594439864234732868023135202747746872581525488567056763386116760 + 2 ^ 256 *
  (514631507721405306667314916400533356242065200879714943961174314918476316380)))

@[expose] def ex (a b : Fin 16) : Fin 16 := ⟨tget xorTab 4 (16 * a.val + b.val), tget_lt _ _ _⟩

theorem ex_assoc : ∀ a b c : Fin 16, ex (ex a b) c = ex a (ex b c) := by decide +kernel

theorem ex_comm : ∀ a b : Fin 16, ex a b = ex b a := by decide +kernel

theorem ex_self : ∀ a : Fin 16, ex a a = 0 := by decide +kernel

theorem ex_zero : ∀ a : Fin 16, ex a 0 = a := by decide +kernel

theorem zero_ex : ∀ a : Fin 16, ex 0 a = a := by decide +kernel

structure TwData (qb : ℕ) where
  qmulT : ℕ
  qinvT : ℕ
  actT : ℕ
  cocT : ℕ

namespace TwData

variable {qb : ℕ} (D : TwData qb)

@[expose] def qmul (g h : Fin (2 ^ qb)) : Fin (2 ^ qb) :=
  ⟨tget D.qmulT qb (2 ^ qb * g.val + h.val), tget_lt _ _ _⟩

@[expose] def qinv (g : Fin (2 ^ qb)) : Fin (2 ^ qb) := ⟨tget D.qinvT qb g.val, tget_lt _ _ _⟩

@[expose] def act (g : Fin (2 ^ qb)) (a : Fin 16) : Fin 16 :=
  ⟨tget D.actT 4 (16 * g.val + a.val), tget_lt _ _ _⟩

@[expose] def coc (g h : Fin (2 ^ qb)) : Fin 16 :=
  ⟨tget D.cocT 4 (2 ^ qb * g.val + h.val), tget_lt _ _ _⟩

@[expose] def qone (_D : TwData qb) : Fin (2 ^ qb) := ⟨0, Nat.two_pow_pos qb⟩

structure Valid : Prop where
  qmul_assoc : ∀ g h k, D.qmul (D.qmul g h) k = D.qmul g (D.qmul h k)
  qone_mul : ∀ g, D.qmul D.qone g = g
  qmul_one : ∀ g, D.qmul g D.qone = g
  qinv_mul : ∀ g, D.qmul (D.qinv g) g = D.qone
  act_ex : ∀ g a b, D.act g (ex a b) = ex (D.act g a) (D.act g b)
  act_one : ∀ a, D.act D.qone a = a
  act_mul : ∀ g h a, D.act (D.qmul g h) a = D.act g (D.act h a)
  coc_one_left : ∀ g, D.coc D.qone g = 0
  coc_one_right : ∀ g, D.coc g D.qone = 0
  coc_cocycle : ∀ g h k,
    ex (D.act g (D.coc h k)) (D.coc g (D.qmul h k)) = ex (D.coc g h) (D.coc (D.qmul g h) k)

@[ext] structure Carrier (_D : TwData qb) where
  a : Fin 16
  g : Fin (2 ^ qb)

instance Carrier.instDecidableEq : DecidableEq D.Carrier := fun x y =>
  if h : x.a = y.a ∧ x.g = y.g then isTrue (Carrier.ext h.1 h.2)
  else isFalse fun e => h ⟨congrArg Carrier.a e, congrArg Carrier.g e⟩

@[expose] def Carrier.equiv : D.Carrier ≃ Fin 16 × Fin (2 ^ qb) where
  toFun x := (x.a, x.g)
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype D.Carrier := Fintype.ofEquiv _ (Carrier.equiv D).symm

@[expose] def mul (x y : D.Carrier) : D.Carrier :=
  ⟨ex (ex x.a (D.act x.g y.a)) (D.coc x.g y.g), D.qmul x.g y.g⟩

@[expose] def one : D.Carrier := ⟨0, D.qone⟩

@[expose] def inv (x : D.Carrier) : D.Carrier :=
  ⟨ex (D.act (D.qinv x.g) x.a) (D.coc (D.qinv x.g) x.g), D.qinv x.g⟩

theorem ex_rearr {a b c d e f g : Fin 16} (h : ex f g = ex c e) :
    ex (ex (ex (ex a b) c) d) e = ex (ex a (ex (ex b d) f)) g := by
  calc ex (ex (ex (ex a b) c) d) e = ex (ex (ex a b) d) (ex c e) := by
        rw [ex_assoc (ex a b) c d, ex_assoc (ex a b), ex_assoc c, ex_comm d e, ← ex_assoc c e d,
          ex_comm (ex c e) d, ← ex_assoc (ex a b) d]
    _ = ex (ex (ex a b) d) (ex f g) := by rw [h]
    _ = ex (ex a (ex (ex b d) f)) g := by
        rw [ex_assoc a b d, ← ex_assoc _ f g, ex_assoc a (ex b d) f]

variable {D}

theorem act_zero (hD : D.Valid) (g : Fin (2 ^ qb)) : D.act g 0 = 0 := by
  have h := hD.act_ex g 0 0
  rw [ex_self, ex_self] at h
  exact h

@[reducible, expose] def group (hD : D.Valid) : Group D.Carrier where
  mul := D.mul
  one := D.one
  inv := D.inv
  mul_assoc x y z := by
    change D.mul (D.mul x y) z = D.mul x (D.mul y z)
    refine Carrier.ext ?_ (hD.qmul_assoc _ _ _)
    change ex (ex (ex (ex x.a (D.act x.g y.a)) (D.coc x.g y.g)) (D.act (D.qmul x.g y.g) z.a))
      (D.coc (D.qmul x.g y.g) z.g) =
      ex (ex x.a (D.act x.g (ex (ex y.a (D.act y.g z.a)) (D.coc y.g z.g))))
        (D.coc x.g (D.qmul y.g z.g))
    rw [hD.act_ex, hD.act_ex, ← hD.act_mul]
    exact ex_rearr (hD.coc_cocycle x.g y.g z.g)
  one_mul x := by
    change D.mul D.one x = x
    refine Carrier.ext ?_ (hD.qone_mul _)
    change ex (ex 0 (D.act D.qone x.a)) (D.coc D.qone x.g) = x.a
    rw [hD.act_one, hD.coc_one_left, zero_ex, ex_zero]
  mul_one x := by
    change D.mul x D.one = x
    refine Carrier.ext ?_ (hD.qmul_one _)
    change ex (ex x.a (D.act x.g 0)) (D.coc x.g D.qone) = x.a
    rw [act_zero hD, hD.coc_one_right, ex_zero, ex_zero]
  inv_mul_cancel x := by
    change D.mul (D.inv x) x = D.one
    refine Carrier.ext ?_ (hD.qinv_mul _)
    change ex (ex (ex (D.act (D.qinv x.g) x.a) (D.coc (D.qinv x.g) x.g))
      (D.act (D.qinv x.g) x.a)) (D.coc (D.qinv x.g) x.g) = 0
    rw [ex_assoc, ex_self]

end TwData

end CFSG.ComponentClassification.HSFLit.Sec8
