module

public import CFSG.LieType.Chevalley.E6Three.ModelKernel

public section

set_option autoImplicit false

namespace CFSG.LieType.Chevalley.E6Three.ModelKernel

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType.TableBExc
  CFSG.StandardType.TableBExc.Three CFSG.StandardType.TableBExc.E6Three
  CFSG.HardMathSupport.Timmesfeld.Steinberg CFSG.StandardType.TwE6HyperplaneTypes

local instance modelPairsE6NeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

abbrev Coord : Type := (Fin 3 → ZMod 3) × ZMod 3

@[expose] def piInv (j : ZMod 3) (i : Fin 3) : Fin 3 :=
  ![![0, 1, 2], ![2, 0, 1], ![1, 2, 0]] ⟨j.val, j.val_lt⟩ i

theorem piInv_eq : ∀ (j : ZMod 3) (i : Fin 3), piInv j i = (piE7 ^ j.val).symm i := by
  decide +kernel

@[expose] def qmul (q r : Coord) : Coord := (fun i => q.1 i + r.1 (piInv q.2 i), q.2 + r.2)

@[expose] def qone : Coord := (0, 0)

@[expose] def qpow (q : Coord) : ℕ → Coord
  | 0 => qone
  | n + 1 => qmul (qpow q n) q

@[expose] def qp (q₁ q₂ : Coord) (a b : ℕ) : Coord := qmul (qpow q₁ a) (qpow q₂ b)

@[expose] def mkModel (q : Coord) : Model piE7 piE7_pow_three :=
  ⟨Multiplicative.ofAdd q.1, Multiplicative.ofAdd q.2⟩

theorem mkModel_qmul (q r : Coord) : mkModel (qmul q r) = mkModel q * mkModel r := by
  have hq : q.2 = ((q.2.val : ℕ) : ZMod 3) := (ZMod.natCast_zmod_val q.2).symm
  refine SemidirectProduct.ext ?_ ?_
  · apply Multiplicative.toAdd.injective
    funext i
    change q.1 i + r.1 (piInv q.2 i) = ((Multiplicative.ofAdd q.1 *
      (phi piE7 piE7_pow_three (Multiplicative.ofAdd q.2)) (Multiplicative.ofAdd r.1)).toAdd) i
    rw [toAdd_mul, Pi.add_apply, hq, phi_ofAdd_natCast, toAdd_shiftAut_pow, ← hq, piInv_eq]
    rfl
  · rfl

theorem mkModel_qone : mkModel qone = 1 := rfl

@[expose] noncomputable def mW (q : Coord) : WeylGroup .E6 := modelHomE6 (mkModel q)

theorem mW_eq (q : Coord) : mW q = (coxeterSystem .E6).wordProd (modelWordE6 q.1 q.2) := by
  rw [mW, modelHomE6_eq_wordProd]
  rfl

theorem mW_qmul (q r : Coord) : mW (qmul q r) = mW q * mW r := by
  rw [mW, mkModel_qmul, map_mul]
  rfl

theorem mW_qone : mW qone = 1 := by
  rw [mW, mkModel_qone, map_one]

theorem mW_qpow (q : Coord) (n : ℕ) : mW (qpow q n) = mW q ^ n := by
  induction n with
  | zero => exact mW_qone
  | succ n ih => rw [qpow, mW_qmul, ih, pow_succ]

theorem mW_qp (q₁ q₂ : Coord) (a b : ℕ) : mW (qp q₁ q₂ a b) = mW q₁ ^ a * mW q₂ ^ b := by
  rw [qp, mW_qmul, mW_qpow, mW_qpow]

@[expose] def isPlanes (q : Coord) : Bool :=
  match modelCert q.1 q.2 with
  | .planes .. => true
  | _ => false

@[expose] def isRefl (q : Coord) : Bool :=
  match modelCert q.1 q.2 with
  | .refl _ => true
  | _ => false

structure SubCert where
  g₁ : Coord
  g₂ : Coord
  f : Fin 2 → Fin Tag.E6.rank → ZMod 3
  P : Fin 2 → Fin Tag.E6.rank → ZMod 3
  s : Fin 4 → Fin Tag.E6.rank → ZMod 3
  rows : Fin 4 → Fin 2 × Fin Tag.E6.rank
  lines : List (ℕ × ℕ × List (List (Fin Tag.E6.rank) × Fin Tag.E6.rank))
deriving Inhabited

@[expose] def lineCoef : Fin 4 → Fin 2 → ZMod 3 := ![![1, 0], ![0, 1], ![1, 1], ![1, 2]]

@[expose] def lineVec (f : Fin 2 → Fin Tag.E6.rank → ZMod 3) (l : Fin 4) :
    Fin Tag.E6.rank → ZMod 3 :=
  lineCoef l 0 • f 0 + lineCoef l 1 • f 1

@[expose] def genCols (c : SubCert) (g : Fin 2) (j : Fin Tag.E6.rank) : Fin Tag.E6.rank → ℤ :=
  wordAct .E6 (modelWordE6 (if g = 0 then c.g₁ else c.g₂).1 (if g = 0 then c.g₁ else c.g₂).2)
    (Pi.single j 1)

@[expose] def SubCert.check (c : SubCert) : Bool :=
  ((List.finRange 2).all fun k => isFixed (genCols c 0) (c.f k) && isFixed (genCols c 1) (c.f k)) &&
  ((List.finRange Tag.E6.rank).all fun i => (List.finRange Tag.E6.rank).all fun i' =>
    decide (c.f 0 i * c.P 0 i' + c.f 1 i * c.P 1 i' +
      c.s 0 i * rowW (genCols c (c.rows 0).1) (c.rows 0).2 i' +
      c.s 1 i * rowW (genCols c (c.rows 1).1) (c.rows 1).2 i' +
      c.s 2 i * rowW (genCols c (c.rows 2).1) (c.rows 2).2 i' +
      c.s 3 i * rowW (genCols c (c.rows 3).1) (c.rows 3).2 i' = if i = i' then 1 else 0)) &&
  (List.finRange 4).all fun l =>
    let e := c.lines.getD l (0, 0, [])
    !decide (qp c.g₁ c.g₂ e.1 e.2.1 = qone) &&
    ((List.finRange Tag.E6.rank).all fun j =>
      veqZ (wordAct .E6 (modelWordE6 (qp c.g₁ c.g₂ e.1 e.2.1).1 (qp c.g₁ c.g₂ e.1 e.2.1).2)
        (Pi.single j 1)) (wordAct .E6 (e.2.2.flatMap reflWordP) (Pi.single j 1))) &&
    e.2.2.all fun p => decide (dot6 (lineVec c.f l) (wordAct .E6 p.1 (Pi.single p.2 1)) = 0)

@[expose] def subCerts : List SubCert := [
  ⟨(![0, 0, 0], 1), (![1, 1, 1], 0), ![![0, 0, 0, 1, 0, 0], ![1, 1, 1, 0, 1, 1]], ![![0, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0, 1], ![0, 2, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 1, 1, 0, 1, 0]], ![(0, 0), (0, 1), (0, 2), (1, 0)], [(0, 1, [([], 5), ([], 4), ([], 1), ([], 0), ([], 2), ([3, 2, 0, 4, 3, 1, 2, 3, 4], 5)]), (1, 0, [([0, 2, 3], 4), ([1, 3, 4], 5), ([0, 1, 2], 3), ([2, 3, 4], 5)]), (0, 1, [([1, 3], 4), ([1, 2], 3), ([3, 4], 5), ([0, 2], 3), ([0, 1, 2, 3, 4], 5), ([2, 3], 4)]), (0, 1, [([1], 3), ([1, 2, 3, 4], 5), ([3], 4), ([0, 2, 3, 4], 5), ([0, 1, 2, 3], 4), ([2], 3)])]⟩,
  ⟨(![0, 1, 1], 0), (![1, 0, 1], 0), ![![0, 0, 0, 1, 0, 0], ![1, 2, 1, 0, 1, 1]], ![![0, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 0, 0]], ![![0, 1, 2, 0, 1, 1], ![0, 0, 0, 0, 2, 2], ![0, 2, 2, 0, 0, 2], ![0, 2, 0, 0, 1, 1]], ![(0, 1), (0, 3), (0, 4), (1, 3)], [(1, 0, [([], 5), ([], 4), ([], 1), ([3, 2, 0, 4, 3, 1, 2, 3, 4], 5)]), (1, 1, [([], 3), ([2, 3, 4], 5), ([1, 3], 4), ([0, 2, 3], 4), ([1, 2], 3), ([0, 1, 2, 3, 4], 5)]), (1, 1, [([3, 4], 5), ([2, 3], 4), ([1], 3), ([0, 2], 3), ([1, 2, 3, 4], 5), ([0, 1, 2, 3], 4)]), (1, 1, [([3], 4), ([2], 3), ([1, 3, 4], 5), ([0, 2, 3, 4], 5), ([1, 2, 3], 4), ([0, 1, 2], 3)])]⟩,
  ⟨(![0, 1, 1], 0), (![1, 0, 2], 0), ![![0, 0, 0, 1, 0, 0], ![1, 1, 1, 0, 2, 2]], ![![0, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 0, 0]], ![![0, 1, 2, 0, 1, 1], ![0, 0, 0, 0, 2, 2], ![0, 1, 2, 0, 1, 0], ![0, 1, 0, 0, 2, 2]], ![(0, 1), (0, 3), (0, 4), (1, 3)], [(1, 0, [([], 5), ([], 4), ([], 1), ([3, 2, 0, 4, 3, 1, 2, 3, 4], 5)]), (2, 1, [([1, 3], 4), ([1, 2, 3, 4], 5), ([], 3), ([0, 2, 3, 4], 5), ([0, 1, 2], 3), ([2, 3], 4)]), (2, 1, [([1, 3, 4], 5), ([1, 2], 3), ([3], 4), ([0, 2], 3), ([0, 1, 2, 3], 4), ([2, 3, 4], 5)]), (2, 1, [([1], 3), ([1, 2, 3], 4), ([3, 4], 5), ([0, 2, 3], 4), ([0, 1, 2, 3, 4], 5), ([2], 3)])]⟩,
  ⟨(![0, 1, 2], 0), (![1, 0, 1], 0), ![![0, 0, 0, 1, 0, 0], ![1, 2, 1, 0, 2, 2]], ![![0, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 0, 0]], ![![0, 2, 1, 0, 2, 2], ![0, 0, 0, 0, 2, 2], ![0, 2, 2, 0, 1, 0], ![0, 2, 0, 0, 2, 2]], ![(0, 1), (0, 3), (0, 4), (1, 3)], [(1, 0, [([], 5), ([], 4), ([3, 2, 0, 4, 3, 1, 2, 3, 4], 5), ([], 1)]), (2, 1, [([], 3), ([2, 3], 4), ([1, 3, 4], 5), ([0, 2, 3, 4], 5), ([1, 2], 3), ([0, 1, 2, 3], 4)]), (2, 1, [([3], 4), ([2, 3, 4], 5), ([1], 3), ([0, 2], 3), ([1, 2, 3], 4), ([0, 1, 2, 3, 4], 5)]), (2, 1, [([3, 4], 5), ([2], 3), ([1, 3], 4), ([0, 2, 3], 4), ([1, 2, 3, 4], 5), ([0, 1, 2], 3)])]⟩,
  ⟨(![0, 1, 2], 0), (![1, 0, 2], 0), ![![0, 0, 0, 1, 0, 0], ![1, 1, 1, 0, 1, 1]], ![![0, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 0, 0]], ![![0, 2, 1, 0, 2, 2], ![0, 0, 0, 0, 2, 2], ![0, 1, 2, 0, 0, 2], ![0, 1, 0, 0, 1, 1]], ![(0, 1), (0, 3), (0, 4), (1, 3)], [(1, 0, [([], 5), ([], 4), ([3, 2, 0, 4, 3, 1, 2, 3, 4], 5), ([], 1)]), (1, 1, [([1, 3, 4], 5), ([1, 2, 3], 4), ([], 3), ([0, 2, 3], 4), ([0, 1, 2], 3), ([2, 3, 4], 5)]), (1, 1, [([1, 3], 4), ([1, 2], 3), ([3, 4], 5), ([0, 2], 3), ([0, 1, 2, 3, 4], 5), ([2, 3], 4)]), (1, 1, [([1], 3), ([1, 2, 3, 4], 5), ([3], 4), ([0, 2, 3, 4], 5), ([0, 1, 2, 3], 4), ([2], 3)])]⟩,
  ⟨(![0, 1, 2], 1), (![0, 2, 1], 2), ![![0, 0, 0, 1, 0, 0], ![1, 1, 1, 0, 1, 1]], ![![0, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 1, 2], ![0, 0, 1, 0, 0, 2], ![0, 0, 0, 0, 0, 2], ![0, 1, 1, 0, 0, 2]], ![(0, 0), (0, 1), (0, 2), (1, 0)], [(1, 1, [([], 5), ([], 4), ([], 1), ([], 0), ([], 2), ([3, 2, 0, 4, 3, 1, 2, 3, 4], 5)]), (1, 1, [([1, 3, 4], 5), ([1, 2, 3], 4), ([], 3), ([0, 2, 3], 4), ([0, 1, 2], 3), ([2, 3, 4], 5)]), (1, 0, [([0, 2], 3), ([1, 3], 4), ([0, 1, 2, 3, 4], 5), ([2, 3], 4)]), (1, 1, [([1], 3), ([1, 2, 3, 4], 5), ([3], 4), ([0, 2, 3, 4], 5), ([0, 1, 2, 3], 4), ([2], 3)])]⟩,
  ⟨(![0, 1, 2], 2), (![0, 2, 1], 1), ![![0, 0, 0, 1, 0, 0], ![1, 1, 1, 0, 1, 1]], ![![0, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 0, 0]], ![![0, 0, 2, 0, 0, 0], ![0, 2, 1, 0, 2, 1], ![0, 0, 2, 0, 2, 1], ![0, 1, 2, 0, 2, 0]], ![(0, 0), (0, 1), (0, 2), (1, 0)], [(2, 2, [([], 5), ([], 4), ([], 1), ([], 0), ([], 2), ([3, 2, 0, 4, 3, 1, 2, 3, 4], 5)]), (2, 2, [([1, 3, 4], 5), ([1, 2, 3], 4), ([], 3), ([0, 2, 3], 4), ([0, 1, 2], 3), ([2, 3, 4], 5)]), (2, 2, [([1, 3], 4), ([1, 2], 3), ([3, 4], 5), ([0, 2], 3), ([0, 1, 2, 3, 4], 5), ([2, 3], 4)]), (1, 0, [([3], 4), ([1, 2, 3, 4], 5), ([0, 1, 2, 3], 4), ([2], 3)])]⟩]

set_option maxRecDepth 100000 in
theorem subCerts_check :
    (List.finRange 7).all (fun j => (subCerts.getD j default).check) = true := by
  decide +kernel

@[expose] def allQ : List Coord :=
  (List.range 81).map fun m => (![((m / 27 % 3 : ℕ) : ZMod 3), ((m / 9 % 3 : ℕ) : ZMod 3),
    ((m / 3 % 3 : ℕ) : ZMod 3)], ((m % 3 : ℕ) : ZMod 3))

theorem mem_allQ : ∀ q : Coord, q ∈ allQ := by
  decide +kernel

@[expose] def spanQ (q₁ q₂ : Coord) : List Coord :=
  (List.range 3).flatMap fun a => (List.range 3).map fun b => qp q₁ q₂ a b

theorem exists_of_mem_spanQ {q₁ q₂ g : Coord} (h : g ∈ spanQ q₁ q₂) :
    ∃ a b : ℕ, g = qp q₁ q₂ a b := by
  obtain ⟨a, -, hb⟩ := List.mem_flatMap.1 h
  obtain ⟨b, -, rfl⟩ := List.mem_map.1 hb
  exact ⟨a, b, rfl⟩

@[expose] def pairOK (q₁ q₂ : Coord) : Bool :=
  !(isPlanes q₁ && isPlanes q₂ && decide (qmul q₁ q₂ = qmul q₂ q₁) && !decide (q₂ = qone) &&
      !decide (q₂ = q₁) && !decide (q₂ = qmul q₁ q₁)) ||
    ((List.range 3).any fun a => (List.range 3).any fun b =>
      !decide (qp q₁ q₂ a b = qone) && isRefl (qp q₁ q₂ a b)) ||
    (List.finRange 7).any fun j =>
      decide ((subCerts.getD j default).g₁ ∈ spanQ q₁ q₂) &&
      decide ((subCerts.getD j default).g₂ ∈ spanQ q₁ q₂) &&
      (List.finRange 4).all fun l =>
        decide (qp (subCerts.getD j default).g₁ (subCerts.getD j default).g₂
          ((subCerts.getD j default).lines.getD l default).1
          ((subCerts.getD j default).lines.getD l default).2.1 ∈ spanQ q₁ q₂)

set_option maxRecDepth 100000 in
theorem pairOK_all : allQ.all (fun q₁ => allQ.all (fun q₂ => pairOK q₁ q₂)) = true := by
  decide +kernel

theorem fixes_mul {x : Fin Tag.E6.rank → ZMod 3} {w w' : WeylGroup .E6}
    (h : ∀ u, triPairing x (w • u) = triPairing x u)
    (h' : ∀ u, triPairing x (w' • u) = triPairing x u) :
    ∀ u, triPairing x ((w * w') • u) = triPairing x u := fun u => by
  rw [mul_smul, h, h']

theorem fixes_pow {x : Fin Tag.E6.rank → ZMod 3} {w : WeylGroup .E6}
    (h : ∀ u, triPairing x (w • u) = triPairing x u) (n : ℕ) :
    ∀ u, triPairing x ((w ^ n) • u) = triPairing x u := by
  induction n with
  | zero => intro u; rw [pow_zero, one_smul]
  | succ n ih => rw [pow_succ]; exact fixes_mul ih h

theorem fixes_qp {x : Fin Tag.E6.rank → ZMod 3} {q₁ q₂ : Coord}
    (h₁ : ∀ u, triPairing x (mW q₁ • u) = triPairing x u)
    (h₂ : ∀ u, triPairing x (mW q₂ • u) = triPairing x u) (a b : ℕ) :
    ∀ u, triPairing x (mW (qp q₁ q₂ a b) • u) = triPairing x u := by
  rw [mW_qp]
  exact fixes_mul (fixes_pow h₁ a) (fixes_pow h₂ b)

theorem isFixed_of_fixes {x : Fin Tag.E6.rank → ZMod 3} {q : Coord}
    (h : ∀ u, triPairing x (mW q • u) = triPairing x u) :
    isFixed (fun j => wordAct .E6 (modelWordE6 q.1 q.2) (Pi.single j 1)) x = true := by
  rw [isFixed, List.all_eq_true]
  intro j _
  rw [decide_eq_true_eq, dot6_eq, ← CFSG.StandardType.TableBExc.wordProd_smul, ← mW_eq, h,
    triPairing_single]

theorem sum_rowW_mul {cols : Fin Tag.E6.rank → Fin Tag.E6.rank → ℤ} {x : Fin Tag.E6.rank → ZMod 3}
    (hx : isFixed cols x = true) (j : Fin Tag.E6.rank) : ∑ i', rowW cols j i' * x i' = 0 := by
  rw [isFixed, List.all_eq_true] at hx
  have hfix := of_decide_eq_true (hx j (List.mem_finRange _))
  rw [dot6_eq, triPairing] at hfix
  have e : ∀ i', rowW cols j i' * x i' =
      (cols j i' : ZMod 3) * x i' - if j = i' then x i' else 0 := by
    intro i'
    simp only [rowW]
    split_ifs <;> ring
  have e2 : ∑ i', rowW cols j i' * x i' = ∑ i', (cols j i' : ZMod 3) * x i' -
      ∑ i', (if j = i' then x i' else 0) := by
    rw [Finset.sum_congr rfl fun i' _ => e i']
    exact Finset.sum_sub_distrib _ _
  rw [e2, Finset.sum_ite_eq, if_pos (Finset.mem_univ _), sub_eq_zero, ← hfix]
  exact Finset.sum_congr rfl fun i' _ => mul_comm _ _

theorem eq_sum_of_identity {m k : ℕ} (f P : Fin m → Fin Tag.E6.rank → ZMod 3)
    (s r : Fin k → Fin Tag.E6.rank → ZMod 3)
    (hid : ∀ i i', (∑ a, f a i * P a i') + (∑ b, s b i * r b i') = if i = i' then 1 else 0)
    {x : Fin Tag.E6.rank → ZMod 3} (hr : ∀ b, ∑ i', r b i' * x i' = 0) (i : Fin Tag.E6.rank) :
    x i = ∑ a, f a i * ∑ i', P a i' * x i' := by
  calc x i = ∑ i', (if i = i' then 1 else 0) * x i' := by
        simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    _ = ∑ i', ((∑ a, f a i * P a i') + (∑ b, s b i * r b i')) * x i' :=
        Finset.sum_congr rfl fun i' _ => by rw [hid]
    _ = (∑ a, f a i * ∑ i', P a i' * x i') + ∑ b, s b i * ∑ i', r b i' * x i' := by
        simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum, mul_assoc]
        rw [Finset.sum_comm, Finset.sum_comm (f := fun x y => s y i * (r y x * _))]
    _ = ∑ a, f a i * ∑ i', P a i' * x i' := by
        simp only [hr, mul_zero, Finset.sum_const_zero, add_zero]

set_option maxRecDepth 10000 in
theorem exists_lineCoef : ∀ c : Fin 2 → ZMod 3, c ≠ 0 →
    ∃ (l : Fin 4) (t : ZMod 3), t ≠ 0 ∧ c = t • lineCoef l := by
  decide +kernel

theorem eq_lineVec_of_subCert {c : SubCert} (hc : c.check = true) {x : Fin Tag.E6.rank → ZMod 3}
    (hx0 : x ≠ 0) (h₁ : isFixed (genCols c 0) x = true) (h₂ : isFixed (genCols c 1) x = true) :
    ∃ (l : Fin 4) (t : ZMod 3), x = t • lineVec c.f l := by
  simp only [SubCert.check, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    decide_eq_true_eq, true_implies] at hc
  obtain ⟨⟨-, hid⟩, -⟩ := hc
  set r : Fin 4 → Fin Tag.E6.rank → ZMod 3 :=
    fun b i' => rowW (genCols c (c.rows b).1) (c.rows b).2 i' with hr
  have hid' : ∀ i i', (∑ a, c.f a i * c.P a i') + (∑ b, c.s b i * r b i') =
      if i = i' then 1 else 0 := by
    intro i i'
    rw [Fin.sum_univ_two, Fin.sum_univ_four, ← hid i i']
    simp only [hr]
    ring
  have hfixr : ∀ b, ∑ i', r b i' * x i' = 0 := by
    intro b
    simp only [hr]
    have hg : ∀ g : Fin 2, isFixed (genCols c g) x = true := by
      intro g
      fin_cases g
      · exact h₁
      · exact h₂
    exact sum_rowW_mul (hg _) _
  set d : Fin 2 → ZMod 3 := fun a => ∑ i', c.P a i' * x i' with hd
  have hxd : x = d 0 • c.f 0 + d 1 • c.f 1 := by
    funext i
    rw [eq_sum_of_identity c.f c.P c.s r hid' hfixr i, Fin.sum_univ_two]
    simp only [hd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hd0 : d ≠ 0 := by
    intro h0
    apply hx0
    rw [hxd, h0]
    simp
  obtain ⟨l, t, -, hl⟩ := exists_lineCoef d hd0
  refine ⟨l, t, ?_⟩
  rw [hxd, hl]
  funext i
  simp only [lineVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem exists_reflections_of_order_nine {q₁ q₂ : Coord} (hp₁ : isPlanes q₁ = true)
    (hp₂ : isPlanes q₂ = true) (hc : qmul q₁ q₂ = qmul q₂ q₁) (hne₁ : q₂ ≠ qone)
    (hne₂ : q₂ ≠ q₁) (hne₃ : q₂ ≠ qmul q₁ q₁) {x : Fin Tag.E6.rank → ZMod 3} (hx0 : x ≠ 0)
    (hx₁ : ∀ u, triPairing x (mW q₁ • u) = triPairing x u)
    (hx₂ : ∀ u, triPairing x (mW q₂ • u) = triPairing x u) :
    ∃ a b : ℕ, qp q₁ q₂ a b ≠ qone ∧ ∃ R : List (List (Fin Tag.E6.rank) × Fin Tag.E6.rank),
      mW (qp q₁ q₂ a b) = (R.map fun p => (coxeterSystem .E6).wordProd p.1 * simple .E6 p.2 *
        ((coxeterSystem .E6).wordProd p.1)⁻¹).prod ∧
      ∀ p ∈ R, triPairing x ((coxeterSystem .E6).wordProd p.1 • Pi.single p.2 1) = 0 := by
  have hall := pairOK_all
  rw [List.all_eq_true] at hall
  have hpair := hall q₁ (mem_allQ q₁)
  rw [List.all_eq_true] at hpair
  have h := hpair q₂ (mem_allQ q₂)
  simp only [pairOK, hp₁, hp₂, hc, hne₁, hne₂, hne₃, decide_true, decide_false, Bool.and_true,
    Bool.not_false, Bool.true_and, Bool.not_true, Bool.false_or, Bool.or_eq_true,
    List.any_eq_true, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨a, -, b, -, hab, hrefl⟩ | ⟨j, -, ⟨hg₁, hg₂⟩, hlines⟩
  ·
    refine ⟨a, b, ?_, ?_⟩
    · simpa using hab
    have hcheck := modelCert_check (qp q₁ q₂ a b).1 (qp q₁ q₂ a b).2
    rw [isRefl] at hrefl
    generalize modelCert (qp q₁ q₂ a b).1 (qp q₁ q₂ a b).2 = M at hcheck hrefl
    cases M with
    | refl R =>
      refine ⟨R.map fun r => (r.u, r.i), ?_, fun p hp => ?_⟩
      · rw [mW_eq, wordProd_eq_of_check_refl hcheck, List.map_map]
        rfl
      · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hp
        have hfix := fixes_qp hx₁ hx₂ a b
        rw [mW_eq] at hfix
        exact triPairing_eq_zero_of_check_refl hcheck hfix hr
    | nine _ => simp at hrefl
    | planes cols f P s jk cs => simp at hrefl
  ·
    set c := subCerts.getD j default with hcdef
    have hcc : c.check = true := by
      have := subCerts_check
      rw [List.all_eq_true] at this
      exact this j (List.mem_finRange j)
    obtain ⟨a₁, b₁, he₁⟩ := exists_of_mem_spanQ hg₁
    obtain ⟨a₂, b₂, he₂⟩ := exists_of_mem_spanQ hg₂
    have hfix₁ : isFixed (genCols c 0) x = true := by
      have := isFixed_of_fixes (q := c.g₁) (by rw [he₁]; exact fixes_qp hx₁ hx₂ a₁ b₁)
      exact this
    have hfix₂ : isFixed (genCols c 1) x = true := by
      have := isFixed_of_fixes (q := c.g₂) (by rw [he₂]; exact fixes_qp hx₁ hx₂ a₂ b₂)
      exact this
    obtain ⟨l, t, hxl⟩ := eq_lineVec_of_subCert hcc hx0 hfix₁ hfix₂
    have hl := hlines l (List.mem_finRange l)
    obtain ⟨a, b, hab⟩ := exists_of_mem_spanQ hl
    simp only [SubCert.check, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
      true_implies] at hcc
    obtain ⟨-, hcl⟩ := hcc
    have hcl' := hcl l
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
      List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] at hcl'
    obtain ⟨⟨hne, hprod⟩, hroots⟩ := hcl'
    refine ⟨a, b, ?_, (c.lines.getD l default).2.2, ?_, fun p hp => ?_⟩
    · rw [← hab]
      exact hne
    · rw [← hab, ← wordProd_flatMap_reflWordP, mW_eq]
      refine CFSG.LieType.Chevalley.ext_single fun i => ?_
      rw [CFSG.StandardType.TableBExc.wordProd_smul, CFSG.StandardType.TableBExc.wordProd_smul]
      exact veqZ_iff.1 (hprod i)
    · rw [hxl, triPairing_smul_left, CFSG.StandardType.TableBExc.wordProd_smul, ← dot6_eq,
        hroots p hp, mul_zero]

end CFSG.LieType.Chevalley.E6Three.ModelKernel
