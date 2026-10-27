module

public import CFSG.Monster.B.Pinned.Primes.SixPrimes
public import CFSG.Monster.B.Intertwiner.PairFacts
public import Certificates.Data.CFSGNative.MonsterB.IntertwinerCheck
public import Certificates.Data.CFSGNative.MonsterB.Primes
public import CFSG.Monster.Existence.BabyTableIVOf
public import CFSG.Monster.Existence.BabyW2Classes
public import Certificates.Certificate17101
public import CFSG.Monster.B.Pinned.Primes.SeedGL

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven

open CFSG.Monster.B CFSG.Monster.B.Bin CFSG.Monster.B.Primes.Native CFSG.Monster.B.Pinned CFSG.Blueprint

local notation "sm" => CFSG.KC.BM.stripMat

local notation "SM" =>
  NativeSporadic.seedMonoid 2 4370 1 NativeSporadic.BSeed1 NativeSporadic.BSeed2

theorem mul_pow_eq_one_of {M : Type*} [Monoid M] {a : M} {n : ℕ} (h : a ^ (n + 1) = 1) :
    a * a ^ n = 1 ∧ a ^ n * a = 1 :=
  ⟨by rw [← pow_succ']; exact h, by rw [← pow_succ]; exact h⟩

theorem pow_seventy_of {M : Type*} [Monoid M] {g y : M} (hy : y = g ^ 14) (hy5 : y ^ 5 = 1) :
    g ^ (69 + 1) = 1 := by
  have e : g ^ (69 + 1) = (g ^ 14) ^ 5 := pow_mul g 14 5
  rw [e, ← hy, hy5]

section Elements

theorem fact17101 : CFSG.KC.BM.SevenFacts.Fact17101 := Certificates.certificate17101.1

theorem elems_mem : sm CFSG.KC.BM.Seven.g ∈ SM ∧ sm CFSG.KC.BM.Seven.al ∈ SM ∧
    sm CFSG.KC.BM.Seven.t1 ∈ SM ∧ sm CFSG.KC.BM.Seven.e3 ∈ SM := by
  refine Certificates.certificate17101.2.2.2 _ ?_ ?_
  · rw [← Certificates.certificate17101.2.1]
    exact genA₁_mem
  · rw [← Certificates.certificate17101.2.2.1]
    exact genA₂_mem

theorem g_pow_seventy : sm CFSG.KC.BM.Seven.g ^ (69 + 1) = 1 := by
  obtain ⟨⟨-, -, hy, -⟩, -, -, -, -, -, -, -, hy5, -⟩ := fact17101
  exact pow_seventy_of hy hy5

theorem al_sq : sm CFSG.KC.BM.Seven.al * sm CFSG.KC.BM.Seven.al = 1 := by
  obtain ⟨-, h, -⟩ := fact17101
  exact h

theorem t1_sq : sm CFSG.KC.BM.Seven.t1 * sm CFSG.KC.BM.Seven.t1 = 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h, -⟩ := fact17101
  exact h

theorem e3_cube : sm CFSG.KC.BM.Seven.e3 ^ (2 + 1) = 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := fact17101
  exact h

@[expose] noncomputable def gSeven : NativeSporadic.B where
  val := ⟨sm CFSG.KC.BM.Seven.g, elems_mem.1⟩
  inv := ⟨sm CFSG.KC.BM.Seven.g ^ 69, pow_mem elems_mem.1 69⟩
  val_inv := Subtype.ext (mul_pow_eq_one_of g_pow_seventy).1
  inv_val := Subtype.ext (mul_pow_eq_one_of g_pow_seventy).2

@[expose] noncomputable def alphaB : NativeSporadic.B where
  val := ⟨sm CFSG.KC.BM.Seven.al, elems_mem.2.1⟩
  inv := ⟨sm CFSG.KC.BM.Seven.al, elems_mem.2.1⟩
  val_inv := Subtype.ext al_sq
  inv_val := Subtype.ext al_sq

@[expose] noncomputable def xSeven : NativeSporadic.B := gSeven ^ 10

@[expose] noncomputable def ySeven : NativeSporadic.B := gSeven ^ 14

@[expose] noncomputable def tauOne : NativeSporadic.B where
  val := ⟨sm CFSG.KC.BM.Seven.t1, elems_mem.2.2.1⟩
  inv := ⟨sm CFSG.KC.BM.Seven.t1, elems_mem.2.2.1⟩
  val_inv := Subtype.ext t1_sq
  inv_val := Subtype.ext t1_sq

@[expose] noncomputable def tauTwo : NativeSporadic.B := ySeven ^ 3 * tauOne * ySeven ^ 2

@[expose] noncomputable def eSeven : NativeSporadic.B where
  val := ⟨sm CFSG.KC.BM.Seven.e3, elems_mem.2.2.2⟩
  inv := ⟨sm CFSG.KC.BM.Seven.e3 ^ 2, pow_mem elems_mem.2.2.2 2⟩
  val_inv := Subtype.ext (mul_pow_eq_one_of e3_cube).1
  inv_val := Subtype.ext (mul_pow_eq_one_of e3_cube).2

theorem bMat_alphaB : bMat alphaB = sm CFSG.KC.BM.Seven.al := rfl

theorem bMat_tauOne : bMat tauOne = sm CFSG.KC.BM.Seven.t1 := rfl

theorem bMat_eSeven : bMat eSeven = sm CFSG.KC.BM.Seven.e3 := rfl

theorem bMat_xSeven : bMat xSeven = sm CFSG.KC.BM.Seven.x := by
  obtain ⟨⟨-, hx, -⟩, -⟩ := fact17101
  rw [hx, xSeven, map_pow]
  rfl

theorem bMat_ySeven : bMat ySeven = sm CFSG.KC.BM.Seven.y := by
  obtain ⟨⟨-, -, hy, -⟩, -⟩ := fact17101
  rw [hy, ySeven, map_pow]
  rfl

theorem bMat_tauTwo : bMat tauTwo = sm CFSG.KC.BM.Seven.t2 := by
  obtain ⟨⟨-, -, -, ht⟩, -⟩ := fact17101
  rw [ht, tauTwo, map_mul, map_mul, map_pow, map_pow, bMat_ySeven, bMat_tauOne]

end Elements

structure ElemParts (alphaB xSeven ySeven tauOne tauTwo eSeven : NativeSporadic.B) : Prop where
  alpha_sq : alphaB ^ 2 = 1
  alpha_ne : alphaB ≠ 1
  alpha_rank : Matrix.rank (alphaB.val.val - 1) = 1860
  alpha_x : alphaB * xSeven = xSeven * alphaB
  alpha_y : alphaB * ySeven = ySeven * alphaB
  x_pow : xSeven ^ 7 = 1
  x_ne : xSeven ≠ 1
  y_pow : ySeven ^ 5 = 1
  y_ne : ySeven ≠ 1
  x_y : xSeven * ySeven = ySeven * xSeven
  tauOne_sq : tauOne * tauOne = 1
  tauOne_rank : Matrix.rank (tauOne.val.val - 1) = 1860
  tauOne_x : tauOne * xSeven = xSeven * tauOne
  tauOne_alpha : tauOne * alphaB = alphaB * tauOne
  tauOne_ne_alpha : tauOne ≠ alphaB
  tauTwo_sq : tauTwo * tauTwo = 1
  tauTwo_rank : Matrix.rank (tauTwo.val.val - 1) = 1860
  tauTwo_x : tauTwo * xSeven = xSeven * tauTwo
  tauOne_tauTwo : tauOne * tauTwo = tauTwo * tauOne
  tauOne_ne_tauTwo : tauOne ≠ tauTwo
  tau_rank : Matrix.rank ((tauOne * tauTwo).val.val - 1) = 2048
  e_pow : eSeven ^ 3 = 1
  e_ne : eSeven ≠ 1
  e_x : eSeven * xSeven = xSeven * eSeven
  e_tauOne : eSeven * tauOne = tauOne * eSeven
  e_alpha : eSeven * alphaB = alphaB * eSeven
  w_pow : (tauOne * eSeven) ^ 6 = 1
  w_sq_ne : (tauOne * eSeven) ^ 2 ≠ 1
  w_cube : (tauOne * eSeven) ^ 3 = tauOne
  c_ne_one : tauOne * ySeven * tauOne * ySeven ^ 4 ≠ 1
  c_ne_alpha : tauOne * ySeven * tauOne * ySeven ^ 4 ≠ alphaB

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)

theorem elemParts_of {a x y t₁ t₂ e : NativeSporadic.B} {Al X Y T1 T2 E : MatB}
    (ha : bMat a = Al) (hx : bMat x = X) (hy : bMat y = Y) (ht₁ : bMat t₁ = T1)
    (ht₂ : bMat t₂ = T2) (he : bMat e = E)
    (F : CFSG.KC.BM.SevenFacts.Fact17101Of Al X Y T1 T2 E) : ElemParts a x y t₁ t₂ e := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19,
    f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31⟩ := F
  have inj : ∀ {g h : NativeSporadic.B}, bMat g = bMat h → g = h := fun h => bMat_injective h
  have rk : ∀ (g : NativeSporadic.B) (G : MatB), bMat g = G →
      Matrix.rank (g.val.val - 1) = Matrix.rank (G - 1) := fun g _ hg => by
    change Matrix.rank (bMat g - 1) = _
    rw [hg]
  refine ⟨inj ?_, fun h => f2 ?_, (rk a Al ha).trans f3, inj ?_, inj ?_, inj ?_, fun h => f7 ?_,
    inj ?_, fun h => f9 ?_, inj ?_, inj ?_, (rk t₁ T1 ht₁).trans f12, inj ?_, inj ?_,
    fun h => f15 ?_, inj ?_, (rk t₂ T2 ht₂).trans f17, inj ?_, inj ?_, fun h => f20 ?_,
    (rk (t₁ * t₂) (T1 * T2) (by rw [map_mul, ht₁, ht₂])).trans f21, inj ?_, fun h => f23 ?_,
    inj ?_, inj ?_, inj ?_, inj ?_, fun h => f28 ?_, inj ?_, fun h => f30 ?_, fun h => f31 ?_⟩
  · rw [map_pow, map_one, ha, sq]
    exact f1
  · rw [← ha, h, map_one]
  · rw [map_mul, map_mul, ha, hx]
    exact f4
  · rw [map_mul, map_mul, ha, hy]
    exact f5
  · rw [map_pow, map_one, hx]
    exact f6
  · rw [← hx, h, map_one]
  · rw [map_pow, map_one, hy]
    exact f8
  · rw [← hy, h, map_one]
  · rw [map_mul, map_mul, hx, hy]
    exact f10
  · rw [map_mul, map_one, ht₁]
    exact f11
  · rw [map_mul, map_mul, ht₁, hx]
    exact f13
  · rw [map_mul, map_mul, ht₁, ha]
    exact f14
  · rw [← ht₁, ← ha, h]
  · rw [map_mul, map_one, ht₂]
    exact f16
  · rw [map_mul, map_mul, ht₂, hx]
    exact f18
  · rw [map_mul, map_mul, ht₁, ht₂]
    exact f19
  · rw [← ht₁, ← ht₂, h]
  · rw [map_pow, map_one, he]
    exact f22
  · rw [← he, h, map_one]
  · rw [map_mul, map_mul, he, hx]
    exact f24
  · rw [map_mul, map_mul, he, ht₁]
    exact f25
  · rw [map_mul, map_mul, he, ha]
    exact f26
  · rw [map_pow, map_mul, map_one, ht₁, he]
    exact f27
  · have h' := congrArg bMat h
    rw [map_pow, map_mul, map_one, ht₁, he] at h'
    exact h'
  · rw [map_pow, map_mul, ht₁, he]
    exact f29
  · have h' := congrArg bMat h
    rw [map_mul, map_mul, map_mul, map_pow, map_one, ht₁, hy] at h'
    exact h'
  · have h' := congrArg bMat h
    rw [map_mul, map_mul, map_mul, map_pow, ht₁, hy, ha] at h'
    exact h'

theorem bSevenElem_parts :
    ElemParts alphaB xSeven ySeven tauOne tauTwo eSeven :=
  elemParts_of bMat_alphaB bMat_xSeven bMat_ySeven bMat_tauOne bMat_tauTwo bMat_eSeven
    fact17101.2

section Classes

theorem babyInv_zero_of_rank_1860 {X : NativeSporadic.B} (hX : orderOf X = 2)
    (hr : Matrix.rank (X.val.val - 1) = 1860) : CFSG.Monster.GMS.BabyInv 0 X :=
  CFSG.Monster.GMS.BabyInv.of_isConj CFSG.Monster.Existence.babyInv_zero_babyRep_one
    (CFSG.Monster.Existence.isConj_rep_one_of_rank hX hr).symm

theorem bSeven_elements_of_parts {alphaB xSeven ySeven tauOne tauTwo eSeven : NativeSporadic.B}
    (P : ElemParts alphaB xSeven ySeven tauOne tauTwo eSeven) :
    ∃ x α y a b w : NativeSporadic.B, orderOf x = 7 ∧ CFSG.Monster.GMS.BabyInv 0 α ∧
      α * x = x * α ∧ CFSG.Monster.GMS.BabyInv 0 a ∧ CFSG.Monster.GMS.BabyInv 0 b ∧
      CFSG.Monster.GMS.BabyInv 1 (a * b) ∧ a * x = x * a ∧ b * x = x * b ∧ a * b = b * a ∧
      a ≠ b ∧ a * α = α * a ∧ a ≠ α ∧ orderOf y = 5 ∧ y * x = x * y ∧ y * α = α * y ∧
      w * x = x * w ∧ w * α = α * w ∧ w ^ 6 = 1 ∧ w ^ 2 ≠ 1 ∧ w ^ 3 = a ∧
      a * y * a⁻¹ * y⁻¹ ≠ 1 ∧ a * y * a⁻¹ * y⁻¹ ≠ α := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hne_of_rank : ∀ {g : NativeSporadic.B} {r : ℕ}, 0 < r →
      Matrix.rank (g.val.val - 1) = r → g ≠ 1 := by
    intro g r hr hrk hg
    subst hg
    simp at hrk
    omega
  have hord2 : ∀ {g : NativeSporadic.B}, g * g = 1 → g ≠ 1 → orderOf g = 2 := fun h1 h2' =>
    orderOf_eq_prime (by rw [sq]; exact h1) h2'
  have hinv : ∀ {g : NativeSporadic.B}, g * g = 1 → g⁻¹ = g := fun h1 => inv_eq_of_mul_eq_one_right h1
  have hyinv : ySeven⁻¹ = ySeven ^ 4 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ']
    exact P.y_pow
  have hα2 : orderOf alphaB = 2 := by
    refine hord2 (by rw [← sq]; exact P.alpha_sq) P.alpha_ne
  have ha2 : orderOf tauOne = 2 := hord2 P.tauOne_sq (hne_of_rank (by norm_num) P.tauOne_rank)
  have hb2 : orderOf tauTwo = 2 := hord2 P.tauTwo_sq (hne_of_rank (by norm_num) P.tauTwo_rank)
  have habsq : (tauOne * tauTwo) * (tauOne * tauTwo) = 1 := by
    calc tauOne * tauTwo * (tauOne * tauTwo) = tauOne * (tauTwo * tauOne) * tauTwo := by group
      _ = tauOne * (tauOne * tauTwo) * tauTwo := by rw [P.tauOne_tauTwo]
      _ = (tauOne * tauOne) * (tauTwo * tauTwo) := by group
      _ = 1 := by rw [P.tauOne_sq, P.tauTwo_sq, one_mul]
  have hab2 : orderOf (tauOne * tauTwo) = 2 :=
    hord2 habsq (hne_of_rank (by norm_num) P.tau_rank)
  have hw : tauOne * eSeven * xSeven = xSeven * (tauOne * eSeven) := by
    rw [mul_assoc, P.e_x, ← mul_assoc, P.tauOne_x, mul_assoc]
  have hwα : tauOne * eSeven * alphaB = alphaB * (tauOne * eSeven) := by
    rw [mul_assoc, P.e_alpha, ← mul_assoc, P.tauOne_alpha, mul_assoc]
  refine ⟨xSeven, alphaB, ySeven, tauOne, tauTwo, tauOne * eSeven,
    orderOf_eq_prime P.x_pow P.x_ne,
    babyInv_zero_of_rank_1860 hα2 P.alpha_rank, P.alpha_x,
    babyInv_zero_of_rank_1860 ha2 P.tauOne_rank, babyInv_zero_of_rank_1860 hb2 P.tauTwo_rank,
    CFSG.Monster.Existence.babyInv_one_of_rank_2048 hab2 P.tau_rank,
    P.tauOne_x, P.tauTwo_x, P.tauOne_tauTwo, P.tauOne_ne_tauTwo, P.tauOne_alpha,
    P.tauOne_ne_alpha, orderOf_eq_prime P.y_pow P.y_ne, P.x_y.symm, P.alpha_y.symm,
    hw, hwα, P.w_pow, P.w_sq_ne, P.w_cube, ?_, ?_⟩
  · rw [hinv P.tauOne_sq, hyinv]
    exact P.c_ne_one
  · rw [hinv P.tauOne_sq, hyinv]
    exact P.c_ne_alpha

theorem bSeven_elements :
    ∃ x α y a b w : NativeSporadic.B, orderOf x = 7 ∧ CFSG.Monster.GMS.BabyInv 0 α ∧
      α * x = x * α ∧ CFSG.Monster.GMS.BabyInv 0 a ∧ CFSG.Monster.GMS.BabyInv 0 b ∧
      CFSG.Monster.GMS.BabyInv 1 (a * b) ∧ a * x = x * a ∧ b * x = x * b ∧ a * b = b * a ∧
      a ≠ b ∧ a * α = α * a ∧ a ≠ α ∧ orderOf y = 5 ∧ y * x = x * y ∧ y * α = α * y ∧
      w * x = x * w ∧ w * α = α * w ∧ w ^ 6 = 1 ∧ w ^ 2 ≠ 1 ∧ w ^ 3 = a ∧
      a * y * a⁻¹ * y⁻¹ ≠ 1 ∧ a * y * a⁻¹ * y⁻¹ ≠ α :=
  bSeven_elements_of_parts bSevenElem_parts

end Classes

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven
