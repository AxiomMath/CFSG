
module

public import CFSG.GF2Type.Smith1979.IdxFourIdentFLDefs
public import CFSG.GF2Type.Smith1979.IdxFourIdentMon2

public section

namespace CFSG.GF2Type.Smith1979.IdxFour

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA

namespace FLCheck

@[expose] def appL : List ℕ → ℕ → ℕ
  | [], _ => 0
  | r :: l, n => Nat.xor (Nat.mul (Nat.mod n 2) r) (appL l (Nat.div n 2))

theorem vecOf_appL (l : List ℕ) (n : ℕ) :
    vecOf (appL l n) =
      ∑ j ∈ Finset.range l.length, (if n.testBit j then (1 : ZMod 2) else 0) • vecOf l[j]! := by
  induction l generalizing n with
  | nil => simp [appL]
  | cons r l ih =>
    change vecOf (n % 2 * r ^^^ appL l (n / 2)) = _
    rw [vecOf_xor, ih, List.length_cons, Finset.sum_range_succ', add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [List.getElem!_cons_succ, Nat.testBit_add_one]
    · rw [List.getElem!_cons_zero, Nat.testBit_zero]
      rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h]

theorem appL_spec {l : List ℕ} (hl : l.length = 12) (n : ℕ) :
    vecOf (appL l n) = linOfRows l.toArray (vecOf n) := by
  rw [vecOf_appL, hl, linOfRows_apply, Finset.sum_range (fun j =>
    (if n.testBit j then (1 : ZMod 2) else 0) • vecOf l[j]!)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [List.getElem!_toArray]
  rfl

theorem appL_zero (l : List ℕ) : appL l 0 = 0 := by
  induction l with
  | nil => rfl
  | cons r l ih =>
    change 0 % 2 * r ^^^ appL l (0 / 2) = 0
    rw [Nat.zero_div, ih]
    simp

@[expose] def mulL (g h : List ℕ) : List ℕ := h.map (appL g)

theorem length_mulL (g h : List ℕ) : (mulL g h).length = h.length := List.length_map _

theorem getElem!_mulL (g h : List ℕ) (j : ℕ) : (mulL g h)[j]! = appL g h[j]! := by
  by_cases hj : j < h.length
  · rw [getElem!_pos (mulL g h) j (by rw [length_mulL]; exact hj), getElem!_pos h j hj]
    exact List.getElem_map _
  · rw [getElem!_neg (mulL g h) j (by rw [length_mulL]; exact hj), getElem!_neg h j hj]
    exact (appL_zero g).symm

theorem mulL_spec {g : List ℕ} (hg : g.length = 12) (h : List ℕ) (x : V12) :
    linOfRows (mulL g h).toArray x = linOfRows g.toArray (linOfRows h.toArray x) := by
  have hf : linOfRows (mulL g h).toArray = (linOfRows g.toArray).comp (linOfRows h.toArray) :=
    linMap_ext fun j => by
      rw [LinearMap.comp_apply, linOfRows_unit, linOfRows_unit, List.getElem!_toArray,
        List.getElem!_toArray, getElem!_mulL, appL_spec hg]
  exact LinearMap.congr_fun hf x

@[expose] def HasRows (g : G12) (r : List ℕ) : Prop :=
  r.length = 12 ∧ ∀ x, g x = linOfRows r.toArray x

theorem HasRows.mul {g h : G12} {r s : List ℕ} (hg : HasRows g r) (hh : HasRows h s) :
    HasRows (g * h) (mulL r s) :=
  ⟨by rw [length_mulL]; exact hh.1, fun x => by
    rw [LinearEquiv.mul_apply, hh.2, hg.2, mulL_spec hg.1]⟩

theorem HasRows.eq {g h : G12} {r : List ℕ} (hg : HasRows g r) (hh : HasRows h r) : g = h :=
  LinearEquiv.ext fun x => (hg.2 x).trans (hh.2 x).symm

@[expose] def idL : List ℕ := [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

theorem eq_one_of_hasRows {g : G12} {r : List ℕ} (hg : HasRows g r) (h : r = idL) : g = 1 :=
  LinearEquiv.ext fun x => by
    rw [hg.2, h]
    exact linOfRows_idR x

@[expose] def notIdL (r : List ℕ) : Bool :=
  (List.range 12).any fun j => decide (r[j]! < 4096) && r[j]! != 2 ^ j

theorem ne_one_of_hasRows {g : G12} {r : List ℕ} (hg : HasRows g r) (h : notIdL r = true) :
    g ≠ 1 := by
  simp only [notIdL, List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    bne_iff_ne, ne_eq] at h
  obtain ⟨j, hj, hlt, hne⟩ := h
  intro h1
  have hu := linOfRows_unit r.toArray ⟨j, hj⟩
  simp only [List.getElem!_toArray] at hu
  rw [← hg.2, h1] at hu
  exact hne (vecOf_inj hlt (two_pow_lt ⟨j, hj⟩) hu.symm)

@[expose] def pow3L (r : List ℕ) : List ℕ := mulL r (mulL r r)

@[expose] def pow11L (r : List ℕ) : List ℕ :=
  let r2 := mulL r r
  let r4 := mulL r2 r2
  mulL (mulL r4 r4) (mulL r2 r)

theorem HasRows.pow3 {g : G12} {r : List ℕ} (hg : HasRows g r) : HasRows (g ^ 3) (pow3L r) := by
  rw [show g ^ 3 = g * (g * g) by simp only [pow_succ, pow_zero, one_mul, mul_assoc]]
  exact hg.mul (hg.mul hg)

theorem HasRows.pow11 {g : G12} {r : List ℕ} (hg : HasRows g r) :
    HasRows (g ^ 11) (pow11L r) := by
  rw [show g ^ 11 = g * g * (g * g) * (g * g * (g * g)) * (g * g * g) by
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]]
  have h2 := hg.mul hg
  have h4 := h2.mul h2
  exact (h4.mul h4).mul (h2.mul hg)

theorem dvd_orderOf_of_pow {w : G12} {q : ℕ} (h11 : (w ^ q) ^ 11 = 1) (hne : w ^ q ≠ 1) :
    11 ∣ orderOf w := by
  have : Fact (Nat.Prime 11) := ⟨by decide⟩
  rw [← orderOf_eq_prime h11 hne]
  exact orderOf_pow_dvd q

@[expose] def frIter (ε : ZMod 2) (p : ZMod 2 × ZMod 2) : ZMod 2 × ZMod 2 :=
  if ε = 0 then p else MonAux.frPair p

theorem frobPow_pairVec (ε : ZMod 2) (i : Fin 6) (p : ZMod 2 × ZMod 2) :
    (frobE ^ ε.val) (MonAux.pairVec i p) = MonAux.pairVec i (frIter ε p) := by
  rcases MonAux.zmod2_cases ε with rfl | rfl
  · rw [MonAux.frobPow_zero]
    rfl
  · rw [MonAux.frobPow_one, MonAux.frobE_pairVec]
    rfl

theorem mon_pairVec (c : Fin 6 → ZMod 3) (π : Equiv.Perm (Fin 6)) (ε : ZMod 2) (i : Fin 6)
    (p : ZMod 2 × ZMod 2) :
    (diagE c * permE π * frobE ^ ε.val) (MonAux.pairVec i p) =
      MonAux.pairVec (π i) (omegaPow (c (π i)) (frIter ε p)) := by
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, frobPow_pairVec, MonAux.permE_pairVec,
    MonAux.diagE_pairVec]

@[expose] def pairCode (i : Fin 6) (p : ZMod 2 × ZMod 2) : ℕ :=
  p.1.val * 2 ^ (i : ℕ) + p.2.val * 2 ^ (6 + (i : ℕ))

theorem vecOf_pairCode : ∀ (i : Fin 6) (p : ZMod 2 × ZMod 2),
    vecOf (pairCode i p) = MonAux.pairVec i p := by
  decide

theorem pairCode_lo : ∀ i : Fin 6, pairCode i (1, 0) = 2 ^ (i : ℕ) := by decide

theorem pairCode_hi : ∀ i : Fin 6, pairCode i (0, 1) = 2 ^ (6 + (i : ℕ)) := by decide

@[expose] def monCode (c : Fin 6 → ZMod 3) (π : Fin 6 → Fin 6) (ε : ZMod 2) (j : Fin 6)
    (p : ZMod 2 × ZMod 2) : ℕ :=
  pairCode (π j) (omegaPow (c (π j)) (frIter ε p))

@[expose] def monRowsF (c : Fin 6 → ZMod 3) (π : Fin 6 → Fin 6) (ε : ZMod 2) : List ℕ :=
  [monCode c π ε 0 (1, 0), monCode c π ε 1 (1, 0), monCode c π ε 2 (1, 0),
    monCode c π ε 3 (1, 0), monCode c π ε 4 (1, 0), monCode c π ε 5 (1, 0),
    monCode c π ε 0 (0, 1), monCode c π ε 1 (0, 1), monCode c π ε 2 (0, 1),
    monCode c π ε 3 (0, 1), monCode c π ε 4 (0, 1), monCode c π ε 5 (0, 1)]

theorem monRowsF_lo (c : Fin 6 → ZMod 3) (π : Fin 6 → Fin 6) (ε : ZMod 2) (i : Fin 6) :
    (monRowsF c π ε)[(i : ℕ)]! = monCode c π ε i (1, 0) := by
  fin_cases i <;> rfl

theorem monRowsF_hi (c : Fin 6 → ZMod 3) (π : Fin 6 → Fin 6) (ε : ZMod 2) (i : Fin 6) :
    (monRowsF c π ε)[6 + (i : ℕ)]! = monCode c π ε i (0, 1) := by
  fin_cases i <;> rfl

theorem exists_lo_hi : ∀ j : Fin 12, ∃ i : Fin 6, j = lo i ∨ j = hi i := by decide

theorem mon_hasRows (c : Fin 6 → ZMod 3) (π : Equiv.Perm (Fin 6)) (ε : ZMod 2) :
    HasRows (diagE c * permE π * frobE ^ ε.val) (monRowsF c π ε) := by
  have hf : ((diagE c * permE π * frobE ^ ε.val : G12) : V12 →ₗ[ZMod 2] V12) =
      linOfRows (monRowsF c π ε).toArray := linMap_ext fun j => by
    rw [linOfRows_unit, List.getElem!_toArray, LinearEquiv.coe_coe]
    obtain ⟨i, rfl | rfl⟩ := exists_lo_hi j
    · rw [Fin.coe_castAdd, monRowsF_lo, monCode, vecOf_pairCode, ← pairCode_lo, vecOf_pairCode,
        mon_pairVec]
    · rw [Fin.coe_natAdd, monRowsF_hi, monCode, vecOf_pairCode, ← pairCode_hi, vecOf_pairCode,
        mon_pairVec]
  exact ⟨rfl, fun x => LinearMap.congr_fun hf x⟩

@[expose] def cF (m : MonData) : Fin 6 → ZMod 3 := fun i => (m.c[(i : ℕ)]! : ZMod 3)

@[expose] def pF (m : MonData) : Fin 6 → Fin 6 :=
  fun j => ⟨m.p[(j : ℕ)]! % 6, Nat.mod_lt _ (by norm_num)⟩

@[expose] def monRows (m : MonData) : List ℕ := monRowsF (cF m) (pF m) (m.e : ZMod 2)

@[expose] def monOK (m : MonData) : Bool :=
  decide (Function.Surjective (pF m)) && decide (∑ i, cF m i = 0)

theorem exists_Nsub {m : MonData} (h : monOK m = true) : ∃ g ∈ Nsub, HasRows g (monRows m) := by
  simp only [monOK, Bool.and_eq_true, decide_eq_true_eq] at h
  let π : Equiv.Perm (Fin 6) :=
    Equiv.ofBijective (pF m) ⟨Finite.injective_iff_surjective.2 h.1, h.1⟩
  exact ⟨_, mem_Nsub_iff.2 ⟨cF m, π, _, h.2, rfl⟩, mon_hasRows (cF m) π (m.e : ZMod 2)⟩

@[expose] def deltaRows (s : ZMod 3) : List ℕ := monRowsF (fun i => if i = 0 then s else 0) id 0

theorem Delta0_hasRows (s : ZMod 3) : HasRows (Delta0 s) (deltaRows s) := by
  have h := mon_hasRows (fun i => if i = 0 then s else 0) 1 0
  rwa [permE_one, ZMod.val_zero, pow_zero, mul_one, mul_one] at h

theorem uRows_len : ∀ a b : Fin 4, (uRowsTable[4 * (a : ℕ) + (b : ℕ)]!).toList.length = 12 := by
  decide +kernel

theorem Umat_hasRows (a b : Fin 4) :
    HasRows (Umat a b) (uRowsTable[4 * (a : ℕ) + (b : ℕ)]!).toList :=
  ⟨uRows_len a b, fun x => Umat_apply a b x⟩

theorem y3e_hasRows : HasRows y3e y3Rows.toList := ⟨rfl, fun x => y3e_apply x⟩

theorem q0_add (x y : V12) : q0 (x + y) = q0 x + q0 y + f0 x y := by
  have h := polar_q0 x y
  rw [QuadraticMap.polar] at h
  rw [← h]
  ring

theorem f0_comm (x y : V12) : f0 x y = f0 y x := by
  unfold f0
  exact Finset.sum_congr rfl fun i _ => by ring

theorem f0_smul_left (c : ZMod 2) (x y : V12) : f0 (c • x) y = c * f0 x y := by
  unfold f0
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

theorem q0_smul (c : ZMod 2) (x : V12) : q0 (c • x) = c * q0 x := by
  rcases MonAux.zmod2_cases c with rfl | rfl
  · simp [q0]
  · simp

theorem f0_zero_left (y : V12) : f0 0 y = 0 := by simp [f0]

theorem q0_linOfRows {r : Array ℕ}
    (hq : ∀ j : Fin 12, q0 (vecOf r[(j : ℕ)]!) = q0 (vecOf (2 ^ (j : ℕ))))
    (hf : ∀ j k : Fin 12, f0 (vecOf r[(j : ℕ)]!) (vecOf r[(k : ℕ)]!) =
      f0 (vecOf (2 ^ (j : ℕ))) (vecOf (2 ^ (k : ℕ)))) (x : V12) :
    q0 (linOfRows r x) = q0 x := by
  have hx : x = ∑ j : Fin 12, x j • vecOf (2 ^ (j : ℕ)) := by
    conv_lhs => rw [← linOfRows_idR x, linOfRows_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 2
    fin_cases j <;> rfl
  have key : ∀ s : Finset (Fin 12),
      q0 (∑ j ∈ s, x j • vecOf r[(j : ℕ)]!) = q0 (∑ j ∈ s, x j • vecOf (2 ^ (j : ℕ))) ∧
        ∀ k : Fin 12, f0 (∑ j ∈ s, x j • vecOf r[(j : ℕ)]!) (vecOf r[(k : ℕ)]!) =
          f0 (∑ j ∈ s, x j • vecOf (2 ^ (j : ℕ))) (vecOf (2 ^ (k : ℕ))) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨rfl, fun k => by rw [Finset.sum_empty, Finset.sum_empty, f0_zero_left,
        f0_zero_left]⟩
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      refine ⟨?_, fun k => ?_⟩
      · rw [q0_add, q0_add, q0_smul, q0_smul, f0_smul_left, f0_smul_left, f0_comm _ (∑ j ∈ s, _),
          f0_comm _ (∑ j ∈ s, _), ih.1, ih.2 i, hq i]
      · rw [f0_add_left, f0_add_left, f0_smul_left, f0_smul_left, ih.2 k, hf i k]
  rw [linOfRows_apply]
  conv_rhs => rw [hx]
  exact (key Finset.univ).1

@[expose] def zRows (k : FLCand) : List ℕ := k.z.toList

@[expose] def wRows (k : FLCand) : List ℕ :=
  mulL (zRows k) (mulL (monRows k.m1) (mulL (zRows k) (monRows k.m2)))

@[expose] def ordRows (k : FLCand) : List ℕ := if k.o = 11 then wRows k else pow3L (wRows k)

@[expose] def candBase (k : FLCand) : Bool :=
  monOK k.m1 && monOK k.m2 && (zRows k).length == 12 &&
    zRows k == mulL (uRowsTable[4 * k.a + k.b]!).toList (deltaRows (k.s : ZMod 3))

@[expose] def candGood (k : FLCand) : Bool :=
  zRows k == mulL (monRows k.m1) (mulL y3Rows.toList (monRows k.m2))

@[expose] def candBad (k : FLCand) : Bool := pow11L (ordRows k) == idL && notIdL (ordRows k)

@[expose] def candCheck (k : FLCand) : Bool :=
  candBase k && if k.good then candGood k else candBad k

theorem cands_ok : flCands.all candCheck = true := by decide +kernel

theorem cover : ∀ a b : Fin 4, ∀ s : ZMod 3, (a ≠ 0 ∨ b ≠ 0) →
    ∃ k ∈ flCands, k.a = a ∧ k.b = b ∧ k.s = s.val := by
  decide +kernel

end FLCheck

open FLCheck

theorem Umat_zero_zero : Umat 0 0 = 1 := by
  have h : (uRowsTable[4 * ((0 : Fin 4) : ℕ) + ((0 : Fin 4) : ℕ)]!).toList = idL := by
    decide +kernel
  exact eq_one_of_hasRows (Umat_hasRows 0 0) h

theorem Delta0_mem_monLin (s : ZMod 3) : Delta0 s ∈ monLin := D6_le_monLin ⟨_, rfl⟩

theorem candidates_ok (a b : Fin 4) (s : ZMod 3) (hab : a ≠ 0 ∨ b ≠ 0) :
    (∃ m₁ ∈ Nsub, ∃ m₂ ∈ Nsub, Umat a b * Delta0 s = m₁ * y3e * m₂) ∨
    (∃ m₁ ∈ Nsub, ∃ m₂ ∈ Nsub,
      11 ∣ orderOf (Umat a b * Delta0 s * m₁ * (Umat a b * Delta0 s) * m₂)) := by
  obtain ⟨k, hk, ha, hb, hs⟩ := cover a b s hab
  have hok := List.all_eq_true.1 cands_ok k hk
  simp only [candCheck, candBase, Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨⟨⟨h1, h2⟩, -⟩, hz⟩, hcase⟩ := hok
  obtain ⟨m₁, hm₁, hr₁⟩ := exists_Nsub h1
  obtain ⟨m₂, hm₂, hr₂⟩ := exists_Nsub h2
  have hZ : HasRows (Umat a b * Delta0 s) (zRows k) := by
    rw [hz, ha, hb, hs, ZMod.natCast_zmod_val]
    exact (Umat_hasRows a b).mul (Delta0_hasRows s)
  cases hg : k.good
  · rw [hg] at hcase
    simp only [Bool.false_eq_true, ↓reduceIte, candBad, Bool.and_eq_true, beq_iff_eq] at hcase
    obtain ⟨hpow, hnot⟩ := hcase
    refine Or.inr ⟨m₁, hm₁, m₂, hm₂, ?_⟩
    have hW : HasRows (Umat a b * Delta0 s * m₁ * (Umat a b * Delta0 s) * m₂) (wRows k) := by
      rw [show Umat a b * Delta0 s * m₁ * (Umat a b * Delta0 s) * m₂ =
        Umat a b * Delta0 s * (m₁ * (Umat a b * Delta0 s * m₂)) by group]
      exact hZ.mul (hr₁.mul (hZ.mul hr₂))
    obtain ⟨q, hq⟩ : ∃ q, HasRows ((Umat a b * Delta0 s * m₁ * (Umat a b * Delta0 s) * m₂) ^ q)
        (ordRows k) := by
      unfold ordRows
      split_ifs
      · exact ⟨1, by rw [pow_one]; exact hW⟩
      · exact ⟨3, hW.pow3⟩
    exact dvd_orderOf_of_pow (eq_one_of_hasRows hq.pow11 hpow) (ne_one_of_hasRows hq hnot)
  · rw [hg] at hcase
    simp only [↓reduceIte, candGood, beq_iff_eq] at hcase
    refine Or.inl ⟨m₁, hm₁, m₂, hm₂, ?_⟩
    have h3 := hr₁.mul (y3e_hasRows.mul hr₂)
    rw [← hcase] at h3
    rw [hZ.eq h3, mul_assoc]

end CFSG.GF2Type.Smith1979.IdxFour
