module

public import CFSG.GF2Type.Smith1979.IdxFourIdentEData
public import CFSG.GF2Type.Smith1979.IdxFourIdentFL

public section

namespace CFSG.GF2Type.Smith1979.IdxFour

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA

namespace ECheck

open FLCheck

@[expose] def invL (l : List ℕ) (j : ℕ) : ℕ := ((List.range 6).find? fun i => l[i]! == j).getD 0

@[expose] def pInv (m : MonData) : Fin 6 → Fin 6 :=
  fun j => ⟨invL m.p j % 6, Nat.mod_lt _ (by norm_num)⟩

@[expose] def monOKR0 (m : MonData) : Bool :=
  (m.e == 0) && decide (∑ i, cF m i = 0) &&
    decide (∃ (h1 : Function.LeftInverse (pInv m) (pF m))
      (h2 : Function.RightInverse (pInv m) (pF m)),
      Equiv.Perm.sign (⟨pF m, pInv m, h1, h2⟩ : Equiv.Perm (Fin 6)) = 1)

theorem exists_R0 {m : MonData} (h : monOKR0 m = true) : ∃ g ∈ R0, HasRows g (monRows m) := by
  simp only [monOKR0, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨he, hs⟩, h1, h2, hsign⟩ := h
  let π : Equiv.Perm (Fin 6) := ⟨pF m, pInv m, h1, h2⟩
  refine ⟨diagE (cF m) * permE π, ⟨cF m, π, hs, Equiv.Perm.mem_alternatingGroup.2 hsign, rfl⟩, ?_⟩
  have h := mon_hasRows (cF m) π 0
  rw [ZMod.val_zero, pow_zero, mul_one] at h
  rw [monRows, he, Nat.cast_zero]
  exact h

@[expose] def t1Rows : List ℕ := s12Rows.toList

@[expose] def zRowsE (k : ECand) : List ℕ :=
  if k.eps = 0 then mulL (uRowsTable[4 * k.a + k.b]!).toList (deltaRows (k.s : ZMod 3))
  else mulL (mulL (uRowsTable[4 * k.a + k.b]!).toList (deltaRows (k.s : ZMod 3))) t1Rows

@[expose] def stepRows (zr : List ℕ) (st : EStep) : List ℕ := if st.z then zr else monRows st.m

@[expose] def wordRows (zr : List ℕ) : List EStep → List ℕ
  | [] => idL
  | st :: l => mulL (stepRows zr st) (wordRows zr l)

@[expose] def stepsOK (l : List EStep) : Bool := l.all fun st => st.z || monOKR0 st.m

@[expose] def targetRows (j : ℕ) : List ℕ :=
  mulL (deltaRows (j : ZMod 3)) (mulL y3Rows.toList (deltaRows (-(j : ZMod 3))))

@[expose] def candGoodE (k : ECand) : Bool :=
  stepsOK k.word && wordRows (zRowsE k) k.word == targetRows k.j

@[expose] def wRowsE (k : ECand) : List ℕ :=
  mulL (zRowsE k) (mulL (monRows k.r1) (mulL (zRowsE k) (monRows k.r2)))

@[expose] def ordRowsE (k : ECand) : List ℕ := if k.o = 11 then wRowsE k else pow3L (wRowsE k)

@[expose] def candBadE (k : ECand) : Bool :=
  monOKR0 k.r1 && monOKR0 k.r2 && pow11L (ordRowsE k) == idL && notIdL (ordRowsE k)

@[expose] def candCheckE (k : ECand) : Bool := if k.good then candGoodE k else candBadE k

theorem cands_okE : eCands.all candCheckE = true := by decide +kernel

theorem coverE : ∀ a b : Fin 4, ∀ s : ZMod 3, ∀ ε : ZMod 2, (a ≠ 0 ∨ b ≠ 0) →
    ∃ k ∈ eCands, k.a = a ∧ k.b = b ∧ k.s = s.val ∧ k.eps = ε.val := by
  decide +kernel

end ECheck

open FLCheck ECheck

theorem hasRows_one : HasRows (1 : G12) idL := ⟨rfl, fun x => (linOfRows_idR x).symm⟩

theorem wordMem {H : Subgroup G12} (hR0 : R0 ≤ H) {Z : G12} {zr : List ℕ} (hZ : Z ∈ H)
    (hZr : HasRows Z zr) : ∀ l : List EStep, stepsOK l = true →
      ∃ g ∈ H, HasRows g (wordRows zr l)
  | [], _ => ⟨1, one_mem H, hasRows_one⟩
  | st :: l, h => by
    simp only [stepsOK, List.all_cons, Bool.and_eq_true] at h
    obtain ⟨hst, hl⟩ := h
    obtain ⟨g, hg, hgr⟩ := wordMem hR0 hZ hZr l hl
    by_cases hz : st.z = true
    · refine ⟨Z * g, mul_mem hZ hg, ?_⟩
      have h1 : stepRows zr st = zr := by simp [stepRows, hz]
      have h2 : wordRows zr (st :: l) = mulL (stepRows zr st) (wordRows zr l) := rfl
      rw [h2, h1]
      exact hZr.mul hgr
    · have hm : monOKR0 st.m = true := by simpa [hz] using hst
      obtain ⟨r, hr, hrr⟩ := exists_R0 hm
      refine ⟨r * g, mul_mem (hR0 hr) hg, ?_⟩
      have h1 : stepRows zr st = monRows st.m := by simp [stepRows, hz]
      have h2 : wordRows zr (st :: l) = mulL (stepRows zr st) (wordRows zr l) := rfl
      rw [h2, h1]
      exact hrr.mul hgr

theorem Delta0_neg (j : ZMod 3) : Delta0 (-j) = (Delta0 j)⁻¹ := by
  refine eq_inv_of_mul_eq_one_right ?_
  unfold Delta0
  rw [← diagE_add]
  have : ((fun i : Fin 6 => if i = 0 then j else 0) + fun i => if i = 0 then -j else 0) = 0 := by
    ext i
    by_cases h : i = 0 <;> simp [h]
  rw [this, diagE_zero]

theorem candidates_E {H : Subgroup G12} (hR0 : R0 ≤ H) (a b : Fin 4) (s : ZMod 3) (ε : ZMod 2)
    (hab : a ≠ 0 ∨ b ≠ 0)
    (hZ : Umat a b * Delta0 s * (permE (Equiv.swap 0 1)) ^ ε.val ∈ H) :
    (∃ j : ZMod 3, Delta0 j * y3e * (Delta0 j)⁻¹ ∈ H) ∨ ∃ g ∈ H, 11 ∣ orderOf g := by
  obtain ⟨k, hk, ha, hb, hs, he⟩ := coverE a b s ε hab
  have hok := List.all_eq_true.1 cands_okE k hk
  have hZr : HasRows (Umat a b * Delta0 s * (permE (Equiv.swap 0 1)) ^ ε.val) (zRowsE k) := by
    have hU := (Umat_hasRows a b).mul (Delta0_hasRows s)
    rcases MonAux.zmod2_cases ε with rfl | rfl
    · have h0 : k.eps = 0 := he
      rw [zRowsE, if_pos h0, ha, hb, hs, ZMod.natCast_zmod_val, ZMod.val_zero, pow_zero, mul_one]
      exact hU
    · have h1 : ¬ k.eps = 0 := by rw [he]; decide
      rw [zRowsE, if_neg h1, ha, hb, hs, ZMod.natCast_zmod_val, ZMod.val_one, pow_one]
      exact hU.mul s12_hasRows
  cases hg : k.good
  · simp only [candCheckE, hg, Bool.false_eq_true, ↓reduceIte, candBadE, Bool.and_eq_true,
      beq_iff_eq] at hok
    obtain ⟨⟨⟨h1, h2⟩, hpow⟩, hnot⟩ := hok
    obtain ⟨m₁, hm₁, hr₁⟩ := exists_R0 h1
    obtain ⟨m₂, hm₂, hr₂⟩ := exists_R0 h2
    refine Or.inr ⟨_, mul_mem hZ (mul_mem (hR0 hm₁) (mul_mem hZ (hR0 hm₂))), ?_⟩
    have hW : HasRows (Umat a b * Delta0 s * (permE (Equiv.swap 0 1)) ^ ε.val *
        (m₁ * (Umat a b * Delta0 s * (permE (Equiv.swap 0 1)) ^ ε.val * m₂))) (wRowsE k) :=
      hZr.mul (hr₁.mul (hZr.mul hr₂))
    obtain ⟨q, hq⟩ : ∃ q, HasRows ((Umat a b * Delta0 s * (permE (Equiv.swap 0 1)) ^ ε.val *
        (m₁ * (Umat a b * Delta0 s * (permE (Equiv.swap 0 1)) ^ ε.val * m₂))) ^ q)
        (ordRowsE k) := by
      unfold ordRowsE
      split_ifs
      · exact ⟨1, by rw [pow_one]; exact hW⟩
      · exact ⟨3, hW.pow3⟩
    exact dvd_orderOf_of_pow (eq_one_of_hasRows hq.pow11 hpow) (ne_one_of_hasRows hq hnot)
  · simp only [candCheckE, hg, ↓reduceIte, candGoodE, Bool.and_eq_true, beq_iff_eq] at hok
    obtain ⟨hsteps, hword⟩ := hok
    obtain ⟨g, hgH, hgr⟩ := wordMem hR0 hZ hZr k.word hsteps
    refine Or.inl ⟨(k.j : ZMod 3), ?_⟩
    have hT : HasRows (Delta0 (k.j : ZMod 3) * (y3e * Delta0 (-(k.j : ZMod 3)))) (targetRows k.j) :=
      (Delta0_hasRows _).mul (y3e_hasRows.mul (Delta0_hasRows _))
    rw [hword] at hgr
    have heq := hgr.eq hT
    rw [← Delta0_neg, mul_assoc, ← heq]
    exact hgH

end CFSG.GF2Type.Smith1979.IdxFour
