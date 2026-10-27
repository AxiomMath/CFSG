module

public import Certificates.Data.Kernel.Misc.RuCoverNetW
public import CFSG.Certificates.Kernel.YModel.SchSem
public import CFSG.Sporadic.Schreier.RuCore

public section

namespace CFSG.KC.Misc.RuCoverNet

open CFSG.KC CFSG.KC.YModel CFSG.KC.YModel.Sem CFSG.KC.YModel.Sch CFSG.Sporadic.RuSchreier

theorem netCode_zero (j : Nat) : netCode j 0 = 2 * j + 2 := by
  unfold netCode
  simp only [Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one]
  omega

theorem netCode_one (j : Nat) : netCode j 1 = 2 * j + 3 := by
  unfold netCode
  simp only [Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one]
  omega

theorem encZ_p1 (iA iB iZ : Nat) : encZ iA iB iZ 1 = netCode iA 0 := rfl
theorem encZ_n1 (iA iB iZ : Nat) : encZ iA iB iZ (-1) = netCode iA 1 := rfl
theorem encZ_p2 (iA iB iZ : Nat) : encZ iA iB iZ 2 = netCode iB 0 := rfl
theorem encZ_n2 (iA iB iZ : Nat) : encZ iA iB iZ (-2) = netCode iB 1 := rfl
theorem encZ_p3 (iA iB iZ : Nat) : encZ iA iB iZ 3 = netCode iZ 0 := rfl
theorem encZ_n3 (iA iB iZ : Nat) : encZ iA iB iZ (-3) = netCode iZ 1 := rfl

theorem brec_lt {a b : Nat} (c : Bool) (ha : a < 64) (hb : b < 64) :
    Bool.rec (motive := fun _ => Nat) a b c < 64 := by
  cases c
  · exact ha
  · exact hb

theorem encZ_lt {iA iB iZ : Nat} (hA : iA < 31) (hB : iB < 31) (hZ : iZ < 31) (l : Int) :
    encZ iA iB iZ l < 64 := by
  have a0 : netCode iA 0 < 64 := by rw [netCode_zero]; omega
  have a1 : netCode iA 1 < 64 := by rw [netCode_one]; omega
  have b0 : netCode iB 0 < 64 := by rw [netCode_zero]; omega
  have b1 : netCode iB 1 < 64 := by rw [netCode_one]; omega
  have z0 : netCode iZ 0 < 64 := by rw [netCode_zero]; omega
  have z1 : netCode iZ 1 < 64 := by rw [netCode_one]; omega
  unfold encZ
  cases l with
  | ofNat n => exact brec_lt _ (brec_lt _ (brec_lt _ (by decide) z0) b0) a0
  | negSucc m => exact brec_lt _ (brec_lt _ (brec_lt _ (by decide) z1) b1) a1

theorem lt_pow_of {e j : Nat} (he : e < 64) (hj : 6 ≤ j) : e < 2 ^ j :=
  Nat.lt_of_lt_of_le (he : e < 2 ^ 6) (Nat.pow_le_pow_right (n := 2) (by decide) hj)

theorem low_or_shl {e p : Nat} (he : e < 64) : fieldAt 6 (e ||| p <<< 6) 0 = e := by
  rw [fieldAt_eq', Nat.mul_zero, Nat.shiftRight_zero]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_mod_two_pow, Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases hj : j < 6
  · simp [hj, show ¬ (6 ≤ j) by omega]
  · rw [Nat.testBit_lt_two_pow (lt_pow_of he (by omega))]
    simp [hj]

theorem high_or_shl {e p : Nat} (he : e < 64) : (e ||| p <<< 6) >>> 6 = p := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_shiftRight, Nat.testBit_or, Nat.testBit_shiftLeft,
    Nat.testBit_lt_two_pow (lt_pow_of he (by omega : 6 ≤ 6 + j))]
  simp

theorem codesL_packZ {iA iB iZ : Nat} (hlt : ∀ l, encZ iA iB iZ l < 64) :
    ∀ u : List Int, codesL 6 (packZ iA iB iZ u) (lenZ u) = u.map (encZ iA iB iZ)
  | [] => rfl
  | l :: u => by
    change codesL 6 (encZ iA iB iZ l ||| packZ iA iB iZ u <<< 6) (lenZ u + 1) = _
    rw [codesL_succ, List.map_cons, low_or_shl (hlt l), high_or_shl (hlt l), codesL_packZ hlt u]

theorem cperm_ev' {k n : Nat} {U : Nat → Nat} (j : Nat) :
    cperm k n U (2 * j + 2) = netPerm k n (U j) := by
  have h1 : (2 * j + 2).testBit 0 = false := by
    rw [Nat.testBit_zero]
    exact decide_eq_false (by omega)
  have h2 : (2 * j + 2) >>> 1 - 1 = j := by
    rw [Nat.shiftRight_eq_div_pow, Nat.pow_one]
    omega
  unfold cperm
  rw [h1, h2]
  simp

theorem cperm_od' {k n : Nat} {U : Nat → Nat} (j : Nat) :
    cperm k n U (2 * j + 3) = (netPerm k n (U j))⁻¹ := by
  have h1 : (2 * j + 3).testBit 0 = true := by
    rw [Nat.testBit_zero]
    exact decide_eq_true (by omega)
  have h2 : (2 * j + 3) >>> 1 - 1 = j := by
    rw [Nat.shiftRight_eq_div_pow, Nat.pow_one]
    omega
  unfold cperm
  rw [h1, h2]
  simp

theorem letter_cases {l : Int} (h0 : l ≠ 0) (h3 : l.natAbs ≤ 3) :
    l = 1 ∨ l = -1 ∨ l = 2 ∨ l = -2 ∨ l = 3 ∨ l = -3 := by
  omega

section Words

variable {V : Nat → Nat} {iA iB iZ : Nat}

theorem cpermL_encZ : ∀ u : List Int, (∀ l ∈ u, l ≠ 0 ∧ l.natAbs ≤ 3) →
    cpermL 14 16240 V (u.map (encZ iA iB iZ)) =
      evalSigned [netPerm 14 16240 (V iA), netPerm 14 16240 (V iB), netPerm 14 16240 (V iZ)] u
  | [], _ => rfl
  | l :: u, h => by
    obtain ⟨h0, h3⟩ := h l List.mem_cons_self
    have ih := cpermL_encZ u fun l' hl' => h l' (List.mem_cons_of_mem _ hl')
    unfold cpermL at ih ⊢
    rw [List.map_cons, List.map_cons, List.prod_cons, ih, evalSigned_cons]
    congr 1
    rcases letter_cases h0 h3 with e | e | e | e | e | e <;> subst e
    · rw [encZ_p1, netCode_zero, cperm_ev']
      simp
    · rw [encZ_n1, netCode_one, cperm_od']
      simp
    · rw [encZ_p2, netCode_zero, cperm_ev']
      simp
    · rw [encZ_n2, netCode_one, cperm_od']
      simp
    · rw [encZ_p3, netCode_zero, cperm_ev']
      simp
    · rw [encZ_n3, netCode_one, cperm_od']
      simp

theorem shr_netCode (j s : Nat) (hs : s < 2) : (netCode j s >>> 1) - 1 = j := by
  unfold netCode
  rw [Nat.shiftRight_eq_div_pow, Nat.pow_one]
  simp only [Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one]
  omega

theorem codesGood_encZ (hA : Good 14 16240 (V iA)) (hB : Good 14 16240 (V iB))
    (hZ : Good 14 16240 (V iZ)) : ∀ u : List Int, (∀ l ∈ u, l ≠ 0 ∧ l.natAbs ≤ 3) →
      CodesGood 14 16240 V (u.map (encZ iA iB iZ)) := by
  intro u hu x hx
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
  obtain ⟨h0, h3⟩ := hu l hl
  rcases letter_cases h0 h3 with e | e | e | e | e | e <;> subst e
  · rw [encZ_p1, shr_netCode _ _ (by decide)]
    exact hA
  · rw [encZ_n1, shr_netCode _ _ (by decide)]
    exact hA
  · rw [encZ_p2, shr_netCode _ _ (by decide)]
    exact hB
  · rw [encZ_n2, shr_netCode _ _ (by decide)]
    exact hB
  · rw [encZ_p3, shr_netCode _ _ (by decide)]
    exact hZ
  · rw [encZ_n3, shr_netCode _ _ (by decide)]
    exact hZ

theorem eqW_spec (hA' : iA < 31) (hB' : iB < 31) (hZ' : iZ < 31) (hA : Good 14 16240 (V iA))
    (hB : Good 14 16240 (V iB)) (hZ : Good 14 16240 (V iZ)) {u v : List Int}
    (hu : ∀ l ∈ u, l ≠ 0 ∧ l.natAbs ≤ 3) (hv : ∀ l ∈ v, l ≠ 0 ∧ l.natAbs ≤ 3)
    (h : eqW V iA iB iZ u v = true) :
    evalSigned [netPerm 14 16240 (V iA), netPerm 14 16240 (V iB), netPerm 14 16240 (V iZ)] u =
      evalSigned [netPerm 14 16240 (V iA), netPerm 14 16240 (V iB), netPerm 14 16240 (V iZ)] v := by
  have hc := codesL_packZ (iA := iA) (iB := iB) (iZ := iZ) (encZ_lt hA' hB' hZ')
  have g1 := codesGood_encZ hA hB hZ u hu
  have g2 := codesGood_encZ hA hB hZ v hv
  rw [← hc u] at g1
  rw [← hc v] at g2
  have e := sweqK_spec (n := 16240) (by decide) g1 g2 h
  rw [hc u, hc v, cpermL_encZ u hu, cpermL_encZ v hv] at e
  exact e

theorem ne_of_notB' {a b : Nat} (h : notB (Nat.beq a b) = true) : a ≠ b := by
  intro hab
  subst hab
  rw [Nat.beq_refl] at h
  exact Bool.false_ne_true h

theorem neW_spec (hA' : iA < 31) (hB' : iB < 31) (hZ' : iZ < 31) (hA : Good 14 16240 (V iA))
    (hB : Good 14 16240 (V iB)) (hZ : Good 14 16240 (V iZ)) {u v : List Int} {b x y : Nat}
    (hb : b < 16240) (hu : ∀ l ∈ u, l ≠ 0 ∧ l.natAbs ≤ 3) (hv : ∀ l ∈ v, l ≠ 0 ∧ l.natAbs ≤ 3)
    (h : neW V iA iB iZ u v b x y = true) :
    evalSigned [netPerm 14 16240 (V iA), netPerm 14 16240 (V iB), netPerm 14 16240 (V iZ)] u ≠
      evalSigned [netPerm 14 16240 (V iA), netPerm 14 16240 (V iB), netPerm 14 16240 (V iZ)] v := by
  have hc := codesL_packZ (iA := iA) (iB := iB) (iZ := iZ) (encZ_lt hA' hB' hZ')
  have g1 := codesGood_encZ hA hB hZ u hu
  have g2 := codesGood_encZ hA hB hZ v hv
  rw [← hc u] at g1
  rw [← hc v] at g2
  unfold neW at h
  obtain ⟨h1, h⟩ := andB_eq h
  obtain ⟨h2, h3⟩ := andB_eq h
  have e1 := mapsTo_spec (n := 16240) (by decide) hb g1 h1
  have e2 := mapsTo_spec (n := 16240) (by decide) hb g2 h2
  rw [hc u, cpermL_encZ u hu] at e1
  rw [hc v, cpermL_encZ v hv] at e2
  intro he
  rw [he] at e1
  exact ne_of_notB' h3 (e1.symm.trans e2)

end Words

end CFSG.KC.Misc.RuCoverNet

end
