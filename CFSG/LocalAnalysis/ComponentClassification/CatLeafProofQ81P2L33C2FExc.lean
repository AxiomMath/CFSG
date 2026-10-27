module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33C2FPSL
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33C2FSpMain

public section

namespace CFSG.ComponentClassification.HarrisLit.L33

open CFSG Subgroup CFSG.Assembly.LowTwoRank

@[expose] def IsTwoNilpExc' (Y : Type) [Group Y] : Prop :=
  IsTwoNilpExc Y ∨ ∃ f : ℕ, 2 ≤ f ∧ Blueprint.LieModel Y .PSp 2 2 f

@[expose] def TwoNilpFor' (C : (Y : Type) → [Group Y] → Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], C Y → IsSimpleGroup Y → (∃ x y : Y, x * y ≠ y * x) →
    ∀ a : MulAut Y, orderOf a = 2 →
      IsPGroup 2 (↥(fixedPoints a) ⧸ pPrimeCore 2 ↥(fixedPoints a)) → IsTwoNilpExc' Y

theorem IsTwoNilpExc.weaken {Y : Type} [Group Y] (h : IsTwoNilpExc Y) : IsTwoNilpExc' Y :=
  Or.inl h

theorem TwoNilpFor.weaken {C : (Y : Type) → [Group Y] → Prop} (h : TwoNilpFor C) :
    TwoNilpFor' C :=
  fun Y _ _ hY hs hn a ha hP => Or.inl (h Y hY hs hn a ha hP)

theorem TwoNilpFor'.mono {C C' : (Y : Type) → [Group Y] → Prop}
    (h : ∀ (Y : Type) [Group Y], C' Y → C Y) (hC : TwoNilpFor' C) : TwoNilpFor' C' :=
  fun Y _ _ hY => hC Y (h Y hY)

theorem TwoNilpFor'.or {C C' : (Y : Type) → [Group Y] → Prop} (hC : TwoNilpFor' C)
    (hC' : TwoNilpFor' C') : TwoNilpFor' fun Y _ => C Y ∨ C' Y :=
  fun Y _ _ hY => hY.elim (hC Y) (hC' Y)

theorem isTwoNilpExc'_of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : IsTwoNilpExc' Y') : IsTwoNilpExc' Y := by
  rcases h with h | ⟨f, hf, h⟩
  · exact Or.inl (isTwoNilpExc_of_mulEquiv e h)
  · exact Or.inr ⟨f, hf, GSThmB.OddQuot.lieModel_of_equiv e.symm h⟩

theorem twoNilpFor'_of_models {C D : (Y : Type) → [Group Y] → Prop}
    (hmod : ∀ (Y : Type) [Group Y] [Finite Y], C Y →
      ∃ (P : Type) (_ : Group P) (_ : Finite P), D P ∧ Nonempty (Y ≃* P))
    (hD : TwoNilpFor' D) : TwoNilpFor' C := by
  intro Y _ _ hY hs hnab a ha hP
  obtain ⟨P, _, _, hDP, ⟨e⟩⟩ := hmod Y hY
  have hsP : IsSimpleGroup P := MulEquiv.isSimpleGroup e.symm
  have hnabP : ∃ x y : P, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hnab
    exact ⟨e x, e y, fun h => hxy (e.injective (by rw [map_mul, map_mul, h]))⟩
  exact isTwoNilpExc'_of_mulEquiv e (hD P hDP hsP hnabP (MulAut.congr e a)
    ((orderOf_congr e a).trans ha) (isPGroup_fixedPoints_congr e a hP))

theorem twoNilpExc'_of_rows
    (hA : TwoNilpFor' fun Y _ => ∃ n : ℕ, 5 ≤ n ∧ Nonempty (Y ≃* alternatingGroup (Fin n)))
    (hC : TwoNilpFor' fun Y _ => Milestones.ClassicalRep Y)
    (hE : TwoNilpFor' fun Y _ => Blueprint.ExceptionalRep Y)
    (hS : TwoNilpFor' fun Y _ => Blueprint.NativeSporadic.SporadicRep Y)
    (Y : Type) [Group Y] [Finite Y] (hcat : Blueprint.Catalog Y) (hs : IsSimpleGroup Y)
    (hnab : ∃ x y : Y, x * y ≠ y * x) (a : MulAut Y) (ha : orderOf a = 2)
    (hP : IsPGroup 2 (↥(fixedPoints a) ⧸ pPrimeCore 2 ↥(fixedPoints a))) : IsTwoNilpExc' Y := by
  rcases hcat with ⟨q, -, ⟨e⟩⟩ | hY' | hY' | hY' | hY'
  · obtain ⟨x, y, hxy⟩ := hnab
    exact (hxy (e.injective (by rw [map_mul, map_mul, mul_comm]))).elim
  · exact hA Y hY' hs hnab a ha hP
  · exact hC Y hY' hs hnab a ha hP
  · exact hE Y hY' hs hnab a ha hP
  · exact hS Y hY' hs hnab a ha hP

theorem odd_orders_psp_two_two {f : ℕ} (hf : 2 ≤ f) :
    Odd (Blueprint.Multiplier.genericOrders .PSp 2 2 f).1 ∧
      Odd (Blueprint.Multiplier.genericOrders .PSp 2 2 f).2 ∧
      Odd (Blueprint.Multiplier.exceptionalOrders .PSp 2 2 f).1 ∧
      Odd (Blueprint.Multiplier.exceptionalOrders .PSp 2 2 f).2 := by
  have hexc : Blueprint.Multiplier.exceptionalOrders .PSp 2 2 f = (1, 1) := by
    unfold Blueprint.Multiplier.exceptionalOrders
    split <;> simp_all
  refine ⟨?_, odd_one, by rw [hexc]; exact odd_one, by rw [hexc]; exact odd_one⟩
  change Odd (Nat.gcd 2 (2 ^ f - 1))
  have h2 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
  have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  exact Odd.of_dvd_nat (Nat.odd_iff.mpr (by omega)) (Nat.gcd_dvd_right 2 _)

theorem twoNilpFor_classicalRep'
    (hOdd : TwoNilpFor' fun Y _ => ∃ t n p f, p ≠ 2 ∧ StatedClassicalModel Y t n p f)
    (hTwo : TwoNilpFor' fun Y _ => ∃ t n f, StatedClassicalModel Y t n 2 f) :
    TwoNilpFor' fun Y _ => Milestones.ClassicalRep Y := by
  refine (hOdd.or hTwo).mono fun Y _ hY => ?_
  obtain ⟨t, n, p, f, h⟩ := hY
  by_cases hp : p = 2
  · subst hp
    exact Or.inr ⟨t, n, f, h⟩
  · exact Or.inl ⟨t, n, p, f, hp, h⟩

end CFSG.ComponentClassification.HarrisLit.L33

namespace CFSG.ComponentClassification.HarrisLit.L33.C2

open CFSG Subgroup CFSG.Assembly.LowTwoRank

theorem twoNilpFor'_psp_two :
    TwoNilpFor' fun Y _ => ∃ f : ℕ, StatedClassicalModel Y .PSp 2 2 f := by
  intro Y _ _ hY _ _ _ _ _
  obtain ⟨f, h⟩ := hY
  obtain ⟨-, hf, -, hq⟩ := h.1
  have hf1 : f ≠ 1 := by
    rintro rfl
    exact hq rfl
  exact Or.inr ⟨f, by omega, Or.inl ⟨by decide, h⟩⟩

theorem twoNilpFor'_classical_two_of_rows
    (hL : TwoNilpFor' fun Y _ => ∃ n f : ℕ, StatedClassicalModel Y .PSL n 2 f)
    (hSp : TwoNilpFor' fun Y _ => ∃ n f : ℕ, 3 ≤ n ∧ StatedClassicalModel Y .PSp n 2 f)
    (hU : TwoNilpFor' fun Y _ => ∃ n f : ℕ, StatedClassicalModel Y .PSU n 2 f)
    (hP : TwoNilpFor' fun Y _ => ∃ n f : ℕ, StatedClassicalModel Y .POmegaPlus n 2 f)
    (hM : TwoNilpFor' fun Y _ => ∃ n f : ℕ, StatedClassicalModel Y .POmegaMinus n 2 f) :
    TwoNilpFor' fun Y _ => ∃ (t : StatedLieTag) (n f : ℕ), StatedClassicalModel Y t n 2 f := by
  intro Y _ _ hY hs hnab a ha hP'
  obtain ⟨t, n, f, h⟩ := hY
  cases t with
  | PSL => exact hL Y ⟨n, f, h⟩ hs hnab a ha hP'
  | PSU => exact hU Y ⟨n, f, h⟩ hs hnab a ha hP'
  | PSp =>
    rcases Nat.lt_or_ge n 3 with hn | hn
    · obtain rfl : n = 2 := by
        have := h.1.2.2.1
        omega
      exact twoNilpFor'_psp_two Y ⟨f, h⟩ hs hnab a ha hP'
    · exact hSp Y ⟨n, f, hn, h⟩ hs hnab a ha hP'
  | POmegaOdd => exact absurd rfl h.1.2.2.2
  | POmegaPlus => exact hP Y ⟨n, f, h⟩ hs hnab a ha hP'
  | POmegaMinus => exact hM Y ⟨n, f, h⟩ hs hnab a ha hP'
  | G2 | F4 | E6 | E7 | E8 | twistedE6 | trialityD4 | twistedB2 | twistedG2 | twistedF4 | Tits =>
    exact h.2.elim

theorem twoNilpFor'_classical_two
    (hA : TwoNilpFor fun Y _ => ∃ n : ℕ, 5 ≤ n ∧ Nonempty (Y ≃* alternatingGroup (Fin n)))
    (hU : PSURow) (hP : POmegaPlusRow) (hM : POmegaMinusRow) :
    TwoNilpFor' fun Y _ => ∃ (t : StatedLieTag) (n f : ℕ), StatedClassicalModel Y t n 2 f :=
  twoNilpFor'_classical_two_of_rows (twoNilpFor_psl hA).weaken twoNilpFor_psp_three.weaken
    (TwoNilpFor.weaken hU) (TwoNilpFor.weaken hP) (TwoNilpFor.weaken hM)

end CFSG.ComponentClassification.HarrisLit.L33.C2
