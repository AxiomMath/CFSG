module

public import CFSG.RankThree.PartOne.KGD.D4T36Torus
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4UnField
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped Matrix


section Torsion

variable {L : Type} [Field L] {Fr : L →+* L} {q : ℕ}

theorem fixed_tuple_ext (hFr : ∀ c, Fr c = c ^ q)
    {b b' : Fin TwistTag.D4.tag.rank → Lˣ}
    (hb : b ∈ fixedCharTuples (d4T36M (-1)) Fr) (hb' : b' ∈ fixedCharTuples (d4T36M (-1)) Fr)
    (h0 : b 0 = b' 0) (h2 : b 2 = b' 2) : b = b' := by
  have hε : (-1 : ℤ) = 1 ∨ (-1 : ℤ) = -1 := Or.inr rfl
  obtain ⟨e1, e3, -, -⟩ := (mem_fixedCharTuples_d4T36 hε hFr b).1 hb
  obtain ⟨e1', e3', -, -⟩ := (mem_fixedCharTuples_d4T36 hε hFr b').1 hb'
  funext i
  fin_cases i
  · exact h0
  · show b 1 = b' 1
    rw [e1, e1', h2]
  · exact h2
  · show b 3 = b' 3
    rw [e3, e3', h0, h2]

@[expose] def torsionTuples (Fr : L →+* L) (r : ℕ) : Set (Fin TwistTag.D4.tag.rank → Lˣ) :=
  {b | b ∈ fixedCharTuples (d4T36M (-1)) Fr ∧ ∀ i, b i ^ r = 1}

theorem natCard_torsionTuples_le (hFr : ∀ c, Fr c = c ^ q) (r : ℕ) [NeZero r] :
    Nat.card (torsionTuples Fr r) ≤ r * r := by
  let f : torsionTuples Fr r → rootsOfUnity r L × rootsOfUnity r L := fun b =>
    (⟨(b : Fin TwistTag.D4.tag.rank → Lˣ) 0, (mem_rootsOfUnity r _).2 (b.2.2 0)⟩,
      ⟨(b : Fin TwistTag.D4.tag.rank → Lˣ) 2, (mem_rootsOfUnity r _).2 (b.2.2 2)⟩)
  have hf : Function.Injective f := by
    intro b b' h
    have h0 : (b : Fin TwistTag.D4.tag.rank → Lˣ) 0 = (b' : Fin TwistTag.D4.tag.rank → Lˣ) 0 :=
      congrArg (fun x => ((x.1 : rootsOfUnity r L) : Lˣ)) h
    have h2 : (b : Fin TwistTag.D4.tag.rank → Lˣ) 2 = (b' : Fin TwistTag.D4.tag.rank → Lˣ) 2 :=
      congrArg (fun x => ((x.2 : rootsOfUnity r L) : Lˣ)) h
    exact Subtype.ext (fixed_tuple_ext hFr b.2.1 b'.2.1 h0 h2)
  have hfin : Finite (rootsOfUnity r L) := inferInstance
  calc Nat.card (torsionTuples Fr r)
      ≤ Nat.card (rootsOfUnity r L × rootsOfUnity r L) := Nat.card_le_card_of_injective f hf
    _ = Nat.card (rootsOfUnity r L) * Nat.card (rootsOfUnity r L) := Nat.card_prod _ _
    _ ≤ r * r := Nat.mul_le_mul (card_rootsOfUnity L r) (card_rootsOfUnity L r)

@[expose] def cTuple (ζ : Lˣ) (q : ℕ) : Fin TwistTag.D4.tag.rank → Lˣ :=
  ![ζ⁻¹, ζ, ζ ^ ((q : ℤ) - 1), ζ]

theorem cTuple_mem_fixed (hFr : ∀ c, Fr c = c ^ q) {r : ℕ} {ζ : Lˣ} (hζ : ζ ^ r = 1)
    (hN : (r : ℤ) ∣ (q : ℤ) ^ 2 + (-1) * q + 1) : cTuple ζ q ∈ fixedCharTuples (d4T36M (-1)) Fr := by
  have hε : (-1 : ℤ) = 1 ∨ (-1 : ℤ) = -1 := Or.inr rfl
  have hζN : ζ ^ ((q : ℤ) ^ 2 + (-1) * q + 1) = 1 := by
    obtain ⟨k, hk⟩ := hN
    rw [hk, zpow_mul, zpow_natCast, hζ, one_zpow]
  have hmul : ∀ m : ℤ, ζ ^ (m * ((q : ℤ) ^ 2 + (-1) * q + 1)) = 1 := fun m => by
    rw [zpow_mul', hζN, one_zpow]
  have hexp : ∀ A B : ℤ, A = B + (A - B) → ∀ m : ℤ, A - B = m * ((q : ℤ) ^ 2 + (-1) * q + 1) →
      ζ ^ A = ζ ^ B := fun A B _ m hm => by
    have : A = B + m * ((q : ℤ) ^ 2 + (-1) * q + 1) := by omega
    rw [this, zpow_add, hmul, mul_one]
  rw [mem_fixedCharTuples_d4T36 hε hFr]
  refine ⟨?_, ?_, ?_, ?_⟩
  · show ζ = ((ζ ^ ((q : ℤ) - 1)) ^ q) ^ (-1 : ℤ)
    rw [← zpow_natCast, ← zpow_mul, ← zpow_mul]
    have := hexp 1 (((q : ℤ) - 1) * ((q : ℤ) * (-1))) (by ring) 1 (by ring)
    rw [zpow_one] at this
    exact this
  · show ζ = ((ζ⁻¹ ^ q) ^ (-1 : ℤ)) * (ζ ^ ((q : ℤ) - 1))⁻¹
    have e : (ζ⁻¹ ^ q) ^ (-1 : ℤ) = ζ ^ (q : ℤ) := by
      rw [inv_pow, zpow_neg_one, inv_inv, zpow_natCast]
    rw [e, ← zpow_neg, ← zpow_add]
    have : (q : ℤ) + -((q : ℤ) - 1) = 1 := by ring
    rw [this, zpow_one]
  · show (ζ ^ ((q : ℤ) - 1)) ^ ((q : ℤ) ^ 2 + (-1) * q + 1) = 1
    rw [← zpow_mul]
    have := hmul ((q : ℤ) - 1)
    exact this
  · show ζ⁻¹ ^ ((q : ℤ) ^ 2 + (-1) * q + 1) = 1
    rw [inv_zpow, hζN, inv_one]

theorem cTuple_pow {r : ℕ} {ζ : Lˣ} (hζ : ζ ^ r = 1) (q : ℕ) (i : Fin TwistTag.D4.tag.rank) :
    cTuple ζ q i ^ r = 1 := by
  have h : ∀ k : ℤ, (ζ ^ k) ^ r = 1 := fun k => by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζ, one_zpow]
  fin_cases i
  · show ζ⁻¹ ^ r = 1
    rw [inv_pow, hζ, inv_one]
  · exact (by simpa using hζ : ζ ^ r = 1)
  · exact h _
  · exact (by simpa using hζ : ζ ^ r = 1)

theorem cTuple_one (ζ : Lˣ) (q : ℕ) : cTuple ζ q 1 = (cTuple ζ q 0)⁻¹ := by
  show ζ = ζ⁻¹⁻¹
  rw [inv_inv]

theorem cTuple_three (ζ : Lˣ) (q : ℕ) : cTuple ζ q 3 = (cTuple ζ q 0)⁻¹ := by
  show ζ = ζ⁻¹⁻¹
  rw [inv_inv]

theorem cTuple_ne_one {ζ : Lˣ} (hζ : ζ ≠ 1) (q : ℕ) : cTuple ζ q ≠ 1 := by
  intro h
  exact hζ (congrFun h 3)

end Torsion

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
