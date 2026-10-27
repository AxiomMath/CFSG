module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2TD4C
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20LieEnd
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2FamB
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2Lvl

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HDesc

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Blueprint TauCeti CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.GLTheoremA CFSG.ComponentClassification.CatLeaf
open CFSG.HardMathSupport.Solomon.Coordinator (LieOrderBridge)

theorem td4_none_lu (ctx : LvCtx) (hbridge : LieOrderBridge) {S : Type} [Group S]
    {t : StatedLieTag} {n f : ℕ} (hS : LieModel S t n 2 f) (ht : t = .PSL ∨ t = .PSU)
    (h : catalogIs S (onLie isTrialityD4Big)) : False := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic _ _ => exact hi.elim
  | alternating _ _ => exact hi.elim
  | sporadic _ => exact hi.elim
  | lie dd =>
    obtain ⟨d, hv⟩ := dd
    cases d with
    | trialityD4 q =>
      obtain ⟨hq2c, -⟩ : 2 < q.card ∧ ¬ 3 ∣ q.card := hi
      by_cases hq2 : q.p = 2
      · have hm := model_TD4 ctx hv hq2 e
        have he : 2 ≤ q.exponent := by
          rw [PrimePower.card_def, hq2] at hq2c
          by_contra hlt
          have : q.exponent ≤ 1 := by omega
          have : 2 ^ q.exponent ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
          omega
        obtain ⟨-, hM⟩ := model_data ctx.ord hS
        obtain ⟨-, hM'⟩ := model_data ctx.ord hm
        exact td4_excl_lu he hS.admissible hM hM' ht
      · haveI : Finite S := (ctx.ord S t n 2 f hS.admissible hS).1
        have hcard : Nat.card S = orderTrialityD4 q.card := hbridge ⟨.trialityD4 q, hv⟩ S ⟨e⟩
        have hadm' : StatedLieAdmissible .trialityD4 0 q.p q.exponent :=
          ⟨q.prime_p, q.exponent_pos, rfl⟩
        have hM' : Nat.card S * lieOrderDivisor .trialityD4 0 (q.p ^ q.exponent) =
            lieOrderNumerator .trialityD4 0 (q.p ^ q.exponent) := by
          rw [hcard]
          simp [orderTrialityD4, lieOrderNumerator, lieOrderDivisor, PrimePower.card_def]
        obtain ⟨-, hM⟩ := model_data ctx.ord hS
        rcases CFSG.SeitzReduction.CrossChar.crossChar_arith hS.admissible hadm' hq2 hM hM' with
          ⟨-, -, -, h1, -, -⟩ | ⟨-, -, -, h1, -, -⟩ | ⟨-, -, -, h1, -, -⟩ <;> cases h1
    | _ => exact hi.elim

theorem td4Ob_linear (ctx : LvCtx) (hbridge : LieOrderBridge) (p : ℕ) : Td4Ob p fLinear := by
  intro hp hp2 Y _ _ K B h hc hcB hT
  exfalso
  obtain ⟨n, q, hv, hq2, hne, ⟨e⟩⟩ := fam_linear hc
  have hm : LieModel (↥K ⧸ Subgroup.center ↥K) .PSL (n + 1) 2 q.exponent := by
    simpa [tagOf, dimOf] using ctx.tup _ ⟨.A n q, hv⟩ (by simpa using hq2) e
  exact td4_none_lu ctx hbridge hm (Or.inl rfl) hT.2.2.2.1

theorem td4Ob_unitary (ctx : LvCtx) (hbridge : LieOrderBridge) (p : ℕ) : Td4Ob p fUnitary := by
  intro hp hp2 Y _ _ K B h hc hcB hT
  exfalso
  obtain ⟨n, q, hv, hq2, hne8, hne32, hne42, ⟨e⟩⟩ := fam_unitary hc
  have hm : LieModel (↥K ⧸ Subgroup.center ↥K) .PSU (n + 1) 2 q.exponent := by
    simpa [tagOf, dimOf] using ctx.tup _ ⟨.twistedA n q, hv⟩ (by simpa using hq2) e
  exact td4_none_lu ctx hbridge hm (Or.inr rfl) hT.2.2.2.1

end CFSG.LocalAnalysis.GLTheoremA.HDesc
