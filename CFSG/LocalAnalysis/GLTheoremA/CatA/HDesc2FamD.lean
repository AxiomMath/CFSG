module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2FamB
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2TD4B
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2Lvl

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HDesc

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Blueprint TauCeti CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.GLTheoremA CFSG.ComponentClassification.CatLeaf

theorem td4_none_gen (ctx : LvCtx) {S : Type} [Group S] {t : StatedLieTag} {n f : ℕ}
    (hS : LieModel S t n 2 f) (hnx : t ≠ .PSL ∧ t ≠ .PSU)
    (hexcl : ∀ {e M : ℕ}, 2 ≤ e →
      M * lieOrderDivisor t n (2 ^ f) = lieOrderNumerator t n (2 ^ f) →
      M * lieOrderDivisor .trialityD4 0 (2 ^ e) = lieOrderNumerator .trialityD4 0 (2 ^ e) → False)
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
        exact hexcl he hM hM'
      · have hodd := ctx.odd S q.p ⟨.trialityD4 q, hv⟩ q.prime_p hq2 (by simp) e
        rcases ctx.xchar S t n f hS hodd with ⟨rfl, -, -⟩ | ⟨rfl, -, -⟩ | ⟨rfl, -, -⟩ <;>
          simp at hnx
    | _ => exact hi.elim

theorem td4Ob_symplectic (ctx : LvCtx) (p : ℕ) : Td4Ob p fSymplectic := by
  intro hp hp2 Y _ _ K B h hc hcB hT
  exfalso
  obtain ⟨n, q, hv, hq2, hne, ⟨e⟩⟩ := fam_symplectic hc
  have hm : LieModel (↥K ⧸ Subgroup.center ↥K) .PSp n 2 q.exponent := by
    simpa [tagOf, dimOf] using ctx.tup _ ⟨.B n q, hv⟩ (by simpa using hq2) e
  exact td4_none_gen ctx hm ⟨by decide, by decide⟩
    (fun he hM hM' => td4_excl_sp he hm.admissible hM hM') hT.2.2.2.1

theorem td4Ob_g2 (ctx : LvCtx) (p : ℕ) : Td4Ob p fG2 := by
  intro hp hp2 Y _ _ K B h hc hcB hT
  exfalso
  obtain ⟨q, hv, hq2, ⟨e⟩⟩ := fam_g2 hc
  have hm : LieModel (↥K ⧸ Subgroup.center ↥K) .G2 0 2 q.exponent := by
    simpa [tagOf, dimOf] using ctx.tup _ ⟨.G2 q, hv⟩ (by simpa using hq2) e
  exact td4_none_gen ctx hm ⟨by decide, by decide⟩
    (fun he hM hM' => td4_excl_g2 he hm.admissible hM hM') hT.2.2.2.1

theorem td4Ob_ree (ctx : LvCtx) (p : ℕ) : Td4Ob p fReeTits := by
  intro hp hp2 Y _ _ K B h hc hcB hT
  exfalso
  obtain ⟨m, hv, ⟨e⟩⟩ := fam_reeTits hc
  have hm : LieModel (↥K ⧸ Subgroup.center ↥K) .twistedF4 0 2 (2 * m + 1) := model_reeF4 ctx hv e
  exact td4_none_gen ctx hm ⟨by decide, by decide⟩
    (fun he hM hM' => td4_excl_ree he hm.admissible hM hM') hT.2.2.2.1

end CFSG.LocalAnalysis.GLTheoremA.HDesc
