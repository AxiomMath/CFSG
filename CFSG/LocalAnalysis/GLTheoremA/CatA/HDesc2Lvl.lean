module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2Tuple
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.List93Facts

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HDesc

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Blueprint TauCeti CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatLeaf

@[expose] def ExcT (p : ℕ) (t : StatedLieTag) (n f : ℕ) : Prop :=
  (t = .PSU ∧ n = 4 ∧ f = 1) ∨
    (p = 3 ∧ ((t = .PSL ∧ n = 2) ∨ (t = .PSL ∧ n = 3 ∧ Even f) ∨ (t = .PSU ∧ n = 3 ∧ Odd f) ∨
      (t = .PSp ∧ n = 2 ∧ f = 3) ∨ (t = .PSp ∧ n = 3 ∧ f = 1) ∨ (t = .POmegaPlus ∧ n = 4 ∧ f = 1) ∨
      (t = .G2 ∧ f = 3) ∨ (t = .PSU ∧ n = 4 ∧ f = 3) ∨ (t = .PSU ∧ n = 5 ∧ f = 1) ∨
      (t = .PSU ∧ n = 6 ∧ f = 1) ∨ (t = .trialityD4 ∧ f = 1) ∨ t = .Tits ∨
      (t = .twistedF4 ∧ f = 3))) ∨
    (p = 5 ∧ (t = .Tits ∨ (t = .twistedF4 ∧ f = 5) ∨ (t = .twistedB2 ∧ f = 5)))

structure LvCtx : Prop where
  ord : LieOrderFormulasInput
  tup : TupleLemma
  nc2 : ∀ (S : Type) [Group S] (j : CFSGIndex), CFSG.LocalAnalysis.GLTheoremA.List93.NotChev2Idx j →
    Nonempty (S ≃* j.Group) → ¬ IsChevSimple 2 S
  xchar : ∀ (S : Type) [Group S] (t : StatedLieTag) (n f : ℕ), LieModel S t n 2 f → OddLieType S →
    (t = .PSL ∧ n = 2 ∧ f = 2) ∨ (t = .PSL ∧ n = 3 ∧ f = 1) ∨ (t = .PSU ∧ n = 4 ∧ f = 1)
  odd : ∀ (S : Type) [Group S] (r : ℕ) (d : ValidLieTypeIndex), r.Prime → r ≠ 2 →
    d.1.characteristic = r → (S ≃* d.Group) → OddLieType S

theorem pp_eq_of_card {q : PrimePower} {r s : ℕ} (hr : r.Prime) (hs : s ≠ 0) (h : q.card = r ^ s) :
    q.p = r ∧ q.exponent = s :=
  Nat.Prime.pow_inj' q.prime_p hr q.exponent_pos.ne' hs (by rw [← PrimePower.card_def]; exact h)

theorem model_data (hO : LieOrderFormulasInput) {S : Type} [Group S] {t : StatedLieTag} {n f : ℕ}
    (hS : LieModel S t n 2 f) :
    StatedLieAdmissible t n 2 f ∧
      Nat.card S * lieOrderDivisor t n (2 ^ f) = lieOrderNumerator t n (2 ^ f) :=
  ⟨hS.admissible, (hO S t n 2 f hS.admissible hS).2.1⟩

theorem model_A1 (ctx : LvCtx) {S : Type} [Group S] {q : PrimePower}
    (hv : (LieTypeIndex.A 1 q).Valid) (hq : q.p = 2)
    (e : S ≃* (CFSGIndex.lie ⟨LieTypeIndex.A 1 q, hv⟩).Group) : LieModel S .PSL 2 2 q.exponent := by
  have h := ctx.tup S ⟨.A 1 q, hv⟩ (by simpa using hq) e
  simpa [tagOf, dimOf] using h

theorem model_A2 (ctx : LvCtx) {S : Type} [Group S] {q : PrimePower}
    (hv : (LieTypeIndex.A 2 q).Valid) (hq : q.p = 2)
    (e : S ≃* (CFSGIndex.lie ⟨LieTypeIndex.A 2 q, hv⟩).Group) : LieModel S .PSL 3 2 q.exponent := by
  have h := ctx.tup S ⟨.A 2 q, hv⟩ (by simpa using hq) e
  simpa [tagOf, dimOf] using h

theorem model_tA (ctx : LvCtx) {S : Type} [Group S] {r : ℕ} {q : PrimePower}
    (hv : (LieTypeIndex.twistedA r q).Valid) (hq : q.p = 2)
    (e : S ≃* (CFSGIndex.lie ⟨LieTypeIndex.twistedA r q, hv⟩).Group) :
    LieModel S .PSU (r + 1) 2 q.exponent := by
  have h := ctx.tup S ⟨.twistedA r q, hv⟩ (by simpa using hq) e
  simpa [tagOf, dimOf] using h

theorem model_B (ctx : LvCtx) {S : Type} [Group S] {r : ℕ} {q : PrimePower}
    (hv : (LieTypeIndex.B r q).Valid) (hq : q.p = 2)
    (e : S ≃* (CFSGIndex.lie ⟨LieTypeIndex.B r q, hv⟩).Group) :
    LieModel S .PSp r 2 q.exponent := by
  have h := ctx.tup S ⟨.B r q, hv⟩ (by simpa using hq) e
  simpa [tagOf, dimOf] using h

theorem model_D (ctx : LvCtx) {S : Type} [Group S] {r : ℕ} {q : PrimePower}
    (hv : (LieTypeIndex.D r q).Valid) (hq : q.p = 2)
    (e : S ≃* (CFSGIndex.lie ⟨LieTypeIndex.D r q, hv⟩).Group) :
    LieModel S .POmegaPlus r 2 q.exponent := by
  have h := ctx.tup S ⟨.D r q, hv⟩ (by simpa using hq) e
  simpa [tagOf, dimOf] using h

theorem model_G2 (ctx : LvCtx) {S : Type} [Group S] {q : PrimePower}
    (hv : (LieTypeIndex.G2 q).Valid) (hq : q.p = 2)
    (e : S ≃* (CFSGIndex.lie ⟨LieTypeIndex.G2 q, hv⟩).Group) : LieModel S .G2 0 2 q.exponent := by
  have h := ctx.tup S ⟨.G2 q, hv⟩ (by simpa using hq) e
  simpa [tagOf, dimOf] using h

theorem model_TD4 (ctx : LvCtx) {S : Type} [Group S] {q : PrimePower}
    (hv : (LieTypeIndex.trialityD4 q).Valid) (hq : q.p = 2)
    (e : S ≃* (CFSGIndex.lie ⟨LieTypeIndex.trialityD4 q, hv⟩).Group) :
    LieModel S .trialityD4 0 2 q.exponent := by
  have h := ctx.tup S ⟨.trialityD4 q, hv⟩ (by simpa using hq) e
  simpa [tagOf, dimOf] using h

theorem model_reeF4 (ctx : LvCtx) {S : Type} [Group S] {m : ℕ} (hv : (LieTypeIndex.reeF4 m).Valid)
    (e : S ≃* (CFSGIndex.lie ⟨LieTypeIndex.reeF4 m, hv⟩).Group) :
    LieModel S .twistedF4 0 2 (2 * m + 1) := by
  have h := ctx.tup S ⟨.reeF4 m, hv⟩ (by simp) e
  simpa [tagOf, dimOf] using h

theorem model_suzuki (ctx : LvCtx) {S : Type} [Group S] {m : ℕ} (hv : (LieTypeIndex.suzuki m).Valid)
    (e : S ≃* (CFSGIndex.lie ⟨LieTypeIndex.suzuki m, hv⟩).Group) :
    LieModel S .twistedB2 0 2 (2 * m + 1) := by
  have h := ctx.tup S ⟨.suzuki m, hv⟩ (by simp) e
  simpa [tagOf, dimOf] using h

theorem model_tits (ctx : LvCtx) {S : Type} [Group S] (hv : LieTypeIndex.tits.Valid)
    (e : S ≃* (CFSGIndex.lie ⟨LieTypeIndex.tits, hv⟩).Group) : LieModel S .Tits 0 2 1 := by
  have h := ctx.tup S ⟨.tits, hv⟩ (by simp) e
  simpa [tagOf, dimOf] using h

end CFSG.LocalAnalysis.GLTheoremA.HDesc
