module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2LvlB
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2TD4

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HDesc

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Blueprint TauCeti CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.GLTheoremA

theorem fam_omegaPlus {S : Type} [Group S] (h : catalogIs S fOmegaPlus) :
    ∃ (n : ℕ) (q : PrimePower) (hv : (LieTypeIndex.D n q).Valid), q.p = 2 ∧ ¬ (n = 4 ∧ q.card = 2) ∧
      Nonempty (S ≃* (CFSGIndex.lie ⟨.D n q, hv⟩).Group) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic _ _ => exact hi.elim
  | alternating _ _ => exact hi.elim
  | sporadic _ => exact hi.elim
  | lie dd =>
    obtain ⟨d, hv⟩ := dd
    cases d with
    | D n q => exact ⟨n, q, hv, hi.1, hi.2, ⟨e⟩⟩
    | _ => exact hi.elim

theorem fam_omegaMinus {S : Type} [Group S] (h : catalogIs S fOmegaMinus) :
    ∃ (n : ℕ) (q : PrimePower) (hv : (LieTypeIndex.twistedD n q).Valid), q.p = 2 ∧
      Nonempty (S ≃* (CFSGIndex.lie ⟨.twistedD n q, hv⟩).Group) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic _ _ => exact hi.elim
  | alternating _ _ => exact hi.elim
  | sporadic _ => exact hi.elim
  | lie dd =>
    obtain ⟨d, hv⟩ := dd
    cases d with
    | twistedD n q => exact ⟨n, q, hv, hi, ⟨e⟩⟩
    | _ => exact hi.elim

theorem fam_e6 {S : Type} [Group S] (h : catalogIs S fE6) :
    ∃ (q : PrimePower) (hv : (LieTypeIndex.E6 q).Valid), q.p = 2 ∧
      Nonempty (S ≃* (CFSGIndex.lie ⟨.E6 q, hv⟩).Group) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic _ _ => exact hi.elim
  | alternating _ _ => exact hi.elim
  | sporadic _ => exact hi.elim
  | lie dd =>
    obtain ⟨d, hv⟩ := dd
    cases d with
    | E6 q => exact ⟨q, hv, hi, ⟨e⟩⟩
    | _ => exact hi.elim

theorem fam_e7 {S : Type} [Group S] (h : catalogIs S fE7) :
    ∃ (q : PrimePower) (hv : (LieTypeIndex.E7 q).Valid), q.p = 2 ∧
      Nonempty (S ≃* (CFSGIndex.lie ⟨.E7 q, hv⟩).Group) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic _ _ => exact hi.elim
  | alternating _ _ => exact hi.elim
  | sporadic _ => exact hi.elim
  | lie dd =>
    obtain ⟨d, hv⟩ := dd
    cases d with
    | E7 q => exact ⟨q, hv, hi, ⟨e⟩⟩
    | _ => exact hi.elim

theorem fam_e8 {S : Type} [Group S] (h : catalogIs S fE8) :
    ∃ (q : PrimePower) (hv : (LieTypeIndex.E8 q).Valid), q.p = 2 ∧
      Nonempty (S ≃* (CFSGIndex.lie ⟨.E8 q, hv⟩).Group) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic _ _ => exact hi.elim
  | alternating _ _ => exact hi.elim
  | sporadic _ => exact hi.elim
  | lie dd =>
    obtain ⟨d, hv⟩ := dd
    cases d with
    | E8 q => exact ⟨q, hv, hi, ⟨e⟩⟩
    | _ => exact hi.elim

theorem fam_f4 {S : Type} [Group S] (h : catalogIs S fF4) :
    ∃ (q : PrimePower) (hv : (LieTypeIndex.F4 q).Valid), q.p = 2 ∧
      Nonempty (S ≃* (CFSGIndex.lie ⟨.F4 q, hv⟩).Group) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic _ _ => exact hi.elim
  | alternating _ _ => exact hi.elim
  | sporadic _ => exact hi.elim
  | lie dd =>
    obtain ⟨d, hv⟩ := dd
    cases d with
    | F4 q => exact ⟨q, hv, hi, ⟨e⟩⟩
    | _ => exact hi.elim

theorem fam_twE6 {S : Type} [Group S] (h : catalogIs S fTwE6) :
    ∃ (q : PrimePower) (hv : (LieTypeIndex.twistedE6 q).Valid), q.p = 2 ∧
      Nonempty (S ≃* (CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic _ _ => exact hi.elim
  | alternating _ _ => exact hi.elim
  | sporadic _ => exact hi.elim
  | lie dd =>
    obtain ⟨d, hv⟩ := dd
    cases d with
    | twistedE6 q => exact ⟨q, hv, hi, ⟨e⟩⟩
    | _ => exact hi.elim

theorem fam_triD4 {S : Type} [Group S] (h : catalogIs S fTriD4) :
    ∃ (q : PrimePower) (hv : (LieTypeIndex.trialityD4 q).Valid), q.p = 2 ∧ ¬ q.card = 2 ∧
      Nonempty (S ≃* (CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic _ _ => exact hi.elim
  | alternating _ _ => exact hi.elim
  | sporadic _ => exact hi.elim
  | lie dd =>
    obtain ⟨d, hv⟩ := dd
    cases d with
    | trialityD4 q => exact ⟨q, hv, hi.1, hi.2, ⟨e⟩⟩
    | _ => exact hi.elim

theorem lv_idx (ctx : LvCtx) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {S : Type} [Group S]
    (d : ValidLieTypeIndex) (hd : d.1.characteristic = 2) (e : S ≃* d.Group) (hlv : LvData p S) :
    ExcT p (tagOf d.1) (dimOf d.1) d.1.fieldExponent :=
  lv_exc ctx hp hp2 (ctx.tup S d hd e) (valT_of_valid d.2 hd)
    (Or.inl ⟨CFSGIndex.lie d, hd, ⟨e⟩⟩) hlv

theorem td4_none_seven (ctx : LvCtx) {S : Type} [Group S] {t : StatedLieTag} {n f : ℕ}
    (hS : LieModel S t n 2 f)
    (ht : t = .POmegaPlus ∨ t = .POmegaMinus ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .F4 ∨
      t = .twistedE6) (h : catalogIs S (onLie isTrialityD4Big)) : False := by
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
        obtain ⟨hadm, hM⟩ := model_data ctx.ord hS
        obtain ⟨-, hM'⟩ := model_data ctx.ord hm
        exact td4_excl he hadm hM hM' ht
      · have hodd := ctx.odd S q.p ⟨.trialityD4 q, hv⟩ q.prime_p hq2 (by simp) e
        rcases ctx.xchar S t n f hS hodd with ⟨rfl, -, -⟩ | ⟨rfl, -, -⟩ | ⟨rfl, -, -⟩ <;>
          simp at ht
    | _ => exact hi.elim

section Seven

variable (ctx : LvCtx) (hK3 : K3NotChev2At) (p : ℕ)

include ctx hK3

theorem kDescFamRes_omegaPlus_aux : KDescFamRes p fOmegaPlus := by
  refine kDescFamRes_of_noLvData hK3 ?_ ?_
  · intro hp hp2 S _ _ h hlv
    obtain ⟨n, q, hv, hq2, hne, ⟨e⟩⟩ := fam_omegaPlus h
    have hx := lv_idx ctx hp hp2 ⟨.D n q, hv⟩ (by simpa using hq2) e hlv
    simp [ExcT, tagOf, dimOf] at hx
    obtain ⟨-, rfl, he1⟩ := hx
    apply hne
    refine ⟨rfl, ?_⟩
    rw [PrimePower.card_def, hq2, he1]
    norm_num
  · intro S _ h hT
    obtain ⟨n, q, hv, hq2, hne, ⟨e⟩⟩ := fam_omegaPlus h
    exact td4_none_seven ctx (ctx.tup S ⟨.D n q, hv⟩ (by simpa using hq2) e)
      (Or.inl rfl) hT

theorem kDescFamRes_omegaMinus_aux : KDescFamRes p fOmegaMinus := by
  refine kDescFamRes_of_noLvData hK3 ?_ ?_
  · intro hp hp2 S _ _ h hlv
    obtain ⟨n, q, hv, hq2, ⟨e⟩⟩ := fam_omegaMinus h
    have hx := lv_idx ctx hp hp2 ⟨.twistedD n q, hv⟩ (by simpa using hq2) e hlv
    simp [ExcT, tagOf, dimOf] at hx
  · intro S _ h hT
    obtain ⟨n, q, hv, hq2, ⟨e⟩⟩ := fam_omegaMinus h
    exact td4_none_seven ctx (ctx.tup S ⟨.twistedD n q, hv⟩ (by simpa using hq2) e)
      (Or.inr (Or.inl rfl)) hT

theorem kDescFamRes_e6_aux : KDescFamRes p fE6 := by
  refine kDescFamRes_of_noLvData hK3 ?_ ?_
  · intro hp hp2 S _ _ h hlv
    obtain ⟨q, hv, hq2, ⟨e⟩⟩ := fam_e6 h
    have hx := lv_idx ctx hp hp2 ⟨.E6 q, hv⟩ (by simpa using hq2) e hlv
    simp [ExcT, tagOf, dimOf] at hx
  · intro S _ h hT
    obtain ⟨q, hv, hq2, ⟨e⟩⟩ := fam_e6 h
    exact td4_none_seven ctx (ctx.tup S ⟨.E6 q, hv⟩ (by simpa using hq2) e)
      (Or.inr (Or.inr (Or.inl rfl))) hT

theorem kDescFamRes_e7_aux : KDescFamRes p fE7 := by
  refine kDescFamRes_of_noLvData hK3 ?_ ?_
  · intro hp hp2 S _ _ h hlv
    obtain ⟨q, hv, hq2, ⟨e⟩⟩ := fam_e7 h
    have hx := lv_idx ctx hp hp2 ⟨.E7 q, hv⟩ (by simpa using hq2) e hlv
    simp [ExcT, tagOf, dimOf] at hx
  · intro S _ h hT
    obtain ⟨q, hv, hq2, ⟨e⟩⟩ := fam_e7 h
    exact td4_none_seven ctx (ctx.tup S ⟨.E7 q, hv⟩ (by simpa using hq2) e)
      (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hT

theorem kDescFamRes_e8_aux : KDescFamRes p fE8 := by
  refine kDescFamRes_of_noLvData hK3 ?_ ?_
  · intro hp hp2 S _ _ h hlv
    obtain ⟨q, hv, hq2, ⟨e⟩⟩ := fam_e8 h
    have hx := lv_idx ctx hp hp2 ⟨.E8 q, hv⟩ (by simpa using hq2) e hlv
    simp [ExcT, tagOf, dimOf] at hx
  · intro S _ h hT
    obtain ⟨q, hv, hq2, ⟨e⟩⟩ := fam_e8 h
    exact td4_none_seven ctx (ctx.tup S ⟨.E8 q, hv⟩ (by simpa using hq2) e)
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) hT

theorem kDescFamRes_f4_aux : KDescFamRes p fF4 := by
  refine kDescFamRes_of_noLvData hK3 ?_ ?_
  · intro hp hp2 S _ _ h hlv
    obtain ⟨q, hv, hq2, ⟨e⟩⟩ := fam_f4 h
    have hx := lv_idx ctx hp hp2 ⟨.F4 q, hv⟩ (by simpa using hq2) e hlv
    simp [ExcT, tagOf, dimOf] at hx
  · intro S _ h hT
    obtain ⟨q, hv, hq2, ⟨e⟩⟩ := fam_f4 h
    exact td4_none_seven ctx (ctx.tup S ⟨.F4 q, hv⟩ (by simpa using hq2) e)
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) hT

theorem kDescFamRes_twE6_aux : KDescFamRes p fTwE6 := by
  refine kDescFamRes_of_noLvData hK3 ?_ ?_
  · intro hp hp2 S _ _ h hlv
    obtain ⟨q, hv, hq2, ⟨e⟩⟩ := fam_twE6 h
    have hx := lv_idx ctx hp hp2 ⟨.twistedE6 q, hv⟩ (by simpa using hq2) e hlv
    simp [ExcT, tagOf, dimOf] at hx
  · intro S _ h hT
    obtain ⟨q, hv, hq2, ⟨e⟩⟩ := fam_twE6 h
    exact td4_none_seven ctx (ctx.tup S ⟨.twistedE6 q, hv⟩ (by simpa using hq2) e)
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))) hT

end Seven

end CFSG.LocalAnalysis.GLTheoremA.HDesc
