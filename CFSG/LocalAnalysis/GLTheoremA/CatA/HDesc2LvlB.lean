module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2Lvl
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2Base
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2Class

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HDesc

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Blueprint TauCeti CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatLeaf

theorem card_alt_fin {m : ℕ} (hm : 2 ≤ m) : Nat.card (alternatingGroup (Fin m)) = m.factorial / 2 := by
  haveI : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 hm
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]

theorem lv_chev (ctx : LvCtx) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {S : Type} [Group S]
    {t : StatedLieTag} {n f : ℕ} (hS : LieModel S t n 2 f) (hval : ValT t n f)
    (hC : IsChevSimple p S) : ExcT p t n f := by
  obtain ⟨hadm, hM⟩ := model_data ctx.ord hS
  rcases hC with ⟨j, hj, ⟨e⟩⟩ | ⟨j, hj, ⟨e⟩⟩
  · cases j with
    | cyclic _ _ => exact hj.elim
    | alternating _ _ => exact hj.elim
    | sporadic _ => exact hj.elim
    | lie jd =>
      have hjd : jd.1.characteristic = p := hj
      have hodd := ctx.odd S p jd hp hp2 hjd e
      rcases ctx.xchar S t n f hS hodd with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · exact absurd (hval.1 rfl rfl) (by norm_num)
      · exact absurd (hval.2.1 rfl rfl) (by norm_num)
      · exact Or.inl ⟨rfl, rfl, rfl⟩
  · cases j with
    | cyclic _ _ => exact hj.elim
    | sporadic _ => exact hj.elim
    | alternating m hm =>
      rcases hj with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨-, hp8⟩
      · have hcard : Nat.card S = 60 := by
          rw [Nat.card_congr e.toEquiv, card_alt_fin (by norm_num)]
          norm_num [Nat.factorial]
        obtain ⟨rfl, rfl, rfl⟩ := cls_alt5 hadm hM hcard
        exact absurd (hval.1 rfl rfl) (by norm_num)
      · have hcard : Nat.card S = 360 := by
          rw [Nat.card_congr e.toEquiv, card_alt_fin (by norm_num)]
          norm_num [Nat.factorial]
        exact (cls_alt6 hadm hM hcard).elim
      · exact absurd hp8 hp2
    | lie jd =>
      obtain ⟨d1, hv⟩ := jd
      cases d1 with
      | A r q =>
        rcases r with _ | _ | _ | r
        · simp [ambiguousChev] at hj
        · simp only [ambiguousChev] at hj
          rcases hj with ⟨-, hp'⟩ | ⟨hq8, hp3⟩
          · exact absurd hp' hp2
          · subst hp3
            obtain ⟨hq2, hqe⟩ := pp_eq_of_card Nat.prime_two (by norm_num)
              (hq8.trans (by norm_num : (8 : ℕ) = 2 ^ 3))
            have hm := model_A1 ctx hv hq2 e
            rw [hqe] at hm
            obtain ⟨-, hM'⟩ := model_data ctx.ord hm
            rcases cls_L2 (e := 3) (by norm_num) hadm hM hM' with
              ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
            · simp [ExcT]
            · exact absurd (hval.2.1 rfl rfl) (by norm_num)
        · simp [ambiguousChev] at hj
        · simp [ambiguousChev] at hj
      | twistedA r q =>
        rcases r with _ | _ | _ | _ | r
        · simp [ambiguousChev] at hj
        · simp [ambiguousChev] at hj
        · simp only [ambiguousChev] at hj
          exact absurd hj.2 hp2
        · simp only [ambiguousChev] at hj
          obtain ⟨hq2c, hp3⟩ := hj
          subst hp3
          obtain ⟨hq2, hqe⟩ := pp_eq_of_card Nat.prime_two (by norm_num)
            (hq2c.trans (by norm_num : (2 : ℕ) = 2 ^ 1))
          have hm := model_tA ctx hv hq2 e
          rw [hqe] at hm
          obtain ⟨-, hM'⟩ := model_data ctx.ord hm
          obtain ⟨rfl, rfl, rfl⟩ := cls_U42 hadm hM hM'
          simp [ExcT]
        · simp [ambiguousChev] at hj
      | _ => simp [ambiguousChev] at hj

theorem lv_k2 (ctx : LvCtx) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {S : Type} [Group S]
    {t : StatedLieTag} {n f : ℕ} (hS : LieModel S t n 2 f) (hval : ValT t n f)
    (hC2 : IsChevSimple 2 S) (hk : catalogIs S (k2 p)) : ExcT p t n f := by
  obtain ⟨hadm, hM⟩ := model_data ctx.ord hS
  obtain ⟨j, hj, ⟨e⟩⟩ := hk
  cases j with
  | cyclic _ _ => exact absurd hj (by simp [k2])
  | alternating m hm =>
    have hj' : (p = 3 ∧ (m = 5 ∨ m = 9)) ∨ (p = 7 ∧ m = 7) := by simpa [k2] using hj
    rcases hj' with ⟨rfl, hm5 | hm9⟩ | ⟨rfl, hm7⟩
    · subst hm5
      have hcard : Nat.card S = 60 := by
        rw [Nat.card_congr e.toEquiv, card_alt_fin (by norm_num)]
        norm_num [Nat.factorial]
      obtain ⟨rfl, rfl, rfl⟩ := cls_alt5 hadm hM hcard
      exact absurd (hval.1 rfl rfl) (by norm_num)
    · subst hm9
      exact (ctx.nc2 S _ (Or.inr (Or.inr (Or.inl ⟨hm, rfl⟩))) ⟨e⟩ hC2).elim
    · subst hm7
      exact (ctx.nc2 S _ (Or.inr (Or.inl ⟨hm, rfl⟩)) ⟨e⟩ hC2).elim
  | sporadic s => exact (ctx.nc2 S _ (Or.inl ⟨s, rfl, p, hj⟩) ⟨e⟩ hC2).elim
  | lie jd =>
    obtain ⟨d1, hv⟩ := jd
    cases d1 with
    | A r q =>
      rcases r with _ | _ | _ | r
      · simp [k2, k2Lie] at hj
      ·
        have hj' : p = 3 ∧ ¬ 3 ∣ q.card := by simpa [k2, k2Lie] using hj
        obtain ⟨rfl, -⟩ := hj'
        by_cases hq2 : q.p = 2
        · have hm := model_A1 ctx hv hq2 e
          have hq4 : 2 ≤ q.exponent := by
            have h4 : 4 ≤ q.card := by
              have := ((LieTypeIndex.inStandardRange_iff _).mp
                ((LieTypeIndex.valid_iff _).mp hv).1).2 rfl
              exact this
            rw [PrimePower.card_def, hq2] at h4
            by_contra hlt
            have : q.exponent ≤ 1 := by omega
            have : 2 ^ q.exponent ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
            omega
          obtain ⟨-, hM'⟩ := model_data ctx.ord hm
          rcases cls_L2 hq4 hadm hM hM' with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
          · simp [ExcT]
          · exact absurd (hval.2.1 rfl rfl) (by norm_num)
        · have hodd := ctx.odd S q.p ⟨.A 1 q, hv⟩ q.prime_p hq2 (by simp) e
          rcases ctx.xchar S t n f hS hodd with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
          · exact absurd (hval.1 rfl rfl) (by norm_num)
          · exact absurd (hval.2.1 rfl rfl) (by norm_num)
          · exact Or.inl ⟨rfl, rfl, rfl⟩
      ·
        have hj' : (p = 3 ∧ q.p = 2 ∧ Even q.exponent) ∨ (p = 13 ∧ q.card = 3) := by
          simpa [k2, k2Lie] using hj
        rcases hj' with ⟨rfl, hq2, hev⟩ | ⟨-, hq3⟩
        · have hm := model_A2 ctx hv hq2 e
          obtain ⟨m, hmm⟩ := hev
          have hmm' : q.exponent = 2 * m := by omega
          rw [hmm'] at hm
          have hm1 : 1 ≤ m := by
            have := q.exponent_pos
            omega
          obtain ⟨-, hM'⟩ := model_data ctx.ord hm
          by_cases hm2 : m = 1
          · subst hm2
            rcases cls_L3four hadm hM hM' with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
            · simp [ExcT]
            · exact absurd (hval.2.2 rfl rfl) (by norm_num)
          · obtain ⟨rfl, rfl, rfl⟩ := cls_L3 (by omega) hadm hM hM'
            exact Or.inr (Or.inl ⟨rfl, Or.inr (Or.inl ⟨rfl, rfl, even_two_mul m⟩)⟩)
        · exact (ctx.nc2 S (CFSGIndex.lie ⟨.A 2 q, hv⟩)
            (Or.inr (Or.inr (Or.inr (show CFSG.LocalAnalysis.GLTheoremA.List93.l33Idx
              (CFSGIndex.lie ⟨.A 2 q, hv⟩) from hq3)))) ⟨e⟩ hC2).elim
      · simp [k2, k2Lie] at hj
    | twistedA r q =>
      rcases r with _ | _ | _ | _ | _ | _ | r
      · simp [k2, k2Lie] at hj
      · simp [k2, k2Lie] at hj
      ·
        have hj' : p = 3 ∧ q.p = 2 ∧ Odd q.exponent ∧ 1 < q.exponent := by simpa [k2, k2Lie] using hj
        obtain ⟨rfl, hq2, hodd, hgt⟩ := hj'
        have hm := model_tA ctx hv hq2 e
        obtain ⟨-, hM'⟩ := model_data ctx.ord hm
        by_cases h3 : q.exponent = 3
        · rw [h3] at hm hM'
          obtain ⟨rfl, rfl, rfl⟩ := cls_U3eight hadm hM hM'
          exact Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr (Or.inl ⟨rfl, rfl, ⟨1, by norm_num⟩⟩))⟩)
        · have h5 : 5 ≤ q.exponent := by
            obtain ⟨k, hk⟩ := hodd
            omega
          obtain ⟨rfl, rfl, rfl⟩ := cls_U3 hodd h5 hadm hM hM'
          exact Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hodd⟩))⟩)
      ·
        have hj' : p = 3 ∧ q.card = 8 := by simpa [k2, k2Lie] using hj
        obtain ⟨rfl, hq8⟩ := hj'
        obtain ⟨hq2, hqe⟩ := pp_eq_of_card Nat.prime_two (by norm_num)
          (hq8.trans (by norm_num : (8 : ℕ) = 2 ^ 3))
        have hm := model_tA ctx hv hq2 e
        rw [hqe] at hm
        obtain ⟨-, hM'⟩ := model_data ctx.ord hm
        obtain ⟨rfl, rfl, rfl⟩ := cls_U48 hadm hM hM'
        simp [ExcT]
      ·
        have hj' : p = 3 ∧ q.card = 2 := by simpa [k2, k2Lie] using hj
        obtain ⟨rfl, hq2c⟩ := hj'
        obtain ⟨hq2, hqe⟩ := pp_eq_of_card Nat.prime_two (by norm_num)
          (hq2c.trans (by norm_num : (2 : ℕ) = 2 ^ 1))
        have hm := model_tA ctx hv hq2 e
        rw [hqe] at hm
        obtain ⟨-, hM'⟩ := model_data ctx.ord hm
        obtain ⟨rfl, rfl, rfl⟩ := cls_U52 hadm hM hM'
        simp [ExcT]
      ·
        have hj' : p = 3 ∧ q.card = 2 := by simpa [k2, k2Lie] using hj
        obtain ⟨rfl, hq2c⟩ := hj'
        obtain ⟨hq2, hqe⟩ := pp_eq_of_card Nat.prime_two (by norm_num)
          (hq2c.trans (by norm_num : (2 : ℕ) = 2 ^ 1))
        have hm := model_tA ctx hv hq2 e
        rw [hqe] at hm
        obtain ⟨-, hM'⟩ := model_data ctx.ord hm
        obtain ⟨rfl, rfl, rfl⟩ := cls_U62 hadm hM hM'
        simp [ExcT]
      · simp [k2, k2Lie] at hj
    | B r q =>
      rcases r with _ | _ | _ | _ | r
      · simp [k2, k2Lie] at hj
      · simp [k2, k2Lie] at hj
      ·
        have hj' : p = 3 ∧ q.card = 8 := by simpa [k2, k2Lie] using hj
        obtain ⟨rfl, hq8⟩ := hj'
        obtain ⟨hq2, hqe⟩ := pp_eq_of_card Nat.prime_two (by norm_num)
          (hq8.trans (by norm_num : (8 : ℕ) = 2 ^ 3))
        have hm := model_B ctx hv hq2 e
        rw [hqe] at hm
        obtain ⟨-, hM'⟩ := model_data ctx.ord hm
        obtain ⟨rfl, rfl, rfl⟩ := cls_Sp48 hadm hM hM'
        simp [ExcT]
      ·
        have hj' : p = 3 ∧ q.card = 2 := by simpa [k2, k2Lie] using hj
        obtain ⟨rfl, hq2c⟩ := hj'
        obtain ⟨hq2, hqe⟩ := pp_eq_of_card Nat.prime_two (by norm_num)
          (hq2c.trans (by norm_num : (2 : ℕ) = 2 ^ 1))
        have hm := model_B ctx hv hq2 e
        rw [hqe] at hm
        obtain ⟨-, hM'⟩ := model_data ctx.ord hm
        obtain ⟨rfl, rfl, rfl⟩ := cls_Sp62 hadm hM hM'
        simp [ExcT]
      · simp [k2, k2Lie] at hj
    | C r q => simp [k2, k2Lie] at hj
    | D r q =>
      rcases r with _ | _ | _ | _ | _ | r
      · simp [k2, k2Lie] at hj
      · simp [k2, k2Lie] at hj
      · simp [k2, k2Lie] at hj
      · simp [k2, k2Lie] at hj
      ·
        have hj' : p = 3 ∧ q.card = 2 := by simpa [k2, k2Lie] using hj
        obtain ⟨rfl, hq2c⟩ := hj'
        obtain ⟨hq2, hqe⟩ := pp_eq_of_card Nat.prime_two (by norm_num)
          (hq2c.trans (by norm_num : (2 : ℕ) = 2 ^ 1))
        have hm := model_D ctx hv hq2 e
        rw [hqe] at hm
        obtain ⟨-, hM'⟩ := model_data ctx.ord hm
        obtain ⟨rfl, rfl, rfl⟩ := cls_O8p2 hadm hM hM'
        simp [ExcT]
      · simp [k2, k2Lie] at hj
    | twistedD r q => simp [k2, k2Lie] at hj
    | E6 q => simp [k2, k2Lie] at hj
    | E7 q => simp [k2, k2Lie] at hj
    | E8 q => simp [k2, k2Lie] at hj
    | F4 q => simp [k2, k2Lie] at hj
    | G2 q =>
      have hj' : p = 3 ∧ q.card = 8 := by simpa [k2, k2Lie] using hj
      obtain ⟨rfl, hq8⟩ := hj'
      obtain ⟨hq2, hqe⟩ := pp_eq_of_card Nat.prime_two (by norm_num)
        (hq8.trans (by norm_num : (8 : ℕ) = 2 ^ 3))
      have hm := model_G2 ctx hv hq2 e
      rw [hqe] at hm
      obtain ⟨-, hM'⟩ := model_data ctx.ord hm
      obtain ⟨rfl, rfl, rfl⟩ := cls_G28 hadm hM hM'
      simp [ExcT]
    | twistedE6 q => simp [k2, k2Lie] at hj
    | trialityD4 q =>
      have hj' : p = 3 ∧ q.card = 2 := by simpa [k2, k2Lie] using hj
      obtain ⟨rfl, hq2c⟩ := hj'
      obtain ⟨hq2, hqe⟩ := pp_eq_of_card Nat.prime_two (by norm_num)
        (hq2c.trans (by norm_num : (2 : ℕ) = 2 ^ 1))
      have hm := model_TD4 ctx hv hq2 e
      rw [hqe] at hm
      obtain ⟨-, hM'⟩ := model_data ctx.ord hm
      obtain ⟨rfl, rfl, rfl⟩ := cls_TD42 hadm hM hM'
      simp [ExcT]
    | suzuki m =>
      have hj' : p = 5 ∧ m = 2 := by simpa [k2, k2Lie] using hj
      obtain ⟨rfl, rfl⟩ := hj'
      have hm := model_suzuki ctx hv e
      obtain ⟨-, hM'⟩ := model_data ctx.ord hm
      obtain ⟨rfl, rfl, rfl⟩ := cls_Sz32 hadm hM hM'
      simp [ExcT]
    | reeG2 m => simp [k2, k2Lie] at hj
    | reeF4 m =>
      have hj' : (p = 3 ∧ m = 1) ∨ (p = 5 ∧ m = 2) := by simpa [k2, k2Lie] using hj
      have hm := model_reeF4 ctx hv e
      obtain ⟨-, hM'⟩ := model_data ctx.ord hm
      rcases hj' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · obtain ⟨rfl, rfl, rfl⟩ := cls_RF48 hadm hM hM'
        simp [ExcT]
      · obtain ⟨rfl, rfl, rfl⟩ := cls_RF432 hadm hM hM'
        simp [ExcT]
    | tits =>
      have hj' : p = 3 ∨ p = 5 := by simpa [k2, k2Lie] using hj
      have hm := model_tits ctx hv e
      obtain ⟨-, hM'⟩ := model_data ctx.ord hm
      obtain ⟨rfl, rfl, rfl⟩ := cls_Tits hadm hM hM'
      rcases hj' with rfl | rfl <;> simp [ExcT]

theorem lv_exc (ctx : LvCtx) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {S : Type} [Group S]
    {t : StatedLieTag} {n f : ℕ} (hS : LieModel S t n 2 f) (hval : ValT t n f)
    (hC2 : IsChevSimple 2 S) (hlv : LvData p S) : ExcT p t n f := by
  rcases hlv with hC | hk
  · exact lv_chev ctx hp hp2 hS hval hC
  · exact lv_k2 ctx hp hp2 hS hval hC2 hk

end CFSG.LocalAnalysis.GLTheoremA.HDesc
