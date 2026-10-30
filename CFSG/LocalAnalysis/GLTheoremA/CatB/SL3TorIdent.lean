module

public import CFSG.HardMathSupport.Solomon.Coordinator.LBIInput6_1Main
public import CFSG.Milestones.CL_LIT_Griess_Schur_multipliers_Lie_type
public import CFSG.Adapters.TauCetiLieModels
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma44bOrd
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.LocalAnalysis.GLTheoremA.S9.Defs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.SL3TorArith
public import CFSG.Models.PGLSimple

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.SL3Tor

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Open.StatedAPI
open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.LocalAnalysis.ComponentInitial

theorem index_A2_of_isL3char2 (d : TauCeti.LieTypeIndex) (hv : d.Valid)
    (h : CFSG.LocalAnalysis.GLTheoremA.S9.isL3char2 (TauCeti.CFSGIndex.lie ⟨d, hv⟩)) :
    ∃ q : TauCeti.PrimePower, d = TauCeti.LieTypeIndex.A 2 q ∧ q.p = 2 ∧ q.card % 3 = 1 := by
  match d, hv, h with
  | .A r q, hv, h =>
    rcases r with _ | _ | _ | r
    · exact (show False from h).elim
    · exact (show False from h).elim
    · exact ⟨q, rfl, h⟩
    · exact (show False from h).elim
  | .twistedA _ _, _, h => exact (show False from h).elim
  | .B _ _, _, h => exact (show False from h).elim
  | .C _ _, _, h => exact (show False from h).elim
  | .D _ _, _, h => exact (show False from h).elim
  | .twistedD _ _, _, h => exact (show False from h).elim
  | .E6 _, _, h => exact (show False from h).elim
  | .E7 _, _, h => exact (show False from h).elim
  | .E8 _, _, h => exact (show False from h).elim
  | .F4 _, _, h => exact (show False from h).elim
  | .G2 _, _, h => exact (show False from h).elim
  | .twistedE6 _, _, h => exact (show False from h).elim

theorem exists_pow_of_card_sq {F : Type} [Field F] [Finite F] {q : ℕ} (hq : 2 ≤ q)
    (h : Nat.card F = q ^ 2) :
    ∃ p j : ℕ, p.Prime ∧ 1 ≤ j ∧ q = p ^ j ∧ CharP F p ∧ Nat.card F = (p ^ j) ^ 2 := by
  classical
  haveI := Fintype.ofFinite F
  obtain ⟨p, hchar, n, hp, hcard⟩ := FiniteField.card' F
  rw [Nat.card_eq_fintype_card] at h
  have hqdvd : q ∣ p ^ (n : ℕ) := by
    have h1 : q ∣ Fintype.card F := by
      rw [h]
      exact dvd_pow_self q two_ne_zero
    rw [hcard] at h1
    exact h1
  obtain ⟨j, hj, hqj⟩ := (Nat.dvd_prime_pow hp).1 hqdvd
  have hj1 : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · subst h0
      simp at hqj
      omega
    · exact h0
  refine ⟨p, j, hp, hj1, hqj, hchar, ?_⟩
  rw [Nat.card_eq_fintype_card, h, hqj]

theorem two_le_of_card_sq {F : Type} [Field F] [Finite F] {q : ℕ} (h : Nat.card F = q ^ 2) :
    2 ≤ q := by
  have h2 : 1 < Nat.card F := Finite.one_lt_card
  by_contra hc
  push Not at hc
  have : q ^ 2 ≤ 1 := by interval_cases q <;> norm_num
  rw [h] at h2
  linarith

theorem card_center_eq_one_of_simple {Y : Type} [Group Y] (hQ : CFSG.Open.IsQuasisimple Y)
    (hs : IsSimpleGroup Y) : Nat.card (Subgroup.center Y) = 1 := by
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center Y) with h | h
  · rw [h, Subgroup.card_bot]
  · exfalso
    have hc : commutator Y = ⊥ := (commutator_eq_bot_iff_center_eq_top Y).mpr h
    have ht := hQ.1
    rw [hc] at ht
    exact bot_ne_top ht

theorem S_ge_four {N : ℕ} (hN : 4 ≤ N) :
    60480 ≤ N ^ 3 * ((N ^ 2 - 1) * (N ^ 3 - 1)) := by
  have h1 : 64 ≤ N ^ 3 := by
    calc 64 = 4 ^ 3 := by norm_num
      _ ≤ N ^ 3 := Nat.pow_le_pow_left hN 3
  have h16 : 16 ≤ N ^ 2 := by
    calc 16 = 4 ^ 2 := by norm_num
      _ ≤ N ^ 2 := Nat.pow_le_pow_left hN 2
  have h2 : 15 ≤ N ^ 2 - 1 := by omega
  have h3 : 63 ≤ N ^ 3 - 1 := by omega
  calc 60480 = 64 * (15 * 63) := by norm_num
    _ ≤ N ^ 3 * ((N ^ 2 - 1) * (N ^ 3 - 1)) := Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)

section Ident


theorem pquot_sl3_iso {G : Type} [Group G] [Finite G] {X K : Subgroup G}
    (hK : GLAPComponent 3 X K)
    (hcat : catalogIs (PSimple 3 K) CFSG.LocalAnalysis.GLTheoremA.S9.isL3char2)
    (hcen : Nat.card (Subgroup.center (PQuot 3 K)) = 3) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), CharP F 2 ∧ Nat.card F % 3 = 1 ∧
      Nonempty (PQuot 3 K ≃* ↥(StatedSL 3 F)) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hQ : CFSG.Open.IsQuasisimple (PQuot 3 K) := isQuasisimple_pQuot_of_glaPComponent hp hK
  have hZp : IsPGroup 3 ↥(Subgroup.center (PQuot 3 K)) :=
    IsPGroup.of_card (n := 1) (by rw [hcen]; norm_num)
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  cases i with
  | cyclic _ _ => exact (show False from hi).elim
  | alternating _ _ => exact (show False from hi).elim
  | sporadic _ => exact (show False from hi).elim
  | lie j =>
    obtain ⟨d, hv⟩ := j
    obtain ⟨q, rfl, hq2, hq3⟩ := index_A2_of_isL3char2 d hv hi
    have hm := CFSG.Models.lieModel_A 2 q hv e
    rcases hm.2 with hcl | ⟨h0, -⟩
    swap
    · exact absurd h0 (by norm_num)
    obtain ⟨-, F, hFf, hFfin, hFcard, ⟨eF⟩⟩ := hcl
    have hFq : Nat.card F = q.card := by rw [hFcard, ← TauCeti.PrimePower.card_def]
    have hNmod : Nat.card F % 3 = 1 := by rw [hFq]; exact hq3
    have hN2 : 2 ≤ Nat.card F := Finite.one_lt_card (α := F)
    have hN4 : 4 ≤ Nat.card F := by omega
    have hYcard : Nat.card (PQuot 3 K) = 3 * Nat.card (PSimple 3 K) := by
      have := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center (PQuot 3 K))
      rw [hcen] at this
      rw [this, Nat.mul_comm]
    have hPSL : Nat.card (PSimple 3 K) = Nat.card (StatedProj (StatedSL 3 F)) :=
      Nat.card_congr eF.toEquiv
    have hPSLmul :=
      CFSG.GH74.GLS.IVK.Proofs2.Lemma44bOrd.card_statedProj_statedSL_three_mul (F := F)
    have hgcd : Nat.gcd 3 (Nat.card F - 1) = 3 := Nat.gcd_eq_left (by omega)
    rw [hgcd, mul_assoc] at hPSLmul
    have hY3 : Nat.card (PQuot 3 K) =
        Nat.card F ^ 3 * ((Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1)) := by
      rw [hYcard, hPSL, Nat.mul_comm 3]
      exact hPSLmul
    have hExt : IsExtremalType (PSimple 3 K) := Or.inl ⟨F, hFf, hFfin, hNmod, ⟨eF⟩⟩
    have hres := HardMathSupport.Solomon.Coordinator.lbiInput6_1_of_griess
        CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement (PQuot 3 K) hQ hZp hExt
    rcases hres with hE | hS
    ·
      exfalso
      rcases hE with ⟨F', hF'f, hF'fin, -, ⟨eY⟩⟩ | ⟨F', hF'f, hF'fin, q', hq'card, hq'3, hq'8, ⟨eY⟩⟩
      · have hsim : IsSimpleGroup (StatedProj (StatedSL 3 F')) :=
          CFSG.Open.StatedAPI.isSimpleGroup_statedProj_statedSL F' (by norm_num) (Or.inl (by norm_num))
            (Or.inl (by norm_num))
        haveI := hsim
        have hYs : IsSimpleGroup (PQuot 3 K) := eY.isSimpleGroup
        have := card_center_eq_one_of_simple hQ hYs
        omega
      · have hq'2 : 2 ≤ q' := two_le_of_card_sq hq'card
        by_cases hq2' : q' = 2
        · subst hq2'
          have hU : UnitaryFieldData 2 1 F' :=
            ⟨Nat.prime_two, le_refl 1, by rw [hq'card]⟩
          have hPSU := CFSG.GH74.GLS.IVK.Proofs2.Lemma44bOrd.card_statedProj_statedSU_three_mul hU
          norm_num at hPSU
          have hYPSU : Nat.card (PQuot 3 K) = 72 := by
            rw [Nat.card_congr eY.toEquiv]
            omega
          have := S_ge_four hN4
          omega
        · obtain ⟨p, j, hp', hj, hqj, hchar', hcardj⟩ := exists_pow_of_card_sq hq'2 hq'card
          haveI : Fact p.Prime := ⟨hp'⟩
          have hnq : ((3 : ℕ), p ^ j) ≠ (3, 2) := by
            intro h
            apply hq2'
            rw [hqj]
            exact (Prod.mk.inj h).2
          have hsim : IsSimpleGroup (StatedProj (StatedSU 3 q' F')) := by
            rw [hqj]
            exact CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F' p j hcardj 3 (by norm_num) hnq
          haveI := hsim
          have hYs : IsSimpleGroup (PQuot 3 K) := eY.isSimpleGroup
          have := card_center_eq_one_of_simple hQ hYs
          omega
    ·
      rcases hS with ⟨F', hF'f, hF'fin, hF'mod, ⟨eY⟩⟩ | ⟨F', hF'f, hF'fin, q', hq'card, hq'3, hq'8, ⟨eY⟩⟩
      · have hcardY : Nat.card (PQuot 3 K) =
            Nat.card F' ^ 3 * ((Nat.card F' ^ 2 - 1) * (Nat.card F' ^ 3 - 1)) := by
          rw [Nat.card_congr eY.toEquiv, card_statedSL_three]
        have hF'2 : 2 ≤ Nat.card F' := Finite.one_lt_card (α := F')
        have hinj := sl_card_inj hF'2 hN2 (hcardY.symm.trans hY3)
        have hF'card : Nat.card F' = 2 ^ q.exponent := by
          rw [hinj, hFcard, hq2]
        exact ⟨F', hF'f, hF'fin, CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hF'card,
          hF'mod, ⟨eY⟩⟩
      · exfalso
        have hq'2 : 2 ≤ q' := two_le_of_card_sq hq'card
        obtain ⟨p, j, hp', hj, hqj, hchar', hcardj⟩ := exists_pow_of_card_sq hq'2 hq'card
        haveI : Fact p.Prime := ⟨hp'⟩
        have hYSU : Nat.card (PQuot 3 K) = q' ^ 3 * ((q' ^ 2 - 1) * (q' ^ 3 + 1)) := by
          rw [Nat.card_congr eY.toEquiv]
          have hc := CFSG.SectionRank.OddCover.card_statedSU_three (K := F') hcardj
          rw [← hqj] at hc
          rw [hc, mul_assoc]
        exact su_sl_false hq'2 hN4 hq'3 hNmod (hYSU.symm.trans hY3)

end Ident

end CFSG.LocalAnalysis.GLTheoremA.CatB.SL3Tor
