module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.FiveCentralLeaf
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.ThreeCentralArith
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.ThreeCentralTable
public import CFSG.HardMathSupport.Solomon.Proving.Fi22AutTables
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20LieEnd

public section

namespace CFSG.HardMathSupport.Dickson.I271.ThreeCentralLeaf

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier CFSG.Models TauCeti
open CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier
open CFSG.HardMathSupport.Timmesfeld.Coordinator
open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.I1420
open CFSG.HardMathSupport.Dickson.I271.ThreeCentralArith
open CFSG.HardMathSupport.Dickson.I271.ThreeCentralTable
open CFSG.HardMathSupport.Dickson.I271.FiveCentralLeaf (card_of_statedClassicalModel_psu')
open CFSG.ComponentClassification.OuterAutomorphisms

theorem lie_three_false (hGA : GriessAllModelsStatement) (hb : LieOrderBridge)
    {K : Type} [Group K] [Finite K] (hq' : CFSG.IsQuasisimple K) (d : ValidLieTypeIndex)
    (e : K ⧸ Subgroup.center K ≃* (CFSGIndex.lie d).Group)
    (h3 : 3 ∣ Nat.card (Subgroup.center K))
    (h12 : 3 ^ 12 ∣ Nat.card (K ⧸ Subgroup.center K))
    (hM : Nat.card (K ⧸ Subgroup.center K) ∣ monsterOrder) : False := by
  obtain ⟨t, n, p, f, hm⟩ := exists_lieModel d
  have htab := h3.trans (center_dvd_table hGA hq' e hm)
  have hcard : Nat.card (K ⧸ Subgroup.center K) = Nat.card (CFSGIndex.lie d).Group :=
    Nat.card_congr e.toEquiv
  obtain ⟨hp, hf, hadm⟩ := hm.1
  rcases three_dvd_table_cases htab with
    ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  ·
    obtain ⟨hn2, -⟩ := hadm
    have h3n : 3 ∣ n := (Nat.dvd_gcd_iff.1 h).1
    have h3q : 3 ∣ p ^ f - 1 := (Nat.dvd_gcd_iff.1 h).2
    have hc : StatedClassicalModel (CFSGIndex.lie d).Group .PSL n p f :=
      hm.2.resolve_right fun h => absurd h.1 (by omega)
    have hbm : CFSG.Blueprint.LieModel (CFSGIndex.lie d).Group .PSL n p f :=
      Or.inl ⟨by decide, hc⟩
    have hord := CFSG.GH74.card_of_lieModel_PSL (by omega) hbm
    rw [hcard, hord] at h12 hM
    exact ordA_three_false hp hf (m := n - 1) (by omega) (by omega) h3q hM h12
  ·
    obtain ⟨hn3, -⟩ := hadm
    have h3n : 3 ∣ n := (Nat.dvd_gcd_iff.1 h).1
    have h3q : 3 ∣ p ^ f + 1 := (Nat.dvd_gcd_iff.1 h).2
    have hc : StatedClassicalModel (CFSGIndex.lie d).Group .PSU n p f :=
      hm.2.resolve_right fun h => absurd h.1 (by omega)
    have hord := card_of_statedClassicalModel_psu' hn3 hc
    rw [hcard, hord] at h12 hM
    exact ordTwistedA_three_false hp hf (m := n - 1) (by omega) (by omega) h3q hM h12
  ·
    obtain ⟨-, hc | ⟨-, ⟨idx, hv⟩, hnames, ⟨e'⟩⟩⟩ := hm
    · exact hc.2.elim
    · cases idx <;> simp only [CFSG.Models.NamesTag] at hnames
      rename_i q
      obtain ⟨rfl, rfl⟩ := hnames
      have hord := hb ⟨.E6 q, hv⟩ (K ⧸ Subgroup.center K) ⟨e.trans e'⟩
      simp only [lieOrderFormula, PrimePower.card_def] at hord
      rw [hord] at hM
      exact orderE6_three_false hp hf h hM
  ·
    obtain ⟨-, hc | ⟨-, ⟨idx, hv⟩, hnames, ⟨e'⟩⟩⟩ := hm
    · exact hc.2.elim
    · cases idx <;> simp only [CFSG.Models.NamesTag] at hnames
      rename_i q
      obtain ⟨rfl, rfl⟩ := hnames
      have hord := hb ⟨.twistedE6 q, hv⟩ (K ⧸ Subgroup.center K) ⟨e.trans e'⟩
      simp only [lieOrderFormula, PrimePower.card_def] at hord
      rw [hord] at h12 hM
      exact orderTwistedE6_three_false hp hf h hM h12
  ·
    obtain ⟨hn2, -⟩ := hadm
    have hc : StatedClassicalModel (CFSGIndex.lie d).Group .PSL 2 3 2 :=
      hm.2.resolve_right fun h => absurd h.1 (by omega)
    have hbm : CFSG.Blueprint.LieModel (CFSGIndex.lie d).Group .PSL 2 3 2 :=
      Or.inl ⟨by decide, hc⟩
    have hord := CFSG.GH74.card_of_lieModel_PSL (by omega) hbm
    rw [hcard, hord] at h12
    exact not_pow_dvd_ordA_one_nine h12
  ·
    have hc : StatedClassicalModel (CFSGIndex.lie d).Group .POmegaOdd 3 3 1 :=
      hm.2.resolve_right fun h => absurd h.1 (by omega)
    have hord := (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two
      (by norm_num) hc).2.2.2.1 rfl
    rw [hcard, hord] at h12
    exact not_pow_dvd_ordBC_three_three h12
  ·
    obtain ⟨-, hc | ⟨-, ⟨idx, hv⟩, hnames, ⟨e'⟩⟩⟩ := hm
    · exact hc.2.elim
    · cases idx <;> simp only [CFSG.Models.NamesTag] at hnames
      rename_i q
      obtain ⟨hq3, hq1⟩ := hnames
      have hord := hb ⟨.G2 q, hv⟩ (K ⧸ Subgroup.center K) ⟨e.trans e'⟩
      simp only [lieOrderFormula, PrimePower.card_def, hq3, hq1] at hord
      rw [hord] at h12
      exact not_pow_dvd_orderG2_three h12
  ·
    obtain ⟨hn3, -⟩ := hadm
    have hc : StatedClassicalModel (CFSGIndex.lie d).Group .PSU 4 3 1 :=
      hm.2.resolve_right fun h => absurd h.1 (by omega)
    have hord := card_of_statedClassicalModel_psu' hn3 hc
    rw [hcard, hord] at h12
    exact not_pow_dvd_ordTwistedA_three_three h12

theorem spor_three_false (s : SporadicName) {c : ℕ} (hc : c = 1 ∨ c = 2)
    (h19 : 3 ^ 19 ∣ sporOrd s * c) (hM : 3 * sporOrd s ∣ monsterOrder) : False := by
  revert h19 hM
  rcases hc with rfl | rfl <;> cases s <;> decide +kernel

theorem sporadic_three_false (hOut : SporadicOuterLeTwo) (hOrd : SporadicOrdersTable)
    {T : Type} [Group T] [Finite T] [IsSimpleGroup T] (hnab : ∃ a b : T, a * b ≠ b * a)
    (s : SporadicName) (e : T ≃* (CFSGIndex.sporadic s).Group)
    (h19 : 3 ^ 19 ∣ Nat.card (MulAut T)) (hM : 3 * Nat.card T ∣ monsterOrder) : False := by
  have hcen : Subgroup.center T = ⊥ := center_eq_bot_of_isSimpleGroup hnab
  have hout : Nat.card (Outer T) ≤ 2 := hOut T inferInstance hnab s ⟨e⟩
  have hmul : Nat.card (MulAut T) = Nat.card T * Nat.card (Outer T) :=
    CFSG.HardMathSupport.Solomon.Proving.fi22_card_mulAut hcen
  have hcard : Nat.card T = sporOrd s := (Nat.card_congr e.toEquiv).trans (hOrd s)
  have hc : Nat.card (Outer T) = 1 ∨ Nat.card (Outer T) = 2 := by
    have := Nat.card_pos (α := Outer T)
    omega
  rw [hmul, hcard] at h19
  rw [hcard] at hM
  exact spor_three_false s hc h19 hM

theorem alternating_three_false {K : Type} [Group K] [Finite K] (hperf : commutator K = ⊤) {n : ℕ}
    [IsSimpleGroup (K ⧸ Subgroup.center K)] (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n))
    (h3 : 3 ∣ Nat.card (Subgroup.center K))
    (h12 : 3 ^ 12 ∣ Nat.card (K ⧸ Subgroup.center K)) : False := by
  haveI : Group.IsPerfect K := ⟨hperf⟩
  have hn := CFSG.HardMathSupport.Timmesfeld.Tables.Alt.five_le_of_centerQuotient hperf e
  have h3' := (CFSG.HardMathSupport.Timmesfeld.Tables.Alt.center_facts hn e Nat.prime_three
    (by norm_num)).2 h3
  have hd := CFSG.HardMathSupport.Timmesfeld.Tables.Alt.card_alternating_dvd hn (by omega)
  rw [← Nat.card_congr e.toEquiv] at hd
  have := Nat.le_of_dvd (by norm_num) (h12.trans hd)
  norm_num at this

theorem three_central_leaf (hGA : GriessAllModelsStatement) (hb : LieOrderBridge)
    (hOut : SporadicOuterLeTwo) (hOrd : SporadicOrdersTable)
    {K : Type} [Group K] [Finite K] (hq : CFSG.Open.IsQuasisimple K) (hK : CFSG.Open.IsKGroup K)
    (hM : Nat.card K ∣ monsterOrder) (h3 : 3 ∣ Nat.card (Subgroup.center K))
    (h12 : 3 ^ 12 ∣ Nat.card (K ⧸ Subgroup.center K))
    (h19 : 3 ^ 19 ∣ Nat.card (MulAut (K ⧸ Subgroup.center K))) : False := by
  have hnab := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hq
  have hq' : CFSG.IsQuasisimple K := ⟨⟨hq.1⟩, hq.2, hnab⟩
  haveI : Group.IsPerfect K := ⟨hq.1⟩
  haveI : IsSimpleGroup (K ⧸ Subgroup.center K) := hq.2
  have hcardK : Nat.card K = Nat.card (K ⧸ Subgroup.center K) * Nat.card (Subgroup.center K) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center K)
  have hdvd : Nat.card (K ⧸ Subgroup.center K) ∣ monsterOrder :=
    (Dvd.intro _ hcardK.symm).trans hM
  have hdvd3 : 3 * Nat.card (K ⧸ Subgroup.center K) ∣ monsterOrder := by
    refine Dvd.dvd.trans ?_ hM
    rw [hcardK, mul_comm]
    exact mul_dvd_mul_left _ h3
  rcases centralQuotient_family hq hK with ⟨n, ⟨e⟩⟩ | ⟨d, ⟨e⟩⟩ | ⟨s, ⟨e⟩⟩
  · exact alternating_three_false hq.1 e h3 h12
  · exact lie_three_false hGA hb hq' d e h3 h12 hdvd
  · exact sporadic_three_false hOut hOrd hnab s e h19 hdvd3

end CFSG.HardMathSupport.Dickson.I271.ThreeCentralLeaf
