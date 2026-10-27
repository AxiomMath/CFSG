module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2TwAModel
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesE8RestTorus
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.E8Arith
public import CFSG.LieType.SeitzGeneration.ExcHigh.Classes
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoRank
public import CFSG.HardMathSupport.Lang.AnisoE6.FieldEmbed
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE8FiveConjClass
public import CFSG.Sporadic.HN.F5Group

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.SeitzGeneration

private theorem rk2Mult_E8 (m : ℕ) :
    rk2Cnt [(2, true), (8, true), (12, true), (14, true), (18, true), (20, true), (24, true),
      (30, true)] m = degCount Tag.E8 m := by
  have h : [(2, true), (8, true), (12, true), (14, true), (18, true), (20, true), (24, true),
      (30, true)] = (degreesE Tag.E8).map (fun d => (d, true)) := rfl
  rw [h]
  simp only [rk2Cnt]
  rw [List.countP_map]
  have hpred : ((fun f : ℕ × Bool => if f.2 = true then decide (m ∣ f.1)
        else decide (m ∣ 2 * f.1 ∧ ¬ m ∣ f.1)) ∘ fun d => (d, true)) = fun d => decide (m ∣ d) := by
    funext d
    simp
  rw [hpred, List.countP_eq_length_filter]
  rfl

private theorem dvd_sub_one_of_orderOf {K : Type} [Field K] [Finite K] {p e : ℕ}
    (hp : p.Prime) (hpq : ¬ p ∣ Nat.card K)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = e) : e ∣ p - 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hq0 : ((Nat.card K : ℕ) : ZMod p) ≠ 0 := fun h0 =>
    hpq ((ZMod.natCast_eq_zero_iff (Nat.card K) p).1 h0)
  have h := ZMod.orderOf_dvd_card_sub_one hq0
  rwa [he] at h

private theorem orderOf_card_eq_rk2Ord {K : Type} [Field K] [Finite K] {p n : ℕ}
    (hcard : Nat.card K = 2 ^ n) :
    orderOf ((Nat.card K : ℕ) : ZMod p) = rk2Ord p n := by
  rw [hcard, rk2Ord]
  push_cast
  rfl




private theorem rk2_E8_toralRankInput {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1) :
    CFSG.StandardType.GGExcToralRankInput Tag.E8 K p := by
  by_cases hp11 : p < 11
  · have h2le := hp.two_le
    interval_cases p
    · exact absurd rfl hp2
    · exact CFSG.StandardType.TableBExc.Three.ggExcToralRankInput_E8_three hpq
    · exact absurd hp (by norm_num)
    · exact CFSG.StandardType.TableBExc.ggExcToralRankInput_E8_five hpq
    · exact absurd hp (by norm_num)
    · exact CFSG.StandardType.TableBExc.ggExcToralRankInput_E8_seven hpq
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
  · exact CFSG.StandardType.TableBExc.ggExcToralRankInput_E8_of_eleven_le hp (by omega) hpq

private theorem rk2_E8_adjoint_card_le_eight {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1) :
    ∀ E : Subgroup (adjointGroup Tag.E8 K), IsElemAbelian p E → Nat.card E ≤ p ^ 8 :=
  fun E hE => CFSG.StandardType.GGExcToralRankInput.card_le
    (rk2_E8_toralRankInput hp hp2 hpq)
    (CFSG.StandardType.TableBExc.card_torusPow_E8 hp hpq) hE

private theorem rk2_E8_adjoint_card_le_of_baseChange {K K' : Type} [Field K] [Finite K]
    [Field K'] [Finite K'] (φ : K →+* K') {p r : ℕ}
    (h : ∀ E : Subgroup (adjointGroup Tag.E8 K'), IsElemAbelian p E → Nat.card E ≤ p ^ r) :
    ∀ E : Subgroup (adjointGroup Tag.E8 K), IsElemAbelian p E → Nat.card E ≤ p ^ r := by
  intro E hE
  have h1 := h (E.map (CFSG.StandardType.TableBExcTwo.adjointMap Tag.E8 φ))
    (CFSG.SectionRank.isElemAbelian_map hE _)
  rwa [Subgroup.card_map_of_injective
    (CFSG.StandardType.TableBExcTwo.adjointMap_injective φ)] at h1

private theorem rk2_E8_adjoint_five_card_le {K : Type} [Field K] [Finite K]
    (he : orderOf ((Nat.card K : ℕ) : ZMod 5) = 4) :
    ∀ E : Subgroup (adjointGroup Tag.E8 K), IsElemAbelian 5 E → Nat.card E ≤ 5 ^ 4 := by
  intro E hE
  by_cases hE4 : 5 ^ 4 ≤ Nat.card E
  · obtain ⟨A, hAel, hAcard⟩ := exists_elemAbelian_E8_four K Nat.prime_five he
    have hA4 : 5 ^ 4 ≤ Nat.card A := by rw [hAcard]
    obtain ⟨c, hc⟩ := CFSG.StandardType.NoOffE8Five.exists_conj_map_eq_E8_five
      (by simpa [pow_two] using dvd_sq_add_one_of_orderOf_eq_four Nat.prime_five he)
      hE hAel hE4 hA4
    have hEq : Nat.card E = 5 ^ 4 := by
      calc Nat.card E = Nat.card (E.map (MulAut.conj c).toMonoidHom) :=
            (Subgroup.card_map_of_injective (MulAut.conj c).injective).symm
        _ = Nat.card A := by rw [hc]
        _ = 5 ^ 4 := hAcard
    omega
  · omega

private theorem rk2_E8_adjoint_card_le
    (K : Type) [Field K] [Finite K] (p e n : ℕ)
    (hp : p.Prime) (hp2 : p ≠ 2) (hcard : Nat.card K = 2 ^ n)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = e) :
    ∀ E : Subgroup (adjointGroup Tag.E8 K), IsElemAbelian p E →
      Nat.card E ≤ p ^ degCount Tag.E8 e := by
  have hpq : ¬ p ∣ Nat.card K := by
    rw [hcard]
    intro hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h
    · rw [h0, pow_zero] at hcard
      have h2 : 1 < Nat.card K := Finite.one_lt_card
      omega
    · exact h
  by_cases hd0 : degCount Tag.E8 e = 0
  · intro E hE
    have he1 : 1 ≤ e := Nat.pos_of_ne_zero (he ▸ orderOf_natCast_ne_zero hp hpq)
    have he7 : 7 ≤ e := by
      by_contra h
      interval_cases e <;> revert hd0 <;> decide
    have hp3 : 3 < p := by
      have := orderOf_lt_prime hp hpq he
      omega
    rw [CFSG.LieType.SeitzGeneration.elemAbelian_card_eq_one_of_degCount_zero
      (τ := Tag.E8) (Or.inr (Or.inr rfl)) K hp hp3 hpq he hd0 hE, hd0]
    simp
  by_cases hd1 : degCount Tag.E8 e = 1
  · intro E hE
    rw [hd1]
    simpa using rankLE1_E8 K hp hpq (by rw [he]; omega) E hE
  by_cases hd2 : degCount Tag.E8 e = 2
  · intro E hE
    rw [hd2]
    exact CFSG.HardMathSupport.Timmesfeld.CrossChar.rankLE2_E8_of_degCount_eq_two K hp
      (by rw [he]; exact hd2) E hE
  have hd3 : 3 ≤ degCount Tag.E8 e := by omega
  rcases CFSG.HardMathSupport.Timmesfeld.CrossChar.eq_of_three_le_degCount_E8 hd3 with
    rfl | rfl | rfl | rfl | rfl
  ·
    intro E hE
    have hpq1 : p ∣ Nat.card K - 1 :=
      CFSG.LieType.SeitzGeneration.ExcHigh.dvd_sub_one_of_orderOf_eq_one Nat.card_pos he
    haveI : CharP K 2 := CFSG.StandardType.charP_two_of_card hcard
    have h8 : degCount Tag.E8 1 = 8 := by decide
    rw [h8]
    exact rk2_E8_adjoint_card_le_eight hp hp2 hpq1 E hE
  ·
    intro E hE
    let K' := GaloisField 2 (2 * n)
    haveI : Field K' := inferInstance
    haveI : Finite K' := inferInstance
    have hK'pow : Nat.card K' = 2 ^ (2 * n) := GaloisField.card 2 (2 * n) (by omega)
    haveI : CharP K' 2 := CFSG.StandardType.charP_two_of_card hK'pow
    have hK'card : Nat.card K' = (2 ^ n) ^ 2 := by
      rw [hK'pow, ← pow_mul]
      ring_nf
    haveI : CharP K 2 := CFSG.StandardType.charP_two_of_card hcard
    obtain ⟨φ⟩ := CFSG.HardMathSupport.Lang.AnisoE6.nonempty_ringHom_of_card_sq
      (ℓ := 2) (f := n) (k := K) (K := K') hcard hK'card
    have hpq' : p ∣ Nat.card K' - 1 := by
      have hsq : ((Nat.card K : ℕ) : ZMod p) ^ 2 = 1 := by
        rw [← he]
        exact pow_orderOf_eq_one _
      have hpos : 1 ≤ (Nat.card K) ^ 2 :=
        Nat.succ_le_of_lt (pow_pos (Nat.card_pos (α := K)) 2)
      have h1 : (((Nat.card K : ℕ) ^ 2 - 1 : ℕ) : ZMod p) = 0 := by
        rw [Nat.cast_sub hpos]
        push_cast
        rw [hsq, sub_self]
      rw [hK'card, ← hcard]
      exact (ZMod.natCast_eq_zero_iff ((Nat.card K) ^ 2 - 1) p).1 h1
    have h8 : degCount Tag.E8 2 = 8 := by decide
    rw [h8]
    exact rk2_E8_adjoint_card_le_of_baseChange φ (fun E' hE' =>
      rk2_E8_adjoint_card_le_eight hp hp2 hpq' E' hE') E hE
  ·
    intro E hE
    have hdvd : 3 ∣ p - 1 := dvd_sub_one_of_orderOf hp hpq he
    have hp7 : 7 ≤ p := by
      have h2le := hp.two_le
      by_contra h
      interval_cases p
      · exact hp2 rfl
      · exact absurd hdvd (by norm_num)
      · exact absurd hp (by norm_num)
      · exact absurd hdvd (by norm_num)
      · exact absurd hp (by norm_num)
    have hS := CFSG.StandardType.ExcFrames.sylowTorus_adjoint_E8_four K hp hp7 hpq (Or.inl he)
    have h4 : degCount Tag.E8 3 = 4 := by decide
    rw [h4]
    exact hS.rank_le hp hE
  ·
    intro E hE
    have h4 : degCount Tag.E8 4 = 4 := by decide
    rw [h4]
    by_cases hp5 : p = 5
    · subst hp5
      exact rk2_E8_adjoint_five_card_le he E hE
    · have hdvd : 4 ∣ p - 1 := dvd_sub_one_of_orderOf hp hpq he
      have hp7 : 7 ≤ p := by
        have h2le := hp.two_le
        by_contra h
        interval_cases p
        · exact hp2 rfl
        · exact absurd hdvd (by norm_num)
        · exact absurd hp (by norm_num)
        · exact hp5 rfl
        · exact absurd hp (by norm_num)
      have hS := CFSG.StandardType.ExcFrames.sylowTorus_adjoint_E8_four K hp hp7 hpq
        (Or.inr (Or.inl he))
      exact hS.rank_le hp hE
  ·
    intro E hE
    have hdvd : 6 ∣ p - 1 := dvd_sub_one_of_orderOf hp hpq he
    have hp7 : 7 ≤ p := by
      have h2le := hp.two_le
      by_contra h
      interval_cases p
      · exact absurd hdvd (by norm_num)
      · exact absurd hdvd (by norm_num)
      · exact absurd hp (by norm_num)
      · exact absurd hdvd (by norm_num)
      · exact absurd hp (by norm_num)
    have hS := CFSG.StandardType.ExcFrames.sylowTorus_adjoint_E8_four K hp hp7 hpq
      (Or.inr (Or.inr he))
    have h4 : degCount Tag.E8 6 = 4 := by decide
    rw [h4]
    exact hS.rank_le hp hE

private theorem rk2_pRank_le_E8_assembly (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (lab : GLALabel) (K : Type) [Group K] [Finite K] (hK : Rk2IsLabel K lab)
    (htag : lab.tag = .E8)
    (hbound : ∀ (F : Type) [Field F] [Finite F], Nat.card F = 2 ^ lab.n →
      ∀ E : Subgroup (adjointGroup Tag.E8 F), IsElemAbelian p E →
        Nat.card E ≤ p ^ degCount Tag.E8 (rk2Ord p lab.n)) :
    CFSG.Open.pRank p (⊤ : Subgroup K) ≤ rk2Mult lab (rk2Ord p lab.n) := by
  obtain ⟨t, l, n⟩ := lab
  simp only at htag
  subst htag
  obtain ⟨hQ, hlab, hM⟩ := rk2_model_of_isLabel hK
  have hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .E8 0 2 n := by
    simpa [CFSG.StandardType.MarkedModel, CFSG.StandardType.markTag, CFSG.StandardType.markRank,
      CFSG.StandardType.markChar, CFSG.StandardType.markDeg] using hM
  have hCE := hM'.chevalleyExceptionalModel (t := .E8) (n := 0) (p := 2) (f := n) (by decide)
  simp only [CFSG.Blueprint.ChevalleyExceptionalModel, CFSG.Blueprint.UntwistedChevalleyModel]
    at hCE
  obtain ⟨-, F, hFld, hFin, hFcard, ⟨e⟩⟩ := hCE
  have hQ' : CFSG.IsQuasisimple K :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff K).2.2.1.2 hQ
  have hZ : Subgroup.center K = ⊥ :=
    CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.center_eq_bot_of_E8 hQ' hlab.1
      hFcard e
  haveI : Finite ↥(adjointGroup Tag.E8 F) :=
    CFSG.LieType.Chevalley.generated_group_finite Tag.E8 F
  have h1 : CFSG.Open.pRank p (⊤ : Subgroup (K ⧸ Subgroup.center K)) =
      CFSG.Open.pRank p (⊤ : Subgroup K) := by
    haveI : Fact p.Prime := ⟨hp⟩
    exact CFSG.SectionRank.pRank_quotient_eq (Subgroup.center K) (by
      rw [hZ]
      simpa using hp.one_lt.ne')
  have h2 : CFSG.Open.pRank p (⊤ : Subgroup (K ⧸ Subgroup.center K)) =
      CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup Tag.E8 F)) := by
    haveI : Fact p.Prime := ⟨hp⟩
    have hAdj : CFSG.Open.pRank p (⊤ : Subgroup (CFSG.Blueprint.AdjointQuotient .E8 F)) =
        CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup Tag.E8 F)) :=
      CFSG.SectionRank.pRank_quotient_eq (Subgroup.center (adjointGroup Tag.E8 F))
        (by
          rw [CFSG.LieType.Chevalley.center_adjointGroup_eq_bot]
          simpa using hp.one_lt.ne')
    exact (CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e).trans hAdj
  have h3 : CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup Tag.E8 F)) ≤
      degCount Tag.E8 (rk2Ord p n) :=
    CFSG.SectionRank.pRank_le hp.one_lt (H := ⊤) (k := degCount Tag.E8 (rk2Ord p n))
      (fun E _ hE => hbound F hFcard E hE)
  have h5 : rk2Mult ⟨.E8, l, n⟩ (rk2Ord p n) = degCount Tag.E8 (rk2Ord p n) := by
    simpa [rk2Mult] using rk2Mult_E8 (rk2Ord p n)
  calc CFSG.Open.pRank p (⊤ : Subgroup K)
      = CFSG.Open.pRank p (⊤ : Subgroup (K ⧸ Subgroup.center K)) := h1.symm
    _ = CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup Tag.E8 F)) := h2
    _ ≤ degCount Tag.E8 (rk2Ord p n) := h3
    _ = rk2Mult ⟨.E8, l, n⟩ (rk2Ord p n) := h5.symm

theorem rk2_pRank_le_E8 (K : Type) [Group K] [Finite K] (lab : GLALabel)
    (hK : Rk2IsLabel K lab) (htag : lab.tag = .E8) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (⊤ : Subgroup K) ≤ rk2Mult lab (rk2Ord p lab.n) := by
  refine rk2_pRank_le_E8_assembly p hp hp2 lab K hK htag ?_
  intro F _ _ hFcard E hE
  exact rk2_E8_adjoint_card_le F p (rk2Ord p lab.n) lab.n hp hp2 hFcard
    (orderOf_card_eq_rk2Ord hFcard) E hE

end CFSG.LocalAnalysis.GLTheoremA
