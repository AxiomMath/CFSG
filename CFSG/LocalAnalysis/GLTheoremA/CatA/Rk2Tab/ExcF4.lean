module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2TwAModel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Num
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Arith
public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoRank
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutInnerExcF4TwoTorus
public import CFSG.LieType.SeitzGeneration.ExcTorusRankF4
public import CFSG.LieType.SeitzGeneration.ExcTorusBlocks
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBExcF4
public import CFSG.HardMathSupport.Lang.AnisoE6.FieldEmbed
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011LabUniq
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs16
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Assembly
public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4S.Inputs
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.Quasithin.EmptyFaithful.S146zYFacts
public import CFSG.Quasithin.EmptyFaithful.S146zYRes
public import CFSG.Quasithin.H13.NQCoreP134Main
public import CFSG.RankThree.PartOne.K159.BorelSL

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Assembly
  CFSG.Assembly.LowTwoRank CFSG.StandardType


private theorem rk2Mult_F4 (lab : GLALabel) (htag : lab.tag = .F4) (m : ℕ) :
    rk2Mult lab m = rk2Cnt [(2, true), (6, true), (8, true), (12, true)] m := by
  obtain ⟨tag, rank, n⟩ := lab
  simp only at htag
  rw [htag]
  rfl

private theorem rk2Cnt_f4_zero {m : ℕ}
    (hm : m ∉ ([1, 2, 3, 4, 6, 8, 12] : List ℕ)) :
    rk2Cnt [(2, true), (6, true), (8, true), (12, true)] m = 0 := by
  by_cases h : m ≤ 24
  · interval_cases m <;> simp_all [rk2Cnt]
  · refine rk2Cnt_large [(2, true), (6, true), (8, true), (12, true)] 24 ?_ (by omega)
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl <;> norm_num

private theorem rk2Cnt_f4_one : rk2Cnt [(2, true), (6, true), (8, true), (12, true)] 1 = 4 := by
  decide

private theorem rk2Cnt_f4_two : rk2Cnt [(2, true), (6, true), (8, true), (12, true)] 2 = 4 := by
  decide

private theorem rk2Cnt_f4_three : rk2Cnt [(2, true), (6, true), (8, true), (12, true)] 3 = 2 := by
  decide

private theorem rk2Cnt_f4_four : rk2Cnt [(2, true), (6, true), (8, true), (12, true)] 4 = 2 := by
  decide

private theorem rk2Cnt_f4_six : rk2Cnt [(2, true), (6, true), (8, true), (12, true)] 6 = 2 := by
  decide

private theorem rk2Cnt_f4_eight : rk2Cnt [(2, true), (6, true), (8, true), (12, true)] 8 = 1 := by
  decide

private theorem rk2Cnt_f4_twelve : rk2Cnt [(2, true), (6, true), (8, true), (12, true)] 12 = 1 := by
  decide

private theorem rk2_not_dvd_card_adjointF4 {K : Type} [Field K] [Finite K] {p n : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpK : ¬ p ∣ Nat.card K)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = rk2Ord p n)
    (hmem : ¬ (rk2Ord p n = 1 ∨ rk2Ord p n = 2 ∨ rk2Ord p n = 3 ∨ rk2Ord p n = 4 ∨
      rk2Ord p n = 6 ∨ rk2Ord p n = 8 ∨ rk2Ord p n = 12)) :
    ¬ p ∣ Nat.card (adjointGroup .F4 K) := by
  intro hdvd
  obtain ⟨m, hm, hpm⟩ := CFSG.LieType.SeitzGeneration.exists_dvd_phi_of_dvd_card_F4
    (K := K) hp hpK hdvd
  have hΦ : Polynomial.eval (Nat.card K : ℤ) (CFSG.RankThree.Chevalley.exhaustionPhi m) =
      Polynomial.eval (Nat.card K : ℤ) (Polynomial.cyclotomic m ℤ) := by
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp [CFSG.RankThree.Chevalley.exhaustionPhi, Polynomial.cyclotomic_one]
    · simp [CFSG.RankThree.Chevalley.exhaustionPhi, Polynomial.cyclotomic_two]
    · simp [CFSG.RankThree.Chevalley.exhaustionPhi,
        CFSG.LieType.SeitzGeneration.cyclotomic_three_eq]
    · simp [CFSG.RankThree.Chevalley.exhaustionPhi,
        CFSG.LieType.SeitzGeneration.cyclotomic_four_eq]
    · simp [CFSG.RankThree.Chevalley.exhaustionPhi,
        CFSG.LieType.SeitzGeneration.cyclotomic_six_eq]
    · simp [CFSG.RankThree.Chevalley.exhaustionPhi,
        CFSG.LieType.SeitzGeneration.cyclotomic_eight_eq]
    · simp [CFSG.RankThree.Chevalley.exhaustionPhi,
        CFSG.LieType.SeitzGeneration.cyclotomic_twelve_eq]
  have hde : m ≠ rk2Ord p n := fun h => hmem (h ▸ hm)
  have hpm' : (p : ℤ) ∣ Polynomial.eval (Nat.card K : ℤ) (Polynomial.cyclotomic m ℤ) := by
    rwa [← hΦ]
  refine CFSG.LieType.SeitzGeneration.not_dvd_cyclotomic_eval_of_ne hp he hde ?_ hpm'
  rintro ⟨c, hc⟩
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    have hle : p ≤ _ := Nat.le_of_dvd (by norm_num) ⟨c, hc⟩
    interval_cases p <;> first | omega | (exfalso; revert hp; norm_num)

private theorem rk2_card_le_three_pow_four (K : Type) [Field K] [Finite K] [CharP K 2]
    {E : Subgroup (adjointGroup .F4 K)} (hE : IsElemAbelian 3 E) : Nat.card E ≤ 3 ^ 4 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨f, -, hfcard⟩ := FiniteField.card K 2
  have hcard : Nat.card K = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hfcard]
  have hfpos : 0 < (f : ℕ) := f.pos
  let K' := GaloisField 2 (2 * (f : ℕ))
  haveI : Field K' := inferInstance
  haveI : Finite K' := inferInstance
  haveI : Fintype K' := Fintype.ofFinite K'
  have hK'card : Nat.card K' = (2 ^ (f : ℕ)) ^ 2 := by
    rw [GaloisField.card 2 (2 * (f : ℕ)) (by omega), ← pow_mul]
    ring_nf
  have hK'four : Nat.card K' = 4 ^ (f : ℕ) := by
    rw [hK'card, ← pow_mul, mul_comm (f : ℕ) 2, pow_mul]
    norm_num
  haveI : CharP K' 2 := charP_of_card_eq_prime_pow (R := K') (f := 2 * (f : ℕ)) (p := 2) (by
    rw [← Nat.card_eq_fintype_card, hK'card]; ring_nf)
  obtain ⟨φ⟩ := CFSG.HardMathSupport.Lang.AnisoE6.nonempty_ringHom_of_card_sq
    (ℓ := 2) (f := (f : ℕ)) hcard hK'card
  have h3 : 3 ∣ Nat.card K' - 1 := by
    have hq : ((Nat.card K' : ℕ) : ZMod 3) = 1 := by
      rw [hK'four, Nat.cast_pow]
      have h4 : ((4 : ℕ) : ZMod 3) = 1 := by decide
      rw [h4, one_pow]
    rw [← ZMod.natCast_eq_zero_iff (Nat.card K' - 1) 3, Nat.cast_sub Nat.card_pos,
      hq, Nat.cast_one, sub_self]
  have hT := TableBF4.ggF4ToralRankInput_three (K := K') h3
  have h1 := hT.card_le Nat.prime_three h3 (E := E.map (TableBF4Two.adjointMap φ))
    (CFSG.SectionRank.isElemAbelian_map hE _)
  rwa [Subgroup.card_map_of_injective (TableBF4Two.adjointMap_injective φ)] at h1

theorem rk2_pRank_adjointF4_le (K : Type) [Field K] [Finite K] {n p : ℕ}
    (hK : Nat.card K = 2 ^ n) (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup .F4 K)) ≤
      rk2Cnt [(2, true), (6, true), (8, true), (12, true)] (rk2Ord p n) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (adjointGroup .F4 K) := CFSG.LieType.Chevalley.generated_group_finite .F4 K
  have hn : 1 ≤ n := by
    by_contra h
    have h0 : n = 0 := by omega
    rw [h0, pow_zero] at hK
    have := Finite.one_lt_card (α := K)
    omega
  haveI : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two hn hK
  have hq : ((Nat.card K : ℕ) : ZMod p) = (2 : ZMod p) ^ n := by
    simp only [hK, Nat.cast_pow, Nat.cast_ofNat]
  have he : orderOf ((Nat.card K : ℕ) : ZMod p) = rk2Ord p n := by
    rw [hq]
    rfl
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    intro hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
  refine CFSG.SectionRank.pRank_le hp.one_lt (H := ⊤) ?_
  intro E _ hE
  by_cases hp3 : p = 3
  · subst hp3
    have h4 := rk2_card_le_three_pow_four K hE
    have h12 : rk2Ord 3 n = 1 ∨ rk2Ord 3 n = 2 := by
      have h2 : rk2Ord 3 n ∣ 2 := by
        simp only [rk2Ord]
        refine orderOf_dvd_of_pow_eq_one ?_
        rw [← pow_mul, mul_comm n 2, pow_mul]
        have hsq : ((2 : ZMod 3) ^ 2) = 1 := by
          have hne : (2 : ZMod 3) ≠ 0 := by
            intro h0
            have h2 : 3 ∣ 2 := (ZMod.natCast_eq_zero_iff 2 3).1 h0
            omega
          simpa using ZMod.pow_card_sub_one_eq_one hne
        rw [hsq, one_pow]
      rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
      · exact Or.inl h
      · exact Or.inr h
    rcases h12 with h | h
    · rw [h]
      simpa [rk2Cnt_f4_one] using h4
    · rw [h]
      simpa [rk2Cnt_f4_two] using h4
  · have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three hp2 hp3
    by_cases hmem : rk2Ord p n = 1 ∨ rk2Ord p n = 2 ∨ rk2Ord p n = 3 ∨ rk2Ord p n = 4 ∨
        rk2Ord p n = 6 ∨ rk2Ord p n = 8 ∨ rk2Ord p n = 12
    · rcases hmem with h1 | h2 | h3 | h4 | h6 | h8 | h12
      ·
        have hpq : p ∣ Nat.card K - 1 := by
          have h1' : ((Nat.card K : ℕ) : ZMod p) = 1 :=
            orderOf_eq_one_iff.1 (by rw [he, h1])
          rw [← ZMod.natCast_eq_zero_iff (Nat.card K - 1) p, Nat.cast_sub Nat.card_pos,
            h1', Nat.cast_one, sub_self]
        have hle := (TableBF4.ggF4ToralRankInput_of_five_le (K := K) hp hp5 hpq).card_le
          hp hpq hE
        rw [h1]
        simpa [rk2Cnt_f4_one] using hle
      ·
        have he2 : orderOf ((Nat.card K : ℕ) : ZMod p) = 2 := by rw [he, h2]
        have hle := (OrdPInnerExc.sylowTorus_F4_two K hp (by omega) he2).rank_le hp hE
        rw [h2]
        simpa [rk2Cnt_f4_two] using hle
      ·
        have he3 : orderOf ((Nat.card K : ℕ) : ZMod p) = 3 := by rw [he, h3]
        have hle := (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.sylowTorus_of_degCount_F4 K hp (by omega) hpK he3
          (by decide)).2.rank_le hp hE
        rw [h3]
        simpa [rk2Cnt_f4_three] using hle
      ·
        have he4 : orderOf ((Nat.card K : ℕ) : ZMod p) = 4 := by rw [he, h4]
        have hle := (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.sylowTorus_of_degCount_F4 K hp (by omega) hpK he4
          (by decide)).2.rank_le hp hE
        rw [h4]
        simpa [rk2Cnt_f4_four] using hle
      ·
        have he6 : orderOf ((Nat.card K : ℕ) : ZMod p) = 6 := by rw [he, h6]
        have hle := (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.sylowTorus_of_degCount_F4 K hp (by omega) hpK he6
          (by decide)).2.rank_le hp hE
        rw [h6]
        simpa [rk2Cnt_f4_six] using hle
      ·
        have he8 : orderOf ((Nat.card K : ℕ) : ZMod p) = 8 := by rw [he, h8]
        have hle := CFSG.LieType.SeitzGeneration.rankLE1_F4 K hp hpK
          (by rw [he8]; decide) E hE
        rw [h8]
        simpa [rk2Cnt_f4_eight] using hle
      ·
        have he12 : orderOf ((Nat.card K : ℕ) : ZMod p) = 12 := by rw [he, h12]
        have hle := CFSG.LieType.SeitzGeneration.rankLE1_F4 K hp hpK
          (by rw [he12]; decide) E hE
        rw [h12]
        simpa [rk2Cnt_f4_twelve] using hle
    ·
      have hnotmem : rk2Ord p n ∉ ([1, 2, 3, 4, 6, 8, 12] : List ℕ) := by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        exact hmem
      have hnd : ¬ p ∣ Nat.card (adjointGroup .F4 K) :=
        rk2_not_dvd_card_adjointF4 hp hp5 hpK he hmem
      have hone : Nat.card E = 1 := by
        have hEp : IsPGroup p ↥E := fun x => ⟨1, by
          apply Subtype.ext
          have hx : (x : adjointGroup .F4 K) ^ p = 1 := hE.2 x x.2
          simpa using hx⟩
        obtain ⟨k, hk⟩ := hEp.exists_card_eq
        by_contra hne
        have hkpos : 0 < k := by
          rcases Nat.eq_zero_or_pos k with h0 | h
          · rw [hk, h0] at hne
            simp at hne
          · exact h
        have hpdE : p ∣ Nat.card E := by
          rw [hk]
          exact dvd_pow_self p hkpos.ne'
        exact hnd (hpdE.trans (Subgroup.card_subgroup_dvd_card E))
      rw [hone, rk2Cnt_f4_zero hnotmem]
      simp

theorem rk2_pRank_three_adjointF4_le (K : Type) [Field K] [Finite K] [CharP K 2] (n : ℕ)
    (hK : Nat.card K = 2 ^ n) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (adjointGroup .F4 K)) ≤ 4 := by
  refine CFSG.SectionRank.pRank_le (by norm_num : 1 < 3) (H := ⊤) ?_
  intro E _ hE
  exact rk2_card_le_three_pow_four K hE

private theorem rk2_not_dvd_center_F4 (X : Type) [Group X] [Finite X] (lab : GLALabel) (p : ℕ)
    (hL : Rk2IsLabel X lab) (htag : lab.tag = .F4) (hp : p.Prime) (hp2 : p ≠ 2)
    (hn : 1 ≤ lab.n) {F : Type} [Field F] [Finite F]
    (hcardF : Nat.card F = 2 ^ lab.n)
    (e0 : (X ⧸ Subgroup.center X) ≃* CFSG.Blueprint.AdjointQuotient .F4 F) :
    ¬ p ∣ Nat.card (Subgroup.center X) := by
  classical
  obtain ⟨hQ, -, -⟩ := rk2_model_of_isLabel hL
  have hQ' : CFSG.IsQuasisimple X := (CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.2.1.2 hQ
  haveI : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two hn hcardF
  haveI : Finite (adjointGroup .F4 F) := CFSG.LieType.Chevalley.generated_group_finite .F4 F
  haveI : Finite (CFSG.Blueprint.AdjointQuotient .F4 F) :=
    Finite.of_surjective (QuotientGroup.mk' (Subgroup.center (adjointGroup .F4 F)))
      (QuotientGroup.mk'_surjective _)
  have hperfG : Group.IsPerfect (adjointGroup .F4 F) :=
    CFSG.LieType.Steinberg.Adjoint.isPerfect_f4 F
  have hperfQ : Group.IsPerfect (CFSG.Blueprint.AdjointQuotient .F4 F) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  haveI : Finite (CFSG.RankThree.PerfectCover.hopfMultiplier
      (CFSG.Blueprint.AdjointQuotient .F4 F)) :=
    CFSG.RankThree.PerfectCover.finite_hopfMultiplier hperfQ
  haveI : Finite (CFSG.Open.griessHopfMultiplier (CFSG.Blueprint.AdjointQuotient .F4 F)) :=
    Finite.of_equiv _ (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).symm.toEquiv
  have h1 := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_center_dvd_hopf hQ' e0
  intro hpd
  have hdvdM : p ∣ Nat.card (CFSG.Open.griessHopfMultiplier
      (CFSG.Blueprint.AdjointQuotient .F4 F)) := hpd.trans h1
  rcases Nat.lt_or_ge lab.n 3 with h3 | h3
  · interval_cases lab.n
    ·
      have hK2 : Nat.card F = 2 := by simpa using hcardF
      have hMle := (CFSG.LieType.Steinberg.CentralExt.F4Two.f4_two_hopfMultiplier
        (K := F) hK2).2
      have hMpos : 0 < Nat.card (CFSG.Open.griessHopfMultiplier
          (CFSG.Blueprint.AdjointQuotient .F4 F)) := Nat.card_pos
      have hple : p ≤ Nat.card (CFSG.Open.griessHopfMultiplier
          (CFSG.Blueprint.AdjointQuotient .F4 F)) := Nat.le_of_dvd hMpos hdvdM
      have hp2le : 2 ≤ p := hp.two_le
      omega
    ·
      have hK4 : Nat.card F = 2 ^ 2 := by simpa using hcardF
      have hsub := (CFSG.LieType.Steinberg.CentralExt.FieldFour.f4_four_hopfMultiplier
        (K := F) hK4).2
      haveI : Subsingleton (CFSG.Open.griessHopfMultiplier
          (CFSG.Blueprint.AdjointQuotient .F4 F)) := hsub
      have hcardM : Nat.card (CFSG.Open.griessHopfMultiplier
          (CFSG.Blueprint.AdjointQuotient .F4 F)) = 1 := Nat.card_unique
      rw [hcardM] at hdvdM
      exact hp.one_lt.ne' (Nat.dvd_one.1 hdvdM)
  · have h5 : 5 ≤ Nat.card F := by
      rw [hcardF]
      calc 5 ≤ 2 ^ 3 := by norm_num
        _ ≤ 2 ^ lab.n := Nat.pow_le_pow_right (by norm_num) h3
    have hsub := (CFSG.LieType.Steinberg.CentralExt.AdjointClosed.f4_hopfMultiplier
      (K := F) h5).2
    haveI : Subsingleton (CFSG.Open.griessHopfMultiplier
        (CFSG.Blueprint.AdjointQuotient .F4 F)) := hsub
    have hcardM : Nat.card (CFSG.Open.griessHopfMultiplier
        (CFSG.Blueprint.AdjointQuotient .F4 F)) = 1 := Nat.card_unique
    rw [hcardM] at hdvdM
    exact hp.one_lt.ne' (Nat.dvd_one.1 hdvdM)

theorem rk2_pRank_le_F4 (X : Type) [Group X] [Finite X] (lab : GLALabel) (p : ℕ)
    (hL : Rk2IsLabel X lab) (htag : lab.tag = .F4) (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (⊤ : Subgroup X) ≤ rk2Mult lab (rk2Ord p lab.n) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hl, hM⟩ := rk2_model_of_isLabel hL
  have hn : 1 ≤ lab.n := hl.1
  have hM' : CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X) .F4 0 2 lab.n := by
    simpa [CFSG.StandardType.MarkedModel, CFSG.StandardType.markTag,
      CFSG.StandardType.markRank, CFSG.StandardType.markChar,
      CFSG.StandardType.markDeg, htag] using hM
  have hCE := hM'.chevalleyExceptionalModel
    (by decide : (.F4 : StatedLieTag) ∈ CFSG.Blueprint.chevalleyExceptionalTags)
  simp only [CFSG.Blueprint.ChevalleyExceptionalModel,
    CFSG.Blueprint.UntwistedChevalleyModel] at hCE
  obtain ⟨F, hF, hFin, hcardF, ⟨e0⟩⟩ := hCE.2
  letI : Field F := hF
  letI : Finite F := hFin
  let χ : CFSG.Blueprint.AdjointQuotient .F4 F ≃* adjointGroup .F4 F :=
    (QuotientGroup.quotientMulEquivOfEq
      (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .F4) (K := F))).trans
        QuotientGroup.quotientBot
  have hZ : ¬ p ∣ Nat.card (Subgroup.center X) :=
    rk2_not_dvd_center_F4 X lab p hL htag hp hp2 hn hcardF e0
  have hquot : CFSG.Open.pRank p (⊤ : Subgroup (X ⧸ Subgroup.center X)) =
      CFSG.Open.pRank p (⊤ : Subgroup X) :=
    CFSG.SectionRank.pRank_quotient_eq (p := p) (Subgroup.center X) hZ
  have htr : CFSG.Open.pRank p (⊤ : Subgroup (X ⧸ Subgroup.center X)) =
      CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup .F4 F)) :=
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt (e0.trans χ)
  rw [← hquot, htr]
  have hmul : rk2Mult lab (rk2Ord p lab.n) =
      rk2Cnt [(2, true), (6, true), (8, true), (12, true)] (rk2Ord p lab.n) :=
    rk2Mult_F4 lab htag _
  rw [hmul]
  exact rk2_pRank_adjointF4_le F hcardF hp hp2

end CFSG.LocalAnalysis.GLTheoremA
