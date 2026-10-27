module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S262GF2Red
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCoreS
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.OutCover
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusCentLift

import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.BlockB.OuterThree.LieTwo
import CFSG.LocalAnalysis.GLTheoremA.CatA.HDescCTwo
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusCentSpMain
import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeD.ModelPlus
import CFSG.HardMathSupport.Curtis.Coordinator.PerfThreeLinear
import CFSG.Adapters.LieModelSimple
import CFSG.CGT.PushingUpLit.CGT6.EmbFourSevenSympl
public import CFSG.HardMathSupport.Solomon.Coordinator.B3LieRes
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S262

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA.KD264Lie
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

theorem dvd_card_of_perfectNoncycThreeIn {X : Type} [Group X] [Finite X]
    {C : Subgroup X} (h : CFSG.AGLEmbedding.ToralCensus.PerfectNoncycThreeIn C) :
    ∃ P : Subgroup X, P ≤ C ∧ ⁅P, P⁆ = P ∧ 3 ∣ Nat.card P := by
  obtain ⟨V, hVC, hV, Q, hQV, hQ, hnc⟩ := h
  refine ⟨V, hVC, hV, ?_⟩
  obtain ⟨j, hj2, hjcard⟩ :=
    CFSG.CGT.PushingUpLit.CGT6.exists_two_le_card_eq_pow_of_not_isCyclic
      Nat.prime_three hQ hnc
  have h3Q : 3 ∣ Nat.card Q := by
    rw [hjcard]
    simpa using (Nat.pow_dvd_pow 3 (m := 1) (n := j) (by omega))
  exact h3Q.trans (Subgroup.card_dvd_of_le hQV)

theorem exists_conj_eq_of_autThreePowInner {X : Type} [Group X] [IsSimpleGroup X]
    (hX : AutThreePowInner X) {a : MulAut X} (ha1 : a ≠ 1) (ha3 : a ^ 3 = 1) :
    ∃ v : X, v ≠ 1 ∧ v ^ 3 = 1 ∧ a = MulAut.conj v := by
  have hpow : ∀ n : ℕ, ∀ x : X, (a ^ n) x = a ^[n] x := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
        intro x
        rw [pow_succ, MulAut.mul_apply, Function.iterate_succ_apply, ih]
  have hfix : ∀ x : X, a ^[3 ^ 1] x = x := by
    intro x
    show a ^[3] x = x
    rw [← hpow 3 x]
    rw [ha3]
    rfl
  obtain ⟨v, hv⟩ := hX a 1 hfix
  have ha : a = MulAut.conj v := by
    ext x
    rw [MulAut.conj_apply]
    exact hv x
  have hconj3 : (MulAut.conj v) ^ 3 = 1 := by
    rw [← ha]
    exact ha3
  have hcent : v ^ 3 ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro x
    have hmap : MulAut.conj (v ^ 3) = 1 := by
      rw [map_pow, hconj3]
    have hx := congrArg (fun f : MulAut X => f x) hmap
    simp only [MulAut.conj_apply, MulAut.one_apply] at hx
    have hx' : v ^ 3 * x = x * v ^ 3 := by
      have := congrArg (· * (v ^ 3)) hx
      simpa [mul_assoc] using this
    exact hx'.symm
  have hv1 : v ≠ 1 := by
    intro h
    exact ha1 (by rw [ha, h, map_one])
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with hZ | hZ
  · have hv3 : v ^ 3 = 1 := by
      rw [hZ] at hcent
      simpa using hcent
    exact ⟨v, hv1, hv3, ha⟩
  · exfalso
    have hconj1 : MulAut.conj v = 1 := by
      ext x
      change v * x * v⁻¹ = x
      have hxmem : v ∈ Subgroup.center X := by
        rw [hZ]
        exact Subgroup.mem_top v
      have hcomm := (Subgroup.mem_center_iff.mp hxmem) x
      rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
    exact ha1 (ha.trans hconj1)

theorem fixed_perfect_of_forall_centralizer {X : Type} [Group X] [IsSimpleGroup X]
    (hX : AutThreePowInner X)
    (h : ∀ v : X, v ^ 3 = 1 → v ≠ 1 →
      ∃ P : Subgroup X, P ≤ Subgroup.centralizer ({v} : Set X) ∧ ⁅P, P⁆ = P ∧
        3 ∣ Nat.card P) :
    ∀ a : MulAut X, a ≠ 1 → a ^ 3 = 1 →
      ∃ P : Subgroup X, P ≤ fixSubgroup a ∧ ⁅P, P⁆ = P ∧ 3 ∣ Nat.card P := by
  intro a ha1 ha3
  obtain ⟨v, hv1, hv3, ha⟩ := exists_conj_eq_of_autThreePowInner hX ha1 ha3
  obtain ⟨P, hP, hperf, h3⟩ := h v hv3 hv1
  exact ⟨P, by
    rwa [ha, CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_fixSubgroup_conj], hperf, h3⟩

theorem fixed_perfect_of_centNoncycThreeGroup {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hX : AutThreePowInner X) (h : CFSG.AGLEmbedding.ToralCensus.CentNoncycThreeGroup X) :
    ∀ a : MulAut X, a ≠ 1 → a ^ 3 = 1 →
      ∃ P : Subgroup X, P ≤ fixSubgroup a ∧ ⁅P, P⁆ = P ∧ 3 ∣ Nat.card P :=
  fixed_perfect_of_forall_centralizer hX fun v hv3 hv1 =>
    dvd_card_of_perfectNoncycThreeIn (h v hv3 hv1)

theorem three_ne_characteristic_of_card_two {e : TauCeti.LieTypeIndex} {q : TauCeti.PrimePower}
    (hc : e.characteristic = q.p) (hq : q.card = 2) : 3 ≠ e.characteristic := by
  rw [hc, (CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.primePower_card_two' hq).1]
  norm_num

theorem good3_of_fixed_perfect (hPL : KD264PL 3) (d : TauCeti.ValidLieTypeIndex)
    [Finite (TauCeti.CFSGIndex.lie d).Group] (hchar : 3 ≠ d.1.characteristic)
    (h : ∀ a : MulAut (TauCeti.CFSGIndex.lie d).Group, a ≠ 1 → a ^ 3 = 1 →
      ∃ P : Subgroup (TauCeti.CFSGIndex.lie d).Group, P ≤ fixSubgroup a ∧ ⁅P, P⁆ = P ∧
        3 ∣ Nat.card P) :
    Good3 (TauCeti.CFSGIndex.lie d).Group := by
  intro a ha1 ha3
  obtain ⟨P, hP, hperf, h3⟩ := h a ha1 ha3
  obtain ⟨J, hJ, hJp⟩ := hPL d hchar a ha3 ha1 P hP hperf h3
  exact CFSG.LocalAnalysis.GLTheoremA.HDesc.layer_ne_bot_of_component d Nat.prime_three hJ hJp

theorem good3On_of_fixed_perfect (hPL : KD264PL 3) {Q : TauCeti.LieTypeIndex → Prop}
    (hchar : ∀ e, Q e → 3 ≠ e.characteristic)
    (h : ∀ (d : TauCeti.ValidLieTypeIndex) [Finite (TauCeti.CFSGIndex.lie d).Group], Q d.1 →
      ∀ a : MulAut (TauCeti.CFSGIndex.lie d).Group, a ≠ 1 → a ^ 3 = 1 →
        ∃ P : Subgroup (TauCeti.CFSGIndex.lie d).Group, P ≤ fixSubgroup a ∧ ⁅P, P⁆ = P ∧
          3 ∣ Nat.card P) :
    Good3On Q := by
  intro d _ hQ
  exact good3_of_fixed_perfect hPL d (hchar d.1 hQ) (h d hQ)

theorem gf2Lin_cases {e : TauCeti.LieTypeIndex} (h : gf2Lin e) :
    ∃ (r : ℕ) (q : TauCeti.PrimePower), e = .A r q ∧ 4 ≤ r ∧ q.card = 2 := by
  cases e <;> simp only [gf2Lin] at h
  · exact ⟨_, _, rfl, h.1, h.2⟩
  all_goals exact h.elim

theorem gf2Symp_cases {e : TauCeti.LieTypeIndex} (h : gf2Symp e) :
    ∃ (r : ℕ) (q : TauCeti.PrimePower), e = .B r q ∧ 5 ≤ r ∧ q.card = 2 := by
  cases e <;> simp only [gf2Symp] at h
  · exact ⟨_, _, rfl, h.1, h.2⟩
  all_goals exact h.elim

theorem gf2OrthPlus_cases {e : TauCeti.LieTypeIndex} (h : gf2OrthPlus e) :
    ∃ (r : ℕ) (q : TauCeti.PrimePower), e = .D r q ∧ 5 ≤ r ∧ q.card = 2 := by
  cases e <;> simp only [gf2OrthPlus] at h
  · exact ⟨_, _, rfl, h.1, h.2⟩
  all_goals exact h.elim

theorem gf2OrthMinus_cases {e : TauCeti.LieTypeIndex} (h : gf2OrthMinus e) :
    ∃ (r : ℕ) (q : TauCeti.PrimePower), e = .twistedD r q ∧ 6 ≤ r ∧ q.card = 2 := by
  cases e <;> simp only [gf2OrthMinus] at h
  · exact ⟨_, _, rfl, h.1, h.2⟩
  all_goals exact h.elim

theorem fixed_perfect_gf2Lin :
    ∀ (d : TauCeti.ValidLieTypeIndex) [Finite (TauCeti.CFSGIndex.lie d).Group],
      gf2Lin d.1 → ∀ a : MulAut (TauCeti.CFSGIndex.lie d).Group, a ≠ 1 → a ^ 3 = 1 →
        ∃ P : Subgroup (TauCeti.CFSGIndex.lie d).Group, P ≤ fixSubgroup a ∧ ⁅P, P⁆ = P ∧
          3 ∣ Nat.card P := by
  intro d _ hd a ha1 ha3
  obtain ⟨e, hv⟩ := d
  change gf2Lin e at hd
  obtain ⟨r, q, he, hr4, hq⟩ := gf2Lin_cases hd
  subst e
  obtain ⟨hp2, hqe⟩ := primePower_card_two' hq
  have hmodel :=
    CFSG.AGLEmbedding.KFactProofs.CoverFive.statedClassicalModel_psl_of_typeA
      r q hv (MulEquiv.refl _)
  rw [hp2, hqe] at hmodel
  haveI : IsSimpleGroup (TauCeti.CFSGIndex.lie ⟨.A r q, hv⟩).Group :=
    CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hmodel
  have hauto :=
    CFSG.LocalAnalysis.RankThreeTheoremC.BlockB.OuterThree.autThreePowInner_typeA_two
      hv hq (MulEquiv.refl _)
  refine fixed_perfect_of_forall_centralizer hauto (fun v hv3 _ => ?_) a ha1 ha3
  exact
    CFSG.HardMathSupport.Curtis.Coordinator.exists_perfect_three_dvd_centralizer_of_model_psl_two
      (by omega) hmodel v hv3

theorem fixed_perfect_gf2Symp :
    ∀ (d : TauCeti.ValidLieTypeIndex) [Finite (TauCeti.CFSGIndex.lie d).Group],
      gf2Symp d.1 → ∀ a : MulAut (TauCeti.CFSGIndex.lie d).Group, a ≠ 1 → a ^ 3 = 1 →
        ∃ P : Subgroup (TauCeti.CFSGIndex.lie d).Group, P ≤ fixSubgroup a ∧ ⁅P, P⁆ = P ∧
          3 ∣ Nat.card P := by
  intro d _ hd a ha1 ha3
  obtain ⟨e, hv⟩ := d
  change gf2Symp e at hd
  obtain ⟨r, q, he, hr5, hq⟩ := gf2Symp_cases hd
  subst e
  obtain ⟨hp2, hqe⟩ := primePower_card_two' hq
  have hmodel :=
    CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even
      r q hv hp2 (by omega) (MulEquiv.refl _)
  rw [hp2, hqe] at hmodel
  haveI : IsSimpleGroup (TauCeti.CFSGIndex.lie ⟨.B r q, hv⟩).Group :=
    CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hmodel
  have hauto :=
    CFSG.LocalAnalysis.RankThreeTheoremC.BlockB.OuterThree.autThreePowInner_typeB_two
      hv hq (MulEquiv.refl _)
  have hcent :=
    CFSG.AGLEmbedding.ToralCensus.centNoncycThreeGroup_of_model_psp
      hmodel (Or.inr ⟨rfl, hr5⟩)
  exact fixed_perfect_of_centNoncycThreeGroup hauto hcent a ha1 ha3

theorem fixed_perfect_gf2OrthPlus :
    ∀ (d : TauCeti.ValidLieTypeIndex) [Finite (TauCeti.CFSGIndex.lie d).Group],
      gf2OrthPlus d.1 → ∀ a : MulAut (TauCeti.CFSGIndex.lie d).Group, a ≠ 1 → a ^ 3 = 1 →
        ∃ P : Subgroup (TauCeti.CFSGIndex.lie d).Group, P ≤ fixSubgroup a ∧ ⁅P, P⁆ = P ∧
          3 ∣ Nat.card P := by
  intro d _ hd a ha1 ha3
  obtain ⟨e, hv⟩ := d
  change gf2OrthPlus e at hd
  obtain ⟨r, q, he, hr5, hq⟩ := gf2OrthPlus_cases hd
  subst e
  obtain ⟨hp2, hqe⟩ := primePower_card_two' hq
  have hmodel :=
    CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even
      r q hv hp2 (MulEquiv.refl _)
  rw [hp2, hqe] at hmodel
  haveI : IsSimpleGroup (TauCeti.CFSGIndex.lie ⟨.D r q, hv⟩).Group :=
    CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hmodel
  have hauto :=
    CFSG.LocalAnalysis.RankThreeTheoremC.BlockB.OuterThree.autThreePowInner_typeD_two
      hv hq hr5 (MulEquiv.refl _)
  refine fixed_perfect_of_forall_centralizer hauto (fun v hv3 _ => ?_) a ha1 ha3
  simpa [CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeCent] using
    CFSG.HardMathSupport.Curtis.NaturalModuleCensus.perfThreeCent_of_model_pomegaPlus
      hr5 hmodel v hv3

theorem fixed_perfect_gf2OrthMinus :
    ∀ (d : TauCeti.ValidLieTypeIndex) [Finite (TauCeti.CFSGIndex.lie d).Group],
      gf2OrthMinus d.1 → ∀ a : MulAut (TauCeti.CFSGIndex.lie d).Group, a ≠ 1 → a ^ 3 = 1 →
        ∃ P : Subgroup (TauCeti.CFSGIndex.lie d).Group, P ≤ fixSubgroup a ∧ ⁅P, P⁆ = P ∧
          3 ∣ Nat.card P := by
  intro d _ hd a ha1 ha3
  obtain ⟨e, hv⟩ := d
  change gf2OrthMinus e at hd
  obtain ⟨r, q, he, hr6, hq⟩ := gf2OrthMinus_cases hd
  subst e
  obtain ⟨hp2, hqe⟩ := primePower_card_two' hq
  have hmodel :=
    CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even
      r q hv hp2 (MulEquiv.refl _)
  rw [hp2, hqe] at hmodel
  haveI : IsSimpleGroup (TauCeti.CFSGIndex.lie ⟨.twistedD r q, hv⟩).Group :=
    CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hmodel
  have hauto :=
    CFSG.LocalAnalysis.RankThreeTheoremC.BlockB.OuterThree.autThreePowInner_typeTwistedD_two
      hv hq (MulEquiv.refl _)
  have hcent :=
    CFSG.AGLEmbedding.ToralCensus.centNoncycThreeGroup_of_model_pomegaMinus
      hmodel (Or.inr ⟨rfl, hr6⟩)
  exact fixed_perfect_of_centNoncycThreeGroup hauto hcent a ha1 ha3

theorem good3On_gf2Lin (hPL : KD264PL 3) : Good3On gf2Lin :=
  good3On_of_fixed_perfect hPL (fun e he => by
    cases e <;> simp only [gf2Lin] at he
    · exact three_ne_characteristic_of_card_two (TauCeti.LieTypeIndex.characteristic_A _ _) he.2
    all_goals exact he.elim)
    (by
      intro d _ hd
      exact fixed_perfect_gf2Lin d hd)

theorem good3On_gf2Symp (hPL : KD264PL 3) : Good3On gf2Symp :=
  good3On_of_fixed_perfect hPL (fun e he => by
    cases e <;> simp only [gf2Symp] at he
    · exact three_ne_characteristic_of_card_two (TauCeti.LieTypeIndex.characteristic_B _ _) he.2
    all_goals exact he.elim)
    (by
      intro d _ hd
      exact fixed_perfect_gf2Symp d hd)

theorem good3On_gf2OrthPlus (hPL : KD264PL 3) : Good3On gf2OrthPlus :=
  good3On_of_fixed_perfect hPL (fun e he => by
    cases e <;> simp only [gf2OrthPlus] at he
    · exact three_ne_characteristic_of_card_two (TauCeti.LieTypeIndex.characteristic_D _ _) he.2
    all_goals exact he.elim)
    (by
      intro d _ hd
      exact fixed_perfect_gf2OrthPlus d hd)

theorem good3On_gf2OrthMinus (hPL : KD264PL 3) : Good3On gf2OrthMinus :=
  good3On_of_fixed_perfect hPL (fun e he => by
    cases e <;> simp only [gf2OrthMinus] at he
    · exact three_ne_characteristic_of_card_two
        (TauCeti.LieTypeIndex.characteristic_twistedD _ _) he.2
    all_goals exact he.elim)
    (by
      intro d _ hd
      exact fixed_perfect_gf2OrthMinus d hd)

end CFSG.LocalAnalysis.GLTheoremA.S262

end
