module

public import CFSG.RankThree.PartOne.KLC.D4OutCentral
public import CFSG.RankThree.PartOne.S11d.PlaneCases
public import CFSG.RankThree.PartOne.MB3.OddOutLinear
public import CFSG.Adapters.TauCetiExceptional.EvenBridgeG2
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFInputs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrModel
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.LocalAnalysis.RankThreeUC.GN15SolvAlt
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3Q8Psl2
public import CFSG.RankThree.PartOne.N143.Inspect613Even

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.RankThree.PartOne.OutStructure CFSG.Assembly.LowTwoRank CFSG.Open
open CFSG.HardMathSupport.Cooperstein.Coordinator CFSG.AGLEmbedding
open scoped commutatorElement

namespace FFO

@[expose] def FamPSL (Y : Type) [Group Y] (r : ℕ) : Prop :=
  ∃ n f : ℕ, StatedClassicalModel Y .PSL n 2 f ∧ r ∣ Nat.gcd n (2 ^ f - 1)

@[expose] def FamPSU (Y : Type) [Group Y] (r : ℕ) : Prop :=
  ∃ n f : ℕ, StatedClassicalModel Y .PSU n 2 f ∧ r ∣ Nat.gcd n (2 ^ f + 1)

@[expose] def FamD4 (Y : Type) [Group Y] (r : ℕ) : Prop :=
  (∃ f : ℕ, StatedClassicalModel Y .POmegaPlus 4 2 f) ∧ r = 3

theorem cases_of_classical {Y : Type} [Group Y] {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    {t : StatedLieTag} {n f : ℕ} (ht : CFSG.AGLEmbedding.ParabAutIrr.ClassicalTag t)
    (hm : StatedClassicalModel Y t n 2 f) :
    OutPNice r Y ∨ OutPCentral r Y ∨ FamPSL Y r ∨ FamPSU Y r ∨ FamD4 Y r := by
  rcases ht with rfl | rfl | rfl | rfl | rfl
  ·
    by_cases hn : n = 2
    · subst hn
      exact Or.inl (outPNice_PSL_two hr hm)
    · obtain ⟨⟨-, -, hn2, -⟩, -⟩ := id hm
      by_cases hd : r ∣ Nat.gcd n (2 ^ f - 1)
      · exact Or.inr (Or.inr (Or.inl ⟨n, f, hm, hd⟩))
      · exact Or.inl (outPNice_PSL_ge_three hr hr2 (by omega) hm hd)
  ·
    by_cases hd : r ∣ Nat.gcd n (2 ^ f + 1)
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n, f, hm, hd⟩)))
    · exact Or.inl (outPNice_PSU hr hm hd)
  ·
    by_cases hn : n = 2
    · subst hn
      exact Or.inl (outPNice_PSp_two hr hm)
    · obtain ⟨⟨-, -, hn2, -⟩, -⟩ := id hm
      exact Or.inl (outPNice_PSp_ge_three hr (by omega) hm)
  ·
    obtain ⟨⟨-, -, hn4⟩, -⟩ := id hm
    by_cases hn : n = 4
    · subst hn
      by_cases h3 : r = 3
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨f, hm⟩, h3⟩)))
      · have hr5 : 5 ≤ r := by
          have h2 := hr.two_le
          have h4 : r ≠ 4 := by
            rintro rfl
            norm_num at hr
          omega
        exact Or.inr (Or.inl (CFSG.RankThree.PartOne.KLC.d4OutCentral _ r f hr hr5 hm))
    · exact Or.inl (outPNice_POmegaPlus_ge_five hr hr2 (by omega) hm)
  ·
    obtain ⟨⟨-, -, hn4⟩, -⟩ := id hm
    exact Or.inl (outPNice_POmegaMinus hr hr2 hn4 hm)

section G2

open TauCeti

theorem outPNice_of_G2_index
    {r : ℕ} (hr : r.Prime) (q : PrimePower) (hv : (LieTypeIndex.G2 q).Valid) (hp2 : q.p = 2)
    {Y : Type} [Group Y] (e : Y ≃* (CFSGIndex.lie ⟨.G2 q, hv⟩).Group) : OutPNice r Y := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hq3 : 3 ≤ q.card :=
    (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', PrimePower.card_def]
  obtain ⟨e0⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hv hp2
    (GaloisField q.p q.exponent) hK
  have hce : CFSG.Blueprint.ChevalleyExceptionalModel (CFSGIndex.lie ⟨.G2 q, hv⟩).Group .G2
      q.p q.exponent := by
    refine ⟨⟨q.prime_p, q.exponent_pos, rfl, ?_⟩, GaloisField q.p q.exponent, inferInstance,
      inferInstance, ?_, ⟨e0.symm⟩⟩
    · rw [← PrimePower.card_def]
      exact hq3
    · rw [hK, PrimePower.card_def]
  rw [hp2] at hce
  exact OutPNice.of_mulEquiv e (outPNice_G2 hr hce)

end G2

section Small

open CFSG.GorensteinWalter

theorem card_outer_psl_two_seven {X : Type} [Group X]
    (h : StatedClassicalModel X .PSL 2 7 1) : Nat.card (Outer X) = 2 := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hK7 : Nat.card K = 7 := by rw [hK]; norm_num
  have hodd : IsOddPrimePower (Nat.card K) :=
    ⟨7, 1, by norm_num, by decide, le_rfl, by rw [hK7]; norm_num⟩
  have hcard : 3 < Nat.card K := by rw [hK7]; norm_num
  have e' : X ≃* PSL2 K := e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  have hbij := CFSG.Quasithin.A312U3.pgl2InnerAutPSL2_bijective hK7 hodd hcard
  let φ : PGL2 K ≃* MulAut (PSL2 K) :=
    MulEquiv.ofBijective (pgl2InnerAutPSL2 K hodd hcard) hbij
  have hInn : CFSG.ComponentClassification.OuterAutomorphisms.inner (PSL2 K) =
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range.map
        φ.toMonoidHom := by
    ext δ
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨Matrix.ProjectiveSpecialLinearGroup.toPGL y, ⟨y, rfl⟩, ?_⟩
      exact pgl2InnerAutPSL2_toPGL K hodd hcard y
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ⟨y, (pgl2InnerAutPSL2_toPGL K hodd hcard y).symm⟩
  have h2 : (Subgroup.map φ.toMonoidHom
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range).index =
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range.index :=
    Subgroup.index_map_equiv _ φ
  have hidx : (CFSG.ComponentClassification.OuterAutomorphisms.inner (PSL2 K)).index = 2 := by
    rw [hInn, h2, pgl2_psl2Range_index_eq_two K hodd]
  have hc2 : Nat.card (Outer (PSL2 K)) = 2 := hidx
  rw [← hc2]
  exact Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e').toEquiv

theorem outPNice_of_psl_two_seven {X : Type} [Group X] [Finite X] {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (h : StatedClassicalModel X .PSL 2 7 1) : OutPNice r X := by
  refine CFSG.RankThree.PartOne.PlaneCases.outPNice_of_not_dvd_outer hr fun hd => ?_
  rw [card_outer_psl_two_seven h] at hd
  exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 hd)

theorem outPNice_of_psu_three_three {X : Type} [Group X] {r : ℕ} (hr : r.Prime)
    (h : StatedClassicalModel X .PSU 3 3 1) : OutPNice r X := by
  refine outPNice_PSU_odd hr h fun hd => ?_
  have : Nat.gcd 3 (3 ^ 1 + 1) = 1 := by norm_num
  rw [this] at hd
  exact hr.not_dvd_one hd

end Small

section Assembly

open TauCeti

theorem outer_cases
    {L : Type} [Group L] [Finite L] [Group.IsPerfect L] {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (h : FFConclusion (L ⧸ Subgroup.center L)) :
    IsMulCommutative (Outer L) ∨ OutPNice r (L ⧸ Subgroup.center L) ∨
      OutPCentral r (L ⧸ Subgroup.center L) ∨ FamPSL (L ⧸ Subgroup.center L) r ∨
      FamPSU (L ⧸ Subgroup.center L) r ∨ FamD4 (L ⧸ Subgroup.center L) r := by
  rcases h with hcl | ⟨m, hm, ⟨e⟩⟩
  · rcases hcl with ⟨d, hd, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨d, hd, ⟨e⟩⟩
    · rcases CFSG.AGLEmbedding.ParabAutIrr.classical_model_or_g2 d hd e with
        ⟨t, n, f, ht, hm⟩ | ⟨q, hv, hq2, hdq⟩
      · rcases cases_of_classical hr hr2 ht hm with h | h | h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
      · subst hdq
        exact Or.inr (Or.inl (outPNice_of_G2_index hr q hv hq2 e))
    · exact Or.inl (isMulCommutative_outer_of_alternating (by omega) e)
    · obtain ⟨d1, hv⟩ := d
      rcases hd with ⟨q, hq, hd1⟩ | ⟨q, hq, hd1⟩
      · simp only at hd1
        subst hd1
        have h := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
        have hq' : q.p ^ q.exponent = 7 := by rw [← PrimePower.card_def]; exact hq
        obtain ⟨hp7, he1⟩ := (Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 7)).mp hq'
        rw [hp7, he1] at h
        exact Or.inr (Or.inl (outPNice_of_psl_two_seven hr hr2 h))
      · simp only at hd1
        subst hd1
        have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
        have hq' : q.p ^ q.exponent = 3 := by rw [← PrimePower.card_def]; exact hq
        obtain ⟨hp3, he1⟩ := (Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 3)).mp hq'
        rw [hp3, he1] at h
        exact Or.inr (Or.inl (outPNice_of_psu_three_three hr h))
  · exact Or.inl (isMulCommutative_outer_of_alternating hm e)

end Assembly

end FFO

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15
