module

public import CFSG.LocalAnalysis.RankThreeUC.TheoremDResidual7
public import CFSG.LocalAnalysis.UniquenessCase.UC6Dict
import CFSG.LocalAnalysis.RankThreeUC.AGL81S16Setup
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankChevUni
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankChevToral
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankChevLinEasy

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.RankFour

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

instance finiteGroupTwistedA3 {q : TauCeti.PrimePower}
    {hv : (TauCeti.LieTypeIndex.twistedA 3 q).Valid} :
    Finite (TauCeti.ValidLieTypeIndex.Group
      ⟨TauCeti.LieTypeIndex.twistedA 3 q, hv⟩) := by
  obtain ⟨-, K, hKfield, hKfinite, -, ⟨ψ⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q hv (MulEquiv.refl _)
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  exact Finite.of_equiv _ ψ.symm.toEquiv

theorem pRank_unitaryFour_le {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    {q : TauCeti.PrimePower} (hq : q.p = 2)
    (hv : (TauCeti.LieTypeIndex.twistedA 3 q).Valid) :
    CFSG.Open.pRank r (⊤ : Subgroup
      (TauCeti.ValidLieTypeIndex.Group ⟨TauCeti.LieTypeIndex.twistedA 3 q, hv⟩)) ≤ 3 := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hm : CFSG.Open.StatedClassicalModel
      (TauCeti.ValidLieTypeIndex.Group ⟨TauCeti.LieTypeIndex.twistedA 3 q, hv⟩)
      .PSU 4 q.p q.exponent :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q hv (MulEquiv.refl _)
  obtain ⟨-, K, hKfield, hKfinite, hKcard, ⟨ψ⟩⟩ := hm
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  have hKcard2 : Nat.card K = 2 ^ (2 * q.exponent) := by
    rw [hKcard, hq, ← pow_mul]
    congr 1
    omega
  have hrK : (r : K) ≠ 0 :=
    CFSG.LocalAnalysis.RankThreeUC.S15.RankChevLinEasyProof.cast_ne_zero_of_card_two_pow
      hr hr2 hKcard2
  let S : Subgroup ↥(CFSG.Open.StatedSU 4 (q.p ^ q.exponent) K) :=
    (CFSG.Open.StatedScalars (Fin 4) K).subgroupOf
      (CFSG.Open.StatedSU 4 (q.p ^ q.exponent) K)
  have hSdvd : Nat.card S ∣ 4 := by
    have h := (CFSG.LocalAnalysis.RankThreeUC.S15.RankChevUniProof.card_scalars_statedSU_dvd
      (F := K) (p := q.p) (f := q.exponent) (m := 4) q.prime_p hKcard (by norm_num)).1
    simpa [S] using h
  have hSnot : ¬ r ∣ Nat.card S := by
    intro hdiv
    have h4 : r ∣ 4 := dvd_trans hdiv hSdvd
    have h4' : r ∣ 2 ^ 2 := by
      rwa [show (2 : ℕ) ^ 2 = 4 by norm_num]
    have h2 : r ∣ 2 := hr.dvd_of_dvd_pow h4'
    rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h1 | h2'
    · exact hr.ne_one h1
    · exact hr2 h2'
  calc
    CFSG.Open.pRank r (⊤ : Subgroup
        (TauCeti.ValidLieTypeIndex.Group ⟨TauCeti.LieTypeIndex.twistedA 3 q, hv⟩))
        = CFSG.Open.pRank r (⊤ : Subgroup (CFSG.Open.StatedProj
            (CFSG.Open.StatedSU 4 (q.p ^ q.exponent) K))) :=
          CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt ψ
    _ = CFSG.Open.pRank r (⊤ : Subgroup
          (↥(CFSG.Open.StatedSU 4 (q.p ^ q.exponent) K) ⧸ S)) := rfl
    _ = CFSG.Open.pRank r (⊤ : Subgroup
          ↥(CFSG.Open.StatedSU 4 (q.p ^ q.exponent) K)) :=
          CFSG.SectionRank.pRank_quotient_eq S hSnot
    _ = CFSG.Open.pRank r (CFSG.Open.StatedSU 4 (q.p ^ q.exponent) K) :=
          (CFSG.SectionRank.pRank_eq_pRank_top_subgroup _).symm
    _ ≤ 3 := by
          have hle := CFSG.LocalAnalysis.RankThreeUC.S15.pRank_statedSU_le
            (F := K) (q := q.p ^ q.exponent) (r := r) (m := 4) (by norm_num) hrK
          simpa using hle

theorem pRank_le_three_of_u4Shape {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {M : Subgroup G} (h : CFSG.LocalAnalysis.RankThreeUC.U4Shape p M) :
    CFSG.Open.pRank p M ≤ 3 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨d, ⟨q, hq, hd, -⟩, ⟨φ⟩⟩ := h
  have hv : (TauCeti.LieTypeIndex.twistedA 3 q).Valid := hd ▸ d.2
  have hd' : d = (⟨TauCeti.LieTypeIndex.twistedA 3 q, hv⟩ : TauCeti.ValidLieTypeIndex) :=
    Subtype.ext hd
  subst hd'
  let H : Subgroup G := CFSG.RankThree.PartOne.pElementSubgroup p M
  have hHcard : ¬ p ∣ Nat.card (CFSG.pCore 2 ↥H) := by
    have hP : IsPGroup 2 (CFSG.pCore 2 ↥H) := CFSG.pCore_isPGroup
    obtain ⟨n, hn⟩ := hP.exists_card_eq
    rw [hn]
    intro hdiv
    have h2 : p ∣ 2 := hp.dvd_of_dvd_pow hdiv
    rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h1 | h2'
    · exact hp.ne_one h1
    · exact hp2 h2'
  calc
    CFSG.Open.pRank p M ≤ CFSG.Open.pRank p H :=
      CFSG.LocalAnalysis.RankThreeUC.pRank_le_pElementSubgroup hp M
    _ = CFSG.Open.pRank p (⊤ : Subgroup ↥H) :=
      CFSG.SectionRank.pRank_eq_pRank_top_subgroup H
    _ = CFSG.Open.pRank p (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) :=
      (CFSG.SectionRank.pRank_quotient_eq (CFSG.pCore 2 ↥H) hHcard).symm
    _ = CFSG.Open.pRank p (⊤ : Subgroup (TauCeti.CFSGIndex.lie
          (⟨TauCeti.LieTypeIndex.twistedA 3 q, hv⟩ : TauCeti.ValidLieTypeIndex)).Group) :=
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt φ
    _ = CFSG.Open.pRank p (⊤ : Subgroup
          (TauCeti.ValidLieTypeIndex.Group ⟨TauCeti.LieTypeIndex.twistedA 3 q, hv⟩)) := rfl
    _ ≤ 3 := pRank_unitaryFour_le hp hp2 hq hv

theorem not_u4Shape_of_four_le_pRank {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {M : Subgroup G} (h4 : 4 ≤ CFSG.Open.pRank p M) :
    ¬ CFSG.LocalAnalysis.RankThreeUC.U4Shape p M := by
  intro h
  have h3 := pRank_le_three_of_u4Shape hp hp2 h
  omega

theorem not_u4Shape_of_mem_uniqueFourSigma {p : ℕ} {M : Subgroup G}
    (hp : p ∈ CFSG.Open.uniqueFourSigma M) :
    ¬ CFSG.LocalAnalysis.RankThreeUC.U4Shape p M := by
  have hp' : p ∈ CFSG.Open.uniqueFourBeta G := hp.1
  exact not_u4Shape_of_four_le_pRank hp'.1 hp'.2.1
    (CFSG.LocalAnalysis.UniquenessCase.UC6.four_le_pRank_of_sigma hp)

end CFSG.LocalAnalysis.AGL81TheoremCD.RankFour
