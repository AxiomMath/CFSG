module

public import CFSG.ClassicalInvolution.RouteD.GapsOrthChain
public import CFSG.ClassicalInvolution.RouteD.GapsOrthSpin
public import CFSG.ClassicalInvolution.RouteD.GapsOrthSpinOdd
public import CFSG.ClassicalInvolution.RouteD.GapsPatternD
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import CFSG.ClassicalInvolution.LBalance.Main
public import CFSG.ClassicalInvolution.RouteD.LocalTwinBRecognition
public import CFSG.LocalAnalysis.ComponentClassification.PrimeComplementQuotientComponents
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.Generic (Commutes conjSub fundamentalSubgroups modelUniv IsClassicalMember
  centralizingMembers)
open CFSG.ClassicalInvolution.RouteD

variable {p f : ℕ} [Fact p.Prime]

section Models

variable {m : ℕ}

theorem chainBound_plusDatum (hp2 : p ≠ 2) (hm : 5 ≤ m) (hm3 : 3 ≤ m) (hq : 5 ≤ p ^ f) :
    ChainBound (Subgroup.center (spinGroup (quadPlus m (GaloisField p f))))
      (fundamentalSubgroups .POmegaPlus (plusDatum m (GaloisField p f) hm3)) (2 * m) := by
  obtain ⟨hf, hK⟩ := RouteD.card_galoisField_of_four_le (p := p) (f := f) (by omega)
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    rw [hK]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have hdim : 9 ≤ Module.finrank (GaloisField p f) (Fin m ⊕ Fin m → GaloisField p f) := by
    rw [finrank_plus]
    omega
  have hb := chainBound_model hodd (nondegenerate_polarBilin_quadPlus m (GaloisField p f)) hdim
  rw [finrank_plus] at hb
  exact (centralQuot_plus hp2 (by omega) hm3 hq).chainBound hb

theorem chainBound_plus (hp2 : p ≠ 2) (hm : 5 ≤ m) (hq : 5 ≤ p ^ f) :
    ChainBound (Subgroup.center (modelUniv .POmegaPlus m p f Fact.out).K)
      (fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus m p f Fact.out).D) (2 * m) := by
  have e := RouteD.modelUniv_POmegaPlus_eq (p := p) (f := f) (by omega : 3 ≤ m)
  rw [e]
  exact chainBound_plusDatum hp2 hm (by omega) hq

theorem chainBound_oddDatum (hp2 : p ≠ 2) (hm : 4 ≤ m) (hm3 : 3 ≤ m) (hq : 5 ≤ p ^ f) :
    ChainBound (Subgroup.center (spinGroup (quadOdd m (GaloisField p f))))
      (fundamentalSubgroups .POmegaOdd (oddDatum m (GaloisField p f))) (2 * m + 1) := by
  obtain ⟨hf, hK⟩ := RouteD.card_galoisField_of_four_le (p := p) (f := f) (by omega)
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    rw [hK]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have h2 : (2 : GaloisField p f) ≠ 0 := ModelFacts.two_ne_zero_galoisField f hp2
  have hdim : 9 ≤ Module.finrank (GaloisField p f) (Fin m ⊕ Fin m ⊕ Unit → GaloisField p f) := by
    rw [finrank_odd]
    omega
  have hb := chainBound_model hodd (nondegenerate_polarBilin_quadOdd m (GaloisField p f) h2) hdim
  rw [finrank_odd] at hb
  exact (centralQuot_odd hp2 hm3 hq).chainBound hb

theorem chainBound_odd (hp2 : p ≠ 2) (hm : 4 ≤ m) (hq : 5 ≤ p ^ f) :
    ChainBound (Subgroup.center (modelUniv .POmegaOdd m p f Fact.out).K)
      (fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd m p f Fact.out).D) (2 * m + 1) :=
  chainBound_oddDatum hp2 hm (by omega) hq

end Models

section Witness

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {tY : StatedLieTag} {nY : ℕ}
  {N : Subgroup G} {x : G}

theorem chain_config (cx : TCtx p f tY nY Ω N x) {d : ℕ}
    (hF : ChainBound (Subgroup.center (modelUniv tY nY p f Fact.out).K)
      (fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D) d)
    {r : ℕ} (hr : 4 ≤ r) {c : ℕ → Subgroup G} {w : ℕ → G}
    (hc : ∀ a < r, c a ∈ centralizingMembers Ω {x})
    (hw : ∀ a < r, IsClassicalMember p f (c a) (w a))
    (hadj : ∀ a, a + 1 < r → c a ≠ c (a + 1) ∧ ¬ Commutes (c a) (c (a + 1)) ∧
      Commute (w a) (w (a + 1)) ∧ conjSub (w (a + 1)) (c a) = c a)
    (hcomm : ∀ a b, a + 1 < b → b < r → Commutes (c a) (c b))
    {A B : Subgroup G} {wA wB : G} (hA : A ∈ centralizingMembers Ω {x})
    (hB : B ∈ centralizingMembers Ω {x}) (hwA : IsClassicalMember p f A wA)
    (hwB : IsClassicalMember p f B wB) (hAB : A ≠ B) (hnAB : ¬ Commutes A B)
    (hcAB : Commute wA wB) (hnA : conjSub wB A = A) (hAc : ∀ a < r, Commutes A (c a))
    (hBc : ∀ a < r, Commutes B (c a)) : 2 * (r + 1) + 6 ≤ d := by
  classical
  have hcL : ∀ a < r, IsLayerMember cx (c a) := by
    intro a ha
    by_cases h1 : a + 1 < r
    · exact IsLayerMember.of_not_commutes cx (hc a ha) (hc (a + 1) h1) (hadj a h1).1
        (hadj a h1).2.1
    · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
      exact IsLayerMember.of_not_commutes cx (hc (a' + 1) ha) (hc a' (by omega))
        (hadj a' (by omega)).1.symm (fun h => (hadj a' (by omega)).2.1 (commutes_symm h))
  have hAL : IsLayerMember cx A := IsLayerMember.of_not_commutes cx hA hB hAB hnAB
  have hBL : IsLayerMember cx B :=
    IsLayerMember.of_not_commutes cx hB hA hAB.symm (fun h => hnAB (commutes_symm h))
  have hex : ∀ a : ℕ, ∃ R : Subgroup (modelUniv tY nY p f Fact.out).K, a < r →
      R ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D ∧
        locImg Ω x (c a) = R.map cx.d.ψ := by
    intro a
    by_cases h : a < r
    · obtain ⟨R, hR, hlR⟩ := (hcL a h).exists_fund
      exact ⟨R, fun _ => ⟨hR, hlR⟩⟩
    · exact ⟨⊥, fun h' => absurd h' h⟩
  choose R hR using hex
  obtain ⟨RA, hRA, hAR⟩ := hAL.exists_fund
  obtain ⟨RB, hRB, hBR⟩ := hBL.exists_fund
  refine hF r hr R ⟨fun a ha => (hR a ha).1, fun a ha => ?_, fun a b hab hb => ?_⟩ RA hRA RB hRB
    (modelAdj_of_adj cx hA hB hRA hRB hAR hBR hwA hwB hAB hnAB hcAB hnA) (fun a ha => ?_)
    (fun a ha => ?_)
  · exact modelAdj_of_adj cx (hc a (by omega)) (hc (a + 1) ha) (hR a (by omega)).1
      (hR (a + 1) ha).1 (hR a (by omega)).2 (hR (a + 1) ha).2 (hw a (by omega)) (hw (a + 1) ha)
      (hadj a ha).1 (hadj a ha).2.1 (hadj a ha).2.2.1 (hadj a ha).2.2.2
  · exact (cx.commutes_iff_fund (hc a (by omega)) (hc b hb) (hR a (by omega)).1
      (hR a (by omega)).2 (hR b hb).2).mp (hcomm a b hab hb)
  · exact (cx.commutes_iff_fund hA (hc a ha) hRA hAR (hR a ha).2).mp (hAc a ha)
  · exact (cx.commutes_iff_fund hB (hc a ha) hRB hBR (hR a ha).2).mp (hBc a ha)

end Witness

end CFSG.ClassicalInvolution.RouteD.Gaps
