module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongGammaCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongGammaDefs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL613Main

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem gammaPara_pointwise {A : Type} [Group A] [Finite A] {K K₀ B H N : Subgroup A} {z : A}
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hKr : CFSG.Open.pRank p K ≤ 1) (hK₀K : K₀ ≤ K)
    (hzo : orderOf z = p) (hB : IsElemAbelian p B) (hBc : Nat.card B = p ^ 2) (hzB : z ∈ B)
    (hHK₀ : H ≤ K₀) (hsec : S622IsSimpleSection H N)
    (hBH : B ≤ normalizer (H : Set A)) (hBN : B ≤ normalizer (N : Set A)) (hzH : z ∈ H)
    (hNp : ¬ p ∣ Nat.card N) (hrel : p ∣ N.relIndex H) (Q : TauCeti.LieTypeIndex → Prop)
    (d : TauCeti.ValidLieTypeIndex) (hdc : d.1.characteristic = 2) (hds : d.1 ≠ .suzuki 2)
    (hdQ : Q d.1) (φ : ↥H →* (TauCeti.CFSGIndex.lie d).Group) (hφs : Function.Surjective φ)
    (hφk : φ.ker = N.subgroupOf H)
    (hI2 : ∀ (J : Type) [Group J] [Finite J] (d : TauCeti.ValidLieTypeIndex) (p : ℕ),
      d.1.characteristic = 2 → d.1 ≠ .suzuki 2 → Q d.1 →
      Nonempty (J ≃* (TauCeti.CFSGIndex.lie d).Group) → p.Prime → 5 ≤ p →
      CFSG.Open.pRank p (⊤ : Subgroup J) ≤ 1 → p ∣ Nat.card J →
      ∀ α : MulAut J, α ^ p = 1 → α ∉ inner J →
        ¬ CFSG.HallHigman.IsPSolvable p ↥(fixedSubgroup α)) :
    ∃ y ∈ B, y ∉ zpowers z ∧
      ¬ CFSG.HallHigman.IsPSolvable p ↥(K₀ ⊓ centralizer ({y} : Set A)) := by
  classical
  obtain ⟨hNH, hNn, -, -, -⟩ := id hsec
  haveI : (N.subgroupOf H).Normal := hNn
  have hJ : IsSimpleGroup (↥H ⧸ N.subgroupOf H) :=
    CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L613.isSimpleGroup_quotient_of_section hsec
  have hJnc : ¬ ∀ a b : ↥H ⧸ N.subgroupOf H, a * b = b * a :=
    CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L613.not_comm_quotient_of_section hsec
  have hJp : p ∣ Nat.card (↥H ⧸ N.subgroupOf H) := by
    have h := hrel
    rwa [Subgroup.relIndex, Subgroup.index_eq_card] at h
  have hK₀r : CFSG.Open.pRank p K₀ ≤ 1 :=
    (CFSG.SectionRank.pRank_mono hp.one_lt hK₀K).trans hKr
  have hJr : CFSG.Open.pRank p (⊤ : Subgroup (↥H ⧸ N.subgroupOf H)) ≤ 1 :=
    (FongGamma.pRank_quot_le hp hHK₀ hNH hNp).trans hK₀r
  let e : (↥H ⧸ N.subgroupOf H) ≃* (TauCeti.CFSGIndex.lie d).Group :=
    (QuotientGroup.quotientMulEquivOfEq hφk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφs)
  refine FongGamma.gammaCore hp hBH hBN hB hBc hzB hzH hzo hHK₀ hNH hNp hJ hJnc hJp hK₀r ?_
  intro α hα hαin
  exact hI2 (↥H ⧸ N.subgroupOf H) d p hdc hds hdQ ⟨e⟩ hp hp5 hJr hJp α hα hαin

theorem kFactGammaParaE3_of_inputs (h1 : KFactGammaLeviE3) (h2 : KFactFieldAutLieE3) :
    KFactGammaParaE3 := by
  intro A _ _ K K₀ B z p hK hp hp5 hKr hzo hzK₀ hpar hne hSyl hB hBc hzB hBK hBK₀ hnb hrk
  obtain ⟨H, N, hHK₀, hsec, hBH, hBN, hzH, hNp, hrel, d, hdc, hds, hdE, φ, hφs, hφk⟩ :=
    h1 A K K₀ B z p hK hp hp5 hKr hzo hzK₀ hpar hne hSyl hB hBc hzB hBK hBK₀ hnb hrk
  exact gammaPara_pointwise hp hp5 hKr hpar.1 hzo hB hBc hzB hHK₀ hsec hBH hBN hzH hNp hrel
    IsE3LeviIndex d hdc hds hdE φ hφs hφk (fun J _ _ d p hc hs hq => h2 J d p hc hs hq)

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
