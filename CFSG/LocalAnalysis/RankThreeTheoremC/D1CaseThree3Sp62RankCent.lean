module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Sp62Rank
import CFSG.LocalAnalysis.AGLEmbedding.Sp62BlockCent

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G]

theorem _root_.CFSG.AGLEmbedding.D1Sp62Data.sylow_eq_of_omegaEight {P : Sylow 3 G}
    {M H R V L : Subgroup G} (h : D1Sp62Data P M H R V) (hKA : KFactOmegaEightMinusAut)
    (hC : blockCentralizer M L ≤ GLBPrimeCore 3 H) (hLn : (barM M L).Normal)
    {d : TauCeti.ValidLieTypeIndex} (hd : IsOmegaMinusTwoIndex 4 d)
    (e : Nonempty (barM M L ≃* CatGroup d)) : R = (P : Subgroup G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : (barM M L).Normal := hLn
  have h3 := h.surv.ph3
  have hPM : (P : Subgroup G) ≤ M := h3.sylow_le
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  let ψ : ↥(P : Subgroup G) →* MulAut ↥(barM M L) :=
    ((MulAut.conjNormal (H := barM M L)).comp mk).comp (Subgroup.inclusion hPM)
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have haC : ((a : G)) ∈ blockCentralizer M L := by
      refine (mem_blockCentralizer_iff (M := M) (L := L) ⟨(a : G), hPM a.2⟩).mpr ?_
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h1 := congrArg (fun φ : MulAut ↥(barM M L) => ((φ ⟨y, hy⟩ : ↥(barM M L)) :
        ↥M ⧸ CFSG.pCore 2 ↥M)) ha
      simp only [ψ, MulAut.one_apply] at h1
      replace h1 : mk ⟨a, hPM a.2⟩ * y * (mk ⟨a, hPM a.2⟩)⁻¹ = y := h1
      calc y * mk ⟨a, hPM a.2⟩ = mk ⟨a, hPM a.2⟩ * y * (mk ⟨a, hPM a.2⟩)⁻¹ *
            mk ⟨a, hPM a.2⟩ := by rw [h1]
        _ = mk ⟨a, hPM a.2⟩ * y := by group
    have haN := hC haC
    have hco : Nat.Coprime 3 (Nat.card (GLBPrimeCore 3 H)) := glbPrimeCore_coprime 3 H
    obtain ⟨k, hk⟩ := P.isPGroup' a
    have hdvd : orderOf (a : G) ∣ Nat.card (GLBPrimeCore 3 H) :=
      Subgroup.orderOf_dvd_natCard _ haN
    have hdvd' : orderOf (a : G) ∣ 3 ^ k :=
      orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
    have h1 : orderOf (a : G) = 1 :=
      Nat.Coprime.eq_one_of_dvd ((Nat.Coprime.coprime_dvd_right hdvd hco).pow_left k).symm hdvd'
    exact Subtype.ext (orderOf_eq_one_iff.mp h1)
  have hpg : IsPGroup 3 ψ.range :=
    P.isPGroup'.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
  have hcard : Nat.card (P : Subgroup G) = Nat.card ψ.range :=
    Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv
  have hdvd : Nat.card ψ.range ∣ 3 ^ 4 := hKA _ d hd e ψ.range hpg
  have hle : Nat.card (P : Subgroup G) ≤ Nat.card R := by
    rw [hcard, h.card_R]
    exact Nat.le_of_dvd (by positivity) hdvd
  exact Subgroup.eq_of_le_of_card_ge h3.le_P hle

@[expose] def D1Sp62Omega8SylowResidue3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1ComponentConfig3 p P M H R Rbar →
    ∀ K : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf K ⊤ →
      (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K) →
      ¬ IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
        Subgroup (H ⧸ primeComplementCore (G := H) p)) →
      (∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
          Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)),
        orderOf c = p → c ∈ (Subgroup.center K).map K.subtype) →
      ¬ HasKlingenData p Rbar
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) →
      ∀ d : TauCeti.ValidLieTypeIndex, p = 3 → IsSpSixTwoIndex d →
        Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) →
        ∀ L : Subgroup G, Sp62Omega8Shape M H R L → blockCentralizer M L ≤ GLBPrimeCore p H →
          Nat.card R = 3 ^ 4 → R = (P : Subgroup G) → False

theorem d1Sp62Omega8Residue3_of_sylow (hDat : StmtSp62Data3 G) (h84 : Asc81bEightFour)
    (hD2 : D1NoXBlock) (hKA : KFactOmegaEightMinusAut) (h : D1Sp62Omega8SylowResidue3 G) :
    D1Sp62Omega8Residue3 G := by
  intro p _ P M H R Rbar hcfg K hK huniq hnc hcent hKD d hp3 hd e L hL
  subst hp3
  obtain ⟨V, hV⟩ := hDat P M H R Rbar hcfg K hK huniq hcent hKD d hd e
  obtain ⟨hL', d', hd', e'⟩ := hL
  have hC := hV.blockCentralizer_le_primeCore h84 hD2 hL'
  exact h 3 P M H R Rbar hcfg K hK huniq hnc hcent hKD d rfl hd e L ⟨hL', d', hd', e'⟩ hC
    hV.card_R (hV.sylow_eq_of_omegaEight hKA hC hL'.2.2.1 hd' e')

theorem d1Sp62BlockResidue3_of_sylow (hSchur : KFactChevTwoSurvivorSchur) (hKF : KFactSp62Local)
    (h84 : Asc81bEightFour) (hD2 : D1NoXBlock) (hKA : KFactOmegaEightMinusAut)
    (hU : KFactU62ThreeRank) (hΩ : KFactOmegaMinusThreeRank) (h : D1Sp62Omega8SylowResidue3 G) :
    D1Sp62BlockResidue3 G :=
  d1Sp62BlockResidue3_of_omega8 hU hΩ (d1Sp62Omega8Residue3_of_sylow
    (stmtSp62Data3_of (stmtChevTwoSocle3_of hSchur) hKF) h84 hD2 hKA h)

end CFSG.LocalAnalysis.RankThreeTheoremC
