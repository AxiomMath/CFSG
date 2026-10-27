module

public import CFSG.LocalAnalysis.AGLEmbedding.Sp62BlockCent
public import CFSG.LocalAnalysis.AGLEmbedding.Sp62Closed

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def KFactOmegaEightMinusAutElemRank : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (d : TauCeti.ValidLieTypeIndex), IsOmegaMinusTwoIndex 4 d →
    Nonempty (L ≃* CatGroup d) → ∀ E : Subgroup (MulAut L), IsElemAbelian 3 E →
      Nat.card E ≤ 3 ^ 3

theorem Sp62Block.isElemAbelian_range {A B : Type*} [Group A] [Group B] {p : ℕ} (f : A →* B)
    (hA : ∀ a b : A, a * b = b * a) (hp : ∀ a : A, a ^ p = 1) : IsElemAbelian p f.range := by
  refine ⟨⟨⟨?_⟩⟩, ?_⟩
  · rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
    exact Subtype.ext (by simp only [Subgroup.coe_mul, ← map_mul, hA a b])
  · rintro _ ⟨a, rfl⟩
    rw [← map_pow, hp a, map_one]

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R V L : Subgroup G}

theorem D1Sp62Data.false_of_omegaEightMinus (h : D1Sp62Data P M H R V)
    (hβ : 3 ∈ GLBBetaFour G) (h84 : Asc81bEightFour) (hD2 : D1NoXBlock)
    (hKA : KFactOmegaEightMinusAutElemRank) (hL : Sp62BlockShape M H R L)
    {d : TauCeti.ValidLieTypeIndex} (hd : IsOmegaMinusTwoIndex 4 d)
    (e : Nonempty (barM M L ≃* CatGroup d)) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 := h.surv.ph3
  have hC := h.blockCentralizer_le_primeCore h84 hD2 hL
  have : (barM M L).Normal := hL.2.2.1
  obtain ⟨E, hEP, hE, hEc⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank
    (betaFour_all_sylows_rank_ge_four hβ P)
  have hEM : E ≤ M := hEP.trans h3.sylow_le
  have hE3 : IsPGroup 3 E := P.isPGroup'.to_le hEP
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  let ψ : E →* MulAut ↥(barM M L) :=
    ((MulAut.conjNormal (H := barM M L)).comp mk).comp (Subgroup.inclusion hEM)
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have haC : ((a : G)) ∈ blockCentralizer M L := by
      refine (mem_blockCentralizer_iff (M := M) (L := L) ⟨(a : G), hEM a.2⟩).mpr ?_
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h1 := congrArg (fun φ : MulAut ↥(barM M L) => ((φ ⟨y, hy⟩ : ↥(barM M L)) :
        ↥M ⧸ CFSG.pCore 2 ↥M)) ha
      simp only [ψ, MonoidHom.comp_apply, MulAut.conjNormal_apply, MulAut.one_apply] at h1
      replace h1 : mk ⟨a, hEM a.2⟩ * y * (mk ⟨a, hEM a.2⟩)⁻¹ = y := h1
      calc y * mk ⟨a, hEM a.2⟩ = mk ⟨a, hEM a.2⟩ * y * (mk ⟨a, hEM a.2⟩)⁻¹ *
            mk ⟨a, hEM a.2⟩ := by rw [h1]
        _ = mk ⟨a, hEM a.2⟩ * y := by group
    have haN := hC haC
    have hco : Nat.Coprime 3 (Nat.card (GLBPrimeCore 3 H)) := glbPrimeCore_coprime 3 H
    obtain ⟨k, hk⟩ := hE3 a
    have hdvd : orderOf (a : G) ∣ Nat.card (GLBPrimeCore 3 H) :=
      Subgroup.orderOf_dvd_natCard _ haN
    have hdvd' : orderOf (a : G) ∣ 3 ^ k :=
      orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
    have h1 : orderOf (a : G) = 1 :=
      Nat.Coprime.eq_one_of_dvd ((Nat.Coprime.coprime_dvd_right hdvd hco).pow_left k).symm hdvd'
    exact Subtype.ext (orderOf_eq_one_iff.mp h1)
  have hcard : Nat.card ψ.range = 3 ^ 4 := by
    rw [← hEc]; exact (Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv).symm
  have hel : IsElemAbelian 3 ψ.range :=
    Sp62Block.isElemAbelian_range ψ (fun a b => Subtype.ext (hE.1.is_comm.comm a b ▸ rfl))
      (fun a => Subtype.ext (by simpa using hE.2 a a.2))
  have := hKA _ d hd e ψ.range hel
  rw [hcard] at this
  norm_num at this

@[expose] def D1Sp62BlockResidueBig : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1ComponentConfig p P M H R Rbar →
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
        ∀ L : Subgroup G, Sp62BlockShape M H R L →
          blockCentralizer M L ≤ GLBPrimeCore p H →
          (∀ d' : TauCeti.ValidLieTypeIndex, IsOmegaMinusTwoIndex 4 d' →
            IsEmpty (barM M L ≃* CatGroup d')) → False

theorem d1Sp62BlockResidue_of_big (hDat : StmtSp62Data) (h84 : Asc81bEightFour)
    (hD2 : D1NoXBlock) (hKA : KFactOmegaEightMinusAutElemRank)
    (hres : D1Sp62BlockResidueBig) : D1Sp62BlockResidue := by
  intro G _ _ p _ P M H R Rbar hcfg K hK huniq hnc hcent hKD d hp3 hd e L hL
  subst hp3
  obtain ⟨V, hV⟩ := hDat G P M H R Rbar hcfg K hK huniq hcent hKD d hd e
  exact hres G 3 P M H R Rbar hcfg K hK huniq hnc hcent hKD d rfl hd e L hL
    (hV.blockCentralizer_le_primeCore h84 hD2 hL)
    (fun d' hd' => ⟨fun e' => hV.false_of_omegaEightMinus hcfg.loc.beta h84 hD2 hKA hL hd' ⟨e'⟩⟩)

theorem d1Sp62BlockResidue_closed (hSchur : KFactChevTwoSurvivorSchur) (hKF : KFactSp62Local)
    (h84 : Asc81bEightFour) (hD2 : D1NoXBlock) (hKA : KFactOmegaEightMinusAutElemRank)
    (hres : D1Sp62BlockResidueBig) : D1Sp62BlockResidue :=
  d1Sp62BlockResidue_of_big (stmtSp62Data_of (stmtChevTwoSocle_of hSchur) hKF) h84 hD2 hKA hres

end CFSG.AGLEmbedding
