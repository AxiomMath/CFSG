module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeBlock
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineNormalNX
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenSevenCfgOf
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ASevenBlockAutProof
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneProof
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeCfg

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Quasithin CFSG.RankThreeCoreUniqueness.Helpers
open Subgroup

@[expose] def IsCaseIThreeSimple (Y : Type*) [Group Y] : Prop :=
  ∃ d : TauCeti.ValidLieTypeIndex,
    ((∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 3 ∧ d.1 = .A 1 q) ∨
      (∃ q : TauCeti.PrimePower, q.p = 3 ∧ q.exponent = 1 ∧ d.1 = .twistedA 2 q)) ∧
    Nonempty (Y ≃* (TauCeti.CFSGIndex.lie d).Group)

@[expose] def IsCaseIThreeProd (Y : Type*) [Group Y] : Prop :=
  ∃ d : TauCeti.ValidLieTypeIndex,
    (∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 3 ∧ d.1 = .A 1 q) ∧
    Nonempty (Y ≃* (TauCeti.CFSGIndex.lie d).Group × (TauCeti.CFSGIndex.lie d).Group)

@[expose] def KFactCaseIThreeShape : Prop :=
  ∀ (B : Type) [Group B] [Finite B] (Kb : Subgroup B) [Kb.Normal] (T : Subgroup B),
    IsPGroup 3 T → (∃ S : Sylow 3 Kb, (S : Subgroup Kb).map Kb.subtype ≤ T) →
    (IsCaseIThreeSimple Kb → TenNineOneThree.ShapeSimple
        (T ⧸ ((MulAut.conjNormal (H := Kb)).comp T.subtype).ker)) ∧
      (IsCaseIThreeProd Kb → TenNineOneThree.ShapeProd
        (T ⧸ ((MulAut.conjNormal (H := Kb)).comp T.subtype).ker))

variable (G : Type) [Group G] [Finite G]

@[expose] def AGL81NineOneThreeCfg : Prop :=
  Setting G → ∀ (P : Sylow 3 G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)), AGL81CfgData 3 P M H Q K →
    ∀ R : Subgroup G, IsSylowIn 3 R (H ⊓ M) → IsSylowIn 3 R H

@[expose] def AGL81TenNineOneThreeNormCfg : Prop :=
  Setting G → ∀ (P : Sylow 3 G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)), AGL81CfgData 3 P M H Q K →
    ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
    Nonempty (↥(barM M L) ≃* alternatingGroup (Fin 7)) → H ⊓ M ≤ normalizer (L : Set G)

@[expose] def AGL81TenNineOneThreeListCfg : Prop :=
  Setting G → ∀ (P : Sylow 3 G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)), AGL81CfgData 3 P M H Q K →
    ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
    Nonempty (↥(barM M L) ≃* alternatingGroup (Fin 7)) → H ⊓ M ≤ normalizer (L : Set G) →
    K.Normal ∧ (IsCaseIThreeSimple K ∨
      (IsCaseIThreeProd K ∧ ¬ 3 ∣ Nat.card (d1PlusCore 3 H K)))

variable {G}

namespace TenNineOneThree

theorem nine_dvd_card_inf {H L Q' : Subgroup G} (hQ : IsSylowIn 3 Q' H)
    (hQL : Q' ≤ normalizer (L : Set G)) (h9 : 9 ∣ Nat.card ↥(H ⊓ L)) :
    9 ∣ Nat.card ↥(Q' ⊓ L) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set K₀ := H ⊓ normalizer (L : Set G)
  have hQK : Q' ≤ K₀ := le_inf hQ.le hQL
  have hK₀H : K₀ ≤ H := inf_le_left
  have hK : IsSylowIn 3 Q' K₀ := by
    refine ⟨hQK, hQ.isPGroup, fun hd => hQ.not_dvd_relIndex ?_⟩
    rw [← Subgroup.relIndex_mul_relIndex Q' K₀ H hQK hK₀H]
    exact Dvd.dvd.mul_right hd _
  have hNK : H ⊓ L ≤ K₀ := inf_le_inf_left H Subgroup.le_normalizer
  have hnorm : ((H ⊓ L).subgroupOf K₀).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hgH : (g : G) ∈ H := g.2.1
    have hgL : (g : G) ∈ normalizer (L : Set G) := g.2.2
    refine ⟨?_, ?_⟩
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact H.mul_mem (H.mul_mem hgH hn.1) (H.inv_mem hgH)
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact (mem_normalizer_iff.mp hgL _).mp hn.2
  have hS := hK.inf_normal hNK hnorm
  have heq : Q' ⊓ (H ⊓ L) = Q' ⊓ L := by
    rw [← inf_assoc, inf_eq_left.mpr hQ.le]
  rw [heq] at hS
  have hcard := Subgroup.relIndex_mul_card (Q' ⊓ L) (H ⊓ L)
  rw [inf_eq_left.mpr hS.le] at hcard
  have hcop : Nat.Coprime 9 ((Q' ⊓ L).relIndex (H ⊓ L)) := by
    rw [show (9 : ℕ) = 3 ^ 2 by norm_num]
    exact Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      hS.not_dvd_relIndex)
  rw [← hcard] at h9
  exact hcop.dvd_of_dvd_mul_left h9

theorem nine_dvd_card_of_barM {M H L : Subgroup G} (hHL : H ⊓ L ≤ M)
    {E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hE : E ≤ barM M (H ⊓ L)) (hE9 : Nat.card E = 9) :
    9 ∣ Nat.card ↥(H ⊓ L) := by
  have h1 : Nat.card E ∣ Nat.card (barM M (H ⊓ L)) := Subgroup.card_dvd_of_le hE
  have h2 : Nat.card (barM M (H ⊓ L)) ∣ Nat.card ((H ⊓ L).subgroupOf M) :=
    Subgroup.card_map_dvd _ _
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHL).toEquiv] at h2
  exact hE9 ▸ h1.trans h2

theorem isElemAbelian_subgroupOf {A Q' : Subgroup G} (hA : IsElemAbelian 3 A) :
    IsElemAbelian 3 (A.subgroupOf Q') := by
  have := hA.1
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · have h := congrArg Subtype.val
      (mul_comm' (⟨((a : Q') : G), a.2⟩ : A) ⟨((b : Q') : G), b.2⟩)
    exact Subtype.ext (Subtype.ext (by simpa using h))
  · apply Subtype.ext
    simpa using hA.2 _ (Subgroup.mem_subgroupOf.mp hx)

end TenNineOneThree

theorem agl81TenNineOneThreeCfg_core (hNX3 : D1NoXBlock3 G) (h98 : AGL81NineEightFour G)
    (hRk3 : AGL81NineThreeRankCfg G)
    (h91s : Setting G → ∀ (P : Sylow 3 G) (M H Q : Subgroup G)
      (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)), AGL81CfgData 3 P M H Q K →
      ∀ R : Subgroup G, IsSylowIn 3 R (H ⊓ M) → Q ≤ R → IsSylowIn 3 R H)
    (hNorm : AGL81TenNineOneThreeNormCfg G) (hList : AGL81TenNineOneThreeListCfg G)
    (hKF : KFactCaseIThreeShape) (hE : Asc81bASevenPLRankNX) (h86 : Asc81bEightSix)
    (h93 : Asc81bNineThree)
    (hord : ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.G2 q).Valid), q.p = 2 →
      Nat.card (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group = CFSG.Open.ordG2 q.card) :
    AGL81TenNineOneThreeCfg G := by
  intro hS P M H Q K hd L hL
  refine ⟨fun e => ?_⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hNX := noXBlockFor_of_setting hNX3 hS
  have hT := hd.toTwoLocalPhaseThree' hS h98
  have hK : Open.IsKGroup ↥M := (hT.toTwoLocalPair.isKGroup_of_isKProper hS.kProper).1
  have hA : Asc81bHyp M (pCoreOf 2 H) := hT.asc81bHyp
  have hNH : normalizer (pCoreOf 2 H : Set G) = H := hT.toTwoLocalPair.normalizer_twoCore_H
  have hLM : L ≤ M := hL.le
  have hLX : ¬ InClassXBlock L := fun h =>
    hNX M L hT.toTwoLocalPair.maxTwoLocal_M hLM hL.subnormal h
  have h5 : NineThreeFive M L :=
    ASevenBlock.nineThreeFive_of_altSeven hord hLX (h93 G M (pCoreOf 2 H) L hK hA hL) e
  have hYL := hNorm hS P M H Q K hd L hL ⟨e⟩
  obtain ⟨hKn, hcase⟩ := hList hS P M H Q K hd L hL ⟨e⟩ hYL
  obtain ⟨Q', hQ'Y, hQQ'⟩ := exists_isSylowIn_ge 3 (le_inf hd.le_H hd.base.1) hd.base.2.1
  have hQ'H := h91s hS P M H Q K hd Q' hQ'Y hQQ'
  have hQ'3 : IsPGroup 3 Q' := hQ'H.isPGroup
  have hQ'L : Q' ≤ normalizer (L : Set G) := hQ'Y.le.trans hYL
  have hQ'S : Q' ≤ normalizer (pCoreOf 2 H : Set G) := by rw [hNH]; exact hQ'H.le
  obtain ⟨E, hEP, hEel, hE9⟩ := hE G M (pCoreOf 2 H) L hK hA hL hLX ⟨e⟩
  rw [hNH] at hEP
  have h9 := TenNineOneThree.nine_dvd_card_inf hQ'H hQ'L
    (TenNineOneThree.nine_dvd_card_of_barM (inf_le_right.trans hLM) hEP hE9)
  obtain ⟨C, hCQ, hAel, hA9, hcomm, hdisj, hgen⟩ :=
    ASevenBlock.directProd_of_nineThreeFive h86 hK hA hL h5 hQ'3 hQ'S hQ'L h9
  set A := Q' ⊓ L
  have hAQ : A ≤ Q' := inf_le_left
  set A' := A.subgroupOf Q'
  set C' := C.subgroupOf Q'
  have hA'el : IsElemAbelian 3 A' := TenNineOneThree.isElemAbelian_subgroupOf hAel
  have hA'9 : Nat.card A' = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAQ).toEquiv, hA9]
  have hcomm' : ∀ a ∈ A', ∀ c ∈ C', Commute a c := fun a ha c hc =>
    Subtype.ext (hcomm _ (Subgroup.mem_subgroupOf.mp ha) _ (Subgroup.mem_subgroupOf.mp hc))
  have hdisj' : A' ⊓ C' = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxA, hxC⟩
    have : (x : G) ∈ A ⊓ C := ⟨Subgroup.mem_subgroupOf.mp hxA, Subgroup.mem_subgroupOf.mp hxC⟩
    rw [hdisj, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).mpr (Subtype.ext this)
  have hgen' : A' ⊔ C' = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hAQ hCQ, hgen, Subgroup.subgroupOf_self]
  have hQ3 : IsPGroup 3 ↥Q' := hQ'3
  haveI := hKn
  set πH : ↥H →* H ⧸ primeComplementCore (G := H) 3 := QuotientGroup.mk' _
  set T : Subgroup (H ⧸ primeComplementCore (G := H) 3) := (Q'.subgroupOf H).map πH
  have hT3 : IsPGroup 3 T := (hQ'3.comap_subtype (K := H)).map πH
  have hTS : ∃ S : Sylow 3 K, (S : Subgroup K).map K.subtype ≤ T := by
    obtain ⟨S, hS'⟩ := hd.sylowK
    refine ⟨S, ?_⟩
    rw [hS']
    exact inf_le_left.trans (Subgroup.map_mono fun x hx => hQQ' hx)
  set ψT : ↥T →* MulAut ↥K := (MulAut.conjNormal (H := K)).comp T.subtype
  set φ : ↥Q' →* ↥T := (πH.comp (Subgroup.inclusion hQ'H.le)).codRestrict T fun q =>
    ⟨Subgroup.inclusion hQ'H.le q, Subgroup.mem_subgroupOf.mpr q.2, rfl⟩
  have hφ : Function.Surjective φ := by
    rintro ⟨_, ⟨q, hq, rfl⟩⟩
    exact ⟨⟨q, Subgroup.mem_subgroupOf.mp hq⟩, Subtype.ext rfl⟩
  set ψ : ↥Q' →* MulAut ↥K := ψT.comp φ
  have hrange : ψ.range = ψT.range := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hφ, ← MonoidHom.range_eq_map]
  let eQT : (↥Q' ⧸ ψ.ker) ≃* (↥T ⧸ ψT.ker) :=
    (QuotientGroup.quotientKerEquivRange ψ).trans ((MulEquiv.subgroupCongr hrange).trans
      (QuotientGroup.quotientKerEquivRange ψT).symm)
  have hkerX : ∀ q ∈ ψ.ker, (q : G) ∈ d1PlusCore 3 H K := by
    intro q hq
    refine ⟨Subgroup.inclusion hQ'H.le q, ?_, rfl⟩
    show πH (Subgroup.inclusion hQ'H.le q) ∈ Subgroup.centralizer (K : Set _)
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have h1 := congrArg (fun f : MulAut ↥K =>
      ((f ⟨k, hk⟩ : ↥K) : H ⧸ primeComplementCore (G := H) 3)) (MonoidHom.mem_ker.mp hq)
    simp only [ψ, ψT, MonoidHom.comp_apply, MulAut.one_apply] at h1
    rw [MulAut.conjNormal_apply] at h1
    change πH (Subgroup.inclusion hQ'H.le q) * k * (πH (Subgroup.inclusion hQ'H.le q))⁻¹ = k at h1
    calc k * πH (Subgroup.inclusion hQ'H.le q)
        = (πH (Subgroup.inclusion hQ'H.le q) * k * (πH (Subgroup.inclusion hQ'H.le q))⁻¹) *
          πH (Subgroup.inclusion hQ'H.le q) := by rw [h1]
      _ = πH (Subgroup.inclusion hQ'H.le q) * k := by group
  have hNrk : Open.pRank 3 ψ.ker ≤ 1 := by
    have hmap : ψ.ker.map Q'.subtype ≤ d1PlusCore 3 H K := by
      rintro _ ⟨q, hq, rfl⟩
      exact hkerX q hq
    calc Open.pRank 3 ψ.ker ≤ Open.pRank 3 (ψ.ker.map Q'.subtype) :=
          CFSG.SectionRank.pRank_le_map (by norm_num) _ Q'.subtype_injective _
      _ ≤ Open.pRank 3 (d1PlusCore 3 H K) := CFSG.SectionRank.pRank_mono (by norm_num) hmap
      _ ≤ 1 := hRk3 hS 3 P M H Q K hd
  have hKFT := hKF _ K T hT3 hTS
  rcases hcase with hsimp | ⟨hprod, hX3⟩
  · exact TenNineOneThree.false_of_shapeSimple hQ3 ψ.ker hA'el hA'9 hcomm' hdisj' hgen' hNrk
      (TenNineOneThree.shapeSimple_congr eQT.symm (hKFT.1 hsimp))
  ·
    have hker : ψ.ker = ⊥ := by
      rw [eq_bot_iff]
      intro q hq
      have hqX := hkerX q hq
      have h1 : orderOf (q : G) ∣ Nat.card (d1PlusCore 3 H K) :=
        Subgroup.orderOf_dvd_natCard _ hqX
      obtain ⟨k, hk⟩ := hQ'3 q
      have h2 : orderOf (q : G) ∣ 3 ^ k :=
        orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
      have hcop : Nat.Coprime (3 ^ k) (Nat.card (d1PlusCore 3 H K)) :=
        Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hX3)
      have h3 : orderOf (q : G) = 1 := Nat.Coprime.eq_one_of_dvd (hcop.coprime_dvd_left h2) h1
      exact (Subgroup.mem_bot).mpr (Subtype.ext (orderOf_eq_one_iff.mp h3))
    let e0 : ↥Q' ≃* (↥Q' ⧸ ψ.ker) :=
      (QuotientGroup.quotientBot).symm.trans (QuotientGroup.quotientMulEquivOfEq hker.symm)
    exact TenNineOneThree.false_of_shapeProd hQ3 hA'el hA'9 hcomm' hdisj' hgen'
      (TenNineOneThree.shapeProd_congr (e0.trans eQT).symm (hKFT.2 hprod))

end CFSG.LocalAnalysis.RankThreeTheoremC
