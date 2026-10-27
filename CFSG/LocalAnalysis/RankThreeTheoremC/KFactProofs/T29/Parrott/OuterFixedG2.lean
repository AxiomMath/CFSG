module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.OuterFixedBasic
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67G2Field
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie2ProofOuter

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott

open CFSG.Open Subgroup TauCeti CFSG.Blueprint.Chevalley

section Field


theorem exists_E9_fixed_g2FieldHom {K : Type} [Field K] [Finite K] (σ : K ≃+* K) :
    ∃ E : Subgroup (adjointGroup .G2 K), IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
      ∀ e ∈ E, CFSG.RankThree.PartTwo.KFacts.g2FieldHom K σ e = e := by
  obtain ⟨φ⟩ := CFSG.GH74.GLS.Stage2.Bender.Thm1.g2_fixSub_equiv σ
  have : Finite (adjointGroup .G2 (CFSG.LieType.Chevalley.fixSubfield σ)) :=
    Finite.of_equiv _ φ.symm.toEquiv
  obtain ⟨u, v, hu1, hu3, hv3, huv, hvu⟩ :=
    CFSG.RankThree.PartTwo.Sec11.KS11Lie2Proof.g2_exists_e9
      (CFSG.LieType.Chevalley.fixSubfield σ)
  obtain ⟨hE, hE9⟩ := isElemAbelian_card_sup_zpowers_of_pair hu1 hu3 hv3 huv hvu
  set ψ := (Subgroup.subtype _).comp φ.toMonoidHom with hψ
  have hψinj : Function.Injective ψ := (Subgroup.subtype_injective _).comp φ.injective
  obtain ⟨hE', hE9'⟩ := isElemAbelian_card_map_of_E9 ψ hψinj hE hE9
  refine ⟨_, hE', hE9', ?_⟩
  rintro _ ⟨y, -, rfl⟩
  exact (φ y).2

theorem outerFixesE9_adjointG2 {K : Type} [Field K] [Finite K] (hK3 : ringChar K ≠ 3)
    (hK4 : 4 ≤ Nat.card K) : OuterFixesE9 (adjointGroup .G2 K) := by
  refine outerFixesE9_of_descent fun α hα3 hαo => ?_
  obtain ⟨σ, -, k, rfl⟩ :=
    CFSG.RankThree.PartTwo.KFacts.g2_order_three_field_descent hK3 hK4 hα3 hαo
  exact ⟨MulAut.conj k, _, rfl, exists_E9_fixed_g2FieldHom σ⟩

end Field

section Index


theorem outerFixedAt_G2 (q : PrimePower) (hv : (LieTypeIndex.G2 q).Valid) (hp3 : q.p ≠ 3) :
    OuterFixedAt ⟨.G2 q, hv⟩ := by
  refine outerFixedAt_of_model fun K _ _ e => ?_
  obtain ⟨F, _, _, hF, hFc, ⟨f⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
    CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 q hv
  have hq3 : 3 ≤ q.card :=
    (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  have hF3 : ringChar F ≠ 3 := by
    rw [ringChar.eq F q.p]
    exact hp3
  have hF4 : 4 ≤ Nat.card F := by
    rw [hF]
    by_contra h
    have h3 : q.card = 3 := by omega
    rw [PrimePower.card_def] at h3
    have hp : q.p ∣ 3 := by
      rw [← h3]
      exact dvd_pow_self _ q.exponent_pos.ne'
    exact hp3 ((Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_three).1 hp)
  exact ⟨_, _, outerFixesE9_adjointG2 hF3 hF4, ⟨e.trans f⟩⟩

end Index

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott
