module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldOrders
public import CFSG.LieType.SeitzGeneration.ExcPlaneG2
public import CFSG.RankThree.SteinbergBRThreeG2Noninner
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldCore

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.LieType.SeitzGeneration CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.TauCetiBridge CFSG.RankThree.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.Chevalley.SteinbergBT
open CFSG.LocalAnalysis.ComponentInitial (finite_field_prime_power_characteristic)

section ThreeG2


theorem fieldCoreAt_G2_three {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdvd : ∀ σ : K ≃+* K, orderOf σ = p →
      ¬ Nat.Coprime p (Nat.card (adjointGroup ReeTag.G2.tag (fixSubfield σ))))
    {x : MulAut (adjointGroup ReeTag.G2.tag K)} (hxp : orderOf x = p)
    (hxo : x ∉ (MulAut.conj : adjointGroup ReeTag.G2.tag K →*
      MulAut (adjointGroup ReeTag.G2.tag K)).range) :
    FieldCoreAt p x := by
  classical
  obtain ⟨hφord, hNF, -⟩ := G2_three_exact_automorphism_normal_form hf K hK
  obtain ⟨⟨y, a⟩, hya, -⟩ := hNF x
  have hαp : orderOf (⟨x, Subgroup.mem_top x⟩ :
      (⊤ : Subgroup (MulAut (adjointGroup ReeTag.G2.tag K)))) = p := by
    rw [Subgroup.orderOf_mk]
    exact hxp
  obtain ⟨hpf, -, ⟨σ, hσ, hσp, hφσ, hφap⟩, ⟨h, hh⟩, -⟩ :=
    CFSG.RankThree.three_G2_noninner_odd_prime_local_core_trivial hf hK hp hp2
      ⊤ le_top ⟨x, Subgroup.mem_top x⟩ hxo hαp y a a.2 hya
  obtain ⟨d, hd⟩ := hpf
  have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have hdp : d * p = f := by rw [hd, mul_comm]
  have hrank : 0 < ReeTag.G2.tag.rank := by decide
  obtain ⟨-, hkcard⟩ := card_fixSubfield Nat.prime_three hf hK σ
  rw [hσp, ← hdp, Nat.mul_div_cancel _ hp.pos] at hkcard
  obtain ⟨hJC, -, hfixing, hFrφ, -⟩ :=
    three_G2_subfield_normalizer_and_pointwise_automorphism_centralizer hf hd0 ⟨p, hdp.symm⟩ hK
      (fixSubfield σ) hkcard
  have hZ : Subgroup.center (adjointGroup ReeTag.G2.tag K) = ⊥ := center_adjointGroup_eq_bot
  have hinj := mulAut_conj_injective_of_center_eq_bot hZ
  have hΓJ : entrywiseFixedGroup ReeTag.G2.tag σ = fixedFieldImage ReeTag.G2.tag σ :=
    CFSG.ComponentClassification.UnbalancedCatalog.entrywiseFixedGroup_eq_fixedFieldImage σ
  have hmemJ : ∀ g : adjointGroup ReeTag.G2.tag K,
      g ∈ (fixedFieldImage ReeTag.G2.tag σ).subgroupOf (adjointGroup ReeTag.G2.tag K) ↔
        entrywiseAdjointAut ReeTag.G2.tag σ g = g := by
    intro g
    rw [Subgroup.mem_subgroupOf]
    refine (Subgroup.ext_iff.1 hΓJ (g : ModGL ReeTag.G2.tag K)).symm.trans ?_
    rw [mem_entrywiseFixedGroup]
    constructor
    · rintro ⟨-, h⟩
      exact Subtype.ext h
    · intro h
      exact ⟨g.2, congrArg Subtype.val h⟩
  have h3 : 3 ≤ Nat.card (fixSubfield σ) := by
    rw [hkcard]
    exact Nat.le_self_pow hd0.ne' 3
  have hq : CFSG.IsQuasisimple (fixedFieldImage ReeTag.G2.tag σ) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (fixedFieldImageEquiv σ)
      (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card (fixSubfield σ) h3)
  have e1 : ((fixedFieldImage ReeTag.G2.tag σ).subgroupOf (adjointGroup ReeTag.G2.tag K)) ≃*
      fixedFieldImage ReeTag.G2.tag σ := Subgroup.subgroupOfEquivOfLe hJC
  have hFrmem : ReeTag.G2.finiteFrobeniusAut K ^ d ∈
      Subgroup.zpowers (entrywiseAdjointAut ReeTag.G2.tag σ) := by
    rw [hFrφ, ← hφσ]
    refine mem_zpowers_of_mem_zpowers_of_pow_eq_one (φ := ReeTag.G2.finiteExceptionalAut K)
      (Subgroup.npow_mem_zpowers _ _) (Subgroup.npow_mem_zpowers _ _) hp.pos hφap ?_
    rw [← pow_mul, show 2 * d * p = 2 * f by rw [hd]; ring, ← hφord, pow_orderOf_eq_one]
  have hcore : FieldCoreAt p (entrywiseAdjointAut ReeTag.G2.tag σ) := by
    refine fieldCoreAt_of_fixSub_eq ((orderOf_entrywiseAdjointAut hrank σ).trans hσp)
      (CFSG.LocalCores.isQuasisimple_of_mulEquiv e1.symm hq) hmemJ (fun β hβ => ?_) ?_
    · have hfixβ : β ∈ fixingSubgroup (MulAut (adjointGroup ReeTag.G2.tag K))
          ((((fixedFieldImage ReeTag.G2.tag σ).subgroupOf (adjointGroup ReeTag.G2.tag K)) :
            Subgroup (adjointGroup ReeTag.G2.tag K)) : Set (adjointGroup ReeTag.G2.tag K)) :=
        (mem_fixingSubgroup_iff _).2 fun u hu => hβ u hu
      have hβZ : β ∈ Subgroup.zpowers (ReeTag.G2.finiteFrobeniusAut K ^ d) := by
        rw [← hfixing]
        exact hfixβ
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hβZ
      exact Subgroup.zpow_mem _ hFrmem m
    · rw [Nat.card_congr e1.toEquiv, ← Nat.card_congr (fixedFieldImageEquiv σ).toEquiv]
      exact hdvd σ hσp
  exact fieldCoreAt_of_conj hcore (MulAut.conj h) (hh.trans hφσ)

theorem isLocallyBalancedAbs_adjointG2_fieldThree {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = 3 ^ f) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpK : ¬ p ∣ Nat.card K)
    (hd : p ∣ Nat.card K ^ 2 - 1) : IsLocallyBalancedAbs p 3 (adjointGroup Tag.G2 K) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K ReeTag.G2.prime := by
    rw [show ReeTag.G2.prime = 3 from rfl]
    exact finite_field_prime_power_characteristic Nat.prime_three hf hK
  have hK1 : 1 ≤ Nat.card K := Nat.card_pos
  refine isLocallyBalancedAbs_adjoint_of_fieldCore K hp
    (rankLE2_adjointGroup_G2 K hp hp5 hpK) fun x hxp hxo => ?_
  have hdf : ∀ σ : K ≃+* K, orderOf σ = p → p ∣ Nat.card (fixSubfield σ) ^ 2 - 1 := fun σ hσp =>
    dvd_sq_sub_one_of_cast_eq hK1 Nat.card_pos
      (card_fixSubfield_cast Nat.prime_three hf hK hp hσp).symm hd
  exact fieldCoreAt_G2_three hf K hK hp (by omega)
    (fun σ hσp => not_coprime_card_adjointG2 (fixSubfield σ) hp (hdf σ hσp)) hxp hxo

end ThreeG2

section FamilyThreeG2


@[expose] def regimeG2FieldThree (idx : TauCeti.ValidLieTypeIndex) (p : ℕ) : Prop :=
  ∃ q : TauCeti.PrimePower, idx.1 = .G2 q ∧ 5 ≤ p ∧ p ∣ q.card ^ 2 - 1 ∧ p ∣ q.exponent ∧
    q.p = 3

theorem crossCharFamAt_G2_fieldThree : CrossCharFamAt .G2 regimeG2FieldThree := by
  rintro ⟨d, hv⟩ _ p hp hp2 hc ⟨q, hd, hp5, hdq, hpf, hq3⟩
  change d = _ at hd
  subst hd
  have hpq : p ≠ q.p := fun h => hc (by simp [h])
  obtain ⟨K, _, _, hK, _, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.g2 q hv
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne hp hpq
  rw [← hK] at hdq
  have hK3 : Nat.card K = 3 ^ q.exponent := by
    rw [hK, TauCeti.PrimePower.card_def, hq3]
  exact IsLocallyBalancedAbs.of_mulEquiv e (isLocallyBalancedAbs_adjointG2_fieldThree
    q.exponent_pos K hK3 hp hp5 hpK hdq)

end FamilyThreeG2


end CFSG.HardMathSupport.Timmesfeld.CrossChar
