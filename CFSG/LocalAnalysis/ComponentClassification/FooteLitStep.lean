module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma21Rel

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

theorem nonempty_fusionZStar_equiv_of_quotient_equiv {X₁ X₂ : Type*} [Group X₁] [Group X₂]
    (e : X₁ ⧸ pPrimeCore 2 X₁ ≃* X₂ ⧸ pPrimeCore 2 X₂) :
    Nonempty (X₁ ⧸ Open.fusionZStar X₁ ≃* X₂ ⧸ Open.fusionZStar X₂) := by
  set Q₂ := X₂ ⧸ pPrimeCore 2 X₂
  let ψ₂ : X₂ →* Q₂ ⧸ center Q₂ :=
    (QuotientGroup.mk' (center Q₂)).comp (QuotientGroup.mk' (pPrimeCore 2 X₂))
  let ψ₁ : X₁ →* Q₂ ⧸ center Q₂ :=
    (QuotientGroup.mk' (center Q₂)).comp (e.toMonoidHom.comp (QuotientGroup.mk' _))
  have hs₂ : Function.Surjective ψ₂ :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  have hs₁ : Function.Surjective ψ₁ :=
    (QuotientGroup.mk'_surjective _).comp (e.surjective.comp (QuotientGroup.mk'_surjective _))
  have hk₂ : Open.fusionZStar X₂ = ψ₂.ker := by
    ext x
    rw [MonoidHom.mem_ker, mem_fusionZStar_iff_forall, ← mk_mem_center_iff]
    change _ ↔ QuotientGroup.mk' (center Q₂) (QuotientGroup.mk' (pPrimeCore 2 X₂) x) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    rfl
  have hk₁ : Open.fusionZStar X₁ = ψ₁.ker := by
    ext x
    rw [MonoidHom.mem_ker, mem_fusionZStar_iff_forall, ← mk_mem_center_iff]
    change _ ↔ QuotientGroup.mk' (center Q₂) (e (QuotientGroup.mk' (pPrimeCore 2 X₁) x)) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      mem_center_iff, mem_center_iff]
    constructor
    · intro h z
      obtain ⟨q, rfl⟩ := e.surjective z
      rw [← map_mul, ← map_mul, h q]
    · intro h q
      apply e.injective
      rw [map_mul, map_mul]
      exact h (e q)
  exact ⟨(QuotientGroup.liftEquiv _ hs₁ hk₁).trans (QuotientGroup.liftEquiv _ hs₂ hk₂).symm⟩

theorem conjClosure_mono {G : Type*} [Group G] {Y Y' : Subgroup G} (h : Y ≤ Y')
    (E : Subgroup G) : conjClosure Y E ≤ conjClosure Y' E := by
  rw [conjClosure_eq_iSup, conjClosure_eq_iSup]
  exact iSup₂_mono fun e _ => map_mono h

theorem le_conjClosure {G : Type*} [Group G] (Y E : Subgroup G) : Y ≤ conjClosure Y E := by
  rw [conjClosure_eq_iSup]
  exact le_iSup₂_of_le 1 (one_mem E) (by rw [conjugate_one])

variable {G : Type} [Group G] [Finite G]

theorem twoLayerIn_le_normalizer {H B : Subgroup G} (hBH : B ≤ H)
    (hB : IsPComponent 2 (B.subgroupOf H)) : twoLayerIn H ≤ normalizer (B : Set G) := by
  rintro _ ⟨e, he, rfl⟩
  exact mem_normalizer_of_subgroupOf hBH (pLayer_le_normalizer_of_isPComponent hB he)

theorem exists_footeStep (hLB : FooteLBalanceInput) {a b : G} {L : Subgroup G}
    (hL : IsTwoComponentAt a L) (hb : orderOf b = 2) (hab : a * b = b * a) (hne : a ≠ b)
    (hbL : b ∈ coreActionKernel L) :
    ∃ B : Subgroup G, IsTwoComponentAt b B ∧ FooteStep L B ∧
      UnbalancedGS.gsFixedLayer L b ≤ B ⊔ conjugate B a ∧
      conjClosure (footeFixed L b) (twoLayerOf b) = B ⊔ conjugate B a ∧
      ((conjugate B a = B ∧ B = oddResidualIn (UnbalancedGS.gsFixedLayer L b ⊔
          oddCoreOfCentralizer b) ∧
          Nonempty (UnbalancedGS.gsFixedLayer L b ⧸ pPrimeCore 2 (UnbalancedGS.gsFixedLayer L b)
            ≃* B ⧸ pPrimeCore 2 B)) ∨
        (conjugate B a = B ∧ UnbalancedGS.gsFixedLayer L b ⊔ oddCoreIn B < B ∧
          IsEmpty (UnbalancedGS.gsFixedLayer L b ⧸ Open.fusionZStar (UnbalancedGS.gsFixedLayer L b)
            ≃* B ⧸ Open.fusionZStar B)) ∨
        (conjugate B a ≠ B ∧
          UnbalancedGS.gsFixedLayer L b =
            twoLayerIn ((B ⊔ conjugate B a) ⊓ centralizer ({a} : Set G)) ∧
          (pPrimeCore 2 (UnbalancedGS.gsFixedLayer L b)).index ≤ (pPrimeCore 2 B).index)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ha, hLa, hLpc⟩ := hL
  set T := UnbalancedGS.gsFixedLayer L b with hT
  set Cb := centralizer ({b} : Set G) with hCb
  set Ob := oddCoreOfCentralizer b with hOb
  have haCb : a ∈ Cb := mem_centralizer_singleton_iff.mpr hab
  have hbCa : b ∈ centralizer ({a} : Set G) := mem_centralizer_singleton_iff.mpr hab.symm
  have hLq := isQuasisimple_quotient_of_isPComponent hLa hLpc
  have hLsub : (L.subgroupOf (centralizer ({a} : Set G))).IsSubnormal := by
    obtain ⟨-, -, hs, -, -⟩ := id hLpc
    exact hs
  have hTpc := gsFixedLayer_isPComponent hLa hLsub hbCa hb hbL.1 hLq hbL.2
  have hTsup : T ⊔ oddCoreIn L = L :=
    gsFixedLayer_sup_map_pPrimeCore hb hLq hbL.1 hbL.2
  have hTLb : T ≤ L ⊓ Cb := UnbalancedGS.gsFixedLayer_le_inf L b
  have hTC : T ≤ Cb ⊓ centralizer ({a} : Set G) :=
    le_inf (hTLb.trans inf_le_right) (hTLb.trans (inf_le_left.trans hLa))
  have hTpc' : IsPComponent 2 (T.subgroupOf (Cb ⊓ centralizer ({a} : Set G))) := by
    rw [inf_comm]; exact hTpc
  obtain ⟨B, hBCb, hBpc, hTB, hcl, hcase⟩ := foote_lemma_2_1_iv_subgroup haCb ha hTC hTpc'
  set J := B ⊔ conjugate B a with hJ
  have hBaCb : conjugate B a ≤ Cb := by
    intro x hx
    rw [mem_conjugate_iff] at hx
    have h1 := mul_mem (mul_mem (inv_mem haCb) (hBCb hx)) haCb
    rwa [show a⁻¹ * (a * x * a⁻¹) * a = x by group] at h1
  have hBapc : IsPComponent 2 ((conjugate B a).subgroupOf Cb) := by
    have h1 := isPComponent_conjugate hBpc (⟨a, haCb⟩ : Cb)
    rwa [conjugate_subgroupOf_eq] at h1
  have hXJ : oddCoreOfCentralizer a ⊓ Cb ≤ normalizer (J : Set G) := fun x hx =>
    mem_normalizer_sup (oddCoreOfCentralizer_inf_le_normalizer hLB ha hab hBCb hBpc hx)
      (oddCoreOfCentralizer_inf_le_normalizer hLB ha hab hBaCb hBapc hx)
  have hOJ : Ob ≤ normalizer (J : Set G) := fun x hx =>
    mem_normalizer_sup (pPrimeCore_le_normalizer_of_isPComponent hBCb hBpc hx)
      (pPrimeCore_le_normalizer_of_isPComponent hBaCb hBapc hx)
  have hOLa : oddCoreIn L ≤ oddCoreOfCentralizer a :=
    UGSChain.map_pPrimeCore_le_of_isPComponent hLa hLpc
  have hTnorm : T ≤ normalizer ((oddCoreIn L : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_oddCoreIn (le_normalizer ((hTLb.trans inf_le_left) hx))
  have hCLb : L ⊓ Cb ≤ T ⊔ (oddCoreOfCentralizer a ⊓ Cb) := by
    intro x hx
    have h1 : x ∈ T ⊔ oddCoreIn L := hTsup.symm.le (mem_inf.mp hx).1
    rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _ hTnorm] at h1
    obtain ⟨t, ht, o, ho, rfl⟩ := h1
    have hoC : o ∈ Cb := by
      rw [show o = t⁻¹ * (t * o) by group]
      exact mul_mem (inv_mem ((hTLb.trans inf_le_right) ht)) (mem_inf.mp hx).2
    exact mul_mem (mem_sup_left ht) (mem_sup_right (mem_inf.mpr ⟨hOLa ho, hoC⟩))
  have hXodd : Odd (Nat.card ↥(oddCoreOfCentralizer a ⊓ Cb)) :=
    Odd.of_dvd_nat (odd_card_oddCoreOfCentralizer a) (card_dvd_of_le inf_le_left)
  have hXOb : oddCoreOfCentralizer a ⊓ Cb ≤ normalizer ((J ⊔ Ob : Subgroup G) : Set G) :=
    fun x hx => mem_normalizer_sup (hXJ hx) (mem_normalizer_oddCoreOfCentralizer (mem_inf.mp hx).2)
  have hLbJ : footeFixed L b ≤ J := by
    refine (closure_le _).mpr fun g hg => ?_
    obtain ⟨hgmem, hg2⟩ := hg
    have hle : (L ⊓ Cb) ⊔ Ob ≤ (oddCoreOfCentralizer a ⊓ Cb) ⊔ (J ⊔ Ob) :=
      sup_le (hCLb.trans (sup_le (hTB.trans (le_sup_of_le_right le_sup_left)) le_sup_left))
        (le_sup_of_le_right le_sup_right)
    have h1 := mem_of_two_element_of_mem_sup hXOb
      (by rw [oddResidualIn_eq_bot_of_odd hXodd]; exact bot_le) (hle hgmem) hg2
    exact mem_of_two_element_of_mem_sup hOJ
      (by rw [oddResidualIn_eq_bot_of_odd (odd_card_oddCoreOfCentralizer b)]; exact bot_le)
      (show g ∈ Ob ⊔ J by rw [sup_comm]; exact h1) hg2
  have hTLb' : T ≤ footeFixed L b := by
    have hTres : oddResidualIn T = T := by
      have hTpc'' : IsPComponent 2 (T.subgroupOf (centralizer ({a} : Set G) ⊓ Cb)) := hTpc
      exact oddResidualIn_eq_self_of_isPComponent (le_inf (hTLb.trans (inf_le_left.trans hLa))
        (hTLb.trans inf_le_right)) hTpc''
    calc T = oddResidualIn T := hTres.symm
      _ ≤ footeFixed L b := oddResidualIn_mono (le_sup_of_le_left hTLb)
  have hclLb : conjClosure (footeFixed L b) (twoLayerOf b) = J := by
    refine le_antisymm ?_ ((le_of_eq hcl.symm).trans (conjClosure_mono hTLb' _))
    rw [conjClosure_eq_iSup]
    refine iSup₂_le fun e he => ?_
    have heJ : e ∈ normalizer (J : Set G) :=
      mem_normalizer_sup (twoLayerIn_le_normalizer hBCb hBpc he)
        (twoLayerIn_le_normalizer hBaCb hBapc he)
    calc conjugate (footeFixed L b) e ≤ conjugate J e := map_mono hLbJ
      _ = J := conjugate_eq_of_mem_normalizer heJ
  have hstep : FooteStep L B := ⟨a, b, ⟨ha, hLa, hLpc⟩, ⟨hb, hBCb, hBpc⟩, hab, hne, hbL, hclLb⟩
  exact ⟨B, ⟨hb, hBCb, hBpc⟩, hstep, hTB, hclLb, hcase⟩

theorem footeStep_cases_of_maximal (hLB : FooteLBalanceInput) {a b : G} {L : Subgroup G}
    (hL : IsTwoComponentAt a L) (hmax : FooteMaximal L) (hb : orderOf b = 2) (hab : a * b = b * a)
    (hne : a ≠ b) (hbL : b ∈ coreActionKernel L) :
    ∃ B : Subgroup G, IsTwoComponentAt b B ∧ FooteStep L B ∧
      Nonempty (L ⧸ Open.fusionZStar L ≃* B ⧸ Open.fusionZStar B) ∧
      conjClosure (footeFixed L b) (twoLayerOf b) = B ⊔ conjugate B a ∧
      ((conjugate B a = B ∧ footeFixed L b = B) ∨
        (conjugate B a ≠ B ∧ UnbalancedGS.gsFixedLayer L b =
          twoLayerIn ((B ⊔ conjugate B a) ⊓ centralizer ({a} : Set G)))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨B, hBb, hstep, hTB, hcl, hcase⟩ := exists_footeStep hLB hL hb hab hne hbL
  obtain ⟨eLB⟩ := hmax.2 B (Relation.ReflTransGen.single hstep)
  refine ⟨B, hBb, hstep, ⟨eLB⟩, hcl, ?_⟩
  obtain ⟨-, hLa, hLpc⟩ := hL
  have hLq := isQuasisimple_quotient_of_isPComponent hLa hLpc
  have hTL : UnbalancedGS.gsFixedLayer L b ≤ L :=
    (UnbalancedGS.gsFixedLayer_le_inf L b).trans inf_le_left
  rcases hcase with ⟨hBa, hBres, -⟩ | ⟨-, -, hiso⟩ | ⟨hBa, hT, -⟩
  · left
    refine ⟨hBa, le_antisymm ?_ ?_⟩
    · have h1 := (le_conjClosure (footeFixed L b) (twoLayerOf b)).trans hcl.le
      rwa [hBa, sup_idem] at h1
    · rw [hBres, footeFixed_eq_oddResidualIn]
      exact oddResidualIn_mono (sup_le_sup_right (UnbalancedGS.gsFixedLayer_le_inf L b) _)
  · exfalso
    obtain ⟨-, eT, -⟩ := restriction_quotient_mulEquiv hTL
      (gsFixedLayer_sup_map_pPrimeCore hb hLq hbL.1 hbL.2)
    obtain ⟨eZ⟩ := nonempty_fusionZStar_equiv_of_quotient_equiv eT
    exact hiso.false (eZ.trans eLB)
  · exact Or.inr ⟨hBa, hT⟩

end CFSG.ComponentClassification.FooteLit
