module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKMURDiagInputs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKFixedCenter
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKMURStrict
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKMUMain
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKMUEq
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKMUW

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

section Pump

namespace HeKMU

theorem isPComponent_of_pump'
    (hS : SchreierFor Blueprint.Catalog) (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome)
    (hheld : KProperRelativeB.HeldInput) (hD : L34RankTwoCentralFixedInput)
    (hDC : L34ProperFixedCenterTrivial) (hH : L34ProperFixedSimpleRank)
    (hW : HeldWGroupStep) (hStd : HeldStandardStep) (hAS : AschbacherSeitzHeldInput)
    (hKMd : HeldKDiagonalPumpUpDiagonalResidue) {X : Type} [Group X] [Finite X] {L : Subgroup X}
    (hset : HeldEndSetting X L) {a u : X} {M : Subgroup X} (ha : orderOf a = 2)
    (hLa : L ≤ centralizer ({a} : Set X))
    (hLc : IsPComponent 2 (L.subgroupOf (centralizer ({a} : Set X)))) (hu : HeldTwoA L u)
    (hMu : M ≤ centralizer ({u} : Set X))
    (hMp : IsPComponent 2 (M.subgroupOf (centralizer ({u} : Set X))))
    (hne : conjugate M a ≠ M) (hfix : gsFixedLayer (M ⊔ conjugate M a) a = gsFixedLayer L u)
    (hc : ∀ x ∈ (pPrimeCore 2 ↥M).map M.subtype, ∀ m ∈ M, x * m = m * x) {c w : X}
    (hc2 : orderOf c = 2) (hw2 : orderOf w = 2) (hcw : c * w = w * c)
    (hcase : c = u ∨ (u * w ≠ w * u ∧ ∃ k : ℕ, orderOf (u * w) = 2 * k ∧ c = (u * w) ^ k))
    (hcu : c * u = u * c) (hMc : M ≤ centralizer ({c} : Set X))
    (hMcp : IsPComponent 2 (M.subgroupOf (centralizer ({c} : Set X))))
    (hMw : M ≤ centralizer ({w} : Set X)) :
    IsPComponent 2 (M.subgroupOf (centralizer ({w} : Set X))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨hsimp, hnab, hK, -⟩, -⟩ := id hset
  have hw1 : w ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hw2
    norm_num at hw2
  have hwtop := HeKC.centralizer_ne_top hsimp hnab hw1
  obtain ⟨htype, z₁, hz₁, z₂, hz₂, hs₁, hs₂, hn₁, hn₂, hz, hcz⟩ :=
    HeKMC.type_and_pair hset ha hLa hLc hu hMu hMp hne hfix hc
  have hMcw : M ≤ centralizer ({c} : Set X) ⊓ centralizer ({w} : Set X) := le_inf hMc hMw
  obtain ⟨N, hNw, hNp, hMNc, hMNcp, hle, hdiag, heq⟩ := HeK.exists_pump hS hK hc2 hcw hwtop hMcw
    (UnbalancedCorr.isPComponent_subgroupOf_of_le hMcw inf_le_left hMcp)
  by_cases hNc : conjugate N c = N
  · have hNN : N ⊔ conjugate N c = N := by rw [hNc, sup_idem]
    have hMNc' : M ≤ N ⊓ centralizer ({c} : Set X) := hNN ▸ hMNc
    have hMNcp' : IsPComponent 2 (M.subgroupOf (N ⊓ centralizer ({c} : Set X))) := hNN ▸ hMNcp
    rcases lt_or_eq_of_le hle with hlt | heqi
    · exfalso
      by_cases hwM : w ∈ M
      · exact HeK.false_of_proper_fixed_l34 hD hK hc2 hwtop hNw hNp hNc hMNc' hMNcp' hlt htype
          hz₁ hz₂ hs₁ hs₂ hn₁ hn₂ hz hcz hwM hw2
      ·
        obtain ⟨eNq⟩ := HeK.held_of_proper_fixed_l34 hDC hH hK hc2 hwtop hNw hNp hNc hMNc'
          hMNcp' hlt htype hz₁ hz₂ hs₁ hs₂ hn₁ hn₂ hz hcz
        have hsetN := HeKR.heldEndSetting_of_steps hW hStd hAS hset hw2 hNw hNp eNq
        obtain ⟨n₀, hTA, hKM, hcn⟩ := HeKR.exists_twoA_of_strict hsetN hc2 hw2 hcw hNw hNp hMc
          hMcp hNc hMNc' hMNcp' hlt htype
        rcases hcn with hcn | hcn
        · exact HeKMUR.false_of_isPComponent hsetN hTA (by rw [hKM, ← hcn]; exact hMcp)
            (by rw [hKM]; exact hc)
        · exact HeKMUR.false_of_commute hset ha hLa hLc hu hMu hMp hne hfix hc hw2 hNw hNp
            (hMNc'.trans inf_le_left) hlt hsetN hTA hKM hcn hcu
    ·
      have hMO := heq heqi hNc.symm
      have hMN : M ≤ N := hMNc'.trans inf_le_left
      obtain ⟨E, hEw, hEM, hEe, hE8, hWE⟩ :=
        exists_elem_eight_wGroup hset ha hLa hLc hu hMu hMp hne hfix hc hw2 hMw
      have hMc' : IsComponent (M.subgroupOf (centralizer ({u} : Set X))) :=
        HeUC.isComponent_of_central hMu hMp hc
      have hMq : IsQuasisimple ↥M :=
        LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hMu) hMc'.1
      have hM2 : 2 ∣ Nat.card M := by
        have hcard := CatLeaf.card_of_isL34Type htype
        have hd := Subgroup.card_quotient_dvd_card (Open.fusionZStar ↥M)
        rw [hcard] at hd
        exact (show 2 ∣ 20160 by norm_num).trans hd
      have hNM := eq_of_sup_oddCore hS hU hheld hsimp hnab hK hw2 hMq hM2 hNw hNp hMN hMO hEw
        hEM hEe hE8 hWE
      rw [← hNM]
      exact hNp
  · exact (hKMd X L hset a u M ha hLa hLc hu hMu hMp hne hfix hc c w hc2 hw2 hcw hcase hMc hMcp N
      hNw hNp hMNc hMNcp hNc (hdiag fun h => hNc h.symm)).elim

end HeKMU

theorem heldKDiagonalComponentRestStep_of_pumpUp'
    (hS : SchreierFor Blueprint.Catalog) (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome)
    (hheld : KProperRelativeB.HeldInput) (hD : L34RankTwoCentralFixedInput)
    (hDC : L34ProperFixedCenterTrivial) (hH : L34ProperFixedSimpleRank)
    (hW : HeldWGroupStep) (hStd : HeldStandardStep) (hAS : AschbacherSeitzHeldInput)
    (hKMd : HeldKDiagonalPumpUpDiagonalResidue) : HeldKDiagonalComponentRestStep := by
  intro X _ _ L hset a u M ha hLa hLc hu hMu hMp hne hfix hc w hw hMw _
  have hu2 : orderOf u = 2 := hu.2.1
  have huu : u * u = 1 := by rw [← pow_two, ← hu2, pow_orderOf_eq_one]
  have hww : w * w = 1 := by rw [← pow_two, ← hw, pow_orderOf_eq_one]
  by_cases huw : u * w = w * u
  · exact HeKMU.isPComponent_of_pump' hS hU hheld hD hDC hH hW hStd hAS hKMd hset ha hLa hLc hu
      hMu hMp hne hfix hc hu2 hw huw (Or.inl rfl) rfl hMu hMp hMw
  rcases Nat.even_or_odd (orderOf (u * w)) with ⟨k, hk⟩ | hodd
  ·
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact (orderOf_pos (u * w)).ne' (by omega)
    set z := (u * w) ^ k with hzdef
    have hz2 : orderOf z = 2 := by
      rw [hzdef, orderOf_pow_of_dvd hk0 ⟨2, by omega⟩, hk, ← two_mul,
        Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hk0)]
    have hzz : z * z = 1 := by rw [← pow_two, ← hz2, pow_orderOf_eq_one]
    have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
    have hzu : u * z = z * u := by
      rw [hzdef, HeKMUR.mul_pow_eq_inv_mul huu hww k, ← hzdef, hzi]
    have hw' : w = u * (u * w) := by rw [← mul_assoc, huu, one_mul]
    have hzw : z * w = w * z := by
      have hxz : (u * w) * z = z * (u * w) := by rw [hzdef, ← pow_succ', ← pow_succ]
      calc z * w = z * (u * (u * w)) := by rw [← hw']
        _ = (u * z) * (u * w) := by rw [← mul_assoc, hzu]
        _ = u * ((u * w) * z) := by rw [mul_assoc, hxz]
        _ = w * z := by rw [← mul_assoc, ← hw']
    have huC : u ∈ centralizer (M : Set X) :=
      mem_centralizer_iff.mpr fun m hm => mem_centralizer_singleton_iff.mp (hMu hm)
    have hwC : w ∈ centralizer (M : Set X) :=
      mem_centralizer_iff.mpr fun m hm => mem_centralizer_singleton_iff.mp (hMw hm)
    have hzC : z ∈ centralizer (M : Set X) := pow_mem (mul_mem huC hwC) _
    have hMz : M ≤ centralizer ({z} : Set X) := fun m hm =>
      mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hzC m hm)
    have hMzp := HeKMU.isPComponent_of_pump' hS hU hheld hD hDC hH hW hStd hAS hKMd hset ha hLa
      hLc hu hMu hMp hne hfix hc hu2 hz2 hzu (Or.inl rfl) rfl hMu hMp hMz
    exact HeKMU.isPComponent_of_pump' hS hU hheld hD hDC hH hW hStd hAS hKMd hset ha hLa hLc hu
      hMu hMp hne hfix hc hz2 hw hzw (Or.inr ⟨huw, k, by omega, hzdef⟩) hzu.symm hMz hMzp hMw
  · exact HeKMU.isPComponent_of_odd hu2 hw hodd hMu hMp hMw

end Pump

end CFSG.ComponentClassification.GrSLit
