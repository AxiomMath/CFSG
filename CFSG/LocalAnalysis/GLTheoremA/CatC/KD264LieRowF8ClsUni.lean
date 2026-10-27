module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowF8ClsMain
public import CFSG.LieType.SemisimpleCentralizers.HeldLangI5
public import CFSG.LieType.SemisimpleCentralizers.HeldLangCoverUni

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms CFSG.ComponentClassification.PerfectAutomorphisms
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.LieType.SemisimpleCentralizers.HeldLang
  CFSG.LieType.Universal.Unitary CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Final

theorem onCenterQuotient_mem_innAutDerived_iff {G : Type*} [Group G]
    (hZ : Subgroup.center G = ⊥) (β : MulAut G) :
    onCenterQuotient β ∈ innAutDerived (G ⧸ Subgroup.center G) ↔ β ∈ innAutDerived G := by
  let e : G ≃* G ⧸ Subgroup.center G :=
    (QuotientGroup.quotientBot (G := G)).symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  have he : ∀ x, e x = QuotientGroup.mk x := fun x => rfl
  have h : onCenterQuotient β = MulAut.congr e β := by
    refine MulEquiv.ext fun y => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    have h1 : e.symm (QuotientGroup.mk x) = x := by
      rw [MulEquiv.symm_apply_eq, he]
    have h2 : onCenterQuotient β (QuotientGroup.mk x) = QuotientGroup.mk (β x) :=
      onCenterQuotient_apply_mk β x
    rw [h2]
    show _ = e (β (e.symm (QuotientGroup.mk x)))
    rw [h1, he]
  rw [h, mem_innAutDerived_congr]

theorem KD264F8ClsUni_holds : KD264F8ClsUni := by
  intro d _hfin _hns hk2 _hk3 hov hP _hTri hTwA _hTwE6 A hA
  obtain ⟨d1, hd1⟩ := d
  obtain ⟨n, q, rfl⟩ := hP
  exfalso
  have hq : q.card = 8 := hov
  have hvalid := (TauCeti.LieTypeIndex.valid_iff _).1 hd1
  have hr : 2 ≤ n ∧ (n = 2 → 3 ≤ q.card) :=
    (TauCeti.LieTypeIndex.inStandardRange_iff _).1 hvalid.1
  have h3n : ¬ 3 ∣ n + 1 := fun h => hTwA ⟨n, q, rfl, h⟩
  have hn3 : n ≠ 3 := by
    rintro rfl
    exact hk2 ⟨rfl, hq⟩
  have hn4 : 4 ≤ n := by
    have : n ≠ 2 := by
      rintro rfl
      exact h3n (by norm_num)
    omega
  have hN : 3 ≤ n + 1 := by omega
  obtain ⟨-, F, hF, hfin, hFcard, ⟨eM⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA n q hd1 (MulEquiv.refl _)
  have hdat : UnitaryFieldData q.p q.exponent F :=
    ⟨q.prime_p, q.exponent_pos, by rw [hFcard, ← pow_mul, mul_comm]⟩
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  haveI : CharP F q.p := hdat.charP
  have hK' : Nat.card F = (q.p ^ q.exponent) ^ 2 := by rw [hdat.card, ← pow_mul, Nat.mul_comm]
  have hNq := not_three_two_of_valid n q hd1 hN
  have hcardq : q.p ^ q.exponent = 8 := by rw [← TauCeti.PrimePower.card_def]; exact hq
  have hc := center_statedSU_eq hdat hN
  have hcard := (CFSG.LinearGroups.unitary_scalar_kernel q.prime_p hK' (n := n + 1) (by omega)).2.2
  have hcop : Nat.Coprime (n + 1) 9 := by
    have h1 : Nat.Coprime 3 (n + 1) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3n
    have h2 := h1.symm.pow_right 2
    simpa using h2
  have hcenter : Subgroup.center ↥(StatedSU (n + 1) (q.p ^ q.exponent) F) = ⊥ := by
    rw [← Subgroup.card_eq_one, Nat.card_congr (MulEquiv.subgroupCongr hc).toEquiv, hcard, hcardq]
    exact hcop
  have hsub : (⊥ : Subgroup ↥(StatedSU (n + 1) (q.p ^ q.exponent) F)) =
      (StatedScalars (Fin (n + 1)) F).subgroupOf (StatedSU (n + 1) (q.p ^ q.exponent) F) :=
    hcenter.symm.trans hc
  let r : ↥(StatedSU (n + 1) (q.p ^ q.exponent) F) ≃*
      StatedProj (StatedSU (n + 1) (q.p ^ q.exponent) F) :=
    (QuotientGroup.quotientBot (G := ↥(StatedSU (n + 1) (q.p ^ q.exponent) F))).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hsub)
  let eSL : (TauCeti.CFSGIndex.lie ⟨.twistedA n q, hd1⟩).Group ≃*
      ↥(StatedSU (n + 1) (q.p ^ q.exponent) F) := eM.trans r.symm
  have hcenterS : Subgroup.center (TauCeti.CFSGIndex.lie ⟨.twistedA n q, hd1⟩).Group = ⊥ := by
    have h1 := Subgroup.map_center_eq eSL
    rw [hcenter] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ eSL.injective).1 h1
  obtain ⟨hAab, h3, h4, hm3, hout, hnot⟩ := hA
  obtain ⟨b, hbA, hbout⟩ := SetLike.not_le_iff_exists.1 hnot
  have hb3 : b ^ 3 = 1 := hAab.2 b hbA
  have hbout' : onCenterQuotient b ∉ innAutDerived
      ((TauCeti.CFSGIndex.lie ⟨.twistedA n q, hd1⟩).Group ⧸ Subgroup.center
        (TauCeti.CFSGIndex.lie ⟨.twistedA n q, hd1⟩).Group) :=
    fun h => hbout ((onCenterQuotient_mem_innAutDerived_iff hcenterS b).1 h)
  have h3q : 3 ∣ q.p ^ q.exponent + 1 := by rw [hcardq]; norm_num
  obtain ⟨E, hEfix, hEab, hEcard⟩ := transport_kd264 (m := n + 1 - 1) eSL
    (fun β' hβ'3 hout'' => kd264I5_SU hdat hN hNq h3q β' hβ'3 hout'') b hb3 hbout'
  have hbnotinn : b ∉ (MulAut.conj : (TauCeti.CFSGIndex.lie ⟨.twistedA n q, hd1⟩).Group →*
      MulAut (TauCeti.CFSGIndex.lie ⟨.twistedA n q, hd1⟩).Group).range :=
    fun h => hbout (inner_le_innAutDerived _ h)
  have h1 := hout b hbA hbnotinn E hEfix hEab
  rw [pRank_eq_of_card' Nat.prime_three hEab hEcard] at h1
  omega

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
