module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma55
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop42CaseThreeProof
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54Ns

theorem i2316e_isPGroup_center {Y : Type*} [Group Y] [Finite Y] {p : ℕ} (hp : p.Prime)
    (hcore : GLAPPrimeCore p Y = ⊥) : IsPGroup p ↥(Subgroup.center Y) := by
  intro z
  have hz0 : orderOf (z : Y) ≠ 0 := (orderOf_pos _).ne'
  obtain ⟨e, m, hm, hem⟩ := Nat.exists_eq_pow_mul_and_not_dvd hz0 p hp.ne_one
  have hzc : (z : Y) ∈ Subgroup.center Y := z.2
  set w : Y := (z : Y) ^ (p ^ e) with hw
  have hwc : w ∈ Subgroup.center Y := Subgroup.pow_mem _ hzc _
  have hord : orderOf w = m := by
    rw [hw, orderOf_pow_of_dvd (pow_ne_zero _ hp.ne_zero) (hem ▸ dvd_mul_right _ _), hem,
      Nat.mul_div_cancel_left _ (pow_pos hp.pos _)]
  have hS : Subgroup.zpowers w ≤ GLAPPrimeCore p Y := by
    have hle : Subgroup.zpowers w ≤ Subgroup.center Y := (Subgroup.zpowers_le).2 hwc
    refine le_sSup ⟨Subgroup.normal_of_le_center hle, ?_⟩
    rw [Nat.card_zpowers, hord]
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 hm
  have hw1 : w = 1 := by
    have := hS (Subgroup.mem_zpowers w)
    rw [hcore] at this
    exact Subgroup.mem_bot.1 this
  have hm1 : m = 1 := by rw [← hord, hw1, orderOf_one]
  refine ⟨e, Subtype.ext ?_⟩
  simpa [hw] using hw1

theorem i2316e_center_eq_pCore {Y : Type*} [Group Y] [Finite Y] {p : ℕ} (hp : p.Prime)
    (hq : CFSG.Open.IsQuasisimple Y) (hcore : GLAPPrimeCore p Y = ⊥) :
    Subgroup.center Y = CFSG.pCore p Y := by
  refine le_antisymm (le_sSup ⟨inferInstance, i2316e_isPGroup_center hp hcore⟩) ?_
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hperf, hsimple⟩ := hq
  have hnt : Nontrivial Y := (QuotientGroup.mk'_surjective (Subgroup.center Y)).nontrivial
  have : Group.IsPerfect Y := ⟨hperf⟩
  set φ := QuotientGroup.mk' (Subgroup.center Y) with hφ
  have hn : ((CFSG.pCore p Y).map φ).Normal :=
    (CFSG.pCore_normal (p := p) (G := Y)).map φ (QuotientGroup.mk'_surjective _)
  have := hn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((CFSG.pCore p Y).map φ) with h | h
  · rw [Subgroup.map_eq_bot_iff, hφ, QuotientGroup.ker_mk'] at h
    exact h
  · exfalso
    have hpg : IsPGroup p ((CFSG.pCore p Y).map φ) := (CFSG.pCore_isPGroup).map φ
    rw [h] at hpg
    have hpg' : IsPGroup p (Y ⧸ Subgroup.center Y) := hpg.of_equiv Subgroup.topEquiv
    have : Group.IsNilpotent (Y ⧸ Subgroup.center Y) := hpg'.isNilpotent
    have hnil : Group.IsNilpotent Y :=
      Subgroup.isNilpotent_of_ker_le_center φ (by rw [hφ, QuotientGroup.ker_mk']) 
    exact Group.IsPerfect.not_isNilpotent Y hnil

noncomputable def i2316e_quotOPrimeP (p : ℕ) (H : Type*) [Group H] :
    (H ⧸ oPrimeP p H) ≃*
      ((H ⧸ GLAPPrimeCore p H) ⧸ CFSG.pCore p (H ⧸ GLAPPrimeCore p H)) := by
  let φ : H →* ((H ⧸ GLAPPrimeCore p H) ⧸ CFSG.pCore p (H ⧸ GLAPPrimeCore p H)) :=
    (QuotientGroup.mk' (CFSG.pCore p (H ⧸ GLAPPrimeCore p H))).comp
      (QuotientGroup.mk' (GLAPPrimeCore p H))
  have hsurj : Function.Surjective φ :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker = oPrimeP p H := by
    ext x
    simp [φ, oPrimeP, MonoidHom.mem_ker]
  exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hsurj)


@[expose] def UpsilonExtremal : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), GLStanding G m 3 → GLCaseFour G 3 →
    ∀ B : Subgroup G, IsBOneMax 3 B → ∀ b ∈ B, b ≠ 1 → ∀ L : Subgroup G,
      IsUpsilonComponent B b L → IsThreeType (barOf 3 L) →
        IsExtremalType (barOf 3 L ⧸ Subgroup.center (barOf 3 L))

theorem upsilonExtremal_of_inputs (hU : Lemma55Ns.InputUpsilonType)
    (hON : Lemma53Ns.Input3_3_ON) : UpsilonExtremal := by
  intro G _ _ m hS hC B hB b hb hb1 L hL hT
  have hp : Nat.Prime 3 := Nat.prime_three
  have hsc : IsSCp 3 ⊤ B := lemma23_proved G m 3 hS B hB
  rcases hU G m hS hC B hB.1 hsc b hb hb1 L hL with hExt | hHat
  · have hq : CFSG.Open.IsQuasisimple (barOf 3 L) :=
      CaseThreeNs.isQuasisimple_barOf_of_glaPComponent hp hL.1
    have hbot : GLAPPrimeCore 3 (barOf 3 L) = ⊥ :=
      glaPPrimeCore_quotient_eq_bot (Z := ↥L) hp
    have hZ : Subgroup.center (barOf 3 L) = CFSG.pCore 3 (barOf 3 L) :=
      i2316e_center_eq_pCore hp hq hbot
    let E1 : (barOf 3 L ⧸ Subgroup.center (barOf 3 L)) ≃* (↥L ⧸ oPrimeP 3 ↥L) :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans (i2316e_quotOPrimeP 3 ↥L).symm
    rcases hExt with ⟨F, iF, iFin, hc, ⟨f⟩⟩ | ⟨F, iF, iFin, q, hq', hq3, hq8, ⟨f⟩⟩
    · exact Or.inl ⟨F, iF, iFin, hc, ⟨E1.trans f⟩⟩
    · exact Or.inr ⟨F, iF, iFin, q, hq', hq3, hq8, ⟨E1.trans f⟩⟩
  · obtain ⟨-, -, ⟨f⟩⟩ := hHat
    rcases hT with ⟨F, iF, iFin, ⟨e⟩⟩ | ⟨F, iF, iFin, q, hq', ⟨e⟩⟩
    · exact (hON.1 F iF iFin).elim (f.symm.trans e)
    · exact (hON.2 F iF iFin q hq').elim (f.symm.trans e)

end CFSG.HardMathSupport.Solomon.Coordinator
