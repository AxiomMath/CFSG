module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShNormDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MTriv
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FQ
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS10I1416RBridge
public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevAutFieldGraph
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Basic
public import CFSG.RankThree.PartTwo.Sec4.LTwoPiCenter
public import CFSG.RankThree.PartTwo.Sec11.Item1120V0BarL3Mat

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.RankThree.PartTwo.Sec4 CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement

private theorem t158NormL3_card2_eq {X : Type} [Group X] [Finite X] {K L₁ : Subgroup X} {x₁ : X}
    (hL1comp : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({x₁} : Set X)) L₁)
    (hx1N : x₁ ∈ Subgroup.normalizer (K : Set X)) (hx13 : x₁ ^ 3 = 1)
    {π : Bool} {p f : ℕ} {F : Type} [Field F] [Finite F]
    (hKf : PiField π p f F) (hq : ModThree π (p ^ f)) (h2 : 2 < p ^ f)
    (heven : Even (p ^ f)) {β : MulAut (PSimple 3 K)}
    {Φ : ↥(slPi π 2 (p ^ f) F) →* PSimple 3 K} (hΦ : Function.Injective Φ)
    (hL1eq : chevTransfer 3 K L₁ = Φ.range)
    (hL1star : GLAPComponent 3 (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns.fixSub β)
      (chevTransfer 3 K L₁)) : card2 3 L₁ = p ^ f := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : 3 ≠ 2 := by norm_num
  have hap1 : IsPGroup 3 (Subgroup.zpowers x₁) :=
    isPGroup_zpowers_of_pow_eq_one (p := 3) hx13
  have hL1star' : GLAPComponent 3
      (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns.fixSub β) Φ.range := by
    rw [← hL1eq]
    exact hL1star
  have hp2eq : p = 2 := hKf.prime.even_iff.1 (Nat.even_pow.1 heven).1
  subst hp2eq
  have hqΦ : CFSG.Open.IsQuasisimple ↥Φ.range :=
    CFSG.Open.IsQuasisimple.of_mulEquiv (MonoidHom.ofInjective hΦ).symm
      (CFSG.HardMathSupport.Solomon.Coordinator.isQuasisimple_open
        (CFSG.HardMathSupport.Solomon.Coordinator.isQuasisimple_slPi_two hKf hq h2))
  have hPS : Nat.card (PSimple 3 L₁) = Nat.card (↥(slPi π 2 (2 ^ f) F) ⧸
      Subgroup.center ↥(slPi π 2 (2 ^ f) F)) := by
    obtain ⟨e1⟩ := nonempty_pSimple_equiv_chevTransfer hp hx1N hap1 hL1comp
    rw [hL1eq] at e1
    obtain ⟨e2⟩ := chev2_quot_equiv hp hL1star' hqΦ
    let eΦ : ↥(slPi π 2 (2 ^ f) F) ≃* ↥Φ.range := MonoidHom.ofInjective hΦ
    let e3 : (↥(slPi π 2 (2 ^ f) F) ⧸
        Subgroup.center ↥(slPi π 2 (2 ^ f) F)) ≃*
        (↥Φ.range ⧸ Subgroup.center ↥Φ.range) :=
      QuotientGroup.congr _ _ eΦ (Subgroup.map_center_eq eΦ)
    exact Nat.card_congr (e1.trans (e2.symm.trans e3.symm)).toEquiv
  rw [FP.card2_eq_twoPart_card_pSimple hp hp2 L₁, hPS]
  have hZ := center_slPi_two_eq_bot hKf
  rw [hZ, Nat.card_congr (QuotientGroup.quotientBot).toEquiv]
  rw [CFSG.RankThree.PartTwo.Sec11.Item1120V0Bar.card_slPi_two hKf]
  have hodd : Odd ((2 ^ f) ^ 2 - 1) :=
    CatDistinct.odd_pow_two_pow_sub_one (a := f) (j := 2) hKf.one_le (by norm_num)
  exact FQ.twoPart_two_pow_mul_odd (N := f) hodd

private theorem t158NormL3_false_of_fieldAut {p f : ℕ} {F : Type} [Field F] [Finite F]
    {π : Bool} (hKf : PiField π p f F) (hσ : ∃ σ : F ≃+* F, orderOf σ = 3)
    (h9 : p ^ f % 9 ≠ 0 ∧ p ^ f % 9 ≠ 1 ∧ p ^ f % 9 ≠ 8) : False := by
  obtain ⟨σ, hσ⟩ := hσ
  obtain ⟨d⟩ := exists_frobData hKf hσ
  have hc := cube_mod_nine (p ^ d.f₀)
  rw [← d.pow_eq] at hc
  rcases hc with h | h | h
  · exact h9.1 h
  · exact h9.2.1 h
  · exact h9.2.2 h

private theorem t158NormL3_beta_one {X : Type} [Group X] [Finite X] {K : Subgroup X} {x₁ x₂ : X}
    {L₂ : Subgroup X} (hKcomp : GLAPComponent 3 (⊤ : Subgroup X) K)
    (hL2comp : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({x₂} : Set X)) L₂)
    (hfg1 : FGOn 3 x₁ L₂) (hx1N : x₁ ∈ Subgroup.normalizer (K : Set X))
    (hβ1 : chevAut 3 K ⟨x₁, hx1N⟩ = 1) : False := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : 3 ≠ 2 := by norm_num
  have hcentK : CentMod 3 K x₁ := (chevAut_eq_one_iff hp hKcomp hx1N).1 hβ1
  have hx1L2N : x₁ ∈ Subgroup.normalizer (L₂ : Set X) := t158m_fgOn_normalizer hfg1
  have hcentL2 : CentMod 3 L₂ x₁ :=
    centMod_of_le hp (hL2comp.1.trans inf_le_left) hx1L2N hcentK
  have hβL2 : chevAut 3 L₂ ⟨x₁, hx1L2N⟩ = 1 :=
    (chevAut_eq_one_iff hp hL2comp hx1L2N).2 hcentL2
  exact chevAut_ne_one_of_fgOn hp hp2 hx1L2N (even_card_pSimple Nat.prime_three hL2comp) hfg1 hβL2

private theorem t158NormL3_inner {X : Type} [Group X] [Finite X] {K B : Subgroup X} {x₁ x₂ : X}
    {L₁ : Subgroup X} (hI : ∀ (X : Type) [Group X] [Finite X], I91CentPartAt X 3)
    (hBel : IsElemAbelian 3 B) (hx1B : x₁ ∈ B) (hx2B : x₂ ∈ B)
    (hL1comp : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({x₁} : Set X)) L₁)
    (hL1chev : IsChevSimple 2 (PSimple 3 L₁)) (hfg2 : FGOn 3 x₂ L₁)
    (hx1N : x₁ ∈ Subgroup.normalizer (K : Set X))
    {π : Bool} {p f : ℕ} {F : Type} [Field F] [Finite F] (hKf : PiField π p f F)
    (hq : ModThree π (p ^ f)) (h2 : 2 < p ^ f) (heven : Even (p ^ f))
    (h9 : p ^ f % 9 ≠ 0 ∧ p ^ f % 9 ≠ 1 ∧ p ^ f % 9 ≠ 8)
    {β : MulAut (PSimple 3 K)} (hβdef : β = chevAut 3 K ⟨x₁, hx1N⟩)
    (hin : InnerAutAt π p f F β) : False := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hx13 : x₁ ^ 3 = 1 := hBel.2 x₁ hx1B
  have hx23 : x₂ ^ 3 = 1 := hBel.2 x₂ hx2B
  have hap1 : IsPGroup 3 (Subgroup.zpowers x₁) :=
    isPGroup_zpowers_of_pow_eq_one (p := 3) hx13
  have hL1star : GLAPComponent 3
      (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns.fixSub β)
      (chevTransfer 3 K L₁) := by
    rw [CFSG.HardMathSupport.Dickson.Sec6.fixSub_eq_fixSubgroup_up34, hβdef]
    exact glaPComponent_chevTransfer hp hx1N hap1 hL1comp
  rcases inner_lay_iso hKf hq h2 hin with hnone | ⟨Φ, hΦ, hall⟩
  · exact absurd hL1star (hnone _)
  · have hL1eq : chevTransfer 3 K L₁ = Φ.range := hall _ hL1star
    have hcard2 : card2 3 L₁ = p ^ f :=
      t158NormL3_card2_eq hL1comp hx1N hx13 hKf hq h2 heven hΦ hL1eq hL1star
    have hcent : centCard2 3 L₁ x₂ ^ 3 = card2 3 L₁ := by
      rcases hfg2 with hF | hG
      · exact hI X (K ⊓ Subgroup.centralizer ({x₁} : Set X)) L₁ x₂ hL1comp hL1chev hx23 hF
      · exact hG.2.2
    have hcube : centCard2 3 L₁ x₂ ^ 3 = p ^ f := hcent.trans hcard2
    have hc := cube_mod_nine (centCard2 3 L₁ x₂)
    rw [hcube] at hc
    rcases hc with h | h | h
    · exact h9.1 h
    · exact h9.2.1 h
    · exact h9.2.2 h

theorem t158NormL3_of (hI : ∀ (X : Type) [Group X] [Finite X], I91CentPartAt X 3) :
    T158NormL3 := by
  intro X _ _ K B x₁ x₂ L₁ L₂ hH hInn hExc
  obtain ⟨hKcomp, hBel, hx1B, hx2B, -, -, hL1comp, hL1chev, hL2comp, -, hfg1, hfg2⟩ :=
    t158m_unpack hH
  have hp : Nat.Prime 3 := Nat.prime_three
  have hx1N : x₁ ∈ Subgroup.normalizer (K : Set X) :=
    hInn.1 (Subgroup.mem_sup_left (Subgroup.mem_zpowers x₁))
  rcases hExc with ⟨F, hFf, hFfin, hFeven, hFmod, ⟨eSL⟩⟩ |
      ⟨F, hFf, hFfin, q, hqeven, hFcard, hqmod, ⟨eSU⟩⟩
  · letI := hFf
    letI := hFfin
    have hc : Nat.card F % 3 = 1 := by
      rcases hFmod with h | h <;> omega
    obtain ⟨p, f, hKf, hq, h2⟩ := exists_true_data F hc
    have hFpc : Nat.card F = p ^ f := by rw [hKf.card, piCard, Bool.cond_true]
    let e : PSimple 3 K ≃* (↥(slPi true 3 (p ^ f) F) ⧸
        Subgroup.center ↥(slPi true 3 (p ^ f) F)) :=
      QuotientGroup.congr _ _ eSL (Subgroup.map_center_eq eSL)
    have heven : Even (p ^ f) := by rw [← hFpc]; exact hFeven
    have h9 : p ^ f % 9 ≠ 0 ∧ p ^ f % 9 ≠ 1 ∧ p ^ f % 9 ≠ 8 := by
      have hmod := hFmod
      rw [hFpc] at hmod
      rcases hmod with h | h
      · refine ⟨by omega, by omega, by omega⟩
      · refine ⟨by omega, by omega, by omega⟩
    have hβ3 : chevAut 3 K ⟨x₁, hx1N⟩ ^ 3 = 1 :=
      chevAut_pow_eq_one 3 K hx1N (hBel.2 x₁ hx1B)
    by_cases hβ1 : chevAut 3 K ⟨x₁, hx1N⟩ = 1
    · exact t158NormL3_beta_one hKcomp hL2comp hfg1 hx1N hβ1
    · rcases dichot_proj_field hKf hq h2 e hβ3 hβ1 with hF | hin
      · exact t158NormL3_false_of_fieldAut hKf hF h9
      · exact t158NormL3_inner hI hBel hx1B hx2B hL1comp hL1chev hfg2 hx1N hKf hq h2
          heven h9 rfl hin
  · letI := hFf
    letI := hFfin
    obtain ⟨p, f, rfl, ⟨hF⟩⟩ := exists_unitaryFieldData hFcard
    have hKf : PiField false p f F :=
      ⟨hF.prime, hF.one_le, by simpa [piCard, pow_mul, mul_comm] using hF.card⟩
    have heven : Even (p ^ f) := hqeven
    have hq : ModThree false (p ^ f) := by
      change p ^ f % 3 = 2
      rcases hqmod with h | h <;> omega
    have h9 : p ^ f % 9 ≠ 0 ∧ p ^ f % 9 ≠ 1 ∧ p ^ f % 9 ≠ 8 := by
      rcases hqmod with h | h
      · refine ⟨by omega, by omega, by omega⟩
      · refine ⟨by omega, by omega, by omega⟩
    by_cases h2 : 2 < p ^ f
    · let e : PSimple 3 K ≃* (↥(slPi false 3 (p ^ f) F) ⧸
          Subgroup.center ↥(slPi false 3 (p ^ f) F)) :=
        QuotientGroup.congr _ _ eSU (Subgroup.map_center_eq eSU)
      have hβ3 : chevAut 3 K ⟨x₁, hx1N⟩ ^ 3 = 1 :=
        chevAut_pow_eq_one 3 K hx1N (hBel.2 x₁ hx1B)
      by_cases hβ1 : chevAut 3 K ⟨x₁, hx1N⟩ = 1
      · exact t158NormL3_beta_one hKcomp hL2comp hfg1 hx1N hβ1
      · rcases dichot_proj_field hKf hq h2 e hβ3 hβ1 with hF | hin
        · exact t158NormL3_false_of_fieldAut hKf hF h9
        · exact t158NormL3_inner hI hBel hx1B hx2B hL1comp hL1chev hfg2 hx1N hKf hq h2
            heven h9 rfl hin
    ·
      have hq2 : p ^ f = 2 := by
        have hle : p ^ f ≤ 2 := Nat.le_of_not_lt h2
        have hpos : 0 < p ^ f := pow_pos hKf.prime.pos f
        obtain ⟨k, hk⟩ := heven
        omega
      have hp2eq : p = 2 := (Nat.prime_two.pow_eq_iff.mp hq2).1
      have hf1 : f = 1 := (Nat.prime_two.pow_eq_iff.mp hq2).2
      have hcard4 : Nat.card F = (2 : ℕ) ^ (2 * 1) := by
        rw [hF.card, hp2eq, hf1]
      have hsol : Group.IsSolvable ↥(StatedSU 3 (p ^ f) F) := by
        rw [hq2]
        exact CFSG.Quasithin.isSolvable_statedSU_one (by simpa using hcard4)
      haveI : Group.IsSolvable ↥(StatedSU 3 (p ^ f) F) := hsol
      exact CFSG.ClassicalInvolution.not_isSolvable_of_open_isQuasisimple
        (isQuasisimple_pQuot_of_glaPComponent hp hKcomp)
        (Group.isSolvable_of_surjective (f := eSU.symm.toMonoidHom) eSU.symm.surjective)

theorem t158NormL3_holds : T158NormL3 :=
  t158NormL3_of fun X _ _ =>
    FP.i91CentPartAt_of_stOrder Nat.prime_three (by norm_num)
      (FQ.s10StOrderAt Nat.prime_three (by norm_num))

end CFSG.LocalAnalysis.GLTheoremA.T158

end
