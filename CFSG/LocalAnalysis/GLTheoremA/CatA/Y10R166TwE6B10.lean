module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.ExcE6Cover
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.SplitTwistedE6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U6Mult
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011I61
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwE6A4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwE6B4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwE6B2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Lang.E6Descent
  CFSG.HardMathSupport.Lang.E6Descent.TwistedDiag


theorem exists_mulEquiv_twE6C_quot_of_isLabel {X : Type} [Group X] [Finite X] {lab : GLALabel}
    (hX : HasLabel X (fun l => l = lab)) (ht : lab.tag = .twE6) (hn : 2 ≤ lab.n) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (σ : F ≃+* F),
      Nat.card F = (2 ^ lab.n) ^ 2 ∧ (∀ c, σ c = c ^ (2 ^ lab.n)) ∧
      Nonempty (X ⧸ Subgroup.center X ≃*
        ↥(twE6C (iterateFrobenius (AlgebraicClosure F) 2 lab.n))) := by
  classical
  obtain ⟨-, -, hM⟩ := rk2_model_of_isLabel hX
  obtain ⟨F, hField, hFin, σ, hcard, hσ, ⟨e1⟩⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.exists_twistedE6RootGroup_of_marked (u6_model_twE6 ht hM)
  letI : Field F := hField
  letI : Finite F := hFin
  haveI : Fintype F := Fintype.ofFinite F
  have hcard2 : Nat.card F = 2 ^ (lab.n * 2) := by
    rw [hcard, pow_mul]
  have hcardF : Fintype.card F = 2 ^ (lab.n * 2) := by
    rw [← Nat.card_eq_fintype_card, hcard2]
  have hcharF : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := lab.n * 2) hcardF
  letI : CharP F 2 := hcharF
  let Ω := AlgebraicClosure F
  let Fr : Ω →+* Ω := iterateFrobenius Ω 2 lab.n
  have hFr : ∀ c, Fr c = c ^ (2 ^ lab.n) := fun c => iterateFrobenius_def 2 lab.n c
  refine ⟨F, hField, hFin, hcharF, σ, hcard, hσ, ?_⟩
  have eBC : ↥(twistedE6RootGroup F σ) ≃* ↥(Cgrp F σ.toRingHom Ω) :=
    Subgroup.equivMapOfInjective (graphFixedRootGroup TwistTag.E6 F σ.toRingHom)
      (baseChangeGL (τ := TwistTag.E6.tag) (algebraMap F Ω)) (baseChangeGL_injective _)
  have e2 : ↥(Cgrp F σ.toRingHom Ω) ≃* ↥(twE6C Fr) :=
    (twE6C_equiv_cgrp (ℓ := 2) (f := lab.n) (K := F) (σ := σ.toRingHom) (Ω := Ω)
      (Fr := Fr) Nat.prime_two (by omega) hcard hσ hFr).some.symm.trans
      (MulEquiv.subgroupCongr (Subgroup.ext fun _ => mem_twE6C.symm))
  exact ⟨e1.trans (eBC.trans e2)⟩

theorem twE6_caseB_arith {X : Type} [Group X] [Finite X] {lab : GLALabel}
    (hX : HasLabel X (fun l => l = lab)) (ht : lab.tag = .twE6) (hn : 2 ≤ lab.n)
    (hZ : Subgroup.center X ≠ ⊥) :
    Nat.card (Subgroup.center X) = 3 ∧ 3 ∣ 2 ^ lab.n + 1 ∧ Odd lab.n ∧ 3 ≤ lab.n := by
  have hdvd : Nat.card (Subgroup.center X) ∣ Nat.gcd 3 (2 ^ lab.n + 1) :=
    rk2_card_center_dvd_twE6 hX ht hn
  have h3dvdZ : Nat.card (Subgroup.center X) ∣ 3 := hdvd.trans (Nat.gcd_dvd_left 3 _)
  have hne : Nat.card (Subgroup.center X) ≠ 1 := by
    intro h1
    exact hZ (Subgroup.card_eq_one.1 h1)
  have hcard : Nat.card (Subgroup.center X) = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 h3dvdZ with h1 | h3
    · exact absurd h1 hne
    · exact h3
  have h3gcd : 3 ∣ Nat.gcd 3 (2 ^ lab.n + 1) := hcard ▸ hdvd
  have h3dvd : 3 ∣ 2 ^ lab.n + 1 := h3gcd.trans (Nat.gcd_dvd_right 3 _)
  have hoddn : Odd lab.n := i61_odd_of_three_dvd_two_pow_add_one h3dvd
  refine ⟨hcard, h3dvd, hoddn, ?_⟩
  obtain ⟨k, hk⟩ := hoddn
  omega

theorem evenRank_eq_five_of_center_ne_bot {X : Type} [Group X] [Finite X] {lab : GLALabel}
    (hX : HasLabel X (fun l => l = lab)) (ht : lab.tag = .twE6) (hn : 2 ≤ lab.n)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpdvd : p ∣ 2 ^ lab.n - 1)
    (hr : GLATwoLocalRank p X + 1 = evenRank X) (hZ : Subgroup.center X ≠ ⊥) :
    evenRank X = 5 := by
  obtain ⟨-, h3dvd, -, -⟩ := twE6_caseB_arith hX ht hn hZ
  have hlow : 5 ≤ evenRank X :=
    (rk2_split_low_twE6_cover hX Nat.prime_three (by norm_num) ht hn h3dvd hZ).trans
      (CFSG.RankThreeEvenClassification.Helpers.twoLocalRank_le_evenRank 3
        Nat.prime_three (by norm_num) X)
  have hup : GLATwoLocalRank p X ≤ 4 := by
    have h1 := CFSG.RankThreeEvenClassification.Helpers.twoLocalRank_le_pRank p hp X
    have h2 : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ rk2Mult lab (rk2Ord p lab.n) :=
      rk2_pRank_le_E6_all X lab p hX (Or.inr ht) hp hp2
    have h3 : rk2Ord p lab.n = 1 := rk2Ord_eq_one_iff.2 hpdvd
    have h4 : rk2Mult lab 1 = 4 := by
      simp [rk2Mult, ht, rk2Cnt]
    calc GLATwoLocalRank p X ≤ CFSG.Open.pRank p (⊤ : Subgroup X) := h1
      _ ≤ rk2Mult lab (rk2Ord p lab.n) := h2
      _ = rk2Mult lab 1 := by rw [h3]
      _ = 4 := h4
  omega

theorem eleven_mul_le_twoRank_of_isLabel_twE6 {X : Type} [Group X] [Finite X]
    {lab : GLALabel} (hX : HasLabel X (fun l => l = lab)) (ht : lab.tag = .twE6)
    (hn : 2 ≤ lab.n) (hodd : Odd (Nat.card (Subgroup.center X))) :
    11 * lab.n ≤ twoRank X := by
  classical
  obtain ⟨-, -, hM⟩ := rk2_model_of_isLabel hX
  obtain ⟨F, hField, hFin, σ, hcard, hσ, ⟨e1⟩⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.exists_twistedE6RootGroup_of_marked (u6_model_twE6 ht hM)
  letI : Field F := hField
  letI : Finite F := hFin
  haveI : Fintype F := Fintype.ofFinite F
  have hcard2 : Nat.card F = 2 ^ (lab.n * 2) := by
    rw [hcard, pow_mul]
  have hcardF : Fintype.card F = 2 ^ (lab.n * 2) := by
    rw [← Nat.card_eq_fintype_card, hcard2]
  have hcharF : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := lab.n * 2) hcardF
  letI : CharP F 2 := hcharF
  let π : X →* twistedE6RootGroup F σ :=
    e1.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
  have hπ : Function.Surjective π :=
    e1.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center X))
  have hkerπ : π.ker = Subgroup.center X := by
    change (e1.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))).ker = _
    rw [MonoidHom.ker_comp_of_injective _ _ e1.injective, QuotientGroup.ker_mk']
  have hstep : twoRank ↥(twistedE6RootGroup F σ) ≤ twoRank X :=
    twoRank_le_of_central_quotient π hπ (le_of_eq hkerπ) (by rw [hkerπ]; exact hodd)
  refine (eleven_mul_le_twoRank_graphFixedRootGroup_twE6 (n := lab.n) (by omega) hcard
    (σ := σ.toRingHom) hσ).trans ?_
  exact hstep

end CFSG.LocalAnalysis.GLTheoremA.Y10F

end
