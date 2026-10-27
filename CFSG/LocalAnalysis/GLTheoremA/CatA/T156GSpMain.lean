module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GSpFix
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GLinMain

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T156

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.RankThree.PartOne.KCSpComm

section Symplectic

variable {p : ℕ}

theorem geomBody_sp4 (hp : p.Prime) (hp2 : p ≠ 2) {t : LargeEvenLieTag} (ht : t = .B ∨ t = .C)
    {n : ℕ} (hn : 2 ≤ n) (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2 ^ n) :
    GeomBody p ⟨t, 2, n⟩ (LargeEvenProj (LargeEvenSpGroup K 2))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K 2)) (LargeEvenGSpSet K 2))
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSpGroup K 2))) := by
  haveI : CharP K 2 := CFSG.ComponentClassification.RankTwoClassical.charP_two_of_card hK
  refine geomBody_of_field (by rcases ht with rfl | rfl <;> simp) fun hS hna f hf hord => ?_
  obtain ⟨σ, hσf⟩ := RecipeFieldSp.exists_fieldAut_of_mem hf
  have hσ : orderOf σ = p := by
    rw [← orderOf_injective (fieldAut 2 K) FieldFixSp.fieldAut_injective σ, ← hσf]
    exact hord
  obtain ⟨hdvd, -⟩ := card_descentField Nat.prime_two (by omega : 1 ≤ n) hK hσ
  obtain ⟨c, hc⟩ := hdvd
  have hnp : n / p = c := by
    rw [hc]
    exact Nat.mul_div_cancel_left c hp.pos
  have hc1 : 1 ≤ c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · rw [h0, mul_zero] at hc
      omega
    · exact h0
  by_cases hc1' : c = 1
  ·
    rw [hc1', mul_one] at hc
    subst hc
    have hlab₀ : LargeEvenInLambda2 ⟨.B2der, 0, 1⟩ := ⟨le_rfl, rfl, rfl⟩
    exact fixAlt_of_raw hlab₀ (Sp.exists_raw_b2der hp hp2 hK hS hna hf hord)
  ·
    have hnp2 : 2 ≤ n / p := by rw [hnp]; omega
    have hlab₀ : LargeEvenInLambda2 ⟨t, 2, n / p⟩ := by
      refine ⟨by rw [hnp]; exact hc1, ?_⟩
      rcases ht with rfl | rfl <;> dsimp only <;> exact ⟨le_rfl, fun _ => hnp2⟩
    have hraw : CFSG.Assembly.LargeEvenRawDatum ⟨t, 2, n / p⟩ =
        LargeEvenRecipeSymplectic 2 (2 ^ (n / p)) false := by
      rcases ht with rfl | rfl <;> rfl
    refine fixAlt_of_raw hlab₀ ?_
    rw [hraw]
    exact Sp.exists_fixGeom' (m := 2) le_rfl (by omega) hp hp2 hK (fun h => hc1' (hnp.symm.trans h.2)) hS
      hna hf hord

theorem cAll_geomBody_BC2 (hp : p.Prime) (hp2 : p ≠ 2) {t : LargeEvenLieTag} (ht : t = .B ∨ t = .C)
    {n : ℕ} (hn : 2 ≤ n) : MI.CAll ⟨t, 2, n⟩ (GeomBody p ⟨t, 2, n⟩) := by
  intro Q hQ
  have hraw : ∀ Q', CFSG.Assembly.LargeEvenRawDatum ⟨t, 2, n⟩ Q' =
      LargeEvenRecipeSymplectic 2 (2 ^ n) false Q' := by
    intro Q'
    rcases ht with rfl | rfl <;> rfl
  rw [hraw] at hQ ⊢
  exact NbrGraphSymplectic.recipeSymplectic_all (fun K _ _ hK => geomBody_sp4 hp hp2 ht hn K hK) hQ

end Symplectic

@[expose] def RestLabel₄ (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .D ∧ 4 ≤ lab.rank ∧ ¬ p ∣ 2 ^ lab.n - 1) ∨
    lab.tag = .G2 ∨ lab.tag = .triD4 ∨ lab.tag = .twB2 ∨ lab.tag = .twF4 ∨
    (lab.tag = .E6 ∧ (p = 3 ∨ ¬ p ∣ 2 ^ lab.n - 1)) ∨ lab.tag = .twE6

@[expose] def T156Rest₄ : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → RestLabel₄ p lab →
    MI.CAll lab (GeomBody p lab)

theorem t156Rest₃_of_rest₄ (h : T156Rest₄) : T156Rest₃ := by
  intro p hp hp2 lab hlab hr
  obtain ⟨t, l, n⟩ := lab
  unfold RestLabel₃ at hr
  dsimp only at hr
  rcases hr with ⟨h1, h2⟩ | h1
  · subst h2
    have hn : 2 ≤ n := by
      rcases h1 with rfl | rfl
      · exact hlab.2.2 rfl
      · exact hlab.2.2 rfl
    exact cAll_geomBody_BC2 hp hp2 h1 hn
  · exact h p hp hp2 ⟨t, l, n⟩ hlab h1

section Core


theorem t156FactOmega_of_rest₄ (h : T156Rest₄) (p : ℕ) : T156FactOmega p :=
  t156FactOmega_of_rest₃ (t156Rest₃_of_rest₄ h) p

end Core

end CFSG.LocalAnalysis.GLTheoremA.T156

end
