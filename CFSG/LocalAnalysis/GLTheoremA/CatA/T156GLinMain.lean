module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GLinSmall
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GUniMain
public import CFSG.LocalAnalysis.StandardType.GGNbrGraphFieldLinear

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T156

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType
open CFSG.LocalAnalysis.GLTheoremA.FQ

section Linear

variable {p : ℕ}

theorem geomBody_l2 (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (htag : lab.tag ≠ .triD4) {m : ℕ} (hm : 2 ≤ m) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ m) :
    GeomBody p lab (LargeEvenProj (LargeEvenSLGroup (Fin 2) K))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin 2) K)) Set.univ)
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin 2) K))) := by
  refine fun _ _ => ⟨fun _ f hf hord => ?_, fun h' => absurd h' htag⟩
  obtain ⟨σ, hσf⟩ := LinearFieldFix.exists_induced hf
  have hσord : orderOf σ = p :=
    (LinearFieldFix.orderOf_eq_of_mk_matAct le_rfl (LinearFieldFix.slMapStable 2 K) hσf).trans hord
  obtain ⟨hdvd, -⟩ := card_fixedPoints_field (m := m) (by omega) hK σ
  rw [hσord] at hdvd
  obtain ⟨c, hc⟩ := hdvd
  have hmp : m / p = c := by
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
    exact Or.inl (Lin.fixAlt_l2 hp hp2 hK hσord hσf)
  ·
    have hmp2 : 2 ≤ m / p := by omega
    have hlab₀ : LargeEvenInLambda2 ⟨.A, 1, m / p⟩ := by
      refine ⟨by rw [hmp]; exact hc1, ?_⟩
      dsimp only
      exact ⟨le_rfl, fun _ => hmp2⟩
    exact Or.inl (fixAlt_of_raw hlab₀ (Lin.exists_raw_linear' (d := 2) le_rfl
      (Lin.slOK_of_two_pow hm hK) (by omega) hK (fun k _ _ hk => Lin.slOK_of_two_pow hmp2 hk)
      hf hord))

theorem cAll_geomBody_A1 (hp : p.Prime) (hp2 : p ≠ 2) {n : ℕ} (hn : 2 ≤ n) :
    MI.CAll ⟨.A, 1, n⟩ (GeomBody p ⟨.A, 1, n⟩) := by
  intro Q hQ
  dsimp only [CFSG.Assembly.LargeEvenRawDatum] at hQ ⊢
  exact NbrGraphLinear.recipeLinear_all (fun K _ _ hK => geomBody_l2 hp hp2 (by simp) hn K hK) hQ

theorem cAll_geomBody_twD2 (hp : p.Prime) (hp2 : p ≠ 2) {n : ℕ} (hn : 1 ≤ n) :
    MI.CAll ⟨.twD, 2, n⟩ (GeomBody p ⟨.twD, 2, n⟩) := by
  intro Q hQ
  dsimp only [CFSG.Assembly.LargeEvenRawDatum] at hQ ⊢
  simp only [↓reduceIte] at hQ ⊢
  exact NbrGraphLinear.recipeLinear_all (fun K _ _ hK => geomBody_l2 hp hp2 (by simp)
    (m := 2 * n) (by omega) K (by rw [hK, ← pow_mul, mul_comm])) hQ

end Linear

@[expose] def RestLabel₃ (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  ((lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = 2) ∨
    (lab.tag = .D ∧ 4 ≤ lab.rank ∧ ¬ p ∣ 2 ^ lab.n - 1) ∨
    lab.tag = .G2 ∨ lab.tag = .triD4 ∨ lab.tag = .twB2 ∨ lab.tag = .twF4 ∨
    (lab.tag = .E6 ∧ (p = 3 ∨ ¬ p ∣ 2 ^ lab.n - 1)) ∨ lab.tag = .twE6

@[expose] def T156Rest₃ : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → RestLabel₃ p lab →
    MI.CAll lab (GeomBody p lab)

theorem t156Rest₂_of_rest₃ (h : T156Rest₃) : T156Rest₂ := by
  intro p hp hp2 lab hlab hr
  obtain ⟨t, l, n⟩ := lab
  have hn : 1 ≤ n := hlab.1
  unfold RestLabel₂ at hr
  dsimp only at hr
  rcases hr with ⟨h1, h2⟩ | h1 | h1 | ⟨h1, h2⟩ | h1 | h1 | h1 | h1 | h1 | h1
  · subst h1
    subst h2
    exact cAll_geomBody_A1 hp hp2 (hlab.2.2 rfl)
  · exact h p hp hp2 ⟨t, l, n⟩ hlab (Or.inl h1)
  · exact h p hp hp2 ⟨t, l, n⟩ hlab (Or.inr (Or.inl h1))
  · subst h1
    subst h2
    exact cAll_geomBody_twD2 hp hp2 hn
  · exact h p hp hp2 ⟨t, l, n⟩ hlab (Or.inr (Or.inr (Or.inl h1)))
  · exact h p hp hp2 ⟨t, l, n⟩ hlab (Or.inr (Or.inr (Or.inr (Or.inl h1))))
  · exact h p hp hp2 ⟨t, l, n⟩ hlab (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1)))))
  · exact h p hp hp2 ⟨t, l, n⟩ hlab (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1))))))
  · exact h p hp hp2 ⟨t, l, n⟩ hlab
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1)))))))
  · exact h p hp hp2 ⟨t, l, n⟩ hlab
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h1)))))))

section Core


theorem t156FactOmega_of_rest₃ (h : T156Rest₃) (p : ℕ) : T156FactOmega p :=
  t156FactOmega_of_rest₂ (t156Rest₂_of_rest₃ h) p

end Core

end CFSG.LocalAnalysis.GLTheoremA.T156

end
