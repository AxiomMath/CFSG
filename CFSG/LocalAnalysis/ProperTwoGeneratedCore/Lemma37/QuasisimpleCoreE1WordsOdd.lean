module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1WordsSubLabels

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

@[expose] def e1H0 (r v : Fin 64) : Prop := v = 0 ∨ v = 40 ∨ v = r ∨ v = c3Mul r 40

instance (r v : Fin 64) : Decidable (e1H0 r v) := by unfold e1H0; infer_instance

@[expose] def e1Cent (r v : Fin 64) : Prop := e1R v ∧ c3Mul v r = c3Mul r v

instance (r v : Fin 64) : Decidable (e1Cent r v) := by unfold e1Cent; infer_instance

@[expose] def e1N (r v : Fin 64) : Prop := e1Cent r v ∧ c3Mul v v = 40

instance (r v : Fin 64) : Decidable (e1N r v) := by unfold e1N; infer_instance

@[expose] def e1H1 (r v : Fin 64) : Prop := e1H0 r v ∨ e1N r v

instance (r v : Fin 64) : Decidable (e1H1 r v) := by unfold e1H1; infer_instance

theorem e1_chain_one : ∀ r : Fin 64, e1Sing r → ∀ v : Fin 64, e1N r v → ∀ w : Fin 64, e1N r w →
    e1H0 r (c3Mul (c3Inv v) w) := by decide +kernel

theorem e1_chain_two : ∀ r : Fin 64, e1Sing r → ∀ v : Fin 64, e1Cent r v → ¬ e1H1 r v →
    ∀ w : Fin 64, e1Cent r w → ¬ e1H1 r w → e1H1 r (c3Mul (c3Inv v) w) := by decide +kernel

theorem e1_chain_three : ∀ r : Fin 64, e1Sing r → ∀ v : Fin 64, e1R v → ¬ e1Cent r v →
    ∀ w : Fin 64, e1R w → ¬ e1Cent r w → e1Cent r (c3Mul (c3Inv v) w) := by decide +kernel

theorem eq_one_of_conj_eq_mul {M : Type*} [Group M] {g w t : M} {k : ℕ} (hk : Odd k)
    (hgk : g ^ k = 1) (ht : g * t * g⁻¹ = t) (ht4 : t ^ 4 = 1) (hw : g * w * g⁻¹ = w * t) :
    t = 1 := by
  have hgt : Commute g t := by
    show g * t = t * g
    calc g * t = g * t * g⁻¹ * g := by group
      _ = t * g := by rw [ht]
  have hpow : ∀ j : ℕ, g ^ j * w * (g ^ j)⁻¹ = w * t ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc g ^ (j + 1) * w * (g ^ (j + 1))⁻¹ = g * (g ^ j * w * (g ^ j)⁻¹) * g⁻¹ := by group
        _ = g * w * g⁻¹ * (g * t ^ j * g⁻¹) := by rw [ih]; group
        _ = w * t * t ^ j := by rw [hw, (hgt.pow_right j).eq, mul_inv_cancel_right]
        _ = w * t ^ (j + 1) := by rw [pow_succ', mul_assoc]
  have htk : t ^ k = 1 := by
    have h := hpow k
    rw [hgk, one_mul, inv_one, mul_one] at h
    exact mul_eq_left.mp h.symm
  have hcop : Nat.Coprime k 4 := by
    simpa using Nat.Coprime.pow_right 2 hk.coprime_two_right
  have h := pow_gcd_eq_one.mpr ⟨htk, ht4⟩
  rwa [hcop.gcd_eq_one, pow_one] at h

namespace CaseC3BCD

variable {G : Type} [Group G] {T Q P₁ S : Subgroup G} {e u y x m : G}
variable {Z : Subgroup G} [Z.Normal] (hb : CaseC3BCD T Q P₁ S e u y x m Z) [Finite G]
include hb

theorem conj_forty_of_normalizes {c : G ⧸ Z}
    (hcR : ∀ s ∈ e1RBar Z u m y x, c * s * c⁻¹ ∈ e1RBar Z u m y x) :
    c * caseC3Word Z u m y x 40 * c⁻¹ = caseC3Word Z u m y x 40 := by
  obtain ⟨w₁, hw₁, h₁⟩ :=
    hb.mem_e1RBar_iff.mp (hcR _ (hb.caseC3Word_mem_e1RBar_iff.mpr e1R_nine.1))
  have hsq : c * caseC3Word Z u m y x 40 * c⁻¹ = caseC3Word Z u m y x (c3Mul w₁ w₁) := by
    rw [← hb.caseC3Word_mul, h₁, ← e1R_nine.2, ← hb.caseC3Word_mul]
    group
  rcases e1R_mul_self w₁ hw₁ with h | h
  · exfalso
    rw [h, caseC3Word_zero] at hsq
    have h40 : caseC3Word Z u m y x 40 = 1 := by
      rw [show caseC3Word Z u m y x 40 = c⁻¹ * (c * caseC3Word Z u m y x 40 * c⁻¹) * c by group,
        hsq]
      group
    exact absurd (hb.caseC3Word_eq_one_iff.mp h40) (by decide)
  · rw [hsq, h]

theorem exists_conj_sing {c : G ⧸ Z}
    (hcR : ∀ s ∈ e1RBar Z u m y x, c * s * c⁻¹ ∈ e1RBar Z u m y x) {gf gef : Bool}
    (hlab : ∀ v, CaseC3.Genuine Z (caseC3Word Z u m y x v) ↔ e1Gen gf gef v = true)
    {v : Fin 64} (hv : e1Sing v) (hvg : e1Gen gf gef v = true) :
    ∃ v', e1Sing v' ∧ e1Gen gf gef v' = true ∧
      c * caseC3Word Z u m y x v * c⁻¹ = caseC3Word Z u m y x v' := by
  obtain ⟨hvR, hss, h1, hz⟩ := hb.sing_iff.mpr hv
  obtain ⟨v', -, hv'⟩ := hb.mem_e1RBar_iff.mp (hcR _ hvR)
  have hinj : ∀ a b : G ⧸ Z, c * a * c⁻¹ = c * b * c⁻¹ → a = b := fun a b h =>
    mul_left_cancel (mul_right_cancel h)
  refine ⟨v', hb.sing_iff.mp ⟨hv' ▸ hcR _ hvR, ?_, fun h => h1 (hinj _ _ ?_), fun h => hz ?_⟩,
    (hlab v').mp ?_, hv'.symm⟩
  · rw [hv', show c * caseC3Word Z u m y x v * c⁻¹ * (c * caseC3Word Z u m y x v * c⁻¹) =
      c * (caseC3Word Z u m y x v * caseC3Word Z u m y x v) * c⁻¹ by group, hss]
    group
  · rw [← hv', h]
    group
  · exact hinj _ _ (by rw [← hv', h, hb.conj_forty_of_normalizes hcR])
  · rw [hv']
    have h' := CaseC3.genuine_conj Z ((hlab v).mpr hvg) c⁻¹
    rwa [inv_inv] at h'

theorem commute_of_odd {g : G ⧸ Z} {k : ℕ} (hk : Odd k) (hgk : g ^ k = 1)
    (hgR : ∀ s ∈ e1RBar Z u m y x, g * s * g⁻¹ ∈ e1RBar Z u m y x) {r : G ⧸ Z}
    (hr : r ∈ e1RBar Z u m y x) (hrr : r * r = 1) (hr1 : r ≠ 1)
    (hrz : r ≠ caseC3Word Z u m y x 40)
    (hgr : g * r * g⁻¹ = r ∨ g * r * g⁻¹ = r * caseC3Word Z u m y x 40) :
    ∀ s ∈ e1RBar Z u m y x, g * s = s * g := by
  obtain ⟨r₀, -, rfl⟩ := hb.mem_e1RBar_iff.mp hr
  have hr₀ : e1Sing r₀ := hb.sing_iff.mp ⟨hr, hrr, hr1, hrz⟩
  have himg : ∀ v, e1R v → ∃ v', e1R v' ∧
      g * caseC3Word Z u m y x v * g⁻¹ = caseC3Word Z u m y x v' := fun v hv => by
    obtain ⟨v', hv', h⟩ :=
      hb.mem_e1RBar_iff.mp (hgR _ (hb.caseC3Word_mem_e1RBar_iff.mpr hv))
    exact ⟨v', hv', h.symm⟩
  have hcm : ∀ a b : G ⧸ Z, g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := fun a b => by
    group
  have hinj : ∀ a b : G ⧸ Z, g * a * g⁻¹ = g * b * g⁻¹ → a = b := fun a b h =>
    mul_left_cancel (mul_right_cancel h)
  have hstep : ∀ v v', g * caseC3Word Z u m y x v * g⁻¹ = caseC3Word Z u m y x v' →
      g * caseC3Word Z u m y x (c3Mul (c3Inv v) v') * g⁻¹ =
        caseC3Word Z u m y x (c3Mul (c3Inv v) v') →
      g * caseC3Word Z u m y x v * g⁻¹ = caseC3Word Z u m y x v := by
    intro v v' hv' hF
    have h1 := eq_one_of_conj_eq_mul hk hgk hF (hb.pow_four_eq_one (hb.caseC3Word_mem _))
      (w := caseC3Word Z u m y x v) (by rw [hv', hb.caseC3Word_mul, c3Mul_c3Inv_mul])
    rw [hb.caseC3Word_eq_one_iff] at h1
    have h2 := c3Mul_c3Inv_mul v v'
    rw [h1, c3Mul_zero_right] at h2
    rw [hv', h2]
  have hF40 := hb.conj_forty_of_normalizes hgR
  have hFr : g * caseC3Word Z u m y x r₀ * g⁻¹ = caseC3Word Z u m y x r₀ := by
    rcases hgr with h | h
    · exact h
    · refine hstep r₀ (c3Mul r₀ 40) (by rw [h, hb.caseC3Word_mul]) ?_
      rw [c3Inv_mul_mul]
      exact hF40
  have hH0 : ∀ v, e1H0 r₀ v → g * caseC3Word Z u m y x v * g⁻¹ = caseC3Word Z u m y x v := by
    rintro v (rfl | rfl | rfl | rfl)
    · rw [caseC3Word_zero]
      group
    · exact hF40
    · exact hFr
    · rw [← hb.caseC3Word_mul, hcm, hFr, hF40]
  have hcomm : ∀ v v', g * caseC3Word Z u m y x v * g⁻¹ = caseC3Word Z u m y x v' →
      c3Mul v r₀ = c3Mul r₀ v → c3Mul v' r₀ = c3Mul r₀ v' := by
    intro v v' hv' hc
    rw [← hb.caseC3Word_inj, ← hb.caseC3Word_mul, ← hb.caseC3Word_mul, ← hv', ← hFr, ← hcm,
      ← hcm, hb.caseC3Word_mul, hb.caseC3Word_mul, hc]
  have hN : ∀ v, e1N r₀ v → g * caseC3Word Z u m y x v * g⁻¹ = caseC3Word Z u m y x v := by
    rintro v ⟨⟨hvR, hvc⟩, hvv⟩
    obtain ⟨v', hv'R, hv'⟩ := himg v hvR
    have hv'v' : c3Mul v' v' = 40 := by
      rw [← hb.caseC3Word_inj, ← hb.caseC3Word_mul, ← hv', ← hcm, hb.caseC3Word_mul, hvv, hF40]
    exact hstep v v' hv' (hH0 _ (e1_chain_one r₀ hr₀ v ⟨⟨hvR, hvc⟩, hvv⟩ v'
      ⟨⟨hv'R, hcomm v v' hv' hvc⟩, hv'v'⟩))
  have hH1 : ∀ v, e1H1 r₀ v → g * caseC3Word Z u m y x v * g⁻¹ = caseC3Word Z u m y x v :=
    fun v hv => hv.elim (hH0 v) (hN v)
  have hC : ∀ v, e1Cent r₀ v → g * caseC3Word Z u m y x v * g⁻¹ = caseC3Word Z u m y x v := by
    rintro v ⟨hvR, hvc⟩
    by_cases hv1 : e1H1 r₀ v
    · exact hH1 v hv1
    obtain ⟨v', hv'R, hv'⟩ := himg v hvR
    have hv'1 : ¬ e1H1 r₀ v' := fun h => hv1 (by
      rwa [show v = v' from hb.caseC3Word_inj.mp (hinj _ _ (hv'.trans (hH1 v' h).symm))])
    exact hstep v v' hv' (hH1 _ (e1_chain_two r₀ hr₀ v ⟨hvR, hvc⟩ hv1 v'
      ⟨hv'R, hcomm v v' hv' hvc⟩ hv'1))
  have hall : ∀ v, e1R v → g * caseC3Word Z u m y x v * g⁻¹ = caseC3Word Z u m y x v := by
    intro v hvR
    by_cases hvc : e1Cent r₀ v
    · exact hC v hvc
    obtain ⟨v', hv'R, hv'⟩ := himg v hvR
    have hv'c : ¬ e1Cent r₀ v' := fun h => hvc (by
      rwa [show v = v' from hb.caseC3Word_inj.mp (hinj _ _ (hv'.trans (hC v' h).symm))])
    exact hstep v v' hv' (hC _ (e1_chain_three r₀ hr₀ v hvR hvc v' hv'R hv'c))
  intro s hs
  obtain ⟨v, hv, rfl⟩ := hb.mem_e1RBar_iff.mp hs
  calc g * caseC3Word Z u m y x v = g * caseC3Word Z u m y x v * g⁻¹ * g := by group
    _ = caseC3Word Z u m y x v * g := by rw [hall v hv]

end CaseC3BCD

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
