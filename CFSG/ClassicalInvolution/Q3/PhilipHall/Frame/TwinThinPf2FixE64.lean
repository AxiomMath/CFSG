module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf2E64
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf2ConjE64

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

theorem mem_memBar_aH : (aH : AEQ 7) ∈ memBar α0 α0_card true := ⟨aW, aW_mem_memAt, rfl⟩

theorem mem_memBar_bH : (bH : AEQ 7) ∈ memBar α0 α0_card true := ⟨bW, bW_mem_memAt, rfl⟩

theorem fixTrivial_e64_proved : FixTrivial e64Sub e64Sets := by
  intro α hα h4 b σ hσ hfix
  obtain ⟨g, hg, hconj⟩ := member_conj α hα h4 b
  set G : ↥e64Sub := ⟨mkQ 7 g, ⟨g, hg, rfl⟩⟩ with hG
  let σ' : ↥e64Sub →* ↥e64Sub :=
    (MulAut.conj G⁻¹).toMonoidHom.comp (σ.comp (MulAut.conj G).toMonoidHom)
  have hσ'app : ∀ r, σ' r = G⁻¹ * σ (G * r * G⁻¹) * G⁻¹⁻¹ := fun r => rfl
  have hfixM : ∀ y : ↥e64Sub, (y : AEQ 7) ∈ memBar α0 α0_card true → σ' y = y := by
    intro y hy
    have hmem : ((G * y * G⁻¹ : ↥e64Sub) : AEQ 7) ∈ memBar α h4 b := by
      have := hconj _ hy
      simpa [hG] using this
    have := hfix _ hmem
    rw [hσ'app, this]
    group
  have hit : ∀ (k : ℕ) (r : ↥e64Sub), (⇑σ')^[k] r = G⁻¹ * (⇑σ)^[k] (G * r * G⁻¹) * G := by
    intro k
    induction k with
    | zero => intro r; simp only [Function.iterate_zero, id_eq]; group
    | succ k ih =>
      intro r
      rw [Function.iterate_succ_apply', ih, hσ'app, Function.iterate_succ_apply']
      group
  obtain ⟨N, hN⟩ := hσ
  have hσ'N : ∃ a : ℕ, ∀ r, (⇑σ')^[3 ^ a] r = r := ⟨N, fun r => by
    rw [hit, hN]; group⟩
  have hall := fix_core_e64 σ' hσ'N (hfixM _ mem_memBar_aH) (hfixM _ mem_memBar_bH)
  intro r
  have := hall (G⁻¹ * r * G)
  rw [hσ'app] at this
  have h2 : σ r = r := by
    have e : G * (G⁻¹ * r * G) * G⁻¹ = r := by group
    rw [e, inv_inv] at this
    calc σ r = G * (G⁻¹ * σ r * G) * G⁻¹ := by group
      _ = G * (G⁻¹ * r * G) * G⁻¹ := by rw [this]
      _ = r := by group
  exact h2

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf
