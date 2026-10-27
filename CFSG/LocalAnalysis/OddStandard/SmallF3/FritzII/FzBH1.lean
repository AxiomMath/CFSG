module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzBM1

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G] [Finite G] {c : Bool} {t : G} {T₂ P : Subgroup G}
  {x₁ x₂ q s lam : G} {β : ℕ → G}

theorem fzb_emb_of_conj (hβ : FzbChart c T₂ P x₁ x₂ t q s lam β)
    (hlt : ∀ x < 1024, ∀ y < 1024, fzbMul c x y < 1024) {g : G} (hgu : g⁻¹ * β 832 * g = t)
    (hg : ∀ x ∈ T₂ ⊓ invCent (β 832), g⁻¹ * x * g ∈ T₂) :
    ∃ ψ : ℕ → ℕ, FzbIsEmb c 832 ψ ∧
      ∀ x < 1024, fzbMul c x 832 = fzbMul c 832 x → ψ x < 1024 ∧ β (ψ x) = g⁻¹ * β x * g := by
  classical
  have h832 : (832 : ℕ) < 1024 := by norm_num
  have h128 : (128 : ℕ) < 1024 := by norm_num
  have hex : ∀ x : ℕ, ∃ y : ℕ,
      (x < 1024 → fzbMul c x 832 = fzbMul c 832 x → y < 1024 ∧ β y = g⁻¹ * β x * g) := by
    intro x
    by_cases hx : x < 1024 ∧ fzbMul c x 832 = fzbMul c 832 x
    · obtain ⟨hxlt, hxcomm⟩ := hx
      have haux : β x * β 832 = β 832 * β x := (fzb_chart_comm hβ hlt hxlt h832).mp hxcomm
      have hmem : β x ∈ T₂ ⊓ invCent (β 832) :=
        ⟨hβ.mem x hxlt,
          Subgroup.mem_centralizer_singleton_iff.mpr haux⟩
      obtain ⟨y, hy, hyβ⟩ := hβ.surj _ (hg _ hmem)
      exact ⟨y, fun _ _ => ⟨hy, hyβ⟩⟩
    · exact ⟨0, fun hxlt hxcomm => absurd ⟨hxlt, hxcomm⟩ hx⟩
  choose ψ hψ using hex
  refine ⟨ψ, ?_, hψ⟩
  refine ⟨?map_u, ?map_one, ?lt, ?comm_t, ?map_mul, ?inj⟩
  · have hc : fzbMul c 832 832 = fzbMul c 832 832 := rfl
    obtain ⟨hu, hβu⟩ := hψ 832 h832 hc
    have heq : β (ψ 832) = β 128 := by rw [hβu, hgu, ← hβ.t_eq]
    exact hβ.inj (ψ 832) hu 128 h128 heq
  · have h0 : (0 : ℕ) < 1024 := by norm_num
    have hc : fzbMul c 0 832 = fzbMul c 832 0 :=
      (fzb_chart_comm hβ hlt h0 h832).mpr (by rw [hβ.one]; group)
    obtain ⟨h0', hβ0⟩ := hψ 0 h0 hc
    have heq : β (ψ 0) = β 0 := by rw [hβ0, hβ.one]; group
    exact hβ.inj (ψ 0) h0' 0 h0 heq
  · intro x hx hc
    exact (hψ x hx hc).1
  · intro x hx hc
    obtain ⟨hx', hβx⟩ := hψ x hx hc
    have haux : β x * β 832 = β 832 * β x := (fzb_chart_comm hβ hlt hx h832).mp hc
    apply (fzb_chart_comm hβ hlt hx' h128).mpr
    rw [hβx, hβ.t_eq, ← hgu]
    calc g⁻¹ * β x * g * (g⁻¹ * β 832 * g)
        = g⁻¹ * (β x * β 832) * g := by group
      _ = g⁻¹ * (β 832 * β x) * g := by rw [haux]
      _ = g⁻¹ * β 832 * g * (g⁻¹ * β x * g) := by group
  · intro x hx y hy hcx hcy
    have hx' : ψ x < 1024 := (hψ x hx hcx).1
    have hy' : ψ y < 1024 := (hψ y hy hcy).1
    have hxy' : fzbMul c x y < 1024 := hlt x hx y hy
    have haux : β x * β 832 = β 832 * β x := (fzb_chart_comm hβ hlt hx h832).mp hcx
    have hauy : β y * β 832 = β 832 * β y := (fzb_chart_comm hβ hlt hy h832).mp hcy
    have hcommxy : fzbMul c (fzbMul c x y) 832 = fzbMul c 832 (fzbMul c x y) := by
      apply (fzb_chart_comm hβ hlt hxy' h832).mpr
      rw [hβ.mul x hx y hy]
      calc β x * β y * β 832 = β x * (β y * β 832) := by rw [mul_assoc]
        _ = β x * (β 832 * β y) := by rw [hauy]
        _ = β x * β 832 * β y := by rw [mul_assoc]
        _ = β 832 * β x * β y := by rw [haux]
        _ = β 832 * (β x * β y) := by rw [mul_assoc]
    have hψxy' : ψ (fzbMul c x y) < 1024 := (hψ (fzbMul c x y) hxy' hcommxy).1
    have h1 : β (ψ (fzbMul c x y)) = g⁻¹ * (β x * β y) * g := by
      rw [(hψ (fzbMul c x y) hxy' hcommxy).2, hβ.mul x hx y hy]
    have h2 : β (fzbMul c (ψ x) (ψ y)) = g⁻¹ * β x * g * (g⁻¹ * β y * g) := by
      rw [hβ.mul (ψ x) hx' (ψ y) hy', (hψ x hx hcx).2, (hψ y hy hcy).2]
    apply hβ.inj (ψ (fzbMul c x y)) hψxy' (fzbMul c (ψ x) (ψ y))
      (hlt (ψ x) hx' (ψ y) hy')
    rw [h1, h2]
    group
  · intro x hx y hy hcx hcy heq
    have hx'' := (hψ x hx hcx).2
    have hy'' := (hψ y hy hcy).2
    have hgx : g⁻¹ * β x * g = g⁻¹ * β y * g := by rw [← hx'', ← hy'', heq]
    have hβeq : β x = β y := mul_left_cancel (mul_right_cancel hgx)
    exact hβ.inj x hx y hy hβeq

end CFSG.OddStandard.SmallF3.FritzII
