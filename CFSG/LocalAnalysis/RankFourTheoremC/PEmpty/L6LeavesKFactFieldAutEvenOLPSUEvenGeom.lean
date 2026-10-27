module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenOLPSUEvenCount
public import CFSG.LieType.BorelTits.FormFlag

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KFAE

open CFSG.LieType.BorelTits (ReflForm)

variable {F V : Type*} [Field F] [Finite F] [CharP F 2] [AddCommGroup V] [Module F V]
  [Module.Finite F V]

theorem eq_bot_of_isometry_normalizing_ppd (β : ReflForm F V) {r d : ℕ} (hr : r.Prime)
    (hd : 2 ≤ d) (hdim : Module.finrank F V = d + 1) (hdvd : r ∣ Nat.card F ^ d - 1)
    (hmin : ∀ k : ℕ, 0 < k → k < d → ¬ r ∣ Nat.card F ^ k - 1) (g : V ≃ₗ[F] V) (hgr : g ^ r = 1)
    (hg1 : g ≠ 1) (hgβ : ∀ u v, β.β (g u) (g v) = β.β u v) (R : Subgroup (V ≃ₗ[F] V))
    (hR2 : IsPGroup 2 R) (hRβ : ∀ x ∈ R, ∀ u v, β.β (x u) (x v) = β.β u v)
    (hRg : ∀ x : V ≃ₗ[F] V, x ∈ R ↔ g * x * g⁻¹ ∈ R) : R = ⊥ := by
  by_contra hR1
  have hq : 1 ≤ Nat.card F := Nat.card_pos
  set C : Submodule F V := LinearMap.ker (g.toLinearMap - LinearMap.id) with hCdef
  have hC : ∀ x : V, x ∈ C ↔ g x = x := fun x => by
    simp [C, LinearMap.mem_ker, sub_eq_zero]
  have hcount : ∀ W : Submodule F V, (∀ v ∈ W, g v ∈ W) →
      Nat.card F ^ Module.finrank F W ≡ Nat.card F ^ Module.finrank F ↥(W ⊓ C) [MOD r] :=
    fun W hW => pow_modEq_pow_finrank_fixed hr g hgr W hW
  have horder : ∀ {a b : ℕ}, a ≤ b → Nat.card F ^ a ≡ Nat.card F ^ b [MOD r] → d ∣ b - a :=
    fun hab h => dvd_sub_of_pow_modEq hq (by omega) hdvd hmin hab h
  have hC1 : Module.finrank F C = 1 := by
    have h1 := hcount ⊤ (fun _ _ => Submodule.mem_top)
    rw [finrank_top, top_inf_eq, hdim] at h1
    have hle : Module.finrank F C ≤ d + 1 := hdim ▸ Submodule.finrank_le C
    obtain ⟨s, hs⟩ := horder hle h1.symm
    have hs2 : s < 2 := by
      by_contra hs2
      push Not at hs2
      have : d * 2 ≤ d * s := Nat.mul_le_mul_left d hs2
      omega
    interval_cases s
    · exfalso
      have hCtop : C = ⊤ := Submodule.eq_top_of_finrank_eq (by omega)
      apply hg1
      ext x
      exact (hC x).1 (hCtop ▸ Submodule.mem_top)
    · omega
  have hCperp : ¬ C ≤ β.perp C := by
    intro hle
    have hMg : ∀ u ∈ β.perp C, g u ∈ β.perp C := by
      intro u hu c hc
      have hgc : g c = c := (hC c).1 hc
      have h1 : β.β c (g u) = β.β (g c) (g u) := by rw [hgc]
      rw [h1, hgβ]
      exact hu c hc
    have hdimM : Module.finrank F (β.perp C) = d := by
      have := β.finrank_perp C
      omega
    have h1 := hcount (β.perp C) hMg
    rw [inf_eq_right.2 hle, hdimM, hC1] at h1
    have h2 := horder (by omega : 1 ≤ d) h1.symm
    have h3 := Nat.le_of_dvd (by omega) h2
    omega
  let W : Submodule F V :=
    { carrier := {w | ∀ x ∈ R, x w = w}
      add_mem' := fun {a b} ha hb x hx => by rw [map_add, ha x hx, hb x hx]
      zero_mem' := fun x _ => map_zero x
      smul_mem' := fun c w hw x hx => by rw [map_smul, hw x hx] }
  have hW : ∀ w : V, w ∈ W ↔ ∀ x ∈ R, x w = w := fun w => Iff.rfl
  have hRg1 : ∀ x ∈ R, g⁻¹ * x * g ∈ R := fun x hx => (hRg _).2 (by
    have : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rw [this]
    exact hx)
  have hRg2 : ∀ x ∈ R, g * x * g⁻¹ ∈ R := fun x hx => (hRg x).1 hx
  have hWg : ∀ w ∈ W, g w ∈ W := by
    intro w hw x hx
    have h1 : (g⁻¹ * x * g) w = w := hw _ (hRg1 x hx)
    have h2 : g⁻¹ (x (g w)) = w := by simpa [LinearEquiv.mul_apply] using h1
    have h3 : g (g⁻¹ (x (g w))) = x (g w) := by
      have : (g * g⁻¹) (x (g w)) = x (g w) := by simp
      simpa [LinearEquiv.mul_apply] using this
    rw [← h3, h2]
  have hWg' : ∀ w ∈ W, g⁻¹ w ∈ W := by
    intro w hw x hx
    have h1 : (g * x * g⁻¹) w = w := hw _ (hRg2 x hx)
    have h2 : g (x (g⁻¹ w)) = w := by simpa [LinearEquiv.mul_apply] using h1
    have h3 : g⁻¹ (g (x (g⁻¹ w))) = x (g⁻¹ w) := by
      have : (g⁻¹ * g) (x (g⁻¹ w)) = x (g⁻¹ w) := by simp
      simpa [LinearEquiv.mul_apply] using this
    rw [← h3, h2]
  have hWtop : W ≠ ⊤ := by
    intro hWt
    apply hR1
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    ext w
    exact (hW w).1 (hWt ▸ Submodule.mem_top) x hx
  have hU0 : β.perp W ≠ ⊥ := by
    intro hU
    apply hWtop
    have h := β.perp_perp W
    rw [hU, β.perp_bot] at h
    exact h.symm
  have hUR : ∀ x ∈ R, ∀ u ∈ β.perp W, x u ∈ β.perp W := by
    intro x hx u hu w hw
    have hxw : x w = w := (hW w).1 hw x hx
    have h1 := hRβ x hx w u
    rw [hxw] at h1
    rw [h1]
    exact hu w hw
  have hUg : ∀ u ∈ β.perp W, g u ∈ β.perp W := by
    intro u hu w hw
    have h1 := hgβ (g⁻¹ w) u
    have h2 : g (g⁻¹ w) = w := by
      have : (g * g⁻¹) w = w := by simp
      simpa [LinearEquiv.mul_apply] using this
    rw [h2] at h1
    rw [h1]
    exact hu _ (hWg' w hw)
  obtain ⟨v, hvU, hv0, hvR⟩ := exists_ne_zero_fixed_of_stable R hR2 (β.perp W) hUR hU0
  let D : Submodule F V := W ⊓ β.perp W
  have hvD : v ∈ D := ⟨(hW v).2 hvR, hvU⟩
  have hD0 : D ≠ ⊥ := fun h => hv0 (by
    have := hvD
    rw [h] at this
    exact (Submodule.mem_bot F).1 this)
  have hDg : ∀ u ∈ D, g u ∈ D := fun u hu => ⟨hWg u hu.1, hUg u hu.2⟩
  have hDiso : D ≤ β.perp D := fun d₂ hd₂ d₁ hd₁ => hd₂.2 d₁ hd₁.1
  by_cases hCD : C ≤ D
  · exact hCperp (hCD.trans (hDiso.trans (β.perp_antitone hCD)))
  · have hDC : Module.finrank F ↥(D ⊓ C) = 0 := by
      by_contra hne
      apply hCD
      have hle : D ⊓ C ≤ C := inf_le_right
      have heq : D ⊓ C = C := Submodule.eq_of_le_of_finrank_eq hle (by
        have := Submodule.finrank_mono hle
        omega)
      exact heq ▸ inf_le_left
    have h1 := hcount D hDg
    rw [hDC] at h1
    have h2 := horder (Nat.zero_le _) h1.symm
    have hdpos : 0 < Module.finrank F D := Submodule.one_le_finrank_iff.2 hD0
    have h3 : d ≤ Module.finrank F D := Nat.le_of_dvd hdpos (by simpa using h2)
    have h4 := β.finrank_perp D
    have h5 := Submodule.finrank_mono hDiso
    omega

end KFAE

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
