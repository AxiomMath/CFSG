module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3Psi

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3

open CFSG.ClassicalInvolution.Q3.Sec13

variable {Γ : Type} [Group Γ]

theorem key_K {S : Subgroup Γ} {z : Γ} {Zc : Subgroup Γ} {Ψ : ↥S →* Multiplicative Sp4.V4}
    (hS : Q8D8Facts S z) (hΨ : PsiSpec S z Ψ) (hZc : ∀ k ∈ Zc, ∀ g : Γ, g * k = k * g)
    (hz : z ∈ Zc) (hZ2 : ∀ k ∈ Zc, k * k = 1 → k = 1 ∨ k = z)
    (hF1 : ∀ g : Γ, (∀ s ∈ S, g * s = s * g) → g ∈ Zc)
    {g : Γ} (hg : ∀ s ∈ S, g * s * g⁻¹ * s⁻¹ ∈ Zc) :
    ∃ s₀ ∈ S, ∃ k ∈ Zc, g = s₀ * k := by
  classical
  obtain ⟨lam, hlam⟩ : ∃ lam : Γ → Γ, ∀ x, lam x = g * x * g⁻¹ * x⁻¹ :=
    ⟨fun x => g * x * g⁻¹ * x⁻¹, fun _ => rfl⟩
  have hgs : ∀ x : Γ, g * x * g⁻¹ = lam x * x := by
    intro x
    rw [hlam]
    group
  have hlamZ : ∀ x ∈ S, lam x ∈ Zc := fun x hx => by
    rw [hlam]
    exact hg x hx
  have hlam_one : lam 1 = 1 := by
    rw [hlam]
    group
  have hlam_z : lam z = 1 := by
    rw [hlam, hZc z hz g]
    group
  have hmul : ∀ x y : Γ, x ∈ S → y ∈ S → lam (x * y) = lam x * lam y := by
    intro x y hx hy
    have e1 : lam (x * y) = (g * x * g⁻¹) * (g * y * g⁻¹) * (x * y)⁻¹ := by
      rw [hlam]
      group
    have hc : x * lam y = lam y * x := hZc (lam y) (hlamZ y hy) x
    rw [e1, hgs x, hgs y]
    calc lam x * x * (lam y * y) * (x * y)⁻¹
        = lam x * (x * lam y) * y * (x * y)⁻¹ := by group
      _ = lam x * (lam y * x) * y * (x * y)⁻¹ := by rw [hc]
      _ = lam x * lam y := by group
  have hsq : ∀ s ∈ S, lam s * lam s = 1 := by
    intro s hs
    rw [← hmul s s hs hs]
    rcases hS.sq_mem s hs with h | h
    · rw [h, hlam_one]
    · rw [h, hlam_z]
  have hlam_val : ∀ s ∈ S, lam s = 1 ∨ lam s = z := fun s hs =>
    hZ2 (lam s) (hlamZ s hs) (hsq s hs)
  have hlam3 : ∀ s t : S, Ψ s = Ψ t → lam (t : Γ) = lam (s : Γ) := by
    intro s t hst
    have hu : Ψ (s⁻¹ * t) = 1 := by
      rw [map_mul, map_inv, hst]
      exact inv_mul_cancel _
    rcases (hΨ.ker_iff (s⁻¹ * t)).mp hu with h | h
    · rw [Subgroup.coe_mul, Subgroup.coe_inv] at h
      have ht : (t : Γ) = (s : Γ) := (inv_mul_eq_one.mp h).symm
      rw [ht]
    · rw [Subgroup.coe_mul, Subgroup.coe_inv] at h
      have ht : (t : Γ) = (s : Γ) * z := by
        calc (t : Γ) = (s : Γ) * ((s : Γ)⁻¹ * (t : Γ)) := by group
          _ = (s : Γ) * z := by rw [h]
      rw [ht, hmul (s : Γ) z s.2 hS.z_mem, hlam_z, mul_one]
  have hsurj : ∀ b : Multiplicative Sp4.V4, ∃ a : S, Ψ a = b := hΨ.surj
  choose σ hσ using hsurj
  obtain ⟨F, hF⟩ : ∃ F : Sp4.V4 → ZMod 2,
      ∀ w, F w = if lam ((σ (Multiplicative.ofAdd w) : S) : Γ) = 1 then 0 else 1 :=
    ⟨fun w => if lam ((σ (Multiplicative.ofAdd w) : S) : Γ) = 1 then 0 else 1, fun _ => rfl⟩
  have hF_add : ∀ a b : Sp4.V4, F (a + b) = F a + F b := by
    intro a b
    have hsa := (σ (Multiplicative.ofAdd a)).2
    have hsb := (σ (Multiplicative.ofAdd b)).2
    have hΨab : Ψ (σ (Multiplicative.ofAdd a) * σ (Multiplicative.ofAdd b))
        = Ψ (σ (Multiplicative.ofAdd (a + b))) := by
      simp only [map_mul, hσ, ofAdd_add]
    have hl := hlam3 _ _ hΨab
    rw [Subgroup.coe_mul, hmul _ _ hsa hsb] at hl
    simp only [hF, hl]
    rcases hlam_val _ hsa with h1 | h1 <;> rcases hlam_val _ hsb with h2 | h2 <;>
      simp [h1, h2, hS.z_ne_one, hS.z_mul_self] <;> decide
  obtain ⟨c, hc⟩ := dual_V4 F hF_add
  obtain ⟨s₁, hs₁⟩ := hΨ.surj (Multiplicative.ofAdd c)
  have hsc : Multiplicative.toAdd (Ψ s₁) = c := congrArg Multiplicative.toAdd hs₁
  have hiff_gen : ∀ P Q : Prop,
      (if P then (0 : ZMod 2) else 1) = (if Q then 0 else 1) → (P ↔ Q) := by
    intro P Q h
    by_cases hP : P <;> by_cases hQ : Q
    · exact ⟨fun _ => hQ, fun _ => hP⟩
    · rw [if_pos hP, if_neg hQ] at h
      exact absurd h (by decide)
    · rw [if_neg hP, if_pos hQ] at h
      exact absurd h (by decide)
    · exact ⟨fun h' => absurd h' hP, fun h' => absurd h' hQ⟩
  have hE : ∀ s ∈ S, (if lam s = 1 then (0 : ZMod 2) else 1)
      = (if (s₁ : Γ) * s * (s₁ : Γ)⁻¹ * s⁻¹ = 1 then 0 else 1) := by
    intro s hs
    have hA : F (Multiplicative.toAdd (Ψ ⟨s, hs⟩)) = if lam s = 1 then 0 else 1 := by
      rw [hF, hlam3 ⟨s, hs⟩ (σ (Multiplicative.ofAdd (Multiplicative.toAdd (Ψ ⟨s, hs⟩))))
        (by rw [hσ, ofAdd_toAdd])]
    have hB := hΨ.form s₁ ⟨s, hs⟩
    rw [← hA, hc, ← hsc, hB]
  have hiff : ∀ s ∈ S, (lam s = 1 ↔ (s₁ : Γ) * s * (s₁ : Γ)⁻¹ * s⁻¹ = 1) := fun s hs =>
    hiff_gen _ _ (hE s hs)
  have hcomm : ∀ s ∈ S, lam s = (s₁ : Γ) * s * (s₁ : Γ)⁻¹ * s⁻¹ := by
    intro s hs
    have hi := hiff s hs
    rcases hlam_val s hs with h1 | h1 <;>
      rcases hS.comm_mem (s₁ : Γ) s₁.2 s hs with h2 | h2
    · rw [h1, h2]
    · exact absurd (hi.mp h1) (by rw [h2]; exact hS.z_ne_one)
    · exact absurd (hi.mpr h2) (by rw [h1]; exact hS.z_ne_one)
    · rw [h1, h2]
  have hcent : ∀ s ∈ S, (s₁ : Γ) * g * s = s * ((s₁ : Γ) * g) := by
    intro s hs
    have hX : (s₁ : Γ) * g * s * ((s₁ : Γ) * g)⁻¹ * s⁻¹ = 1 := by
      calc (s₁ : Γ) * g * s * ((s₁ : Γ) * g)⁻¹ * s⁻¹
          = (s₁ : Γ) * (g * s * g⁻¹) * (s₁ : Γ)⁻¹ * s⁻¹ := by group
        _ = (s₁ : Γ) * (lam s * s) * (s₁ : Γ)⁻¹ * s⁻¹ := by rw [hgs s]
        _ = ((s₁ : Γ) * lam s) * s * (s₁ : Γ)⁻¹ * s⁻¹ := by group
        _ = (lam s * (s₁ : Γ)) * s * (s₁ : Γ)⁻¹ * s⁻¹ := by
            rw [hZc (lam s) (hlamZ s hs) (s₁ : Γ)]
        _ = lam s * ((s₁ : Γ) * s * (s₁ : Γ)⁻¹ * s⁻¹) := by group
        _ = lam s * lam s := by rw [← hcomm s hs]
        _ = 1 := hsq s hs
    calc (s₁ : Γ) * g * s
        = ((s₁ : Γ) * g * s * ((s₁ : Γ) * g)⁻¹ * s⁻¹) * s * ((s₁ : Γ) * g) := by group
      _ = s * ((s₁ : Γ) * g) := by rw [hX, one_mul]
  have hcentral : (s₁ : Γ) * g ∈ Zc := hF1 ((s₁ : Γ) * g) hcent
  exact ⟨(s₁ : Γ)⁻¹, S.inv_mem s₁.2, (s₁ : Γ) * g, hcentral, by group⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3
