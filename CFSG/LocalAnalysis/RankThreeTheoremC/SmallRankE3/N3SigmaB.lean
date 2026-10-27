module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3Q8D8

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3

open CFSG.ClassicalInvolution.Q3.Sec13

variable {Γ : Type} [Group Γ]

theorem sigmaB_conj_mem {Zc : Subgroup Γ} (hZc : ∀ k ∈ Zc, ∀ g : Γ, g * k = k * g)
    {k : Γ} (hk : k ∈ Zc) (g : Γ) : g * k * g⁻¹ = k := by
  rw [hZc k hk g, mul_inv_cancel_right]

theorem sigmaB_decomp {S Zc : Subgroup Γ} (hZc : ∀ k ∈ Zc, ∀ g : Γ, g * k = k * g)
    {g : Γ} (hg : g ∈ Subgroup.normalizer ((S ⊔ Zc : Subgroup Γ) : Set Γ))
    {s : Γ} (hs : s ∈ S) :
    ∃ s' ∈ S, ∃ k ∈ Zc, g * s * g⁻¹ = s' * k := by
  haveI : Zc.Normal := ⟨fun n hn x => by rw [sigmaB_conj_mem hZc hn x]; exact hn⟩
  have hmem : g * s * g⁻¹ ∈ S ⊔ Zc :=
    (Subgroup.mem_set_normalizer_iff.mp hg s).mp ((le_sup_left : S ≤ S ⊔ Zc) hs)
  obtain ⟨s', hs', k, hk, e⟩ := Subgroup.mem_sup_of_normal_right.mp hmem
  exact ⟨s', hs', k, hk, e.symm⟩

theorem sigmaB_symp_nondeg : ∀ x : Sp4.V4, (∀ y : Sp4.V4, Sp4.symp x y = 0) → x = 0 := by
  unfold Sp4.symp
  decide

theorem sigmaB_psi_one_of_comm {S : Subgroup Γ} {z : Γ} {Ψ : ↥S →* Multiplicative Sp4.V4}
    (hΨ : PsiSpec S z Ψ) (c : ↥S)
    (hc : ∀ t : ↥S, (c : Γ) * (t : Γ) * (c : Γ)⁻¹ * (t : Γ)⁻¹ = 1) : Ψ c = 1 := by
  have h0 : ∀ y : Sp4.V4, Sp4.symp (Multiplicative.toAdd (Ψ c)) y = 0 := by
    intro y
    obtain ⟨t, ht⟩ := hΨ.surj (Multiplicative.ofAdd y)
    have hy : Multiplicative.toAdd (Ψ t) = y := by simp [ht]
    rw [← hy, hΨ.form c t, if_pos (hc t)]
  have hx : Multiplicative.toAdd (Ψ c) = 0 := sigmaB_symp_nondeg _ h0
  simpa using congrArg Multiplicative.ofAdd hx

theorem sigmaB_psi_eq {S Zc : Subgroup Γ} {z : Γ} {Ψ : ↥S →* Multiplicative Sp4.V4}
    (hΨ : PsiSpec S z Ψ) (hZc : ∀ k ∈ Zc, ∀ g : Γ, g * k = k * g)
    {a b : ↥S} (hab : (a : Γ)⁻¹ * (b : Γ) ∈ Zc) : Ψ a = Ψ b := by
  have hc : ((a⁻¹ * b : ↥S) : Γ) ∈ Zc := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv]; exact hab
  have h1 : Ψ (a⁻¹ * b) = 1 := by
    apply sigmaB_psi_one_of_comm hΨ
    intro t
    rw [(hZc _ hc (t : Γ)).symm]
    group
  rw [map_mul, map_inv] at h1
  exact inv_mul_eq_one.mp h1

theorem sigmaB_inv_mul_mem {S Zc : Subgroup Γ} {z : Γ} {Ψ : ↥S →* Multiplicative Sp4.V4}
    (hΨ : PsiSpec S z Ψ) (hz : z ∈ Zc) {a b : ↥S} (hab : Ψ a = Ψ b) :
    (a : Γ)⁻¹ * (b : Γ) ∈ Zc := by
  have h1 : Ψ (a⁻¹ * b) = 1 := by
    rw [map_mul, map_inv, hab]
    exact inv_mul_cancel _
  have hcoe : ((a⁻¹ * b : ↥S) : Γ) = (a : Γ)⁻¹ * (b : Γ) := by simp
  rcases (hΨ.ker_iff (a⁻¹ * b)).mp h1 with h2 | h2
  · rw [← hcoe, h2]; exact Zc.one_mem
  · rw [← hcoe, h2]; exact hz

theorem actsAs_unique {S : Subgroup Γ} {z : Γ} {Zc : Subgroup Γ}
    {Ψ : ↥S →* Multiplicative Sp4.V4}
    (hΨ : PsiSpec S z Ψ) (hZc : ∀ k ∈ Zc, ∀ g : Γ, g * k = k * g)
    {g : Γ} (hg : g ∈ Subgroup.normalizer ((S ⊔ Zc : Subgroup Γ) : Set Γ))
    {φ φ' : Sp4.V4 ≃+ Sp4.V4} (h : ActsAs S Zc Ψ g φ) (h' : ActsAs S Zc Ψ g φ') : φ = φ' := by
  refine AddEquiv.ext fun w => ?_
  obtain ⟨s, hs⟩ := hΨ.surj (Multiplicative.ofAdd w)
  obtain ⟨s', hs', k, hk, e⟩ := sigmaB_decomp hZc hg s.2
  have hw : Multiplicative.toAdd (Ψ s) = w := by simp [hs]
  have e1 := h s ⟨s', hs'⟩ k hk e
  have e2 := h' s ⟨s', hs'⟩ k hk e
  calc φ w = φ (Multiplicative.toAdd (Ψ s)) := by rw [hw]
    _ = Multiplicative.toAdd (Ψ ⟨s', hs'⟩) := e1
    _ = φ' (Multiplicative.toAdd (Ψ s)) := e2.symm
    _ = φ' w := by rw [hw]

theorem actsAs_one {S : Subgroup Γ} {z : Γ} {Zc : Subgroup Γ} {Ψ : ↥S →* Multiplicative Sp4.V4}
    (hS : Q8D8Facts S z) (hΨ : PsiSpec S z Ψ) (hZc : ∀ k ∈ Zc, ∀ g : Γ, g * k = k * g) :
    ActsAs S Zc Ψ 1 (AddEquiv.refl _) := by
  intro s s' k hk h
  have h1 : (s' : Γ)⁻¹ * (s : Γ) = k := by
    simp only [one_mul, inv_one, mul_one] at h
    rw [h, inv_mul_cancel_left]
  have h2 : Ψ s' = Ψ s := sigmaB_psi_eq hΨ hZc (by rw [h1]; exact hk)
  rw [AddEquiv.refl_apply, h2]

theorem actsAs_mul {S : Subgroup Γ} {z : Γ} {Zc : Subgroup Γ}
    {Ψ : ↥S →* Multiplicative Sp4.V4}
    (hΨ : PsiSpec S z Ψ) (hZc : ∀ k ∈ Zc, ∀ g : Γ, g * k = k * g)
    {g h : Γ} (hg : g ∈ Subgroup.normalizer ((S ⊔ Zc : Subgroup Γ) : Set Γ))
    (hh : h ∈ Subgroup.normalizer ((S ⊔ Zc : Subgroup Γ) : Set Γ))
    {φ ψ : Sp4.V4 ≃+ Sp4.V4} (hφ : ActsAs S Zc Ψ g φ) (hψ : ActsAs S Zc Ψ h ψ) :
    ActsAs S Zc Ψ (g * h) (ψ.trans φ) := by
  intro s s' k hk hsk
  obtain ⟨s₁, hs₁, k₁, hk₁, e₁⟩ := sigmaB_decomp hZc hh s.2
  obtain ⟨s₂, hs₂, k₂, hk₂, e₂⟩ := sigmaB_decomp hZc hg hs₁
  have hψ' := hψ s ⟨s₁, hs₁⟩ k₁ hk₁ e₁
  have hφ' := hφ ⟨s₁, hs₁⟩ ⟨s₂, hs₂⟩ k₂ hk₂ e₂
  have key : (s' : Γ) * k = s₂ * (k₂ * k₁) := by
    calc (s' : Γ) * k = g * h * s * (g * h)⁻¹ := hsk.symm
      _ = g * (h * s * h⁻¹) * g⁻¹ := by group
      _ = g * (s₁ * k₁) * g⁻¹ := by rw [e₁]
      _ = g * s₁ * (k₁ * g⁻¹) := by simp only [mul_assoc]
      _ = g * s₁ * (g⁻¹ * k₁) := by rw [← hZc k₁ hk₁ g⁻¹]
      _ = g * s₁ * g⁻¹ * k₁ := by simp only [mul_assoc]
      _ = s₂ * k₂ * k₁ := by rw [e₂]
      _ = s₂ * (k₂ * k₁) := by simp only [mul_assoc]
  have hm : (s' : Γ)⁻¹ * (s₂ : Γ) ∈ Zc := by
    have e3 : (s' : Γ)⁻¹ * (s₂ : Γ) = k * (k₂ * k₁)⁻¹ := by
      calc (s' : Γ)⁻¹ * (s₂ : Γ) = (s' : Γ)⁻¹ * (s₂ * (k₂ * k₁)) * (k₂ * k₁)⁻¹ := by group
        _ = (s' : Γ)⁻¹ * ((s' : Γ) * k) * (k₂ * k₁)⁻¹ := by rw [key]
        _ = k * (k₂ * k₁)⁻¹ := by group
    rw [e3]
    exact Zc.mul_mem hk (Zc.inv_mem (Zc.mul_mem hk₂ hk₁))
  have hΨs : Ψ s' = Ψ ⟨s₂, hs₂⟩ := sigmaB_psi_eq (a := s') (b := ⟨s₂, hs₂⟩) hΨ hZc hm
  rw [AddEquiv.trans_apply, hψ', hφ', hΨs]

theorem actsAs_refl_iff {S : Subgroup Γ} {z : Γ} {Zc : Subgroup Γ}
    {Ψ : ↥S →* Multiplicative Sp4.V4}
    (hS : Q8D8Facts S z) (hΨ : PsiSpec S z Ψ) (hZc : ∀ k ∈ Zc, ∀ g : Γ, g * k = k * g)
    (hz : z ∈ Zc) {g : Γ} (hg : g ∈ Subgroup.normalizer ((S ⊔ Zc : Subgroup Γ) : Set Γ))
    {φ : Sp4.V4 ≃+ Sp4.V4} (h : ActsAs S Zc Ψ g φ) :
    φ = AddEquiv.refl _ ↔ ∀ s ∈ S, g * s * g⁻¹ * s⁻¹ ∈ Zc := by
  constructor
  · intro hφ s hs
    obtain ⟨s', hs', k, hk, e⟩ := sigmaB_decomp hZc hg hs
    have h1 := h ⟨s, hs⟩ ⟨s', hs'⟩ k hk e
    rw [hφ, AddEquiv.refl_apply] at h1
    have hΨeq : Ψ ⟨s, hs⟩ = Ψ ⟨s', hs'⟩ := Multiplicative.toAdd.injective h1
    have hc : (s : Γ)⁻¹ * s' ∈ Zc := sigmaB_inv_mul_mem hΨ hz hΨeq
    have hcs : (s' : Γ) * (s : Γ)⁻¹ = (s : Γ)⁻¹ * s' := by
      calc (s' : Γ) * (s : Γ)⁻¹ = (s : Γ) * ((s : Γ)⁻¹ * s') * (s : Γ)⁻¹ := by group
        _ = ((s : Γ)⁻¹ * s') * (s : Γ) * (s : Γ)⁻¹ := by rw [hZc _ hc (s : Γ)]
        _ = (s : Γ)⁻¹ * s' := by group
    have e' : g * s * g⁻¹ * s⁻¹ = ((s : Γ)⁻¹ * s') * k := by
      calc g * s * g⁻¹ * s⁻¹ = (s' : Γ) * k * (s : Γ)⁻¹ := by rw [e]
        _ = (s' : Γ) * ((s : Γ)⁻¹ * k) := by rw [mul_assoc, hZc k hk ((s : Γ)⁻¹)]
        _ = ((s' : Γ) * (s : Γ)⁻¹) * k := (mul_assoc _ _ _).symm
        _ = ((s : Γ)⁻¹ * s') * k := by rw [hcs]
    rw [e']
    exact Zc.mul_mem hc hk
  · intro H
    refine AddEquiv.ext fun w => ?_
    rw [AddEquiv.refl_apply]
    obtain ⟨s, hs⟩ := hΨ.surj (Multiplicative.ofAdd w)
    have hk := H (s : Γ) s.2
    have hsk : g * (s : Γ) * g⁻¹ = (s : Γ) * (g * (s : Γ) * g⁻¹ * (s : Γ)⁻¹) := by
      rw [hZc _ hk (s : Γ)]
      group
    have e := h s s _ hk hsk
    have hw : Multiplicative.toAdd (Ψ s) = w := by simp [hs]
    calc φ w = φ (Multiplicative.toAdd (Ψ s)) := by rw [hw]
      _ = Multiplicative.toAdd (Ψ s) := e
      _ = w := hw

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3
