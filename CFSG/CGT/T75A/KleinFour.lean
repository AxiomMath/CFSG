module

public import CFSG.CGT.T75A.RootPair
public import CFSG.CGT.T75A.InnerCase

public section

namespace CFSG.CGT.T75A

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.CGT.Timmesfeld75 CFSG.BenderSuzuki
open CFSG.ComponentClassification.AschbacherToolkit.Bender

section Abstract

variable {D : Type} [Group D] [Finite D]

theorem klein_four_bound {X₀ X₁ : Set D}
    (htwo : ∀ P : Subgroup (MulAut D), IsPGroup 2 P →
      (∀ β ∈ P, (∀ x ∈ X₀, β x = x) ∧ ∀ x ∈ X₁, β x = x) → Nat.card P ≤ 2)
    {γ δ : MulAut D} (hγ : γ * γ = 1) (hδ : δ * δ = 1) (hc : γ * δ = δ * γ)
    (hγ₀ : ∀ x ∈ X₀, γ x = x) (hγ₁ : ∀ x ∈ X₁, γ x = x) (hδ₀ : ∀ x ∈ X₀, δ x = x)
    (hδ₁ : ∀ x ∈ X₁, δ x = x) : γ = 1 ∨ δ = 1 ∨ γ = δ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hγ1, hδ1, hγδ⟩ := hcon
  have h1 : γ * (γ * δ) = δ := by rw [← mul_assoc, hγ, one_mul]
  have h2 : δ * γ = γ * δ := hc.symm
  have h3 : δ * (γ * δ) = γ := by rw [hc, ← mul_assoc, hδ, one_mul]
  have h4 : (γ * δ) * γ = δ := by rw [hc, mul_assoc, hγ, mul_one]
  have h5 : (γ * δ) * δ = γ := by rw [mul_assoc, hδ, mul_one]
  have h6 : (γ * δ) * (γ * δ) = 1 := by rw [← mul_assoc, h4, hδ]
  let P : Subgroup (MulAut D) :=
    { carrier := {x | x = 1 ∨ x = γ ∨ x = δ ∨ x = γ * δ}
      mul_mem' := by
        rintro a b (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl)
        · simp
        · simp
        · simp
        · simp
        · simp
        · left; exact hγ
        · right; right; right; exact rfl
        · right; right; left; simpa using h1
        · simp
        · right; right; right; exact h2
        · left; exact hδ
        · right; left; exact h3
        · simp
        · right; right; left; exact h4
        · right; left; exact h5
        · left; exact h6
      one_mem' := Or.inl rfl
      inv_mem' := by
        rintro a (rfl | rfl | rfl | rfl)
        · simp
        · right; left; exact inv_eq_of_mul_eq_one_right hγ
        · right; right; left; exact inv_eq_of_mul_eq_one_right hδ
        · right; right; right; exact inv_eq_of_mul_eq_one_right h6 }
  have hP2 : IsPGroup 2 P := by
    intro x
    refine ⟨1, ?_⟩
    obtain ⟨x, hx⟩ := x
    apply Subtype.ext
    rcases hx with rfl | rfl | rfl | rfl
    · simp
    · simpa [pow_two] using hγ
    · simpa [pow_two] using hδ
    · simpa [pow_two] using h6
  have hfix : ∀ β ∈ P, (∀ x ∈ X₀, β x = x) ∧ ∀ x ∈ X₁, β x = x := by
    rintro β (rfl | rfl | rfl | rfl)
    · exact ⟨fun x _ => rfl, fun x _ => rfl⟩
    · exact ⟨hγ₀, hγ₁⟩
    · exact ⟨hδ₀, hδ₁⟩
    · exact ⟨fun x hx => by rw [MulAut.mul_apply, hδ₀ x hx, hγ₀ x hx],
        fun x hx => by rw [MulAut.mul_apply, hδ₁ x hx, hγ₁ x hx]⟩
  have hle := htwo P hP2 hfix
  have hinj : Function.Injective (![⟨1, Or.inl rfl⟩, ⟨γ, Or.inr (Or.inl rfl)⟩,
      ⟨δ, Or.inr (Or.inr (Or.inl rfl))⟩] : Fin 3 → P) := by
    intro i j hij
    have := congrArg Subtype.val hij
    fin_cases i <;> fin_cases j <;> simp at this ⊢
    · exact hγ1 this.symm
    · exact hδ1 this.symm
    · exact hγ1 this
    · exact hγδ this
    · exact hδ1 this
    · exact hγδ this.symm
  have : Finite (MulAut D) :=
    Finite.of_injective (fun e : MulAut D => (e : D → D)) fun e₁ e₂ h => MulEquiv.ext (congrFun h)
  have h3le := Nat.card_le_card_of_injective _ hinj
  simp at h3le
  omega

end Abstract

section Model

variable {D : Type} [Group D] [Finite D] {f : ℕ}

theorem exists_conj_sylow_pair (hf : 2 ≤ f) (hD : StatedClassicalModel D .PSU 3 2 f)
    {S S' S₀ S₁ : Sylow 2 D} (h' : S' ≠ S) (h₁ : S₁ ≠ S₀) :
    ∃ g : D, g • S = S₀ ∧ g • S' = S₁ := by
  have hB := benderBorel_of_model hf hD
  have hK := isBenderGroup_of_model hf hD
  have hcard : Nat.card (Sylow 2 D) = Nat.card (S₀ : Subgroup D) + 1 := by
    rw [card_sylow_psu3 hD, (hB S₀).2.2.2.2, ← pow_mul, mul_comm]
  obtain ⟨g₁, hg₁⟩ := MulAction.exists_smul_eq D S S₀
  have h2 : g₁ • S' ≠ S₀ := fun h => h' (by
    have h3 : S' = g₁⁻¹ • S₀ := by rw [← h, inv_smul_smul]
    rw [h3, ← hg₁, inv_smul_smul])
  obtain ⟨u, huS₀, hu⟩ := exists_smul_eq_of_card_sylow hK S₀ hcard h2 h₁
  refine ⟨u * g₁, ?_, ?_⟩
  · rw [mul_smul, hg₁]
    exact Sylow.smul_eq_iff_mem_normalizer.2 (Subgroup.le_normalizer huS₀)
  · rw [mul_smul]
    exact hu

theorem klein_four_root_pair_sc (hf : 2 ≤ f) (hD : StatedClassicalModel D .PSU 3 2 f)
    {S S' : Sylow 2 D} (hSS' : S' ≠ S) {α β : MulAut D} (hα : α * α = 1) (hβ : β * β = 1)
    (hc : α * β = β * α)
    (hαT : ∀ x ∈ sylowCenter (S : Subgroup D), α x ∈ sylowCenter (S : Subgroup D))
    (hαT' : ∀ x ∈ sylowCenter (S' : Subgroup D), α x ∈ sylowCenter (S' : Subgroup D))
    (hβT : ∀ x ∈ sylowCenter (S : Subgroup D), β x ∈ sylowCenter (S : Subgroup D))
    (hβT' : ∀ x ∈ sylowCenter (S' : Subgroup D), β x ∈ sylowCenter (S' : Subgroup D)) :
    α = 1 ∨ β = 1 ∨ α = β := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hα1, hβ1, hαβ⟩ := hcon
  have hB := benderBorel_of_model hf hD
  have hK := isBenderGroup_of_model hf hD
  have hinf : (S : Subgroup D) ⊓ S' = ⊥ := sylow_inf_eq_bot hK hSS'.symm
  have houter : ∀ γ : MulAut D, γ * γ = 1 → γ ≠ 1 →
      (∀ x ∈ sylowCenter (S : Subgroup D), γ x ∈ sylowCenter (S : Subgroup D)) →
      (∀ x ∈ sylowCenter (S' : Subgroup D), γ x ∈ sylowCenter (S' : Subgroup D)) →
      γ ∉ (MulAut.conj : D →* MulAut D).range := by
    intro γ hγγ hγ1 hγT hγT' hin
    obtain ⟨t, htT, rfl⟩ := inner_involution_eq_conj_root hf hD γ hγγ hin hγT
    have ht2 : t * t = 1 := by
      have := (benderBorel_sylowCenter hB S).2.1 t htT
      rwa [pow_two] at this
    have htT' : t ∈ sylowCenter (S' : Subgroup D) :=
      mem_root_of_involution hf hD ht2 (fun x hx => by
        simpa [MulAut.conj_apply] using hγT' x hx)
    have ht1 : t = 1 := by
      have : t ∈ (S : Subgroup D) ⊓ S' := ⟨(mem_sylowCenter.1 htT).1, (mem_sylowCenter.1 htT').1⟩
      rw [hinf] at this
      exact Subgroup.mem_bot.1 this
    exact hγ1 (by rw [ht1, map_one])
  have hα2 : orderOf α = 2 := orderOf_eq_prime (by rw [pow_two]; exact hα) hα1
  have hαout := houter α hα hα1 hαT hαT'
  have hβout := houter β hβ hβ1 hβT hβT'
  obtain ⟨S₀, S₁, hne, -, -, hrig⟩ := exists_fixed_root_pair hf hD α hα2 hαout
  have hS₁₀ : S₁ ≠ S₀ := fun h => hne (by rw [h])
  obtain ⟨g, hgS, hgS'⟩ := exists_conj_sylow_pair hf hD hSS' hS₁₀
  have hcen : ∀ (R : Sylow 2 D) (R₀ : Sylow 2 D), g • R = R₀ →
      sylowCenter (R₀ : Subgroup D) =
        (sylowCenter (R : Subgroup D)).map (MulAut.conj g).toMonoidHom := by
    intro R R₀ h
    rw [← h]
    exact sylowCenter_map_equiv (MulAut.conj g) (R : Subgroup D)
  have hαS := fix_sylowCenter hf hD α hα hαT
  have hαS' := fix_sylowCenter hf hD α hα hαT'
  have hβS := fix_sylowCenter hf hD β hβ hβT
  have hβS' := fix_sylowCenter hf hD β hβ hβT'
  set c : MulAut D := MulAut.conj g with hcdef
  have hfix : ∀ (γ : MulAut D) (R R₀ : Sylow 2 D), g • R = R₀ →
      (∀ x ∈ sylowCenter (R : Subgroup D), γ x = x) →
      ∀ x ∈ sylowCenter (R₀ : Subgroup D), (c * γ * c⁻¹) x = x := by
    intro γ R R₀ h hγ x hx
    rw [hcen R R₀ h] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have h1 : c⁻¹ (c y) = y := by
      rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
    change c (γ (c⁻¹ (c y))) = c y
    rw [h1, hγ y hy]
  have hconj : ∀ γ δ : MulAut D, γ * γ = 1 → δ * δ = 1 → γ * δ = δ * γ →
      (c * γ * c⁻¹) * (c * γ * c⁻¹) = 1 ∧ (c * δ * c⁻¹) * (c * δ * c⁻¹) = 1 ∧
        (c * γ * c⁻¹) * (c * δ * c⁻¹) = (c * δ * c⁻¹) * (c * γ * c⁻¹) := by
    intro γ δ hγ hδ hcomm
    refine ⟨?_, ?_, ?_⟩
    · calc (c * γ * c⁻¹) * (c * γ * c⁻¹) = c * (γ * γ) * c⁻¹ := by group
        _ = 1 := by rw [hγ]; group
    · calc (c * δ * c⁻¹) * (c * δ * c⁻¹) = c * (δ * δ) * c⁻¹ := by group
        _ = 1 := by rw [hδ]; group
    · calc (c * γ * c⁻¹) * (c * δ * c⁻¹) = c * (γ * δ) * c⁻¹ := by group
        _ = c * (δ * γ) * c⁻¹ := by rw [hcomm]
        _ = (c * δ * c⁻¹) * (c * γ * c⁻¹) := by group
  obtain ⟨h1, h2, h3⟩ := hconj α β hα hβ hc
  rcases klein_four_bound (X₀ := (sylowCenter (S₀ : Subgroup D) : Set D))
    (X₁ := (sylowCenter (S₁ : Subgroup D) : Set D))
    (fun P hP hPfix => hrig P hP hPfix) h1 h2 h3
    (hfix α S S₀ hgS hαS) (hfix α S' S₁ hgS' hαS') (hfix β S S₀ hgS hβS)
    (hfix β S' S₁ hgS' hβS') with h | h | h
  · exact hα1 (by
      have : α = c⁻¹ * (c * α * c⁻¹) * c := by group
      rw [this, h]
      group)
  · exact hβ1 (by
      have : β = c⁻¹ * (c * β * c⁻¹) * c := by group
      rw [this, h]
      group)
  · exact hαβ (by
      have e1 : α = c⁻¹ * (c * α * c⁻¹) * c := by group
      have e2 : β = c⁻¹ * (c * β * c⁻¹) * c := by group
      rw [e1, e2, h])

theorem klein_four_root_pair (hf : 2 ≤ f) (hD : StatedClassicalModel D .PSU 3 2 f)
    {S S' : Sylow 2 D}
    (hTT' : (Subgroup.center (S' : Subgroup D)).map (S' : Subgroup D).subtype ≠
      (Subgroup.center (S : Subgroup D)).map (S : Subgroup D).subtype)
    {α β : MulAut D} (hα : α * α = 1) (hβ : β * β = 1) (hc : α * β = β * α)
    (hαT : ∀ x ∈ (Subgroup.center (S : Subgroup D)).map (S : Subgroup D).subtype,
      α x ∈ (Subgroup.center (S : Subgroup D)).map (S : Subgroup D).subtype)
    (hαT' : ∀ x ∈ (Subgroup.center (S' : Subgroup D)).map (S' : Subgroup D).subtype,
      α x ∈ (Subgroup.center (S' : Subgroup D)).map (S' : Subgroup D).subtype)
    (hβT : ∀ x ∈ (Subgroup.center (S : Subgroup D)).map (S : Subgroup D).subtype,
      β x ∈ (Subgroup.center (S : Subgroup D)).map (S : Subgroup D).subtype)
    (hβT' : ∀ x ∈ (Subgroup.center (S' : Subgroup D)).map (S' : Subgroup D).subtype,
      β x ∈ (Subgroup.center (S' : Subgroup D)).map (S' : Subgroup D).subtype) :
    α = 1 ∨ β = 1 ∨ α = β := by
  simp only [map_center_eq_sylowCenter] at hTT' hαT hαT' hβT hβT'
  exact klein_four_root_pair_sc hf hD (fun h => hTT' (by rw [h])) hα hβ hc hαT hαT' hβT hβT'

end Model

end CFSG.CGT.T75A
