module

public import CFSG.LocalAnalysis.SectionRank.SignLines

public section

namespace CFSG.SectionRank

open CFSG.Open

variable {G Q : Type*} [Group G] [Group Q]

@[expose] def conjRestrict (P : Subgroup G) (g : G) (h₁ : ∀ x ∈ P, g * x * g⁻¹ ∈ P)
    (h₂ : ∀ x ∈ P, g⁻¹ * x * g ∈ P) : P ≃* P where
  toFun x := ⟨g * x * g⁻¹, h₁ x x.2⟩
  invFun x := ⟨g⁻¹ * x * g, h₂ x x.2⟩
  left_inv x := Subtype.ext (by simp only; group)
  right_inv x := Subtype.ext (by simp only; group)
  map_mul' x y := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem conjRestrict_apply (P : Subgroup G) (g : G) (h₁ : ∀ x ∈ P, g * x * g⁻¹ ∈ P)
    (h₂ : ∀ x ∈ P, g⁻¹ * x * g ∈ P) (x : P) :
    ((conjRestrict P g h₁ h₂ x : P) : G) = g * x * g⁻¹ := rfl

variable {p : ℕ} [hp : Fact p.Prime]

theorem inv_conj_of_sign {ψ : Multiplicative (Fin 3 → ZMod p) →* Q} {s : Fin 3 → ZMod p}
    (hs : s * s = 1) {d : Q}
    (hd : ∀ v, d * ψ v * d⁻¹ = ψ (Multiplicative.ofAdd (s * Multiplicative.toAdd v))) (v) :
    d⁻¹ * ψ v * d = ψ (Multiplicative.ofAdd (s * Multiplicative.toAdd v)) := by
  have h := hd (Multiplicative.ofAdd (s * Multiplicative.toAdd v))
  rw [toAdd_ofAdd, ← mul_assoc, hs, one_mul, ofAdd_toAdd] at h
  rw [← h]
  group

theorem three_le_pRank_of_sign_lines [Finite G] (hp2 : p ≠ 2) (A : Subgroup G) [A.Normal]
    (hAZ : A ≤ Subgroup.center G) (ρ : G →* Q) (hρ : Function.Surjective ρ) (hker : ρ.ker = A)
    (ψ : Multiplicative (Fin 3 → ZMod p) →* Q) (hψ : Function.Injective ψ) (d₀ d₁ : Q)
    (h₀ : ∀ v, d₀ * ψ v * d₀⁻¹ =
      ψ (Multiplicative.ofAdd (![1, -1, -1] * Multiplicative.toAdd v)))
    (h₁ : ∀ v, d₁ * ψ v * d₁⁻¹ =
      ψ (Multiplicative.ofAdd (![-1, -1, 1] * Multiplicative.toAdd v))) :
    3 ≤ pRank p (⊤ : Subgroup G) := by
  have hs₀ : (![1, -1, -1] : Fin 3 → ZMod p) * ![1, -1, -1] = 1 := by
    funext i; fin_cases i <;> simp <;> exact (neg_one_mul _).trans (neg_neg _)
  have hs₁ : (![-1, -1, 1] : Fin 3 → ZMod p) * ![-1, -1, 1] = 1 := by
    funext i; fin_cases i <;> simp <;> exact (neg_one_mul _).trans (neg_neg _)
  set P : Subgroup G := ψ.range.comap ρ with hPdef
  have hmemP : ∀ x : G, x ∈ P ↔ ρ x ∈ ψ.range := fun x => Iff.rfl
  let ρP : P →* ψ.range := (ρ.comp P.subtype).codRestrict ψ.range fun x => x.2
  let τ : P →* Multiplicative (Fin 3 → ZMod p) :=
    (MonoidHom.ofInjective hψ).symm.toMonoidHom.comp ρP
  have hψτ : ∀ x : P, ψ (τ x) = ρ x := fun x => by
    have h := congrArg Subtype.val ((MonoidHom.ofInjective hψ).apply_symm_apply (ρP x))
    rw [MonoidHom.ofInjective_apply] at h
    exact h
  have hτsurj : Function.Surjective τ := fun v => by
    obtain ⟨g, hg⟩ := hρ (ψ v)
    exact ⟨⟨g, (hmemP g).2 ⟨v, hg.symm⟩⟩, hψ ((hψτ _).trans hg)⟩
  set A' : Subgroup P := A.subgroupOf P with hA'def
  have hkerτ : A' = τ.ker := by
    ext x
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, ← hker, MonoidHom.mem_ker, ← hψτ,
      ← map_one ψ]
    exact hψ.eq_iff
  have hA'Z : A' ≤ Subgroup.center P := fun x hx => by
    rw [Subgroup.mem_center_iff]
    intro y
    have hc := Subgroup.mem_center_iff.1 (hAZ (Subgroup.mem_subgroupOf.1 hx)) (y : G)
    exact Subtype.ext hc
  let θ : P ⧸ A' ≃* Multiplicative (Fin 3 → ZMod p) :=
    (QuotientGroup.quotientMulEquivOfEq hkerτ).trans
      (QuotientGroup.quotientKerEquivOfSurjective τ hτsurj)
  have hθ : ∀ x : P, θ (x : P ⧸ A') = τ x := fun x => rfl
  have hsignAut : ∀ (s : Fin 3 → ZMod p) (d : Q), s * s = 1 →
      (∀ v, d * ψ v * d⁻¹ = ψ (Multiplicative.ofAdd (s * Multiplicative.toAdd v))) →
      ∃ α : P ≃* P, (∀ a ∈ A', α a = a) ∧
        ∀ x : P, Multiplicative.toAdd (θ (α x : P ⧸ A')) =
          s * Multiplicative.toAdd (θ (x : P ⧸ A')) := by
    intro s d hs hd
    obtain ⟨g, hg⟩ := hρ d
    have hd' := inv_conj_of_sign hs hd
    have h₁ : ∀ x ∈ P, g * x * g⁻¹ ∈ P := fun x hx => by
      obtain ⟨v, hv⟩ := (hmemP x).1 hx
      exact (hmemP _).2 ⟨Multiplicative.ofAdd (s * Multiplicative.toAdd v), by
        rw [← hd, hv, ← hg]
        simp only [map_mul, map_inv]⟩
    have h₂ : ∀ x ∈ P, g⁻¹ * x * g ∈ P := fun x hx => by
      obtain ⟨v, hv⟩ := (hmemP x).1 hx
      exact (hmemP _).2 ⟨Multiplicative.ofAdd (s * Multiplicative.toAdd v), by
        rw [← hd', hv, ← hg]
        simp only [map_mul, map_inv]⟩
    refine ⟨conjRestrict P g h₁ h₂, fun a ha => Subtype.ext ?_, fun x => ?_⟩
    · rw [conjRestrict_apply]
      have hc := Subgroup.mem_center_iff.1 (hAZ (Subgroup.mem_subgroupOf.1 ha)) g
      rw [hc]
      group
    · rw [hθ, hθ]
      have : τ (conjRestrict P g h₁ h₂ x) =
          Multiplicative.ofAdd (s * Multiplicative.toAdd (τ x)) := by
        apply hψ
        rw [← hd, hψτ, hψτ, conjRestrict_apply, ← hg]
        simp only [map_mul, map_inv]
      rw [this, toAdd_ofAdd]
  obtain ⟨α, hαA, hα⟩ := hsignAut _ d₀ hs₀ h₀
  obtain ⟨β, hβA, hβ⟩ := hsignAut _ d₁ hs₁ h₁
  obtain ⟨E, hE, hcard, -, -⟩ :=
    three_sign_lines_central_splitting hp2 A' hA'Z θ α β hαA hβA hα hβ
  refine le_pRank hp.out.one_lt le_top (isElemAbelian_map hE P.subtype) ?_
  rw [Subgroup.card_map_of_injective P.subtype_injective, hcard]

end CFSG.SectionRank
