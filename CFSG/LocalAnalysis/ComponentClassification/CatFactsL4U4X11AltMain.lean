module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4X11AltSym

public section

namespace CFSG.ComponentClassification.GSThmB.X11.Sym

open Equiv Subgroup
open scoped commutatorElement

theorem exists_ne_of_card {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (hQ : Nat.card Q = 25920) : ∃ x y : Q, x * y ≠ y * x := by
  by_contra hcon
  push Not at hcon
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := Q) 2 (by rw [hQ]; norm_num)
  have hn : (zpowers g).Normal := ⟨fun x hx y => by rwa [hcon y x, mul_inv_cancel_right]⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (zpowers g) with h | h
  · rw [zpowers_eq_bot] at h
    rw [h, orderOf_one] at hg
    exact absurd hg (by norm_num)
  · have h1 : Nat.card (zpowers g) = 2 := by rw [Nat.card_zpowers, hg]
    rw [h, card_top, hQ] at h1
    exact absurd h1 (by norm_num)

theorem false_of_factor {L : Type*} [Group L] {Z : Type*} [Fintype Z] [DecidableEq Z]
    (ρ : L →* Perm Z) (hρ : ρ.range.IsSubnormal) {Q : Type*} [Group Q] [Finite Q] (φ : L →* Q)
    (hφ : Function.Surjective φ) (hQ : Nat.card Q = 25920) (hker : ρ.ker ≤ φ.ker) : False := by
  let ψ : ↥ρ.range →* Q :=
    (QuotientGroup.lift ρ.ker φ hker).comp (QuotientGroup.quotientKerEquivRange ρ).symm.toMonoidHom
  have hψ : Function.Surjective ψ := by
    intro q
    obtain ⟨l, rfl⟩ := hφ q
    refine ⟨⟨ρ l, l, rfl⟩, ?_⟩
    have e : (QuotientGroup.quotientKerEquivRange ρ).symm ⟨ρ l, l, rfl⟩ =
        (QuotientGroup.mk l : L ⧸ ρ.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    change QuotientGroup.lift ρ.ker φ hker ((QuotientGroup.quotientKerEquivRange ρ).symm _) = _
    rw [e]
    rfl
  exact false_of_subnormal_perm hρ ψ hψ hQ

variable {α : Type} [Fintype α] [LinearOrder α] {β : Perm α}

theorem false_of_subnormal_centralizer (hβ : ∀ x, β (β x) = x)
    {L : Subgroup ↥(centralizer ({β} : Set (Perm α)))} (hL : L.IsSubnormal) {Q : Type*} [Group Q]
    [Finite Q] [IsSimpleGroup Q] (φ : ↥L →* Q) (hφ : Function.Surjective φ)
    (hQ : Nat.card Q = 25920) : False := by
  obtain ⟨x₀, y₀, hxy₀⟩ := exists_ne_of_card hQ
  set ρ₁ := (rho1 β).comp L.subtype with hρ₁
  set ρ₂ := (rho2 hβ).comp L.subtype with hρ₂
  have hE : ∀ e ∈ ρ₁.ker ⊓ ρ₂.ker, φ e = 1 := by
    have hab : ∀ e₁ ∈ ρ₁.ker ⊓ ρ₂.ker, ∀ e₂ ∈ ρ₁.ker ⊓ ρ₂.ker, e₁ * e₂ = e₂ * e₁ := by
      intro e₁ he₁ e₂ he₂
      have h1 := apply_eq_or_of_mem_ker hβ (c := e₁.1) (MonoidHom.mem_ker.mp he₁.1)
        (MonoidHom.mem_ker.mp he₁.2)
      have h2 := apply_eq_or_of_mem_ker hβ (c := e₂.1) (MonoidHom.mem_ker.mp he₂.1)
        (MonoidHom.mem_ker.mp he₂.2)
      exact Subtype.ext (Subtype.ext (commute_of_orbitwise e₁.1.2 e₂.1.2 h1 h2))
    have hn : ((ρ₁.ker ⊓ ρ₂.ker).map φ).Normal :=
      (inferInstance : (ρ₁.ker ⊓ ρ₂.ker).Normal).map φ hφ
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((ρ₁.ker ⊓ ρ₂.ker).map φ) with h | h
    · intro e he
      have : φ e ∈ (ρ₁.ker ⊓ ρ₂.ker).map φ := mem_map_of_mem φ he
      rwa [h, mem_bot] at this
    · exfalso
      apply hxy₀
      obtain ⟨a, ha, rfl⟩ := (h ▸ mem_top x₀ : x₀ ∈ (ρ₁.ker ⊓ ρ₂.ker).map φ)
      obtain ⟨b, hb, rfl⟩ := (h ▸ mem_top y₀ : y₀ ∈ (ρ₁.ker ⊓ ρ₂.ker).map φ)
      rw [← map_mul, ← map_mul, hab a ha b hb]
  have hcomm : ∀ d₁ ∈ ρ₂.ker, ∀ d₂ ∈ ρ₁.ker, φ d₁ * φ d₂ = φ d₂ * φ d₁ := by
    intro d₁ h₁ d₂ h₂
    have hc : ⁅d₁, d₂⁆ ∈ ρ₁.ker ⊓ ρ₂.ker := by
      refine Subgroup.mem_inf.mpr ⟨MonoidHom.mem_ker.mpr ?_, MonoidHom.mem_ker.mpr ?_⟩
      · rw [map_commutatorElement, MonoidHom.mem_ker.mp h₂, commutatorElement_one_right]
      · rw [map_commutatorElement, MonoidHom.mem_ker.mp h₁, commutatorElement_one_left]
    have h1 := hE _ hc
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  have hn₂ : (ρ₂.ker.map φ).Normal := (inferInstance : ρ₂.ker.Normal).map φ hφ
  have hn₁ : (ρ₁.ker.map φ).Normal := (inferInstance : ρ₁.ker.Normal).map φ hφ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (ρ₂.ker.map φ) with h₂ | h₂
  ·
    refine false_of_factor ρ₂ ?_ φ hφ hQ fun d hd => ?_
    · rw [hρ₂, MonoidHom.range_comp, range_subtype]
      exact hL.map (rho2_surjective hβ)
    · have : φ d ∈ ρ₂.ker.map φ := mem_map_of_mem φ hd
      rwa [h₂, mem_bot] at this
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (ρ₁.ker.map φ) with h₁ | h₁
  ·
    refine false_of_factor ρ₁ ?_ φ hφ hQ fun d hd => ?_
    · rw [hρ₁, MonoidHom.range_comp, range_subtype]
      exact hL.map rho1_surjective
    · have : φ d ∈ ρ₁.ker.map φ := mem_map_of_mem φ hd
      rwa [h₁, mem_bot] at this
  ·
    apply hxy₀
    obtain ⟨a, ha, rfl⟩ := (h₂ ▸ mem_top x₀ : x₀ ∈ ρ₂.ker.map φ)
    obtain ⟨b, hb, rfl⟩ := (h₁ ▸ mem_top y₀ : y₀ ∈ ρ₁.ker.map φ)
    exact hcomm a ha b hb

end CFSG.ComponentClassification.GSThmB.X11.Sym
