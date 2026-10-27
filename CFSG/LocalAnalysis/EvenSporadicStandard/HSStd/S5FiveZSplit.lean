module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveSplit
public import Certificates.Certificate26964

public section

namespace CFSG.EvenSporadicStandard.HSStd

open Subgroup Equiv

theorem zmod_five_trivial {g : Multiplicative (ZMod 5)} (h : g * g = 1 ∨ g ^ 3 = 1) : g = 1 := by
  revert g
  decide

theorem exists_mulEquiv_of_central_five
    {Q : Type*} [Group Q] {z r : Q} (hz : z ∈ center Q) (hz2 : orderOf z = 2)
    (hr : r ∈ center Q) (hr5 : orderOf r = 5)
    (ψ : Q →* Multiplicative (ZMod 5) × Perm (Fin 5)) (hψs : Function.Surjective ψ)
    (hψk : ∀ x : Q, ψ x = 1 ↔ x ∈ zpowers z)
    {x y₁ y₂ : Q} (hx : x * x = 1) (hx1 : x ∉ zpowers z) (hy₁ : y₁ * y₁ = 1)
    (hy₂ : y₂ * y₂ = 1) (hy3 : (y₁ * y₂) ^ 3 = 1) (hy12 : y₁ * y₂ ∉ zpowers z)
    (hxy₁ : x * y₁ = y₁ * x) (hxy₂ : x * y₂ = y₂ * x) :
    Nonempty (Q ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 5) × Perm (Fin 5)) := by
  have hsq : ∀ q : Q, q * q = 1 → (ψ q).1 = 1 := fun q hq => by
    apply zmod_five_trivial
    left
    have := congrArg ψ hq
    rw [map_mul, map_one] at this
    exact congrArg Prod.fst this
  have hcb : ∀ q : Q, q ^ 3 = 1 → (ψ q).1 = 1 := fun q hq => by
    apply zmod_five_trivial
    right
    have := congrArg ψ hq
    rw [map_pow, map_one] at this
    exact congrArg Prod.fst this
  have hne : ∀ q : Q, q * q = 1 → q ∉ zpowers z → (ψ q).2 ≠ 1 := fun q hq hqz h2 => by
    apply hqz
    rw [← hψk]
    exact Prod.ext (hsq q hq) h2
  have hsq2 : ∀ q : Q, q * q = 1 → (ψ q).2 * (ψ q).2 = 1 := fun q hq => by
    have := congrArg ψ hq
    rw [map_mul, map_one] at this
    exact congrArg Prod.snd this
  have hτ1 : (ψ x).2 ≠ 1 := hne x hx hx1
  have hμ₁ : (ψ y₁).2 * (ψ y₁).2 = 1 := hsq2 y₁ hy₁
  have hμ₂ : (ψ y₂).2 * (ψ y₂).2 = 1 := hsq2 y₂ hy₂
  have hcube : ((ψ y₁).2 * (ψ y₂).2) ^ 3 = 1 := by
    have := congrArg ψ hy3
    rw [map_pow, map_mul, map_one] at this
    exact congrArg Prod.snd this
  have hne12 : (ψ y₁).2 * (ψ y₂).2 ≠ 1 := by
    intro h
    apply hy12
    rw [← hψk]
    have h1 : (ψ (y₁ * y₂)).1 = 1 := hcb _ hy3
    exact Prod.ext h1 (by rw [map_mul]; exact h)
  have hcomm₁ : (ψ x).2 * (ψ y₁).2 = (ψ y₁).2 * (ψ x).2 := by
    have := congrArg ψ hxy₁
    rw [map_mul, map_mul] at this
    exact congrArg Prod.snd this
  have hcomm₂ : (ψ x).2 * (ψ y₂).2 = (ψ y₂).2 * (ψ x).2 := by
    have := congrArg ψ hxy₂
    rw [map_mul, map_mul] at this
    exact congrArg Prod.snd this
  obtain ⟨i, j, k, l, hij, hkl, hik, hil, hjk, hjl, hτs, hμ⟩ :=
    Certificates.certificate26964 (ψ x).2 (ψ y₁).2 (ψ y₂).2 (hsq2 x hx) hτ1 hμ₁ hμ₂ hcube
      hne12 hcomm₁ hcomm₂
  rcases hμ with hμ | hμ
  · exact exists_mulEquiv_of_central_ext_prod_five hz hz2 hr hr5 ψ hψs hψk hx hy₁ hxy₁ hij hkl
      hik hil hjk hjl hτs hμ
  · have hb : y₁ * x * (y₁ * x) = 1 := by
      calc y₁ * x * (y₁ * x) = y₁ * (x * y₁) * x := by group
        _ = y₁ * (y₁ * x) * x := by rw [hxy₁]
        _ = (y₁ * y₁) * (x * x) := by group
        _ = 1 := by rw [hy₁, hx, one_mul]
    have hab : x * (y₁ * x) = (y₁ * x) * x := by
      calc x * (y₁ * x) = (x * y₁) * x := by group
        _ = (y₁ * x) * x := by rw [hxy₁]
    refine exists_mulEquiv_of_central_ext_prod_five hz hz2 hr hr5 ψ hψs hψk hx hb hab hij hkl
      hik hil hjk hjl hτs ?_
    rw [map_mul]
    exact hμ

end CFSG.EvenSporadicStandard.HSStd
