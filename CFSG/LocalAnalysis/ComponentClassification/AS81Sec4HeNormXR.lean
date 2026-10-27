module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeNormX

public section

namespace CFSG.ComponentClassification.AS81.HeTri

open Subgroup CFSG.ComponentClassification.AS81.HeSylow CFSG.ComponentClassification.AS81.Hexa

variable {G : Type} [Group G]

theorem mem_hexaR0_iff (hF : HexaFacts) {X R L : Subgroup G} (ι : ↥X ≃* ↥hexaT)
    (f : ↥heN0 ≃* ↥L) (hfX : ∀ n : ↥heN0, (n : Equiv.Perm (Fin 64)) ∈ hexaT ↔ (f n : G) ∈ X)
    {d : ↥heN0} (hd : ∀ (t : Equiv.Perm (Fin 64)) (ht : t ∈ hexaT),
      ((f (d * ⟨t, mem_sup_left ht⟩ * d⁻¹) : ↥L) : G) = ι.symm ⟨t, ht⟩)
    (hRX : R ≤ X) (hR : ∀ x : ↥X, (x : G) ∈ R ↔ (ι x : Equiv.Perm (Fin 64)) ∈ hexaR0)
    (n : ↥heN0) : (n : Equiv.Perm (Fin 64)) ∈ hexaR0 ↔ (f (d * n * d⁻¹) : G) ∈ R := by
  have hT : ∀ ht : (n : Equiv.Perm (Fin 64)) ∈ hexaT,
      ((f (d * n * d⁻¹) : ↥L) : G) = ι.symm ⟨n, ht⟩ := fun ht => hd n ht
  have hRiff : ∀ ht : (n : Equiv.Perm (Fin 64)) ∈ hexaT,
      (n : Equiv.Perm (Fin 64)) ∈ hexaR0 ↔ ((ι.symm ⟨n, ht⟩ : ↥X) : G) ∈ R := fun ht => by
    rw [hR, MulEquiv.apply_symm_apply]
  constructor
  · intro hn
    have ht := hF.R0T hn
    rw [hT ht]
    exact (hRiff ht).mp hn
  · intro hn
    have h1 : ((d * n * d⁻¹ : ↥heN0) : Equiv.Perm (Fin 64)) ∈ hexaT := (hfX _).mpr (hRX hn)
    have hdN : (d : Equiv.Perm (Fin 64)) ∈ normalizer (hexaT : Set (Equiv.Perm (Fin 64))) :=
      sup_le le_normalizer hF.normT d.2
    have ht : (n : Equiv.Perm (Fin 64)) ∈ hexaT := (mem_normalizer_iff.mp hdN _).mpr h1
    rw [hT ht] at hn
    exact (hRiff ht).mpr hn

theorem exists_normX_R [Finite G] (hF : HexaFacts) (hM : HeModelFacts) {X Y S₁ R : Subgroup G}
    {z : G} (ι : ↥X ≃* ↥hexaT)
    (ψ : ↥(AS76b.oUpperTwoPrime (normalizer (X : Set G))) →* ↥hexaM)
    (hψs : Function.Surjective ψ)
    (hψk : ψ.ker = X.subgroupOf (AS76b.oUpperTwoPrime (normalizer (X : Set G))))
    (hequiv : ∀ (ℓ : ↥(AS76b.oUpperTwoPrime (normalizer (X : Set G)))) (x y : ↥X),
      (y : G) = ℓ * x * (ℓ : G)⁻¹ →
        (ι y : Equiv.Perm (Fin 64)) = ψ ℓ * ι x * (ψ ℓ : Equiv.Perm (Fin 64))⁻¹)
    (hX2 : ∀ x ∈ X, x * x = 1) (hX64 : Nat.card X = 64) (hzX : z ∈ X) (hz1 : z ≠ 1)
    (hCz : Nat.card (centralizer ({z} : Set G)) = 21504) (hS₁I : S₁ ≤ iX z X)
    (hS₁ : Nat.card S₁ = 1024) (hYS : Y ≤ S₁) (hSY : S₁ ≤ normalizer (Y : Set G))
    (hY2 : ∀ y ∈ Y, y * y = 1) (hY64 : Nat.card Y = 64) (hYX : Y ≠ X) (hRX : R ≤ X)
    (hR : ∀ x : ↥X, (x : G) ∈ R ↔ (ι x : Equiv.Perm (Fin 64)) ∈ hexaR0) :
    ∃ f : ↥heN0 ≃* ↥(AS76b.oUpperTwoPrime (normalizer (X : Set G))),
      (∀ n : ↥heN0, (n : Equiv.Perm (Fin 64)) = hexaT0P ↔ (f n : G) = z) ∧
      (∀ n : ↥heN0, (n : Equiv.Perm (Fin 64)) ∈ hexaT ↔ (f n : G) ∈ X) ∧
      (∀ n : ↥heN0, (n : Equiv.Perm (Fin 64)) ∈ heP12 ↔ (f n : G) ∈ iX z X) ∧
      (∀ n : ↥heN0, (n : Equiv.Perm (Fin 64)) ∈ heB0 ↔ (f n : G) ∈ S₁) ∧
      (∀ n : ↥heN0, (n : Equiv.Perm (Fin 64)) ∈ heF0 ↔ (f n : G) ∈ Y) ∧
      (∀ n : ↥heN0, (n : Equiv.Perm (Fin 64)) ∈ heP23 ↔
        (f n : G) ∈ AS76b.oUpperTwoPrime (normalizer (Y : Set G))) ∧
      ∃ c : ↥heN0, ∀ n : ↥heN0, (n : Equiv.Perm (Fin 64)) ∈ hexaR0 ↔ (f (c * n * c⁻¹) : G) ∈ R := by
  obtain ⟨f, h1, h2, h3, h4, h5, h6, d, hd⟩ := exists_normX hF hM ι ψ hψs hψk hequiv hX2 hX64
    hzX hz1 hCz hS₁I hS₁ hYS hSY hY2 hY64 hYX
  exact ⟨f, h1, h2, h3, h4, h5, h6, d, mem_hexaR0_iff hF ι f h2 hd hRX hR⟩

end CFSG.ComponentClassification.AS81.HeTri
