module

public import CFSG.GH74.E2.Isolation
public import CFSG.GH74.E2.DirectSylow

public section

namespace CFSG.GH74.E2

open Subgroup

theorem noncentral_direct_product {G : Type} [Group G] [Finite G] {t : G}
    (hnc : ∀ S : Sylow 2 G, ¬ ((S : Subgroup G) ≤ Cen t)) {K D : Subgroup G} (hKC : K ≤ Cen t)
    (hDC : D ≤ Cen t) (hcomm : ∀ k ∈ K, ∀ d ∈ D, k * d = d * k) (hdisj : K ⊓ D = ⊥)
    (hCKD : Cen t = K ⊔ D) {SK : Subgroup G} (hSKK : SK ≤ K) (hSKp : IsPGroup 2 SK)
    (hSKmax : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ K → SK ≤ P → P = SK) {SD : Subgroup G}
    (hSDD : SD ≤ D) (hSDp : IsPGroup 2 SD)
    (hSDmax : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ D → SD ≤ P → P = SD) (htSD : t ∈ SD)
    {L Q : Type} [Group L] [Group Q] (eK : ↥SK ≃* L) (eD : ↥SD ≃* Q)
    (hfix : ∀ ψ : MulAut (L × Q), ψ (1, eD ⟨t, htSD⟩) ∈ Subgroup.center (L × Q) →
      ψ (1, eD ⟨t, htSD⟩) = (1, eD ⟨t, htSD⟩)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcommS : ∀ a ∈ SK, ∀ b ∈ SD, a * b = b * a := fun a ha b hb =>
    hcomm a (hSKK ha) b (hSDD hb)
  have hdisjS : SK ⊓ SD = ⊥ := le_bot_iff.1 ((inf_le_inf hSKK hSDD).trans hdisj.le)
  have htS : t ∈ SK ⊔ SD := Subgroup.mem_sup_right htSD
  obtain ⟨-, hS1C, hS12, hmax⟩ := directProduct_sylow hKC hDC hcomm hdisj hCKD hSKK hSKp hSKmax
    hSDD hSDp hSDmax
  have haut := haut_of_prod hcommS hdisjS htSD htS eK eD hfix
  by_cases hP : ∃ P : Subgroup G, IsPGroup 2 P ∧ SK ⊔ SD ≤ P ∧ P ≠ SK ⊔ SD
  · obtain ⟨n, hn, hne, hmem, hcent⟩ := exists_normalizer_moving hS1C hmax htS hP
    exact hne (hfix_of_aut htS haut n hn _ hmem hcent rfl)
  · push Not at hP
    obtain ⟨S, hS⟩ := hS12.exists_le_sylow
    have hSeq : (S : Subgroup G) = SK ⊔ SD := hP _ S.isPGroup' hS
    exact hnc S (hSeq ▸ hS1C)

end CFSG.GH74.E2
