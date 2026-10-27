module

public import CFSG.GH74.E2.DirectProd
public import CFSG.GH74.E2.AutCert
public import CFSG.GH74.E2.Cen

public section

namespace CFSG.GH74.E2

open Subgroup

theorem card_of_max {G : Type} [Group G] [Finite G] {K S : Subgroup G} (hS : S ≤ K)
    (hSp : IsPGroup 2 S) (hmax : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ K → S ≤ P → P = S) :
    Nat.card S = 2 ^ (Nat.card K).factorization 2 := by
  have hp' : IsPGroup 2 (S.subgroupOf K) := hSp.comap_subtype
  obtain ⟨T, hT⟩ := hp'.exists_le_sylow
  have h1 : IsPGroup 2 ((T : Subgroup ↥K).map K.subtype) := T.isPGroup'.map K.subtype
  have h2 : (T : Subgroup ↥K).map K.subtype ≤ K := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have h3 : S ≤ (T : Subgroup ↥K).map K.subtype := fun x hx =>
    ⟨⟨x, hS hx⟩, hT (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  have h4 := hmax _ h1 h2 h3
  rw [← h4, Subgroup.card_map_of_injective K.subtype_injective]
  exact T.card_eq_multiplicity

theorem directProduct_sylow {G : Type} [Group G] [Finite G] {t : G} {K D : Subgroup G}
    (hKC : K ≤ Cen t) (hDC : D ≤ Cen t) (hcomm : ∀ k ∈ K, ∀ d ∈ D, k * d = d * k)
    (hdisj : K ⊓ D = ⊥) (hCKD : Cen t = K ⊔ D) {SK : Subgroup G} (hSKK : SK ≤ K)
    (hSKp : IsPGroup 2 SK)
    (hSKmax : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ K → SK ≤ P → P = SK) {SD : Subgroup G}
    (hSDD : SD ≤ D) (hSDp : IsPGroup 2 SD)
    (hSDmax : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ D → SD ≤ P → P = SD) :
    Nat.card ↥(SK ⊔ SD) = Nat.card SK * Nat.card SD ∧ SK ⊔ SD ≤ Cen t ∧
      IsPGroup 2 ↥(SK ⊔ SD) ∧
      ∀ P : Subgroup G, IsPGroup 2 P → P ≤ Cen t → SK ⊔ SD ≤ P → P = SK ⊔ SD := by
  have hcommS : ∀ a ∈ SK, ∀ b ∈ SD, a * b = b * a := fun a ha b hb =>
    hcomm a (hSKK ha) b (hSDD hb)
  have hdisjS : SK ⊓ SD = ⊥ := le_bot_iff.1 ((inf_le_inf hSKK hSDD).trans hdisj.le)
  have hS1C : SK ⊔ SD ≤ Cen t := sup_le (hSKK.trans hKC) (hSDD.trans hDC)
  have hS1card : Nat.card ↥(SK ⊔ SD) = Nat.card SK * Nat.card SD := by
    rw [← Nat.card_prod]
    exact (Nat.card_congr (prodSupEquiv SK SD hcommS hdisjS).toEquiv).symm
  have hS12 : IsPGroup 2 ↥(SK ⊔ SD) := by
    obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 hSKp
    obtain ⟨b, hb⟩ := (IsPGroup.iff_card).1 hSDp
    exact IsPGroup.of_card (n := a + b) (by rw [hS1card, ha, hb, pow_add])
  refine ⟨hS1card, hS1C, hS12, ?_⟩
  intro P hP hPC hS1P
  have hK : Nat.card SK = 2 ^ (Nat.card K).factorization 2 := card_of_max hSKK hSKp hSKmax
  have hD : Nat.card SD = 2 ^ (Nat.card D).factorization 2 := card_of_max hSDD hSDp hSDmax
  have hCcard : Nat.card ↥(Cen t) = Nat.card K * Nat.card D := by
    rw [hCKD, ← Nat.card_prod]
    exact (Nat.card_congr (prodSupEquiv K D hcomm hdisj).toEquiv).symm
  have hdvd : Nat.card P ∣ Nat.card K * Nat.card D := by
    rw [← hCcard]
    exact Subgroup.card_dvd_of_le hPC
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 hP
  have hKne : Nat.card K ≠ 0 := Nat.card_pos.ne'
  have hDne : Nat.card D ≠ 0 := Nat.card_pos.ne'
  have hle : a ≤ (Nat.card K).factorization 2 + (Nat.card D).factorization 2 := by
    have h1 : 2 ^ a ∣ Nat.card K * Nat.card D := ha ▸ hdvd
    have h2 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two
      (mul_ne_zero hKne hDne)).1 h1
    rwa [Nat.factorization_mul hKne hDne, Finsupp.add_apply] at h2
  have hcardP : Nat.card P ≤ Nat.card ↥(SK ⊔ SD) := by
    rw [hS1card, hK, hD, ← pow_add, ha]
    exact Nat.pow_le_pow_right (by norm_num) hle
  exact (Subgroup.eq_of_le_of_card_ge hS1P hcardP).symm

theorem haut_of_prod {G : Type} [Group G] {t : G} {SK SD : Subgroup G}
    (hcommS : ∀ a ∈ SK, ∀ b ∈ SD, a * b = b * a) (hdisjS : SK ⊓ SD = ⊥) (htSD : t ∈ SD)
    (htS : t ∈ SK ⊔ SD) {L Q : Type} [Group L] [Group Q] (eK : ↥SK ≃* L) (eD : ↥SD ≃* Q)
    (hfix : ∀ ψ : MulAut (L × Q), ψ (1, eD ⟨t, htSD⟩) ∈ Subgroup.center (L × Q) →
      ψ (1, eD ⟨t, htSD⟩) = (1, eD ⟨t, htSD⟩)) :
    ∀ ψ : MulAut ↥(SK ⊔ SD), ψ ⟨t, htS⟩ ∈ Subgroup.center ↥(SK ⊔ SD) →
      ψ ⟨t, htS⟩ = ⟨t, htS⟩ := by
  let e : ↥(SK ⊔ SD) ≃* L × Q :=
    (prodSupEquiv SK SD hcommS hdisjS).symm.trans (eK.prodCongr eD)
  have het : e ⟨t, htS⟩ = (1, eD ⟨t, htSD⟩) := by
    have h1 : (prodSupEquiv SK SD hcommS hdisjS).symm ⟨t, htS⟩ = (1, ⟨t, htSD⟩) := by
      rw [MulEquiv.symm_apply_eq]
      apply Subtype.ext
      simp [prodSupEquiv_apply]
    show (eK.prodCongr eD) ((prodSupEquiv SK SD hcommS hdisjS).symm ⟨t, htS⟩) = _
    rw [h1]
    show (eK 1, eD ⟨t, htSD⟩) = _
    rw [map_one]
  refine fix_transport e ?_
  rw [het]
  exact hfix

theorem quat_sq_eq_one {m : ℕ} (hm : m = 2 ∨ m = 4) :
    ∀ x : QuaternionGroup m, x * x = 1 → x = 1 ∨ x = QuaternionGroup.a (m : ZMod (2 * m)) := by
  rcases hm with rfl | rfl <;> decide

theorem eD_t_eq_a {G : Type} [Group G] {t : G} {SD : Subgroup G} (htSD : t ∈ SD)
    (ht : orderOf t = 2) {m : ℕ} (hm : m = 2 ∨ m = 4) (eD : ↥SD ≃* QuaternionGroup m) :
    eD ⟨t, htSD⟩ = QuaternionGroup.a (m : ZMod (2 * m)) := by
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have ht2 : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht, pow_two] at this
  have h1 : eD ⟨t, htSD⟩ * eD ⟨t, htSD⟩ = 1 := by
    rw [← map_mul]
    have : (⟨t, htSD⟩ : ↥SD) * ⟨t, htSD⟩ = 1 := Subtype.ext ht2
    rw [this, map_one]
  rcases quat_sq_eq_one hm _ h1 with h | h
  · exfalso
    apply ht1
    have : (⟨t, htSD⟩ : ↥SD) = 1 := by
      apply eD.injective
      rw [h, map_one]
    exact congrArg Subtype.val this
  · exact h

end CFSG.GH74.E2
