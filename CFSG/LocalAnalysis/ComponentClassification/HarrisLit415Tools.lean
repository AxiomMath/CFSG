module

public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.GroupTheory.ABGLocalTools.Basic

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ABGLocalTools

namespace L415

variable {G : Type*} [Group G]

theorem exists_map_conj [Finite G] {p : ℕ} [Fact p.Prime] {P P' K : Subgroup G}
    (h : IsSylowOf p P K) (h' : IsSylowOf p P' K) :
    ∃ k ∈ K, P' = P.map (MulAut.conj k).toMonoidHom := by
  obtain ⟨Q, rfl⟩ := h
  obtain ⟨Q', rfl⟩ := h'
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K Q Q'
  refine ⟨k, k.2, ?_⟩
  rw [← hk]
  ext x
  simp only [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hy
    refine ⟨K.subtype ((MulAut.conj k)⁻¹ • y), ⟨_, hy, rfl⟩, ?_⟩
    simp [MulAut.smul_def, MulAut.conj_apply, mul_assoc]
  · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    refine ⟨MulAut.conj k s, ?_, ?_⟩
    · rw [Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ hs
    · simp [MulAut.conj_apply]

theorem map_conj_inf_centralizer (P : Subgroup G) (c : G) :
    (P ⊓ centralizer (P : Set G)).map (MulAut.conj c).toMonoidHom =
      P.map (MulAut.conj c).toMonoidHom ⊓
        centralizer ((P.map (MulAut.conj c).toMonoidHom : Subgroup G) : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine mem_inf.mpr ⟨⟨y, (mem_inf.mp hy).1, rfl⟩, mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨q, hq, rfl⟩
    have h1 := (mem_centralizer_iff.mp (mem_inf.mp hy).2) q hq
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc c * q * c⁻¹ * (c * y * c⁻¹) = c * (q * y) * c⁻¹ := by group
      _ = c * (y * q) * c⁻¹ := by rw [h1]
      _ = c * y * c⁻¹ * (c * q * c⁻¹) := by group
  · intro hx
    obtain ⟨⟨y, hyP, rfl⟩, hc⟩ := mem_inf.mp hx
    refine ⟨y, mem_inf.mpr ⟨hyP, mem_centralizer_iff.mpr fun q hq => ?_⟩, rfl⟩
    have h1 := (mem_centralizer_iff.mp hc) _ ⟨q, hq, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
    have h2 : c * (q * y) * c⁻¹ = c * (y * q) * c⁻¹ := by
      calc c * (q * y) * c⁻¹ = c * q * c⁻¹ * (c * y * c⁻¹) := by group
        _ = c * y * c⁻¹ * (c * q * c⁻¹) := h1
        _ = c * (y * q) * c⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)

theorem map_conj_centralizer (a c : G) :
    (centralizer ({a} : Set G)).map (MulAut.conj c).toMonoidHom =
      centralizer ({c * a * c⁻¹} : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have h1 : y * a = a * y := mem_centralizer_singleton_iff.mp hy
    rw [mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc c * y * c⁻¹ * (c * a * c⁻¹) = c * (y * a) * c⁻¹ := by group
      _ = c * (a * y) * c⁻¹ := by rw [h1]
      _ = c * a * c⁻¹ * (c * y * c⁻¹) := by group
  · intro hx
    have h1 : x * (c * a * c⁻¹) = c * a * c⁻¹ * x := mem_centralizer_singleton_iff.mp hx
    refine ⟨c⁻¹ * x * c, mem_centralizer_singleton_iff.mpr ?_, by
      simp [MulAut.conj_apply, mul_assoc]⟩
    calc c⁻¹ * x * c * a = c⁻¹ * (x * (c * a * c⁻¹)) * c := by group
      _ = c⁻¹ * (c * a * c⁻¹ * x) * c := by rw [h1]
      _ = a * (c⁻¹ * x * c) := by group

theorem elem_sup [Finite G] {E : Subgroup G} {x : G} (hE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hE2 : ∀ a ∈ E, a * a = 1) (hx : x * x = 1) (hxE : x ∉ E) (hc : ∀ a ∈ E, a * x = x * a) :
    (∀ a ∈ E ⊔ zpowers x, ∀ b ∈ E ⊔ zpowers x, a * b = b * a) ∧
      (∀ a ∈ E ⊔ zpowers x, a * a = 1) ∧ Nat.card ↥(E ⊔ zpowers x) = 2 * Nat.card E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx1 : x ≠ 1 := fun h1 => hxE (h1 ▸ one_mem E)
  have hxo : orderOf x = 2 := orderOf_eq_prime (by rw [sq]; exact hx) hx1
  have hz : ∀ b ∈ zpowers x, b = 1 ∨ b = x := by
    intro b hb
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hb
    rw [← zpow_mod_orderOf, hxo]
    rcases Int.emod_two_eq_zero_or_one k with h | h <;> simp [h]
  have hcz : ∀ a ∈ E, ∀ b ∈ zpowers x, a * b = b * a := by
    intro a ha b hb
    rcases hz b hb with rfl | rfl
    · simp
    · exact hc a ha
  obtain ⟨hcard, hset⟩ := GroupTheory.card_sup_mul_card_inf_of_commute E (zpowers x) hcz
  have hbot : E ⊓ zpowers x = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rcases hz y (mem_inf.mp hy).2 with rfl | rfl
    · exact one_mem _
    · exact absurd (mem_inf.mp hy).1 hxE
  rw [hbot, Subgroup.card_bot, mul_one, Nat.card_zpowers, hxo] at hcard
  have hmem : ∀ g ∈ E ⊔ zpowers x, ∃ a ∈ E, ∃ b ∈ zpowers x, g = a * b := by
    intro g hg
    have hg' : g ∈ ((E ⊔ zpowers x : Subgroup G) : Set G) := hg
    rw [hset] at hg'
    obtain ⟨a, ha, b, hb, rfl⟩ := hg'
    exact ⟨a, ha, b, hb, rfl⟩
  refine ⟨fun g hg g' hg' => ?_, fun g hg => ?_, by rw [hcard, mul_comm]⟩
  · obtain ⟨a, ha, b, hb, rfl⟩ := hmem g hg
    obtain ⟨a', ha', b', hb', rfl⟩ := hmem g' hg'
    have hbb : b * b' = b' * b := by
      rcases hz b hb with rfl | rfl <;> rcases hz b' hb' with rfl | rfl <;> simp
    calc a * b * (a' * b') = a * (b * a') * b' := by group
      _ = a * (a' * b) * b' := by rw [hcz a' ha' b hb]
      _ = (a * a') * (b * b') := by group
      _ = (a' * a) * (b' * b) := by rw [hE a ha a' ha', hbb]
      _ = a' * (a * b') * b := by group
      _ = a' * (b' * a) * b := by rw [hcz a ha b' hb']
      _ = a' * b' * (a * b) := by group
  · obtain ⟨a, ha, b, hb, rfl⟩ := hmem g hg
    have hb2 : b * b = 1 := by rcases hz b hb with rfl | rfl <;> simp [hx]
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hcz a ha b hb]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [hE2 a ha, hb2, one_mul]

theorem mem_zpowers_two {a x : G} (ha : a * a = 1) (hx : x ∈ zpowers a) : x = 1 ∨ x = a := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
  rcases Int.even_or_odd' k with ⟨q, rfl | rfl⟩
  · left
    rw [zpow_mul, zpow_two, ha, one_zpow]
  · right
    rw [zpow_add_one, zpow_mul, zpow_two, ha, one_zpow, one_mul]

theorem elem_zpowers {a : G} (ha : a * a = 1) :
    (∀ x ∈ zpowers a, ∀ y ∈ zpowers a, x * y = y * x) ∧ ∀ x ∈ zpowers a, x * x = 1 := by
  refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
  · rcases mem_zpowers_two ha hx with rfl | rfl <;> rcases mem_zpowers_two ha hy with rfl | rfl <;>
      simp
  · rcases mem_zpowers_two ha hx with rfl | rfl
    · simp
    · exact ha

theorem card_zpowers_two [Finite G] {a : G} (ha : a * a = 1) (ha1 : a ≠ 1) :
    Nat.card (zpowers a) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime (by rw [sq]; exact ha) ha1

@[expose] def centralInv (P : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ P ∧ (∀ y ∈ P, x * y = y * x) ∧ x * x = 1}
  mul_mem' := by
    rintro a b ⟨haP, hac, ha2⟩ ⟨hbP, hbc, hb2⟩
    refine ⟨mul_mem haP hbP, fun y hy => ?_, ?_⟩
    · rw [mul_assoc, hbc y hy, ← mul_assoc, hac y hy, mul_assoc]
    · calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [hbc a haP]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [ha2, hb2, one_mul]
  one_mem' := ⟨one_mem P, fun y _ => by simp, by simp⟩
  inv_mem' := by
    rintro a ⟨haP, hac, ha2⟩
    have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
    rw [Set.mem_ofPred_eq, hai]
    exact ⟨haP, hac, ha2⟩

theorem mem_centralInv {P : Subgroup G} {x : G} :
    x ∈ centralInv P ↔ x ∈ P ∧ (∀ y ∈ P, x * y = y * x) ∧ x * x = 1 :=
  Iff.rfl

theorem conj_mem_centralInv {P : Subgroup G} {c x : G}
    (hc₁ : ∀ y ∈ P, c * y * c⁻¹ ∈ P) (hc₂ : ∀ y ∈ P, c⁻¹ * y * c ∈ P)
    (hx : x ∈ centralInv P) : c * x * c⁻¹ ∈ centralInv P := by
  obtain ⟨hxP, hxc, hx2⟩ := hx
  refine ⟨hc₁ x hxP, fun y hy => ?_, ?_⟩
  · have h1 := hxc _ (hc₂ y hy)
    calc c * x * c⁻¹ * y = c * (x * (c⁻¹ * y * c)) * c⁻¹ := by group
      _ = c * ((c⁻¹ * y * c) * x) * c⁻¹ := by rw [h1]
      _ = y * (c * x * c⁻¹) := by group
  · calc c * x * c⁻¹ * (c * x * c⁻¹) = c * (x * x) * c⁻¹ := by group
      _ = 1 := by rw [hx2]; group

end L415

end CFSG.ComponentClassification.HarrisLit
