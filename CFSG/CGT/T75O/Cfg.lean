module

public import CFSG.CGT.Timmesfeld75.Sec5SixB

public section

namespace CFSG.CGT.T75O

open CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] {T T₁ : Subgroup G}

structure Cfg56 (T T₁ : Subgroup G) : Prop where
  hy : StepHyp T T₁
  hS : Sec3Global T
  hI : Sec3IsoGlobal T
  hnab : ¬ ∀ x ∈ secR₁ T T₁, ∀ y ∈ secR₁ T T₁, x * y = y * x
  h2 : IsPGroup 2 ↥(secR₁ T T₁)
  hR' : ∀ x ∈ secR₁ T T₁, ∀ y ∈ secR₁ T T₁, ⁅x, y⁆ ∈ secA T T₁
  hcard : Nat.card (secA T T₁) * Nat.card (normIn T T₁) ≤ Nat.card T
  hplus : ∀ g : G, conjSubgroup g (secA T T₁) ≤ Subgroup.normalizer (T : Set G) →
    conjSubgroup g T ≠ T → IsUIdx T T₁ g
  hnc : ∀ g : G, IsUIdx T T₁ g →
    ¬ ∀ a ∈ conjSubgroup g (secA T T₁), ∀ x ∈ secR₁ T T₁, a * x = x * a

namespace Cfg56

variable (c : Cfg56 T T₁)
include c

theorem secA_ne_bot : secA T T₁ ≠ ⊥ := fun h =>
  c.hnab (by
    rw [secR₁_eq_bot_of_secA_eq_bot h]
    intro x hx y hy
    rw [Subgroup.mem_bot] at hx hy
    rw [hx, hy])

theorem exists_isUIdx : ∃ g : G, IsUIdx T T₁ g := by
  have := c.hy.finite
  obtain ⟨x, hx⟩ := c.hy.pair.conj
  have hs : Sec3 T T₁ := c.hy.pair.sec3 c.hS
  refine ⟨x, ?_, ?_⟩
  · rw [← hx]
    exact c.hy.pair.ne
  · rw [← hx]
    exact hs.card_normIn_swap

theorem card_secA_eq {g : G} (hu : IsUIdx T T₁ g) :
    ∃ f : ℕ, f ≠ 0 ∧ Nat.card (secA T T₁) = 2 ^ f ∧
      Nat.card T = Nat.card (normIn T T₁) * 2 ^ f := by
  have := c.hy.finite
  obtain ⟨hN, f, hf, hiso⟩ := c.hI g hu.1 (hu.normIn_ne_bot c.hy.pair)
  have hsec : Sec3 T (conjSubgroup g T) := hu.sec3 c.hy.pair c.hS
  have hmul := hsec.card_eq_mul hf hiso
  rw [hu.card_normIn c.hy.pair c.hS] at hmul
  have hle := card_le_normIn_mul_card_secA c.hy.pair c.hS c.hI hu.1
    (hu.normIn_ne_bot c.hy.pair) c.secA_ne_bot
  rw [hu.card_normIn c.hy.pair c.hS] at hle
  have hLpos : 0 < Nat.card (normIn T T₁) := Nat.card_pos
  refine ⟨f, hf, ?_, hmul⟩
  have h1 : Nat.card (normIn T T₁) * 2 ^ f ≤ Nat.card (normIn T T₁) * Nat.card (secA T T₁) := by
    rw [← hmul]
    exact hle
  have h2 : 2 ^ f ≤ Nat.card (secA T T₁) := Nat.le_of_mul_le_mul_left h1 hLpos
  have h3 : Nat.card (secA T T₁) * Nat.card (normIn T T₁) ≤ 2 ^ f * Nat.card (normIn T T₁) := by
    rw [mul_comm (2 ^ f), ← hmul]
    exact c.hcard
  exact le_antisymm (Nat.le_of_mul_le_mul_right h3 hLpos) h2

theorem torus_transitive {g : G} (hu : IsUIdx T T₁ g) :
    ∃ K : Subgroup G, K ≤ Subgroup.normalizer (T : Set G) ∧
      ∀ a ∈ secA T T₁, a ≠ 1 → ∀ b ∈ secA T T₁, b ≠ 1 → ∃ k ∈ K, k * a * k⁻¹ = b := by
  have := c.hy.finite
  obtain ⟨hN, f, hf, hiso⟩ := c.hI g hu.1 (hu.normIn_ne_bot c.hy.pair)
  have hsec : Sec3 T (conjSubgroup g T) := hu.sec3 c.hy.pair c.hS
  obtain ⟨f', hf', hAcard, -⟩ := c.card_secA_eq hu
  obtain ⟨K, -, hKT, hKcard, hKfree⟩ := hsec.exists_odd_normalizing_subgroup hf hiso
  have hmul := hsec.card_eq_mul hf hiso
  rw [hu.card_normIn c.hy.pair c.hS] at hmul
  obtain ⟨f'', hf'', hAcard'', hmul''⟩ := c.card_secA_eq hu
  have hLpos : 0 < Nat.card (normIn T T₁) := Nat.card_pos
  have hff : 2 ^ f = 2 ^ f'' := Nat.eq_of_mul_eq_mul_left hLpos (hmul.symm.trans hmul'')
  have hAcard2 : Nat.card (secA T T₁) = 2 ^ f := by rw [hAcard'', ← hff]
  have hAM : secA T T₁ ≤ cfgM T (conjSubgroup g T) :=
    (secA_le_normIn_conj c.hy.pair c.hS hu.1 (hu.normIn_ne_bot c.hy.pair)).trans le_sup_left
  refine ⟨K, hKT, fun a ha ha1 b hb hb1 => ?_⟩
  have hkA : ∀ k : K, (k : G) * a * (k : G)⁻¹ ∈ secA T T₁ := fun k => by
    have := conjSubgroup_secA (T₁ := T₁) (hKT k.2)
    rw [← this]
    exact ⟨a, ha, rfl⟩
  have hk1 : ∀ k : K, (k : G) * a * (k : G)⁻¹ ≠ 1 := fun k h => ha1 (by
    have : a = (k : G)⁻¹ * ((k : G) * a * (k : G)⁻¹) * (k : G) := by group
    rw [this, h]
    group)
  let φ : Option K → secA T T₁ := fun o => match o with
    | none => 1
    | some k => ⟨(k : G) * a * (k : G)⁻¹, hkA k⟩
  have hφinj : Function.Injective φ := by
    intro o o' h
    cases o with
    | none =>
      cases o' with
      | none => rfl
      | some k' =>
        exfalso
        exact hk1 k' (by simpa [φ] using (congrArg Subtype.val h).symm)
    | some k =>
      cases o' with
      | none =>
        exfalso
        exact hk1 k (by simpa [φ] using congrArg Subtype.val h)
      | some k' =>
        have h' : (k : G) * a * (k : G)⁻¹ = (k' : G) * a * (k' : G)⁻¹ := by
          simpa [φ] using congrArg Subtype.val h
        have h'' : ((k' : G)⁻¹ * (k : G)) * a * ((k' : G)⁻¹ * (k : G))⁻¹ = a := by
          calc ((k' : G)⁻¹ * (k : G)) * a * ((k' : G)⁻¹ * (k : G))⁻¹
              = (k' : G)⁻¹ * ((k : G) * a * (k : G)⁻¹) * (k' : G) := by group
            _ = (k' : G)⁻¹ * ((k' : G) * a * (k' : G)⁻¹) * (k' : G) := by rw [h']
            _ = a := by group
        have hkk : (k' : G)⁻¹ * (k : G) = 1 :=
          by_contra fun hne => ha1 (hKfree _ (K.mul_mem (K.inv_mem k'.2) k.2) hne a (hAM ha) h'')
        have : k = k' := Subtype.ext (by
          have := congrArg (fun z => (k' : G) * z) hkk
          simpa using this)
        rw [this]
  have hoption : Nat.card (Option K) = Nat.card K + 1 := by
    have := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_option]
  have hcard : Nat.card (secA T T₁) ≤ Nat.card (Option K) := by
    rw [hAcard2, hoption, hKcard]
    have : 0 < 2 ^ f := by positivity
    omega
  have hbij := hφinj.bijective_of_nat_card_le hcard
  obtain ⟨o, ho⟩ := hbij.2 ⟨b, hb⟩
  cases o with
  | none =>
    exfalso
    exact hb1 (by simpa [φ] using (congrArg Subtype.val ho).symm)
  | some k =>
    exact ⟨k, k.2, by simpa [φ] using congrArg Subtype.val ho⟩

end Cfg56

end CFSG.CGT.T75O
