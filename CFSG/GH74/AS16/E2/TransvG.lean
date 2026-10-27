module

public import CFSG.GH74.AS16.E2.Transv
public import CFSG.Quasithin.Background.A1cTransfer
public import CFSG.Adapters.Involutions
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.GH74.AS16.E2

open Subgroup CFSG.Quasithin

theorem false_of_isolated {G : Type} [Group G] [Finite G] (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) {S : Sylow 2 G} {t : G} (ht : orderOf t = 2)
    (htS : t ∈ (S : Subgroup G)) (htc : ∀ s ∈ (S : Subgroup G), s * t = t * s)
    (hwc : ∀ g : G, g⁻¹ * t * g ∈ (S : Subgroup G) → g⁻¹ * t * g = t) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2 : (⟨t, htS⟩ : (S : Subgroup G)) ^ 2 = 1 := by
    apply Subtype.ext
    have := pow_orderOf_eq_one t
    rwa [ht] at this
  have hz1 : (⟨t, htS⟩ : (S : Subgroup G)) ≠ 1 := by
    intro h
    have : t = 1 := congrArg Subtype.val h
    rw [this, orderOf_one] at ht
    omega
  let z : (S : Subgroup G) := ⟨t, htS⟩
  have hzZ : z ∈ Subgroup.center (S : Subgroup G) :=
    Subgroup.mem_center_iff.2 (fun s => Subtype.ext (htc s s.2))
  have hwc' : ∀ g : G, g⁻¹ * (z : G) * g ∈ (S : Subgroup G) → g⁻¹ * (z : G) * g = z := hwc
  obtain ⟨hG, hcen⟩ := CFSG.Adapters.glauberman_zStar S z hzZ (orderOf_eq_prime hz2 hz1) hwc'
  have hodd : CFSG.oddCore G = ⊥ := by
    rcases hs.eq_bot_or_eq_top_of_normal (CFSG.oddCore G) with h | h
    · exact h
    · exfalso
      apply CFSG.Adapters.not_mem_oddCore_of_orderOf_eq_two ht
      rw [h]; trivial
  have htcentG : t ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨c, hc, k, hk, rfl⟩ := hG g
    rw [hodd, Subgroup.mem_bot] at hk
    subst hk
    have := mem_centralizer_iff.1 hc t (Set.mem_singleton_iff.2 rfl)
    simpa using this.symm
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · rw [h, Subgroup.mem_bot] at htcentG
    rw [htcentG, orderOf_one] at ht
    omega
  · obtain ⟨a, b, hab⟩ := hnab
    apply hab
    have ha : a ∈ Subgroup.center G := by rw [h]; trivial
    exact (Subgroup.mem_center_iff.1 ha b).symm

theorem card_conjSubgroup {G : Type*} [Group G] (A : Subgroup G) (g : G) :
    Nat.card (conjSubgroup A g) = Nat.card A :=
  Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

theorem false_of_transv_fusion {G : Type} [Group G] [Finite G] (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) {T : Sylow 2 G} {A : Subgroup G} {z : G}
    (hz : orderOf z = 2) (hAT : A ≤ (T : Subgroup G)) (hzA : z ∈ A)
    (hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hA2 : ∀ a ∈ A, a * a = 1)
    (hcard : 4 < Nat.card A)
    (hinv : ∀ t ∈ (T : Subgroup G), t * t = 1 → t ∈ A)
    (hTA : ∀ t ∈ (T : Subgroup G), ∀ a ∈ A, t * a * t⁻¹ = a ∨ t * a * t⁻¹ = a * z)
    (hmove : ∀ b ∈ A, b ≠ 1 → b ≠ z → ∃ t ∈ (T : Subgroup G), t * b * t⁻¹ ≠ b) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz, pow_two] at this
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz
    omega
  have hzc : ∀ t ∈ (T : Subgroup G), t * z = z * t := by
    intro t ht
    rcases hTA t ht z hzA with h | h
    · calc t * z = (t * z * t⁻¹) * t := by group
        _ = z * t := by rw [h]
    · exfalso
      have h1 : t * z * t⁻¹ = 1 := by rw [h, hz2]
      apply hz1
      calc z = t⁻¹ * (t * z * t⁻¹) * t := by group
        _ = 1 := by rw [h1]; group
  have hTN : (T : Subgroup G) ≤ normalizer (A : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rcases hTA t ht x hx with h | h
      · rw [h]; exact hx
      · rw [h]; exact A.mul_mem hx hzA
    · intro hx
      have ht' : t⁻¹ ∈ (T : Subgroup G) := (T : Subgroup G).inv_mem ht
      have hx' : t⁻¹ * (t * x * t⁻¹) * t⁻¹⁻¹ ∈ A := by
        rcases hTA t⁻¹ ht' _ hx with h | h
        · rw [h]; exact hx
        · rw [h]; exact A.mul_mem hx hzA
      have e : t⁻¹ * (t * x * t⁻¹) * t⁻¹⁻¹ = x := by group
      rw [e] at hx'
      exact hx'
  have hwcl : IsWeaklyClosedIn A (T : Subgroup G) := by
    intro g hg
    have hle : conjSubgroup A g ≤ A := by
      intro x hx
      apply hinv x (hg hx)
      have h1 : (g * x * g⁻¹) * (g * x * g⁻¹) = 1 := hA2 _ (mem_conjSubgroup_iff.1 hx)
      have h2 : g * (x * x) * g⁻¹ = 1 := by
        calc g * (x * x) * g⁻¹ = (g * x * g⁻¹) * (g * x * g⁻¹) := by group
          _ = 1 := h1
      calc x * x = g⁻¹ * (g * (x * x) * g⁻¹) * g := by group
        _ = 1 := by rw [h2]; group
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSubgroup])
  have hfix : ∀ n ∈ normalizer (A : Set G), n⁻¹ * z * n = z :=
    fixed_of_transv_normalizer hz1 hzA hAcomm hA2 hcard hTN hTA hmove
  have hwc : ∀ g : G, g⁻¹ * z * g ∈ (T : Subgroup G) → g⁻¹ * z * g = z := by
    intro g hg
    have hu2 : (g⁻¹ * z * g) * (g⁻¹ * z * g) = 1 := by
      calc (g⁻¹ * z * g) * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
        _ = 1 := by rw [hz2]; group
    have huA : g⁻¹ * z * g ∈ A := hinv _ hg hu2
    obtain ⟨n, hn, hn2⟩ := burnside_fusion_lemma_centralizer T hAT hwcl (x := z)
      (y := g⁻¹ * z * g)
      (Subgroup.mem_centralizer_iff.2 fun w hw => (hAcomm z hzA w hw).symm)
      (Subgroup.mem_centralizer_iff.2 fun w hw => (hAcomm _ huA w hw).symm) rfl
    rw [← hn2]
    exact hfix n hn
  exact false_of_isolated hs hnab hz (hAT hzA) hzc hwc

end CFSG.GH74.AS16.E2
