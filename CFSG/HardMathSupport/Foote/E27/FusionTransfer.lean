module

public import CFSG.HardMathSupport.Foote.E27.Fusion

public section

namespace CFSG.HardMathSupport.Foote.E27

open Subgroup

variable {K J : Type*} [Group K] [Group J]

theorem card_inf_centralizer_comap (e : K ≃* J) (T : Subgroup J) (x : K) :
    Nat.card ↥((T.comap (e : K →* J)) ⊓ centralizer ({x} : Set K)) =
      Nat.card ↥(T ⊓ centralizer ({e x} : Set J)) := by
  refine Nat.card_congr (Equiv.subtypeEquiv e.toEquiv fun y => ?_)
  change (y ∈ (T.comap (e : K →* J)) ⊓ centralizer ({x} : Set K)) ↔
    (e y ∈ T ⊓ centralizer ({e x} : Set J))
  simp only [mem_inf, mem_comap, mem_centralizer_singleton_iff]
  change (e y ∈ T ∧ y * x = x * y) ↔ (e y ∈ T ∧ e y * e x = e x * e y)
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rw [← map_mul, ← map_mul, h2]⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, e.injective ?_⟩
    rw [map_mul, map_mul]
    exact h2

theorem card_centralizer_equiv (e : K ≃* J) (x : K) :
    Nat.card ↥(centralizer ({e x} : Set J)) = Nat.card ↥(centralizer ({x} : Set K)) := by
  refine (Nat.card_congr (Equiv.subtypeEquiv e.toEquiv fun y => ?_)).symm
  change (y ∈ centralizer ({x} : Set K)) ↔ (e y ∈ centralizer ({e x} : Set J))
  simp only [mem_centralizer_singleton_iff]
  constructor
  · intro h2
    rw [← map_mul, ← map_mul, h2]
  · intro h2
    apply e.injective
    rw [map_mul, map_mul]
    exact h2

theorem card_comap_equiv (e : K ≃* J) (T : Subgroup J) :
    Nat.card ↥(T.comap (e : K →* J)) = Nat.card ↥T := by
  rw [Subgroup.comap_equiv_eq_map_symm]
  exact Subgroup.card_map_of_injective (MulEquiv.injective e.symm)

theorem exists_sylow_fusion_of_equiv [Finite J] (e : K ≃* J) (T : Subgroup J)
    (hTcard : Nat.card ↥T = 3 ^ (Nat.card J).factorization 3)
    (hgood : ∀ s ∈ T, orderOf s = 3 → FusGood T s) :
    ∃ S₀ : Sylow 3 K, ∀ s ∈ (S₀ : Subgroup K), orderOf s = 3 →
      FusGood (S₀ : Subgroup K) s := by
  have : Finite K := Finite.of_equiv J e.symm.toEquiv
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card ↥(T.comap (e : K →* J)) = 3 ^ (Nat.card K).factorization 3 := by
    rw [card_comap_equiv, hTcard, Nat.card_congr e.toEquiv]
  refine ⟨Sylow.ofCard (T.comap (e : K →* J)) hcard, fun s hs hs3 => ?_⟩
  have hsT : e s ∈ T := hs
  have hs3' : orderOf (e s) = 3 := by rw [MulEquiv.orderOf_eq]; exact hs3
  obtain ⟨σ, hk1, hk2⟩ := hgood (e s) hsT hs3'
  let σ' : K ≃* K := (e.trans σ).trans e.symm
  have hx : e (σ' s) = σ (e s) := by
    show e (e.symm (σ (e s))) = σ (e s)
    exact MulEquiv.apply_symm_apply e _
  refine ⟨σ', ?_, ?_⟩
  · show e (σ' s) ∈ T
    rw [hx]; exact hk1
  · have := card_inf_centralizer_comap e T (σ' s)
    rw [hx] at this
    show 81 ∣ Nat.card ↥((T.comap (e : K →* J)) ⊓ _)
    rw [this]
    exact hk2

theorem exists_sylow_gen_of_equiv [Finite J] (e : K ≃* J) (T : Subgroup J)
    (hTcard : Nat.card ↥T = 3 ^ (Nat.card J).factorization 3)
    (hgen : ∀ R' T' : Subgroup J, R' ≤ T → (∀ x ∈ R', x ^ 3 = 1) →
      (∀ x ∈ R', ∀ y ∈ R', x * y = y * x) → Nat.card ↥R' = 27 → T' ≤ R' → Nat.card ↥T' = 9 →
      ∃ r ∈ R', r ∉ T' ∧ 81 ∣ Nat.card ↥(centralizer ({r} : Set J))) :
    ∃ S₀ : Sylow 3 K, ∀ R' T' : Subgroup K, R' ≤ (S₀ : Subgroup K) → (∀ x ∈ R', x ^ 3 = 1) →
      (∀ x ∈ R', ∀ y ∈ R', x * y = y * x) → Nat.card ↥R' = 27 → T' ≤ R' → Nat.card ↥T' = 9 →
      ∃ r ∈ R', r ∉ T' ∧ 81 ∣ Nat.card ↥(centralizer ({r} : Set K)) := by
  have : Finite K := Finite.of_equiv J e.symm.toEquiv
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card ↥(T.comap (e : K →* J)) = 3 ^ (Nat.card K).factorization 3 := by
    rw [card_comap_equiv, hTcard, Nat.card_congr e.toEquiv]
  refine ⟨Sylow.ofCard (T.comap (e : K →* J)) hcard, fun R' T' hR hR3 hRc hRcard hTR hTcard => ?_⟩
  have hinj : Function.Injective (e : K →* J) := e.injective
  have := hgen (R'.map (e : K →* J)) (T'.map (e : K →* J)) ?_ ?_ ?_ ?_ (Subgroup.map_mono hTR) ?_
  · obtain ⟨r, hr, hrT, hdvd⟩ := this
    obtain ⟨r', hr', rfl⟩ := Subgroup.mem_map.mp hr
    refine ⟨r', hr', fun h => hrT (Subgroup.mem_map_of_mem _ h), ?_⟩
    rw [← card_centralizer_equiv e r']
    exact hdvd
  · rintro _ ⟨x, hx, rfl⟩
    exact hR hx
  · rintro _ ⟨x, hx, rfl⟩
    show e x ^ 3 = 1
    rw [← map_pow, hR3 x hx, map_one]
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    show e x * e y = e y * e x
    rw [← map_mul, ← map_mul, hRc x hx y hy]
  · rw [Subgroup.card_map_of_injective hinj, hRcard]
  · rw [Subgroup.card_map_of_injective hinj, hTcard]

end CFSG.HardMathSupport.Foote.E27

end
