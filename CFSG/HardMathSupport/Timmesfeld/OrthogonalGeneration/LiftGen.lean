module

public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.Lift
public import CFSG.Open.GLADefs

public section

open scoped commutatorElement

namespace CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration

open CFSG.Open

theorem odd_card_center_of_primeCore_eq_bot {Y : Type*} [Group Y] [Finite Y] {p : ℕ}
    (hp2 : p ≠ 2) (hp : p.Prime) (h : GLAPPrimeCore p Y = ⊥) :
    Odd (Nat.card (Subgroup.center Y)) := by
  by_contra hodd
  have h2 : 2 ∣ Nat.card (Subgroup.center Y) := by
    rcases Nat.even_or_odd (Nat.card (Subgroup.center Y)) with he | ho
    · exact even_iff_two_dvd.mp he
    · exact absurd ho hodd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center Y) 2 h2
  have hzo : orderOf (z : Y) = 2 := by rw [Subgroup.orderOf_coe]; exact hz
  set N : Subgroup Y := Subgroup.zpowers (z : Y) with hN
  have hNc : N ≤ Subgroup.center Y := by
    rw [hN, Subgroup.zpowers_le]; exact z.2
  have hNn : N.Normal := Subgroup.normal_of_le_center hNc
  have hcard : Nat.card N = 2 := by rw [hN, Nat.card_zpowers, hzo]
  have hcop : Nat.Coprime p (Nat.card N) := by
    rw [hcard]
    exact (Nat.coprime_primes hp Nat.prime_two).mpr hp2
  have hle : N ≤ GLAPPrimeCore p Y := le_sSup ⟨hNn, hcop⟩
  rw [h, le_bot_iff] at hle
  have : (z : Y) ∈ N := Subgroup.mem_zpowers _
  rw [hle] at this
  have hz1 : (z : Y) = 1 := by simpa using this
  rw [hz1] at hzo
  simp at hzo

variable {X : Type*} [Group X]

theorem le_iSup_centralizer_of_lifts [Finite X] {K : Subgroup X} (hK : commutator ↥K = ⊤)
    (hZ : Odd (Nat.card (Subgroup.center ↥K))) (ℰ : Set (Subgroup X))
    (hℰ : ∀ E ∈ ℰ, E ≤ Subgroup.normalizer (K : Set X)) (𝒢 : Set ↥K)
    (hgen : Subgroup.closure 𝒢 ⊔ Subgroup.center ↥K = ⊤)
    (hsq : ∀ y ∈ 𝒢, y ^ 2 ∈ Subgroup.center ↥K)
    (hfix : ∀ y ∈ 𝒢, ∃ E, ∃ hE : E ∈ ℰ, ∀ (a : X) (ha : a ∈ E),
      ((K.normalizerMonoidHom ⟨a, hℰ E hE ha⟩ : MulAut ↥K) y)⁻¹ * y ∈ Subgroup.center ↥K) :
    K ≤ ⨆ E ∈ ℰ, K ⊓ Subgroup.centralizer (E : Set X) := by
  set M : Subgroup ↥K := (⨆ E ∈ ℰ, K ⊓ Subgroup.centralizer (E : Set X)).subgroupOf K with hM
  have hy : ∀ y ∈ 𝒢, ∃ t ∈ M, t⁻¹ * y ∈ Subgroup.center ↥K := by
    intro y hy
    obtain ⟨t, ⟨ht2, htz⟩, -⟩ := existsUnique_involution_lift hZ (hsq y hy)
    obtain ⟨E, hE, hEfix⟩ := hfix y hy
    refine ⟨t, ?_, htz⟩
    rw [hM, Subgroup.mem_subgroupOf]
    have hcent : (t : X) ∈ Subgroup.centralizer (E : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have h1 := map_involution_lift hZ (K.normalizerMonoidHom ⟨a, hℰ E hE ha⟩) ht2 htz
        (hEfix a ha)
      have h2 := congrArg (fun x : ↥K => (x : X)) h1
      simp only [Subgroup.normalizerMonoidHom_apply_apply_coe] at h2
      exact (by
        calc a * (t : X) = a * t * a⁻¹ * a := by group
          _ = t * a := by rw [h2])
    have hmem : (t : X) ∈ K ⊓ Subgroup.centralizer (E : Set X) := ⟨t.2, hcent⟩
    exact (le_iSup₂ (f := fun E (_ : E ∈ ℰ) => K ⊓ Subgroup.centralizer (E : Set X)) E hE) hmem
  have hsup : M ⊔ Subgroup.center ↥K = ⊤ := by
    rw [eq_top_iff, ← hgen]
    refine sup_le ((Subgroup.closure_le _).mpr fun y hy' => ?_) le_sup_right
    obtain ⟨t, htM, htz⟩ := hy y hy'
    have : y = t * (t⁻¹ * y) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left htM) (Subgroup.mem_sup_right htz)
  have hMtop : M = ⊤ := eq_top_of_sup_center_eq_top hK hsup
  intro k hk
  have : (⟨k, hk⟩ : ↥K) ∈ M := by rw [hMtop]; trivial
  rwa [hM, Subgroup.mem_subgroupOf] at this

end CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration
