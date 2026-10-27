module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxNineA
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36V

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

@[expose] def SignalizerNineConjugateInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : X) (J : Subgroup X)
    (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 9)) (E : Subgroup X) (D : Finset (Fin 9)),
    Sig36 X t J 9 e E D → Sol78.signalizerCompletion E E ≠ ⊥ →
    ∀ M : Subgroup X, M ≤ normalizer (Sol78.signalizerCompletion E E : Set X) →
      IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))) →
      J ≤ M → normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X) →
      J ⊔ FooteLit.oddCoreIn M = M →
    ∀ (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 9))
      (ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 9)), IsPermAction θ ρ →
    ∀ Q S : Subgroup X,
      Q ≤ normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
        UnbalancedLayer.coreActionKernel M → IsPGroup 2 Q →
      Nat.card Q = 2 ^ (Nat.card ↥(normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
        UnbalancedLayer.coreActionKernel M)).factorization 2 → t ∈ Q → Q ≤ S →
      S ≤ normalizer (Sol78.signalizerCompletion E E : Set X) → IsPGroup 2 S →
      Nat.card S =
        2 ^ (Nat.card ↥(normalizer (Sol78.signalizerCompletion E E : Set X))).factorization 2 →
    ∀ s ∈ S, s ∉ Q →
      (∀ s' ∈ S, s' ∉ Q → orderOf s' < orderOf s → ∀ a' ∈ Q, ∀ g' : X, g'⁻¹ * a' * g' ≠ s') →
    ∀ a ∈ Q, ∀ g : X, g⁻¹ * a * g = s → g ∉ normalizer (Sol78.signalizerCompletion E E : Set X) →
      s ∈ normalizer (Q : Set X) → s * s ∈ Q →
    ∀ hsN : s ∈ normalizer (M : Set X), ρ ⟨s, hsN⟩ * ρ ⟨s, hsN⟩ = 1 → ρ ⟨s, hsN⟩ ≠ 1 → False

variable {X : Type} [Group X]

theorem signalizerNineStrongClosureInput_of_conjugate (hNC9 : SignalizerNineConjugateInput) :
    SignalizerNineStrongClosureInput := by
  intro X _ _ _ t J e E D S₀ hW M hMH hMpc hJM hHN hθ hsup Q S hQK hQ2 hQcard htQ hQS hSH hS2
    hScard
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨θ⟩ := hθ
  obtain ⟨ρ, hρ⟩ := exists_isPermAction (M := M) (by norm_num) (by norm_num) θ
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  have hQH : Q ≤ H := hQK.trans inf_le_left
  have hQc : Q ≤ UnbalancedLayer.coreActionKernel M := hQK.trans inf_le_right
  have hQeq : ∀ y ∈ S, y ∈ UnbalancedLayer.coreActionKernel M → y ∈ Q := by
    intro y hyS hyK
    set P : Subgroup X := S ⊓ (H ⊓ UnbalancedLayer.coreActionKernel M) with hPdef
    have hQP : Q ≤ P := le_inf hQS hQK
    have hP2 : IsPGroup 2 P := hS2.to_le inf_le_left
    obtain ⟨k, hk⟩ := hP2.exists_card_eq
    have hPdvd : Nat.card P ∣ Nat.card ↥(H ⊓ UnbalancedLayer.coreActionKernel M) :=
      card_dvd_of_le inf_le_right
    have hkle : k ≤ (Nat.card ↥(H ⊓ UnbalancedLayer.coreActionKernel M)).factorization 2 := by
      rw [hk] at hPdvd
      exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp hPdvd
    have hcard : Nat.card P ≤ Nat.card Q := by
      rw [hk, hQcard]
      exact Nat.pow_le_pow_right (by norm_num) hkle
    have hPQ : P = Q := (Subgroup.eq_of_le_of_card_ge hQP hcard).symm
    have hyP : y ∈ P := ⟨hyS, hSH hyS, hyK⟩
    rwa [hPQ] at hyP
  have hSNQ : ∀ b ∈ S, b ∈ normalizer (Q : Set X) := by
    intro b hbS
    have hbH : b ∈ H := hSH hbS
    rw [mem_normalizer_iff]
    intro q
    constructor
    · intro hq
      exact hQeq _ (mul_mem (mul_mem hbS (hQS hq)) (inv_mem hbS))
        (hρ.conj_mem_coreActionKernel (by norm_num) (hHN hbH) (hQc hq))
    · intro hq
      have h1 : q = b⁻¹ * (b * q * b⁻¹) * b⁻¹⁻¹ := by group
      rw [h1]
      exact hQeq _ (mul_mem (mul_mem (inv_mem hbS) (hQS hq)) (inv_mem (inv_mem hbS)))
        (hρ.conj_mem_coreActionKernel (by norm_num) (inv_mem (hHN hbH)) (hQc hq))
  intro a ha g hbS
  by_contra hbQ
  have hex : ∃ k : ℕ, ∃ s ∈ S, s ∉ Q ∧ orderOf s = k ∧ ∃ a' ∈ Q, ∃ g' : X, g'⁻¹ * a' * g' = s :=
    ⟨_, _, hbS, hbQ, rfl, a, ha, g, rfl⟩
  obtain ⟨s, hsS, hsQ, hso, a₀, ha₀, g₀, hg₀⟩ := Nat.find_spec hex
  have hmin : ∀ s' ∈ S, s' ∉ Q → orderOf s' < orderOf s → ∀ a' ∈ Q, ∀ g' : X,
      g'⁻¹ * a' * g' ≠ s' := by
    intro s' hs'S hs'Q hlt a' ha' g' hg'
    rw [hso] at hlt
    exact Nat.find_min hex hlt ⟨s', hs'S, hs'Q, rfl, a', ha', g', hg'⟩
  have hsH : s ∈ H := hSH hsS
  have hs2Q : s * s ∈ Q := by
    by_contra hs2
    have hs1 : s ≠ 1 := fun h => hsQ (h ▸ one_mem Q)
    have hs2' : IsPGroup 2 (zpowers s) := hS2.to_le (zpowers_le.mpr hsS)
    obtain ⟨m, hm⟩ := hs2'.exists_card_eq
    have hos : orderOf s = 2 ^ m := by rw [← Nat.card_zpowers]; exact hm
    have hm1 : m ≠ 0 := by
      rintro rfl
      rw [pow_zero, orderOf_eq_one_iff] at hos
      exact hs1 hos
    have hlt : orderOf (s * s) < orderOf s := by
      rw [← sq, orderOf_pow' s two_ne_zero, hos]
      have h1 : Nat.gcd (2 ^ m) 2 = 2 := by
        obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm1
        rw [pow_succ, Nat.gcd_mul_left_left]
      rw [h1]
      have h2 : 0 < 2 ^ m := by positivity
      omega
    refine hmin (s * s) (mul_mem hsS hsS) hs2 hlt (a₀ * a₀) (mul_mem ha₀ ha₀) g₀ ?_
    rw [← hg₀]
    group
  have hρs2 : ρ ⟨s, hHN hsH⟩ * ρ ⟨s, hHN hsH⟩ = 1 := by
    rw [← map_mul]
    have h1 : (⟨s, hHN hsH⟩ : ↥(normalizer (M : Set X))) * ⟨s, hHN hsH⟩ =
        ⟨s * s, mul_mem (hHN hsH) (hHN hsH)⟩ := rfl
    rw [h1]
    exact hρ.eq_one_of_mem_coreActionKernel (by norm_num) (hQc hs2Q)
  have hρs1 : ρ ⟨s, hHN hsH⟩ ≠ 1 := fun h1 =>
    hsQ (hQeq s hsS (hρ.mem_coreActionKernel _ h1))
  have hg₀H : g₀ ∉ H := by
    intro hg
    apply hsQ
    refine hQeq s hsS ?_
    rw [← hg₀]
    have h1 := hρ.conj_mem_coreActionKernel (by norm_num) (inv_mem (hHN hg)) (hQc ha₀)
    rwa [inv_inv] at h1
  exact hNC9 X t J e E D S₀ hW M hMH hMpc hJM hHN hsup θ ρ hρ Q S hQK hQ2 hQcard htQ hQS hSH hS2
    hScard s hsS hsQ hmin a₀ ha₀ g₀ hg₀ hg₀H (hSNQ s hsS) hs2Q (hHN hsH) hρs2 hρs1

end CFSG.ComponentClassification.SolMax
