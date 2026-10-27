module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxEightA
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxEightG

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

@[expose] def SignalizerNineEightLiftInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : X) (J : Subgroup X)
    (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 9)) (E : Subgroup X) (D : Finset (Fin 9)),
    Sig36 X t J 9 e E D → Sol78.signalizerCompletion E E ≠ ⊥ →
    ∀ M : Subgroup X, M ≤ normalizer (Sol78.signalizerCompletion E E : Set X) →
      IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))) →
      J ≤ M → normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X) →
      J ⊔ FooteLit.oddCoreIn M = M →
    ∀ (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 9))
      (ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 9)), IsPermAction θ ρ →
      (∀ (x : X) (hx : x ∈ M), x * x = 1 → (ρ ⟨x, le_normalizer hx⟩).support.card = 4 →
        ∀ K : Subgroup X, K ≤ centralizer ({x} : Set X) →
          IsPComponent 2 (K.subgroupOf (centralizer ({x} : Set X))) →
          IsEmpty (↥K ⧸ pPrimeCore 2 ↥K ≃* alternatingGroup (Fin 9))) →
    ∀ Q S : Subgroup X,
      Q ≤ normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
        UnbalancedLayer.coreActionKernel M → IsPGroup 2 Q →
      Nat.card Q = 2 ^ (Nat.card ↥(normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
        UnbalancedLayer.coreActionKernel M)).factorization 2 → t ∈ Q → Q ≤ S →
      S ≤ normalizer (Sol78.signalizerCompletion E E : Set X) → IsPGroup 2 S →
      Nat.card S =
        2 ^ (Nat.card ↥(normalizer (Sol78.signalizerCompletion E E : Set X))).factorization 2 →
      (∀ y ∈ S, y * t = t * y) →
      (∀ y ∈ Q, orderOf y = 2 →
        centralizer ({y} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X)) →
      (∀ x y : X, y ∈ S → y ∉ Q → y ∈ Q.map (MulAut.conj x).toMonoidHom →
        Q ⊓ Q.map (MulAut.conj x).toMonoidHom = ⊥) →
    ∀ s ∈ S, s ∉ Q → ∀ g : X, g⁻¹ * t * g = s →
      g ∉ normalizer (Sol78.signalizerCompletion E E : Set X) → s * s = 1 →
      (∀ y ∈ Q, y * s = s * y → y ≠ 1 → ∀ hy : g * y * g⁻¹ ∈ normalizer (M : Set X),
        6 ≤ (ρ ⟨g * y * g⁻¹, hy⟩).support.card) →
    ∀ hsN : s ∈ normalizer (M : Set X), ρ ⟨s, hsN⟩ * ρ ⟨s, hsN⟩ = 1 → ρ ⟨s, hsN⟩ ≠ 1 →
      5 ≤ (ρ ⟨s, hsN⟩).support.card → ρ ⟨s, hsN⟩ ∈ alternatingGroup (Fin 9) →
      (∃ q ∈ Q, ∃ m ∈ S, m ∈ M ∧ (∀ y ∈ Q, y * m = m * y) ∧ s = q * m) →
      Q = zpowers t →
    ∀ f ∈ normalizer (Sol78.signalizerCompletion E E : Set X), f * s = s * f → f * t = t * f →
      (f * f = 1 ∨ f * f = t) →
      ∀ hfN : f ∈ normalizer (M : Set X), (ρ ⟨f, hfN⟩).support.card = 2 → False

theorem signalizerNineEightEvenInput_of_lift (hL : SignalizerNineEightLiftInput) :
    SignalizerNineEightEvenInput := by
  intro X _ _ _ t J e E D S₀ hW M hMH hMpc hJM hHN hsup θ ρ hρ hNoA9 Q Sc hQK hQ2 hQcard htQ hQS
    hSH hS2 hScard htZ hCQ hd3 s hsS hsQ g hgs hgH hs2 hd4 hsN hρs2 hρs1 h5 hsA hsplit hQt
    h hhH hhN
  classical
  by_contra hodd
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  have htH : t ∈ H := (hQK htQ).1
  have htK : t ∈ UnbalancedLayer.coreActionKernel M := (hQK htQ).2
  have hto : orderOf t = 2 := S₀.pair.1.1
  have ht2 : t * t = 1 := by rw [← sq, ← hto, pow_orderOf_eq_one]
  have ht1 : t ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hto
    exact absurd hto (by norm_num)
  have hQ2' : Nat.card Q = 2 := by rw [hQt, Nat.card_zpowers, hto]
  have hK2 : ∀ P : Subgroup X, P ≤ H ⊓ UnbalancedLayer.coreActionKernel M → IsPGroup 2 P →
      Nat.card P ≤ 2 := by
    intro P hPK hP2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp hP2
    have hdvd : 2 ^ k ∣ Nat.card ↥(H ⊓ UnbalancedLayer.coreActionKernel M) := by
      rw [← hk]
      exact Subgroup.card_dvd_of_le hPK
    have hkle := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two
      Nat.card_pos.ne').mp hdvd
    have h1 : 2 ^ (Nat.card ↥(H ⊓ UnbalancedLayer.coreActionKernel M)).factorization 2 = 2 := by
      rw [← hQcard, hQ2']
    rw [hk]
    calc 2 ^ k ≤ 2 ^ (Nat.card ↥(H ⊓ UnbalancedLayer.coreActionKernel M)).factorization 2 :=
          Nat.pow_le_pow_right (by norm_num) hkle
      _ = 2 := h1
  have hsH : s ∈ H := hSH hsS
  have hst : s * t = t * s := (htZ s hsS)
  set σ := ρ ⟨s, hHN hsH⟩ with hσdef
  obtain ⟨a, ha⟩ : ∃ a, σ a ≠ a := by
    by_contra h1
    push Not at h1
    exact hρs1 (Equiv.ext h1)
  have hσa : σ (σ a) = a := by rw [← Perm.mul_apply, hρs2, Perm.one_apply]
  have hτσ : swap a (σ a) * σ = σ * swap a (σ a) := by
    rw [Equiv.mul_swap_eq_swap_mul, hσa, swap_comm]
  have hhodd : Perm.sign (ρ ⟨h, hhN⟩) = -1 := by
    rcases Int.units_eq_one_or (Perm.sign (ρ ⟨h, hhN⟩)) with h1 | h1
    · exact absurd (Perm.mem_alternatingGroup.mpr h1) hodd
    · exact h1
  have hbA : (ρ ⟨h, hhN⟩)⁻¹ * swap a (σ a) ∈ alternatingGroup (Fin 9) := by
    rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_inv, hhodd, Perm.sign_swap ha.symm]
    decide
  obtain ⟨q, hq⟩ := θ.surjective ⟨_, hbA⟩
  obtain ⟨⟨m, hm⟩, rfl⟩ := QuotientGroup.mk_surjective q
  have hmρ : ρ ⟨m, hHN (hMH hm)⟩ = (ρ ⟨h, hhN⟩)⁻¹ * swap a (σ a) := by
    have h1 := hρ.apply_of_mem (by norm_num) ⟨m, hm⟩
    rw [hq] at h1
    exact h1
  have hh'H : h * m ∈ H := H.mul_mem hhH (hMH hm)
  have hh'ρ : ρ ⟨h * m, hHN hh'H⟩ = swap a (σ a) := by
    have h1 : (⟨h * m, hHN hh'H⟩ : ↥(normalizer (M : Set X))) = ⟨h, hhN⟩ * ⟨m, hHN (hMH hm)⟩ :=
      rfl
    rw [h1, map_mul, hmρ, mul_inv_cancel_left]
  have hcomm : ρ ⟨h * m, hHN hh'H⟩ * ρ ⟨s, hHN hsH⟩ = ρ ⟨s, hHN hsH⟩ * ρ ⟨h * m, hHN hh'H⟩ := by
    rw [hh'ρ]
    exact hτσ
  have hh2 : ρ ⟨h * m, hHN hh'H⟩ * ρ ⟨h * m, hHN hh'H⟩ = 1 := by
    rw [hh'ρ, swap_mul_self]
  obtain ⟨f, hfH, hfs, hft, hfρ, hf2⟩ := exists_commute_of_rho_involution_kernel_two hρ hMH hHN
    htH ht2 ht1 htK hK2 hsH hs2 hst hsA hh'H hcomm hh2
  refine hL X t J e E D S₀ hW M hMH hMpc hJM hHN hsup θ ρ hρ hNoA9 Q Sc hQK hQ2 hQcard htQ hQS
    hSH hS2 hScard htZ hCQ hd3 s hsS hsQ g hgs hgH hs2 hd4 hsN hρs2 hρs1 h5 hsA hsplit hQt f hfH
    hfs hft hf2 (hHN hfH) ?_
  rw [hfρ, hh'ρ]
  exact Perm.card_support_swap ha.symm

end CFSG.ComponentClassification.SolMax
