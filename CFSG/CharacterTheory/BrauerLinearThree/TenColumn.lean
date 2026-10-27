module

public import CFSG.CharacterTheory.BrauerLinearThree.TenColumnNorm
public import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizersSupport

public section

open scoped BigOperators Classical

namespace CFSG.BrauerLinearThree

namespace TenColumn

open CFSG.TwoRankLowerBound.Helpers CFSG.LyonsUnitaryFour

variable {G : Type} [Group G] [Fintype G]

theorem global_column_count {t : G} (ht : t * t = 1) (K : Subgroup G) (ψ : K → ℂ)
    (basis : FiniteIrreducibleCharacterBasis G) :
    (Nat.card G : ℂ) * ∑ α, characterPairing (inducedFunction K ψ)
        (basis.representation α).character *
        ((basis.representation α).character t * (basis.representation α).character t /
          (basis.representation α).character 1) =
      (Nat.card K : ℂ)⁻¹ * ∑ k : K, ψ k *
        ((Nat.card (Subgroup.centralizer ({t} : Set G)) : ℂ) ^ 2 *
          (productCount (conjClassFinset t) (conjClassFinset t) (k : G)⁻¹ : ℂ)) := by
  set c : ℂ := (Nat.card (Subgroup.centralizer ({t} : Set G)) : ℂ) with hc
  have hfrobG : ∀ α : basis.index, characterPairing (inducedFunction K ψ)
      (basis.representation α).character =
      (Nat.card K : ℂ)⁻¹ * ∑ k : K, ψ k * (basis.representation α).character ((k : G)⁻¹) := by
    intro α
    rw [characterPairing_inducedFunction_left K ψ _ (fun x g => by
      simp only [FiniteComplexRepresentation.character, Representation.char_conj])]
    rfl
  have hprodG : ∀ x : G, (Nat.card G : ℂ) * ∑ α, (basis.representation α).character t *
      (basis.representation α).character t * (basis.representation α).character x /
        (basis.representation α).character 1 =
      c * c * (productCount (conjClassFinset t) (conjClassFinset t) x : ℂ) := fun x =>
    (involution_classes_product_character_formula basis t t ht ht x).symm
  simp_rw [hfrobG, ← sq, show c ^ 2 = c * c from sq c, ← hprodG]
  rw [Finset.mul_sum, Finset.mul_sum]
  simp_rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun α _ => ?_
  ring

theorem productCount_eq_card_invertingInvolutions {t : G}
    (hinvol : ∀ x : G, orderOf x = 2 ↔ IsConj x t) {k : G} (hk : k * k ≠ 1 ∨ k = 1) :
    productCount (conjClassFinset t) (conjClassFinset t) k⁻¹ =
      (invertingInvolutions k).card := by
  have hmemA : ∀ a : G, a ∈ conjClassFinset t ↔ a * a = 1 ∧ a ≠ 1 := by
    intro a
    simp only [conjClassFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [isConj_comm, ← hinvol, orderOf_eq_prime_iff, sq]
  unfold productCount
  refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨ha, hb⟩, hab⟩ := hp
    rw [hmemA] at ha hb
    rw [mem_invertingInvolutions]
    refine ⟨ha.1, ha.2, ?_⟩
    have ha' : p.1⁻¹ = p.1 := inv_eq_of_mul_eq_one_right ha.1
    have hb' : p.2 = p.1 * k⁻¹ := by rw [← hab, ← mul_assoc, ha.1, one_mul]
    have hb2 := hb.1
    rw [hb'] at hb2
    have h1 : p.1 * k⁻¹ * p.1 = k := by
      calc p.1 * k⁻¹ * p.1 = p.1 * k⁻¹ * (p.1 * k⁻¹) * k := by group
        _ = k := by rw [hb2, one_mul]
    have h2 : (p.1 * k⁻¹ * p.1)⁻¹ = k⁻¹ := by rw [h1]
    rw [mul_inv_rev, mul_inv_rev, inv_inv, ha', ← mul_assoc] at h2
    rw [ha']
    exact h2
  · rintro ⟨a₁, b₁⟩ h₁ ⟨a₂, b₂⟩ h₂ heq
    simp only at heq
    rw [Finset.mem_filter] at h₁ h₂
    have hb₁ : b₁ = a₁⁻¹ * k⁻¹ := by rw [← h₁.2, inv_mul_cancel_left]
    have hb₂ : b₂ = a₂⁻¹ * k⁻¹ := by rw [← h₂.2, inv_mul_cancel_left]
    rw [Prod.mk.injEq]
    exact ⟨heq, by rw [hb₁, hb₂, heq]⟩
  · intro a ha
    rw [mem_invertingInvolutions] at ha
    obtain ⟨ha2, ha1, hak⟩ := ha
    have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
    refine ⟨(a, a * k⁻¹), ?_, rfl⟩
    rw [Finset.mem_filter, Finset.mem_product, hmemA, hmemA]
    refine ⟨⟨⟨ha2, ha1⟩, ?_, ?_⟩, by rw [← mul_assoc, ha2, one_mul]⟩
    · have h1 : a * k⁻¹ * a = k := by
        have h := congrArg (·⁻¹) hak
        simp only [mul_inv_rev, inv_inv] at h
        rw [ha', ← mul_assoc] at h
        exact h
      calc a * k⁻¹ * (a * k⁻¹) = a * k⁻¹ * a * k⁻¹ := by group
        _ = 1 := by rw [h1, mul_inv_cancel]
    · intro h1
      have hak' : a = k := by
        have := congrArg (· * k) h1
        simpa using this
      subst hak'
      rcases hk with hk | hk
      · exact hk ha2
      · exact ha1 hk

variable {W K H : Subgroup G} (hWK : W ≤ K) (hKH : K ≤ H)
  (hcent : ∀ k ∈ K, ∀ w ∈ W, k * w = w * k)
  (hinv : ∀ h ∈ H, h ∉ K → ∀ w ∈ W, h * w * h⁻¹ = w⁻¹)
  (hKn : ∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K) (hHK : Nat.card H = 2 * Nat.card K)
  (hKH2 : ∀ x ∈ H, ∀ y ∈ H, x ∉ K → y ∉ K → x * y ∈ K)
  (hTI : ∀ g : G, ∀ w ∈ W, w ≠ 1 → g * w * g⁻¹ ∈ W → g ∈ H)

include hKH hcent hinv hKH2 hTI in
theorem column_identity (χ : W →* ℂˣ) (hχ : Odd (orderOf χ)) {w₀ : G} (hw₀ : w₀ ∈ W)
    (hw₀1 : torusTransfer hWK χ ⟨w₀, hWK hw₀⟩ ≠ 1) {t : G} (ht : orderOf t = 2)
    (hinvol : ∀ x : G, orderOf x = 2 ↔ IsConj x t)
    (basis : FiniteIrreducibleCharacterBasis G) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) (ρ τ : basis.index) (δ : ℤ)
    (hδ : δ = 1 ∨ δ = -1)
    (hT : ∀ g, torusColumn hWK χ g = 1 + δ * (basis.representation ρ).character g -
      δ * (basis.representation τ).character g)
    (hdeg : (Module.finrank ℂ (basis.representation τ).vector : ℤ) =
      Module.finrank ℂ (basis.representation ρ).vector + δ) :
    (Nat.card G : ℂ) * (((Module.finrank ℂ (basis.representation ρ).vector : ℂ) -
        (basis.representation ρ).character t) ^ 2 /
      ((Module.finrank ℂ (basis.representation ρ).vector : ℂ) *
        ((Module.finrank ℂ (basis.representation ρ).vector : ℂ) + δ))) =
      (Nat.card (Subgroup.centralizer ({t} : Set G)) : ℂ) ^ 2 *
        ((outerInvolutions K H).card : ℂ) ^ 2 / Nat.card K := by
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  set F : ℂ := (Module.finrank ℂ (basis.representation ρ).vector : ℂ) with hF
  set x : ℂ := (basis.representation ρ).character t with hx
  have hTt : torusColumn hWK χ t = 0 := by
    apply torusColumn_eq_zero_of_coprime hWK hcent χ
    rw [ht]
    exact Nat.coprime_two_left.mpr hχ
  have hδC : (δ : ℂ) = 1 ∨ (δ : ℂ) = -1 := by rcases hδ with h | h <;> rw [h] <;> norm_num
  have hτt : (basis.representation τ).character t = x + δ := by
    have h := hT t
    rw [hTt] at h
    rcases hδC with h' | h' <;> rw [h'] at h ⊢
    · linear_combination h
    · linear_combination -h
  have hFc : ∀ θ : basis.index, (basis.representation θ).character 1 =
      (Module.finrank ℂ (basis.representation θ).vector : ℂ) := fun θ =>
    (CFSG.Semidihedral.Principal.basis_character_one basis θ).1
  have hτF : (basis.representation τ).character 1 = F + δ := by
    rw [hFc]
    have h := congrArg (Int.cast : ℤ → ℂ) hdeg
    push_cast at h
    exact h
  have hcoef : ∀ α, characterPairing (torusColumn hWK χ) (basis.representation α).character =
      (if principal = α then 1 else 0) + (δ : ℂ) * (if ρ = α then 1 else 0) -
        (δ : ℂ) * (if τ = α then 1 else 0) := fun α =>
    CFSG.Semidihedral.Principal.LargePrimeTorus.characterPairing_column_eq basis principal
      hprincipal ρ τ δ _ hT α
  have hL : ∑ α, characterPairing (torusColumn hWK χ) (basis.representation α).character *
      ((basis.representation α).character t * (basis.representation α).character t /
        (basis.representation α).character 1) = (F - x) ^ 2 / (F * (F + δ)) := by
    simp_rw [hcoef]
    rw [CFSG.Semidihedral.Principal.LargePrimeTorus.sum_column_coefficients principal ρ τ (δ : ℂ)
      (fun α => (basis.representation α).character t * (basis.representation α).character t /
        (basis.representation α).character 1)]
    simp only [hprincipal, Pi.one_apply, mul_one, div_one, hτt, hτF, hFc ρ]
    have hF0 : F ≠ 0 := by
      have h := irreducible_character_degree_ne_zero _ (basis.irreducible ρ)
      rw [hFc] at h
      exact h
    have hFδ0 : F + δ ≠ 0 := by
      have h := irreducible_character_degree_ne_zero _ (basis.irreducible τ)
      rw [hτF] at h
      exact h
    rw [← CFSG.Semidihedral.Principal.LargePrimeTorus.column_bracket_eq hδC hF0 hFδ0]
    ring
  have hR := global_column_count htt K (fun k => 1 - (torusTransfer hWK χ k : ℂ)) basis
  rw [← torusColumn, hL] at hR
  rw [hR]
  have hcount := sum_torusTransfer_involution_count hWK hKH hcent hinv hKH2 hTI χ hχ hw₀ hw₀1
  have hterm : ∀ k : K, (1 - (torusTransfer hWK χ k : ℂ)) *
      ((Nat.card (Subgroup.centralizer ({t} : Set G)) : ℂ) ^ 2 *
        (productCount (conjClassFinset t) (conjClassFinset t) (k : G)⁻¹ : ℂ)) =
      (Nat.card (Subgroup.centralizer ({t} : Set G)) : ℂ) ^ 2 *
        ((1 - (torusTransfer hWK χ k : ℂ)) * ((invertingInvolutions (k : G)).card : ℂ)) := by
    intro k
    by_cases hk : torusTransfer hWK χ k = 1
    · rw [hk, Units.val_one, sub_self, zero_mul, zero_mul, mul_zero]
    · have hk' : (k : G) * k ≠ 1 ∨ (k : G) = 1 := by
        by_contra hcon
        push Not at hcon
        apply hk
        apply torusTransfer_eq_one_of_eq_inv hWK hcent χ hχ
        have hkk : k * k = 1 := Subtype.ext hcon.1
        rw [← map_inv, inv_eq_of_mul_eq_one_right hkk]
      rw [productCount_eq_card_invertingInvolutions hinvol hk']
      ring
  rw [Finset.sum_congr rfl fun k _ => hterm k, ← Finset.mul_sum, hcount]
  ring

include hKH hcent hinv hKn hHK hKH2 hTI in
theorem exists_odd_column (χ : W →* ℂˣ) (hχ : Odd (orderOf χ)) {w₀ : G} (hw₀ : w₀ ∈ W)
    (hw₀1 : torusTransfer hWK χ ⟨w₀, hWK hw₀⟩ ≠ 1) {t : G} (ht : orderOf t = 2)
    (hinvol : ∀ x : G, orderOf x = 2 ↔ IsConj x t)
    (basis : FiniteIrreducibleCharacterBasis G) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) :
    ∃ (ρ : basis.index) (δ : ℤ), (δ = 1 ∨ δ = -1) ∧ ρ ≠ principal ∧
      Odd (Module.finrank ℂ (basis.representation ρ).vector) ∧
      0 < (Module.finrank ℂ (basis.representation ρ).vector : ℤ) + δ ∧
      (∀ g, starRingEnd ℂ ((basis.representation ρ).character g) =
        (basis.representation ρ).character g) ∧
      (Nat.card G : ℂ) * (((Module.finrank ℂ (basis.representation ρ).vector : ℂ) -
          (basis.representation ρ).character t) ^ 2 /
        ((Module.finrank ℂ (basis.representation ρ).vector : ℂ) *
          ((Module.finrank ℂ (basis.representation ρ).vector : ℂ) + δ))) =
        (Nat.card (Subgroup.centralizer ({t} : Set G)) : ℂ) ^ 2 *
          ((outerInvolutions K H).card : ℂ) ^ 2 / Nat.card K := by
  obtain ⟨ρ, τ, δ, hδ, hρo, hτo, hρτ, hT, hdeg, hρr, hτr⟩ :=
    torusColumn_decomposition hWK hKH hcent hinv hKn hHK hTI χ hχ hw₀1 basis principal hprincipal
  have hdegpos : ∀ θ : basis.index, 0 < (Module.finrank ℂ (basis.representation θ).vector : ℤ) :=
    fun θ => by
      have h := irreducible_character_degree_ne_zero _ (basis.irreducible θ)
      rw [FiniteComplexRepresentation.character, Representation.char_one] at h
      have : Module.finrank ℂ (basis.representation θ).vector ≠ 0 := by exact_mod_cast h
      omega
  by_cases hρodd : Odd (Module.finrank ℂ (basis.representation ρ).vector)
  · exact ⟨ρ, δ, hδ, hρo, hρodd, hdeg ▸ hdegpos τ, hρr, column_identity hWK hKH hcent hinv hKH2
      hTI χ hχ hw₀ hw₀1 ht hinvol basis principal hprincipal ρ τ δ hδ hT hdeg⟩
  · have hτodd : Odd (Module.finrank ℂ (basis.representation τ).vector) := by
      rw [Nat.not_odd_iff_even] at hρodd
      obtain ⟨k, hk⟩ := hρodd
      have h : (Module.finrank ℂ (basis.representation τ).vector : ℤ) = 2 * k + δ := by
        rw [hdeg, hk]
        push_cast
        ring
      rcases hδ with rfl | rfl
      · exact ⟨k, by omega⟩
      · exact ⟨k - 1, by omega⟩
    have hδ' : -δ = 1 ∨ -δ = -1 := by rcases hδ with rfl | rfl <;> simp
    have hT' : ∀ g, torusColumn hWK χ g = 1 + ((-δ : ℤ) : ℂ) *
        (basis.representation τ).character g - ((-δ : ℤ) : ℂ) *
          (basis.representation ρ).character g := by
      intro g
      rw [hT g]
      push_cast
      ring
    have hdeg' : (Module.finrank ℂ (basis.representation ρ).vector : ℤ) =
        Module.finrank ℂ (basis.representation τ).vector + -δ := by
      rw [hdeg]
      ring
    exact ⟨τ, -δ, hδ', hτo, hτodd, hdeg' ▸ hdegpos ρ, hτr, column_identity hWK hKH hcent hinv
      hKH2 hTI χ hχ hw₀ hw₀1 ht hinvol basis principal hprincipal τ ρ (-δ) hδ' hT' hdeg'⟩

end TenColumn

end CFSG.BrauerLinearThree
