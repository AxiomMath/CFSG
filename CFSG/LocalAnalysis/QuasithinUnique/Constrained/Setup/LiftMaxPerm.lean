module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open Equiv CFSG.ABGLocalTools

section Five

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

omit [DecidableEq Ω] in
theorem exists_equiv_fin_five (h5 : Fintype.card Ω = 5) (ω : Ω) : ∃ e : Ω ≃ Fin 5, e ω = 4 := by
  let e₀ : Ω ≃ Fin 5 := Fintype.equivFinOfCardEq h5
  refine ⟨e₀.trans (Equiv.swap (e₀ ω) 4), ?_⟩
  simp

theorem sq_eq_one_of_fix_alt (h5 : Fintype.card Ω = 5) (ω : Ω) (σ : Perm Ω) (hω : σ ω = ω)
    (hs : Perm.sign σ = 1) (h4 : σ ^ 4 = 1) : σ * σ = 1 := by
  obtain ⟨e, he⟩ := exists_equiv_fin_five h5 ω
  have key : ∀ τ : Perm (Fin 5), τ 4 = 4 → Perm.sign τ = 1 → τ ^ 4 = 1 → τ * τ = 1 := by
    decide +kernel
  let φ : Perm Ω ≃* Perm (Fin 5) := Equiv.permCongrHom e
  have hφ : ∀ x, φ σ x = e (σ (e.symm x)) := fun x => rfl
  have h1 := key (φ σ) (by rw [hφ, ← he, e.symm_apply_apply, hω])
    (by rw [show φ σ = e.permCongr σ from rfl, Perm.sign_permCongr]; exact hs)
    (by rw [← map_pow, h4, map_one])
  rw [← map_mul] at h1
  exact φ.map_eq_one_iff.1 h1

theorem card_inv_five (h5 : Fintype.card Ω = 5) (ω : Ω) :
    Nat.card {σ : Perm Ω // σ ω = ω ∧ Perm.sign σ = 1 ∧ σ * σ = 1} = 4 := by
  obtain ⟨e, he⟩ := exists_equiv_fin_five h5 ω
  let φ : Perm Ω ≃* Perm (Fin 5) := Equiv.permCongrHom e
  have hφ : ∀ σ x, φ σ x = e (σ (e.symm x)) := fun σ x => rfl
  have h4 : Nat.card {τ : Perm (Fin 5) // τ 4 = 4 ∧ Perm.sign τ = 1 ∧ τ * τ = 1} = 4 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    decide +kernel
  rw [← h4]
  refine Nat.card_congr (Equiv.subtypeEquiv φ.toEquiv fun σ => ?_)
  show _ ↔ φ σ 4 = 4 ∧ Perm.sign (φ σ) = 1 ∧ φ σ * φ σ = 1
  rw [hφ, ← he, e.symm_apply_apply, e.apply_eq_iff_eq,
    show Perm.sign (φ σ) = Perm.sign σ from Perm.sign_permCongr e σ, ← map_mul, φ.map_eq_one_iff]

theorem card_alt_five (h5 : Fintype.card Ω = 5) : Nat.card (alternatingGroup Ω) = 60 := by
  have : Nontrivial Ω := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, h5]
  rfl

theorem card_sylow_alt_five (h5 : Fintype.card Ω = 5) {P : Subgroup (Perm Ω)}
    (hP : IsSylowOf 2 P (alternatingGroup Ω)) : Nat.card P = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h60 : (60 : ℕ).factorization 2 = 2 := by
    have h : (60 : ℕ) = 2 ^ 2 * 15 := by norm_num
    rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization Nat.prime_two,
      Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    rfl
  rw [hP.card_eq, card_alt_five h5, h60]
  norm_num

theorem alt5_order_four (h5 : Fintype.card Ω = 5) {P : Subgroup (Perm Ω)}
    (hPalt : ∀ σ ∈ P, Perm.sign σ = 1) (hP : Nat.card P = 4) :
    ∃ ω : Ω, (∀ σ ∈ P, σ ω = ω) ∧ (∀ ω', (∀ σ ∈ P, σ ω' = ω') → ω' = ω) ∧
      ∀ g : Perm Ω, g ∈ Subgroup.normalizer (P : Set (Perm Ω)) ↔ g ω = ω := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPp : IsPGroup 2 P := IsPGroup.of_card (n := 2) (by rw [hP]; norm_num)
  have hmod := hPp.card_modEq_card_fixedPoints Ω
  let Fix : Finset Ω := Finset.univ.filter fun ω => ∀ σ ∈ P, σ ω = ω
  have hfix : Nat.card (MulAction.fixedPoints (↥P) Ω) = Fix.card := by
    have e : MulAction.fixedPoints (↥P) Ω = {ω : Ω | ∀ σ ∈ P, σ ω = ω} := by
      ext ω
      simp only [MulAction.mem_fixedPoints, Set.mem_ofPred_eq]
      constructor
      · intro h σ hσ
        exact h ⟨σ, hσ⟩
      · intro h σ
        exact h σ σ.2
    rw [e, Nat.card_eq_fintype_card, Fintype.card_subtype]
    rfl
  rw [hfix, Nat.card_eq_fintype_card, h5] at hmod
  have hodd : Fix.card % 2 = 1 := by
    have := hmod
    unfold Nat.ModEq at this
    omega
  have hle3 : ¬ 3 ≤ Fix.card := by
    intro h3
    have hall : ∀ σ ∈ P, σ = 1 := by
      intro σ hσ
      have hsub : σ.support ⊆ Fixᶜ := by
        intro x hx
        rw [Perm.mem_support] at hx
        simp only [Finset.mem_compl, Fix, Finset.mem_filter, Finset.mem_univ, true_and]
        intro hxF
        exact hx (hxF σ hσ)
      have hcard : σ.support.card ≤ 2 := by
        have := Finset.card_le_card hsub
        rw [Finset.card_compl, h5] at this
        omega
      by_contra hne
      have h0 : σ.support.card ≠ 0 := fun h => hne (Perm.card_support_eq_zero.1 h)
      have h1 := Perm.card_support_ne_one σ
      have h2 : σ.support.card = 2 := by omega
      have hsw := (Perm.card_support_eq_two.1 h2).sign_eq
      rw [hPalt σ hσ] at hsw
      exact absurd hsw (by decide)
    have : P = ⊥ := (Subgroup.eq_bot_iff_forall P).2 hall
    rw [this, Subgroup.card_bot] at hP
    omega
  have hone : Fix.card = 1 := by omega
  obtain ⟨ω, hω⟩ := Finset.card_eq_one.1 hone
  have hωfix : ∀ σ ∈ P, σ ω = ω := by
    have : ω ∈ Fix := by rw [hω]; exact Finset.mem_singleton_self _
    simpa [Fix] using this
  have huniq : ∀ ω', (∀ σ ∈ P, σ ω' = ω') → ω' = ω := by
    intro ω' h
    have : ω' ∈ Fix := by simpa [Fix] using h
    rw [hω] at this
    exact Finset.mem_singleton.1 this
  refine ⟨ω, hωfix, huniq, fun g => ⟨fun hg => ?_, fun hg => ?_⟩⟩
  · apply huniq
    intro σ hσ
    have h1 : g⁻¹ * σ * g ∈ P := by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem hg) σ).1 hσ
      simpa using this
    have h2 := hωfix _ h1
    have h3 : σ (g ω) = g ω := by
      have := congrArg g h2
      simpa [Perm.mul_apply] using this
    exact h3
  · let S : Set (Perm Ω) := {σ | σ ω = ω ∧ Perm.sign σ = 1 ∧ σ * σ = 1}
    have hPS : (P : Set (Perm Ω)) ⊆ S := by
      intro σ hσ
      refine ⟨hωfix σ hσ, hPalt σ hσ, sq_eq_one_of_fix_alt h5 ω σ (hωfix σ hσ) (hPalt σ hσ) ?_⟩
      have := pow_card_eq_one' (x := (⟨σ, hσ⟩ : ↥P))
      rw [hP] at this
      exact congrArg Subtype.val this
    have hScard : S.ncard = 4 := (Nat.card_coe_set_eq S).symm.trans (card_inv_five h5 ω)
    have hPcard : (P : Set (Perm Ω)).ncard = 4 := (Nat.card_coe_set_eq _).symm.trans hP
    have hPSeq : (P : Set (Perm Ω)) = S :=
      Set.eq_of_subset_of_ncard_le hPS (by rw [hScard, hPcard]) (Set.toFinite S)
    have hinv : ∀ g : Perm Ω, g ω = ω → ∀ σ ∈ P, g * σ * g⁻¹ ∈ P := by
      intro g hgω σ hσ
      have hσS : σ ∈ S := hPS hσ
      rw [← SetLike.mem_coe, hPSeq]
      refine ⟨?_, ?_, ?_⟩
      · have hg' : g⁻¹ ω = ω := by rw [Perm.inv_eq_iff_eq]; exact hgω.symm
        simp [Perm.mul_apply, hg', hσS.1, hgω]
      · rw [map_mul, map_mul, map_inv, hσS.2.1]
        simp
      · have : g * σ * g⁻¹ * (g * σ * g⁻¹) = g * (σ * σ) * g⁻¹ := by group
        rw [this, hσS.2.2]
        group
    have hgω : g ω = ω := hg
    have hgi : g⁻¹ ω = ω := by rw [Perm.inv_eq_iff_eq]; exact hgω.symm
    rw [Subgroup.mem_normalizer_iff]
    intro σ
    constructor
    · intro hσ
      exact hinv g hgω σ hσ
    · intro hσ
      have := hinv g⁻¹ hgi _ hσ
      simpa [mul_assoc] using this

end Five

end CFSG.QuasithinUnique.Setup.Lift
