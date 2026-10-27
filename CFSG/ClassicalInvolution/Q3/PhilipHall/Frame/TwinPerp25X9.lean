module

public import CFSG.ClassicalInvolution.Q3.Basic

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25S.X

open scoped MatrixGroups
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3

section SL2

@[expose] def sl23u : SL(2, ZMod 3) := ⟨!![1, 1; 0, 1], by decide⟩

@[expose] def sl23m : SL(2, ZMod 3) := ⟨!![-1, 0; 0, -1], by decide⟩

theorem sl23_u3 : sl23u ^ 3 = 1 := by decide +kernel

theorem sl23_neg_u3 : (sl23m * sl23u) ^ 3 ≠ 1 := by decide +kernel

theorem sl23_decomp : ∀ g : SL(2, ZMod 3), ∃ q : SL(2, ZMod 3), q ^ 4 = 1 ∧
    ∃ k : Fin 3, g = q * sl23u ^ (k : ℕ) := by decide +kernel

theorem sl23_cent : ∀ c : SL(2, ZMod 3), (∀ q : SL(2, ZMod 3), q ^ 4 = 1 → c * q = q * c) →
    c = 1 ∨ c = sl23m := by decide +kernel

theorem sl23_card4 : (Finset.univ.filter fun g : SL(2, ZMod 3) => g ^ 4 = 1).card = 8 := by
  decide +kernel

theorem sl23_mu_comm : sl23m * sl23u = sl23u * sl23m := by decide +kernel

theorem sl23_hom_eq_id_of_fix (γ : SL(2, ZMod 3) →* SL(2, ZMod 3))
    (hγ : ∀ q : SL(2, ZMod 3), q ^ 4 = 1 → γ q = q) : ∀ g, γ g = g := by
  have hu : γ sl23u = sl23u := by
    have hc : ∀ q : SL(2, ZMod 3), q ^ 4 = 1 →
        (sl23u⁻¹ * γ sl23u) * q = q * (sl23u⁻¹ * γ sl23u) := by
      intro q hq
      have hq' : (sl23u * q * sl23u⁻¹) ^ 4 = 1 := by rw [conj_pow, hq]; group
      have h1 := hγ _ hq'
      rw [map_mul, map_mul, hγ q hq, map_inv] at h1
      calc sl23u⁻¹ * γ sl23u * q = sl23u⁻¹ * (γ sl23u * q * (γ sl23u)⁻¹) * γ sl23u := by group
        _ = sl23u⁻¹ * (sl23u * q * sl23u⁻¹) * γ sl23u := by rw [h1]
        _ = q * (sl23u⁻¹ * γ sl23u) := by group
    rcases sl23_cent _ hc with h | h
    · calc γ sl23u = sl23u * (sl23u⁻¹ * γ sl23u) := by group
        _ = sl23u := by rw [h, mul_one]
    · exfalso
      have h3 : (γ sl23u) ^ 3 = 1 := by rw [← map_pow, sl23_u3, map_one]
      have : γ sl23u = sl23m * sl23u := by
        calc γ sl23u = sl23u * (sl23u⁻¹ * γ sl23u) := by group
          _ = sl23u * sl23m := by rw [h]
          _ = sl23m * sl23u := sl23_mu_comm.symm
      rw [this] at h3
      exact sl23_neg_u3 h3
  intro g
  obtain ⟨q, hq, k, rfl⟩ := sl23_decomp g
  rw [map_mul, map_pow, hγ q hq, hu]

theorem fix_of_fix_sylow {X : Type} [Group X] {A Q : Subgroup X} (e : A ≃* SL(2, ZMod 3))
    (hQeq : ∀ a ∈ A, a ^ 4 = 1 → a ∈ Q) (β : MulAut X) (hβA : ∀ a ∈ A, β a ∈ A)
    (hβQ : ∀ q ∈ Q, β q = q) : ∀ a ∈ A, β a = a := by
  let γ : SL(2, ZMod 3) →* SL(2, ZMod 3) :=
    { toFun := fun s => e ⟨β (e.symm s : X), hβA _ (e.symm s).2⟩
      map_one' := by
        have : (⟨β ((e.symm 1 : A) : X), hβA _ (e.symm 1).2⟩ : A) = 1 := by
          apply Subtype.ext
          simp
        simp [this]
      map_mul' := by
        intro s t
        have : (⟨β ((e.symm (s * t) : A) : X), hβA _ (e.symm (s * t)).2⟩ : A) =
            ⟨β ((e.symm s : A) : X), hβA _ (e.symm s).2⟩ *
              ⟨β ((e.symm t : A) : X), hβA _ (e.symm t).2⟩ := by
          apply Subtype.ext
          simp
        show e ⟨β ((e.symm (s * t) : A) : X), hβA _ (e.symm (s * t)).2⟩ = _
        rw [this, map_mul] }
  have hγ : ∀ q : SL(2, ZMod 3), q ^ 4 = 1 → γ q = q := by
    intro s hs
    have h4 : ((e.symm s : A) : X) ^ 4 = 1 := by
      have : (e.symm s) ^ 4 = 1 := by rw [← map_pow, hs, map_one]
      have := congrArg Subtype.val this
      simpa using this
    have hmem := hQeq _ (e.symm s).2 h4
    have hfix := hβQ _ hmem
    show e ⟨β (e.symm s : X), hβA _ (e.symm s).2⟩ = s
    have : (⟨β (e.symm s : X), hβA _ (e.symm s).2⟩ : A) = e.symm s := Subtype.ext hfix
    rw [this, MulEquiv.apply_symm_apply]
  intro a ha
  have h := sl23_hom_eq_id_of_fix γ hγ (e ⟨a, ha⟩)
  have h' : e ⟨β a, hβA a ha⟩ = e ⟨a, ha⟩ := by
    have : e ⟨β a, hβA a ha⟩ = γ (e ⟨a, ha⟩) := by
      show _ = e ⟨β (e.symm (e ⟨a, ha⟩) : X), _⟩
      simp
    rw [this, h]
  have := congrArg Subtype.val (e.injective h')
  exact this

theorem mem_of_pow_four_eq_one {X : Type} [Group X] {A Q : Subgroup X} (e : A ≃* SL(2, ZMod 3))
    (hQA : Q ≤ A) (hQ4 : ∀ q ∈ Q, q ^ 4 = 1) (hQc : Nat.card Q = 8) :
    ∀ a ∈ A, a ^ 4 = 1 → a ∈ Q := by
  classical
  have hfin : Finite Q := Nat.finite_of_card_ne_zero (by rw [hQc]; norm_num)
  intro a ha ha4
  set T : Finset (SL(2, ZMod 3)) := Finset.univ.filter fun g => g ^ 4 = 1 with hT
  have hTc : T.card = 8 := sl23_card4
  let f : Q → SL(2, ZMod 3) := fun q => e ⟨q, hQA q.2⟩
  have hfinj : Function.Injective f := by
    intro q₁ q₂ h
    have := e.injective h
    exact Subtype.ext (congrArg (fun a : A => (a : X)) this)
  have hfT : ∀ q, f q ∈ T := by
    intro q
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and]
    have : (⟨(q : X), hQA q.2⟩ : A) ^ 4 = 1 := by
      apply Subtype.ext
      simpa using hQ4 q q.2
    show (e ⟨(q : X), hQA q.2⟩) ^ 4 = 1
    rw [← map_pow, this, map_one]
  have hsurj : ∀ s ∈ T, ∃ q : Q, f q = s := by
    have hinj' : Function.Injective (fun q : Q => (⟨f q, hfT q⟩ : T)) := by
      intro q₁ q₂ h
      exact hfinj (congrArg Subtype.val h)
    have hbij : Function.Bijective (fun q : Q => (⟨f q, hfT q⟩ : T)) :=
      hinj'.bijective_of_nat_card_le (by
        rw [Nat.card_eq_fintype_card (α := T), Fintype.card_coe, hTc, hQc])
    intro s hs
    obtain ⟨q, hq⟩ := hbij.2 ⟨s, hs⟩
    exact ⟨q, congrArg Subtype.val hq⟩
  have hsT : e ⟨a, ha⟩ ∈ T := by
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and]
    have : (⟨a, ha⟩ : A) ^ 4 = 1 := by
      apply Subtype.ext
      simpa using ha4
    rw [← map_pow, this, map_one]
  obtain ⟨q, hq⟩ := hsurj _ hsT
  have : (⟨(q : X), hQA q.2⟩ : A) = ⟨a, ha⟩ := e.injective hq
  have := congrArg Subtype.val this
  simp only at this
  rw [← this]
  exact q.2

end SL2

end CFSG.ClassicalInvolution.Q8P.Asc77.P25S.X
