module

public import CFSG.ClassicalInvolution.ModelFacts.E8ExclRowStmt

public section

namespace CFSG.ClassicalInvolution.ModelFacts.E8D8

open CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.RouteD.NonClassical
  (UniversalPartner ThirdMember card_ne_none_add_one)

section Abstract

variable {K : Type*} [Group K] {Fund : Set (Subgroup K)} {R₀ : Subgroup K} {k : K}

theorem le_centralizer_of_commutes {S : Subgroup K} (hkR : k ∈ R₀) (hS : Commutes S R₀) :
    S ≤ Subgroup.centralizer ({k} : Set K) := fun s hs =>
  Subgroup.mem_centralizer_iff.mpr fun h hh => by
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact (hS s hs h hkR).symm

theorem exists_partner_of_layer {P : Type*} {rel : P → P → Prop} {p₀ q r : P} (hR₀ : R₀ ∈ Fund)
    (hkR : k ∈ R₀) (hk : R₀ ≤ Subgroup.centralizer ({k} : Set K))
    (φ : {R : Subgroup K // R ∈ Fund ∧ R ≤ Subgroup.centralizer ({k} : Set K)} ≃ P)
    (hφ : ∀ R R', Commutes R.1 R'.1 ↔ rel (φ R) (φ R')) (h0 : φ ⟨R₀, hR₀, hk⟩ = p₀)
    (hq : q ≠ p₀) (hr : r ≠ p₀) (hrq : r ≠ q) (hrelq : ∀ x, x ≠ q → rel x q)
    (hrel₀ : ∀ x, x ≠ p₀ → rel x p₀) (hrel₀' : ∀ x, x ≠ p₀ → rel p₀ x) :
    ∃ R₁, UniversalPartner Fund R₀ R₁ ∧ ThirdMember Fund R₀ R₁ := by
  set A : {R : Subgroup K // R ∈ Fund ∧ R ≤ Subgroup.centralizer ({k} : Set K)} :=
    ⟨R₀, hR₀, hk⟩ with hA
  set B := φ.symm q with hB
  set C := φ.symm r with hC
  have hBφ : φ B = q := φ.apply_symm_apply _
  have hCφ : φ C = r := φ.apply_symm_apply _
  have hBA : B ≠ A := fun h => by
    have := congrArg φ h
    rw [hBφ, h0] at this
    exact hq this
  have hCA : C ≠ A := fun h => by
    have := congrArg φ h
    rw [hCφ, h0] at this
    exact hr this
  have hCB : C ≠ B := fun h => by
    have := congrArg φ h
    rw [hCφ, hBφ] at this
    exact hrq this
  refine ⟨B.1, ⟨B.2.1, fun h => hBA (Subtype.ext h), ?_, ?_⟩, C.1, C.2.1,
    fun h => hCA (Subtype.ext h), fun h => hCB (Subtype.ext h), ?_⟩
  · refine (hφ A B).mpr ?_
    rw [h0, hBφ]
    exact hrel₀' q hq
  · intro S hS hSc
    have hSk : S ≤ Subgroup.centralizer ({k} : Set K) := le_centralizer_of_commutes hkR hSc
    by_cases hX : φ ⟨S, hS, hSk⟩ = q
    · left
      exact congrArg Subtype.val (φ.injective (hX.trans hBφ.symm))
    · right
      refine (hφ ⟨S, hS, hSk⟩ B).mpr ?_
      rw [hBφ]
      exact hrelq _ hX
  · refine (hφ C A).mpr ?_
    rw [h0, hCφ]
    exact hrel₀ r hr

theorem card_commuting_add_one_of_layer [Finite K] {β : Type*} {rel : Option β → Option β → Prop}
    (hR₀ : R₀ ∈ Fund) (hkR : k ∈ R₀) (hk : R₀ ≤ Subgroup.centralizer ({k} : Set K))
    (φ : {R : Subgroup K // R ∈ Fund ∧ R ≤ Subgroup.centralizer ({k} : Set K)} ≃ Option β)
    (hφ : ∀ R R', Commutes R.1 R'.1 ↔ rel (φ R) (φ R')) (h0 : φ ⟨R₀, hR₀, hk⟩ = none)
    (hnone : ¬ rel none none) (hrel : ∀ x, x ≠ none → rel x none) :
    Nat.card {S : Subgroup K // S ∈ Fund ∧ Commutes S R₀} + 1 = Nat.card (Option β) := by
  classical
  set A : {R : Subgroup K // R ∈ Fund ∧ R ≤ Subgroup.centralizer ({k} : Set K)} :=
    ⟨R₀, hR₀, hk⟩ with hA
  have hfin : Finite (Option β) := Finite.of_equiv _ φ
  have hβ : Finite β := Finite.of_injective (some : β → Option β) (Option.some_injective β)
  have e : {S : Subgroup K // S ∈ Fund ∧ Commutes S R₀} ≃ {x : Option β // x ≠ none} :=
    { toFun := fun S => ⟨φ ⟨S.1, S.2.1, le_centralizer_of_commutes hkR S.2.2⟩, fun h => by
        have hX : (⟨S.1, S.2.1, le_centralizer_of_commutes hkR S.2.2⟩ :
            {R : Subgroup K // R ∈ Fund ∧ R ≤ Subgroup.centralizer ({k} : Set K)}) = A :=
          φ.injective (h.trans h0.symm)
        have hS : S.1 = R₀ := congrArg Subtype.val hX
        have hc : Commutes R₀ R₀ := by
          have := S.2.2
          rwa [hS] at this
        have := (hφ A A).mp hc
        rw [h0] at this
        exact hnone this⟩
      invFun := fun x => ⟨(φ.symm x.1).1, (φ.symm x.1).2.1, by
        have := (hφ (φ.symm x.1) A).mpr (by
          rw [φ.apply_symm_apply, h0]
          exact hrel _ x.2)
        exact this⟩
      left_inv := fun S => Subtype.ext (by simp)
      right_inv := fun x => Subtype.ext (by simp) }
  rw [Nat.card_congr e]
  exact card_ne_none_add_one

end Abstract

end CFSG.ClassicalInvolution.ModelFacts.E8D8

namespace CFSG.ClassicalInvolution.RouteD.TypeE8

open CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.RouteD.NonClassical (UniversalPartner ThirdMember)

variable (p f : ℕ) [Fact p.Prime]

section D8

variable {K : Type*} [Group K] {Fund : Set (Subgroup K)} {R₀ : Subgroup K} {k : K}

theorem exists_partner_of_d8Layer (hne : Nonempty (Fund12 p f)) (hR₀ : R₀ ∈ Fund) (hkR : k ∈ R₀)
    (hk : R₀ ≤ Subgroup.centralizer ({k} : Set K))
    (φ : {R : Subgroup K // R ∈ Fund ∧ R ≤ Subgroup.centralizer ({k} : Set K)} ≃ D8Layer p f)
    (hφ : ∀ R R', Commutes R.1 R'.1 ↔ D8Layer.rel p f (φ R) (φ R'))
    (h0 : φ ⟨R₀, hR₀, hk⟩ = none) :
    ∃ R₁, UniversalPartner Fund R₀ R₁ ∧ ThirdMember Fund R₀ R₁ := by
  obtain ⟨R⟩ := hne
  refine ModelFacts.E8D8.exists_partner_of_layer hR₀ hkR hk φ hφ h0 (q := some none)
    (r := some (some R)) (Option.some_ne_none _) (Option.some_ne_none _)
    (fun h => by simp at h) ?_ ?_ ?_
  · intro x hx
    rcases x with _ | _ | R'
    · exact trivial
    · exact absurd rfl hx
    · exact trivial
  · intro x hx
    rcases x with _ | _ | R'
    · exact absurd rfl hx
    · exact trivial
    · exact trivial
  · intro x hx
    rcases x with _ | _ | R'
    · exact absurd rfl hx
    · exact trivial
    · exact trivial

theorem card_commuting_of_d8Layer [Finite K] (hR₀ : R₀ ∈ Fund) (hkR : k ∈ R₀)
    (hk : R₀ ≤ Subgroup.centralizer ({k} : Set K))
    (φ : {R : Subgroup K // R ∈ Fund ∧ R ≤ Subgroup.centralizer ({k} : Set K)} ≃ D8Layer p f)
    (hφ : ∀ R R', Commutes R.1 R'.1 ↔ D8Layer.rel p f (φ R) (φ R'))
    (h0 : φ ⟨R₀, hR₀, hk⟩ = none) :
    Nat.card {S : Subgroup K // S ∈ Fund ∧ Commutes S R₀} = Nat.card (Fund12 p f) + 1 := by
  have hfin : Finite (D8Layer p f) := Finite.of_equiv _ φ
  have hβ : Finite (Fund12 p f) :=
    Finite.of_injective (fun R => some (some R) : Fund12 p f → D8Layer p f)
      (fun a b h => by simpa using h)
  have h1 : Nat.card {S : Subgroup K // S ∈ Fund ∧ Commutes S R₀} + 1 =
      Nat.card (D8Layer p f) := ModelFacts.E8D8.card_commuting_add_one_of_layer hR₀ hkR hk φ hφ h0
    (rel := D8Layer.rel p f) (fun h => h) (fun x hx => by
      rcases x with _ | _ | R'
      · exact absurd rfl hx
      · exact trivial
      · exact trivial)
  have h2 : Nat.card (D8Layer p f) = Nat.card (Fund12 p f) + 2 := by
    have := Fintype.ofFinite (Fund12 p f)
    simp [Nat.card_eq_fintype_card, Fintype.card_option]
  omega

end D8

end CFSG.ClassicalInvolution.RouteD.TypeE8
