module

public import CFSG.LieType.CurtisTits.Exceptional
public import CFSG.LieType.Steinberg.Adjoint.Perfect
public import CFSG.LieType.Steinberg.G2

public section

namespace CFSG.LieType.Simplicity

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.TwistedE6

theorem isSimpleGroup_of_mulEquiv {K G : Type*} [Group K] [Group G] (hK : IsQuasisimple K)
    (e : G ≃* K ⧸ Subgroup.center K) : IsSimpleGroup G := by
  have := hK.2.1
  have : Nontrivial G := e.toEquiv.nontrivial
  exact IsSimpleGroup.isSimpleGroup_of_surjective e.symm.toMonoidHom e.symm.surjective

theorem isSimpleGroup_adjointQuotient_f4
    (K : Type) [Field K] :
    IsSimpleGroup (AdjointQuotient .F4 K) :=
  (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_f4 K).2.1

theorem isSimpleGroup_adjointQuotient_e8
    (K : Type) [Field K] :
    IsSimpleGroup (AdjointQuotient .E8 K) :=
  (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_e8 K).2.1

theorem isQuasisimple_adjointGroup_e6
    (K : Type) [Field K] [Finite K] :
    IsQuasisimple ↥(adjointGroup .E6 K) :=
  isQuasisimple_of_surjective (isQuasisimple_e6 K) (e6Isogeny_surjective K) (e6Isogeny_ne_one K)

theorem isQuasisimple_adjointGroup_e7
    (K : Type) [Field K] [Finite K] :
    IsQuasisimple ↥(adjointGroup .E7 K) :=
  isQuasisimple_of_surjective (isQuasisimple_e7 K) (e7Isogeny_surjective K)
    (exists_e7Isogeny_ne_one K)

section Twisted

variable {K : Type} [Field K] [Finite K] (θ : K →+* K)

@[expose] noncomputable def twistedIsogeny
    (hθ : ∀ c, θ (θ c) = c) (hK : 4 ≤ Nat.card K) :
    ↥(fixedGroup K θ) →* ↥⁅twistedFixedGroup .E6 K θ, twistedFixedGroup .E6 K θ⁆ :=
  (e6IsogenyFixed θ).codRestrict _ fun g => by
    rw [← range_e6IsogenyFixed θ hθ hK]
    exact ⟨g, rfl⟩

theorem coe_twistedIsogeny
    (hθ : ∀ c, θ (θ c) = c) (hK : 4 ≤ Nat.card K) (g : ↥(fixedGroup K θ)) :
    ((twistedIsogeny θ hθ hK g : ↥⁅twistedFixedGroup .E6 K θ, twistedFixedGroup .E6 K θ⁆) :
        ModGL TwistTag.E6.tag K) =
      ((e6IsogenyT K g : ↥(adjointGroup TwistTag.E6.tag K)) : ModGL TwistTag.E6.tag K) :=
  rfl

theorem twistedIsogeny_surjective
    (hθ : ∀ c, θ (θ c) = c) (hK : 4 ≤ Nat.card K) :
    Function.Surjective (twistedIsogeny θ hθ hK) := by
  rintro ⟨y, hy⟩
  rw [← range_e6IsogenyFixed θ hθ hK] at hy
  obtain ⟨g, rfl⟩ := hy
  exact ⟨g, rfl⟩

theorem twistedIsogeny_ne_one
    (hθ : ∀ c, θ (θ c) = c) (hK : 4 ≤ Nat.card K) :
    ∃ g, twistedIsogeny θ hθ hK g ≠ 1 := by
  set i : Fin (Tag.rank .E6) := ⟨1, by decide⟩
  have hfix : e6Data_valid.xm K (Pi.single i 1) 1 ∈ fixedGroup K θ := by
    rw [mem_fixedGroup, sigma_xm_single, map_one]
    rfl
  refine ⟨⟨_, hfix⟩, fun h => ?_⟩
  have h' := congrArg (fun y : ↥⁅twistedFixedGroup .E6 K θ, twistedFixedGroup .E6 K θ⁆ =>
    (y : ModGL TwistTag.E6.tag K)) h
  simp only [coe_twistedIsogeny, OneMemClass.coe_one] at h'
  exact e6Isogeny_xm_single_one_ne_one _ i (Subtype.ext h')

theorem isQuasisimple_derived_twistedFixedGroup
    (hθ : ∀ c, θ (θ c) = c) (hK : 4 ≤ Nat.card K) :
    IsQuasisimple ↥⁅twistedFixedGroup .E6 K θ, twistedFixedGroup .E6 K θ⁆ :=
  isQuasisimple_of_surjective (fixedGroup_isQuasisimple_of_four_le_card θ hθ hK)
    (twistedIsogeny_surjective θ hθ hK) (twistedIsogeny_ne_one θ hθ hK)

end Twisted

theorem fam_g2_simplicity
    (G : Type) [Group G] (p f : ℕ)
    (h : ChevalleyExceptionalModel G .G2 p f) : Nontrivial G ∧ IsSimpleGroup G := by
  obtain ⟨⟨-, -, -, h3⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have := isSimpleGroup_of_mulEquiv
    (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card K (hK ▸ h3)) e
  exact ⟨inferInstance, this⟩

theorem fam_f4_simplicity
    (G : Type) [Group G] (p f : ℕ)
    (h : ChevalleyExceptionalModel G .F4 p f) : Nontrivial G ∧ IsSimpleGroup G := by
  obtain ⟨-, K, _, _, -, ⟨e⟩⟩ := h
  have := isSimpleGroup_of_mulEquiv (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_f4 K) e
  exact ⟨inferInstance, this⟩

theorem fam_e8_simplicity
    (G : Type) [Group G] (p f : ℕ)
    (h : ChevalleyExceptionalModel G .E8 p f) : Nontrivial G ∧ IsSimpleGroup G := by
  obtain ⟨-, K, _, _, -, ⟨e⟩⟩ := h
  have := isSimpleGroup_of_mulEquiv (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_e8 K) e
  exact ⟨inferInstance, this⟩

theorem fam_e6_simplicity
    (G : Type) [Group G] (p f : ℕ)
    (h : ChevalleyExceptionalModel G .E6 p f) : Nontrivial G ∧ IsSimpleGroup G := by
  obtain ⟨-, K, _, _, -, ⟨e⟩⟩ := h
  have := isSimpleGroup_of_mulEquiv (isQuasisimple_adjointGroup_e6 K) e
  exact ⟨inferInstance, this⟩

theorem fam_e7_simplicity
    (G : Type) [Group G] (p f : ℕ)
    (h : ChevalleyExceptionalModel G .E7 p f) : Nontrivial G ∧ IsSimpleGroup G := by
  obtain ⟨-, K, _, _, -, ⟨e⟩⟩ := h
  have := isSimpleGroup_of_mulEquiv (isQuasisimple_adjointGroup_e7 K) e
  exact ⟨inferInstance, this⟩

theorem pow_pow_card_sq {K : Type} [Field K] [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 2)
    (c : K) : (c ^ q) ^ q = c := by
  have := Fintype.ofFinite K
  rw [← pow_mul, ← sq, ← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]

theorem fam_2e6_simplicity
    (G : Type) [Group G] (p f : ℕ)
    (h : ChevalleyExceptionalModel G .twistedE6 p f) : Nontrivial G ∧ IsSimpleGroup G := by
  obtain ⟨⟨hp, hf, -⟩, K, _, _, hK, σ, hσ, ⟨e⟩⟩ := h
  have hK2 : Nat.card K = (p ^ f) ^ 2 := hK
  have hθ : ∀ c, σ (σ c) = c := fun c => by rw [hσ, hσ, pow_pow_card_sq hK2]
  have h4 : 4 ≤ Nat.card K := by
    rw [hK2]
    have h2 : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
    nlinarith
  have := isSimpleGroup_of_mulEquiv (isQuasisimple_derived_twistedFixedGroup σ hθ h4) e
  exact ⟨inferInstance, this⟩

end CFSG.LieType.Simplicity
