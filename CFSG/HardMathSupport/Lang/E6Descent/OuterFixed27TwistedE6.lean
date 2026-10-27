module

public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27TwistedE6Order
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedE6Adjoint
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderPSU
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderTwistedE6Descent
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderTwistedE6Diag

public noncomputable section

namespace CFSG.HardMathSupport.Lang.Coordinator

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

set_option linter.unusedSectionVars false


def TwistedE6DiagCase : Prop :=
  ∀ (ℓ f : ℕ), ℓ.Prime → 1 ≤ f → ∀ (K : Type) [Field K] [Finite K], Nat.card K = (ℓ ^ f) ^ 2 →
    ∀ (σ : K ≃+* K), (∀ c, σ c = c ^ ℓ ^ f) → 3 ∣ ℓ ^ f + 1 →
    ∀ (g : twistedE6RootGroup K σ)
      (u : (a : Fin TwistTag.E6.foldedTag.rank) → (orbitField TwistTag.E6 K σ.toRingHom a)ˣ)
      (β : MulAut (twistedE6RootGroup K σ)),
    β = MulAut.conj g * compatDiagAutHom TwistTag.E6 K σ.toRingHom u → β ^ 3 = 1 →
    β ∉ twistedE6Inn K σ → 27 ∣ Nat.card (fixedSubgroup β)

theorem fieldActor_one {K : Type} [Field K] [Finite K] (σ : K ≃+* K) :
    fieldActor (t := TwistTag.E6) σ (1 : K ≃+* K) = 1 :=
  MulEquiv.ext fun x => Subtype.ext (by
    rw [coe_fieldActor]
    have e1 : (1 : K ≃+* K).toRingHom = RingHom.id K := RingHom.ext fun _ => rfl
    rw [e1]
    exact Units.ext (entrywise_id (R := K) _))

theorem twentySeven_dvd_fixedSubgroup_twistedE6RootGroup_of_diag' {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ ℓ ^ f)
    (β : MulAut (twistedE6RootGroup K σ)) (hβ3 : β ^ 3 = 1) (hβ : β ∉ twistedE6Inn K σ)
    (hdiag : ∀ (g : twistedE6RootGroup K σ)
      (u : (a : Fin TwistTag.E6.foldedTag.rank) → (orbitField TwistTag.E6 K σ.toRingHom a)ˣ),
      3 ∣ ℓ ^ f + 1 → β = MulAut.conj g * compatDiagAutHom TwistTag.E6 K σ.toRingHom u →
      27 ∣ Nat.card (fixedSubgroup β)) :
    27 ∣ Nat.card (fixedSubgroup β) := by
  classical
  have hK2 : Nat.card K = ℓ ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨-, -, -, -, -, -, -, hex, ⟨Θ, hΘ, -, -, -, -, -⟩, -, -, -, -, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf K hK σ hσ
  by_cases hη : Θ β = 1
  ·
    obtain ⟨g, u, δ, hgu⟩ := hex β
    have hδ : δ = 1 := by rw [← hΘ β g u δ hgu, hη]
    subst hδ
    rw [fieldActor_one, mul_one] at hgu
    by_cases h3 : Nat.gcd 3 (ℓ ^ f + 1) = 1
    · exact absurd (by
        rw [hgu]
        exact mul_mem ⟨g, rfl⟩ (compatDiagAutHom_mem_inner hK hσ h3 u)) hβ
    · have hg3 : Nat.gcd 3 (ℓ ^ f + 1) = 3 :=
        ((Nat.dvd_prime Nat.prime_three).1 (Nat.gcd_dvd_left 3 (ℓ ^ f + 1))).resolve_left h3
      exact hdiag g u (hg3 ▸ Nat.gcd_dvd_right 3 (ℓ ^ f + 1)) hgu
  ·
    obtain ⟨d, hd, hd0, r, ε, hε, ψ, hψ⟩ :=
      twisted_E6_field_descent_of_prime_order hℓ hf K hK2 σ hσ Θ hΘ Nat.prime_three
        (by norm_num) β hβ3 hη
    have hβo : orderOf β = 3 := orderOf_eq_prime hβ3 fun h => hη (by rw [h, map_one])
    have hKd : Nat.card K = ℓ ^ (2 * (d * 3)) := by
      rw [hK2, hd, show 3 * d = d * 3 by ring]
    have hσ' : ∀ c, σ c = c ^ ℓ ^ (d * 3) := fun c => by rw [hσ, hd, mul_comm]
    have hεo := (fieldAut_four_data hℓ hd0 K hKd ε hε).1
    have hr3 : ¬ 3 ∣ r := by
      rintro ⟨t, rfl⟩
      have h1 : β ^ (3 * t) = 1 := by rw [pow_mul, hβ3, one_pow]
      rw [h1, mul_one, mul_inv_cancel] at hψ
      have h2 : Θ (fieldActor (t := TwistTag.E6) σ ε) = ε := by
        refine hΘ _ 1 1 ε ?_
        rw [show (MulAut.conj (1 : twistedE6RootGroup K σ)) = 1 from map_one _,
          map_one (compatDiagAutHom TwistTag.E6 K σ.toRingHom), one_mul, one_mul]
      rw [← hψ, map_one] at h2
      rw [← h2, orderOf_one] at hεo
      exact absurd hεo (by norm_num)
    obtain ⟨j, hj⟩ : ∃ j, r * j % 3 = 1 := by
      have : r % 3 = 1 ∨ r % 3 = 2 := by omega
      rcases this with h | h
      · exact ⟨1, by omega⟩
      · exact ⟨2, by omega⟩
    have hβj : (β ^ r) ^ j = β := by
      rw [← pow_mul]
      exact pow_eq_self_of_mod_eq_one hβo hj
    have hconj : Nat.card (fixedSubgroup (β ^ r)) =
        Nat.card (fixedSubgroup (fieldActor (t := TwistTag.E6) σ ε)) :=
      card_fixedSubgroup_eq_of_intertwine
        (ψ : twistedE6RootGroup K σ ≃* twistedE6RootGroup K σ) (β ^ r) _ fun x => by
          have h := congrArg (fun g : MulAut (twistedE6RootGroup K σ) => g (ψ x)) hψ
          simpa [MulAut.mul_apply] using h.symm
    rw [CFSG.HardMathSupport.Lang.E6Descent.fixedSubgroup_pow_eq hβj, hconj]
    exact twentySeven_dvd_card_fixedSubgroup_fieldActor hℓ hd0 K hKd σ ε hσ' hε

theorem twentySeven_dvd_fixedSubgroup_twistedE6RootGroup_of_diag (hD : TwistedE6DiagCase)
    {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ ℓ ^ f)
    (β : MulAut (twistedE6RootGroup K σ)) (hβ3 : β ^ 3 = 1) (hβ : β ∉ twistedE6Inn K σ) :
    27 ∣ Nat.card (fixedSubgroup β) :=
  twentySeven_dvd_fixedSubgroup_twistedE6RootGroup_of_diag' hℓ hf K hK σ hσ β hβ3 hβ
    fun g u h3 hgu => hD ℓ f hℓ hf K hK σ hσ h3 g u β hgu hβ3 hβ

theorem twentySeven_dvd_fixedSubgroup_twistedE6RootGroup_char_three {f : ℕ} (hf : 1 ≤ f)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = (3 ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 3 ^ f) (β : MulAut (twistedE6RootGroup K σ)) (hβ3 : β ^ 3 = 1)
    (hβ : β ∉ twistedE6Inn K σ) : 27 ∣ Nat.card (fixedSubgroup β) := by
  refine twentySeven_dvd_fixedSubgroup_twistedE6RootGroup_of_diag' Nat.prime_three hf K hK σ hσ
    β hβ3 hβ fun g u h3 _ => ?_
  exfalso
  obtain ⟨m, hm⟩ : 3 ∣ 3 ^ f := dvd_pow_self 3 (by omega)
  omega

theorem twentySeven_dvd_fixedSubgroup_derivedCentralQuotient_of_diag (hD : TwistedE6DiagCase)
    {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ ℓ ^ f)
    (α : MulAut (DerivedCentralQuotient (twistedFixedGroup TwistTag.E6 K σ.toRingHom)))
    (hα3 : α ^ 3 = 1)
    (hα : α ∉ inner (DerivedCentralQuotient (twistedFixedGroup TwistTag.E6 K σ.toRingHom))) :
    27 ∣ Nat.card (fixedSubgroup α) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, ⟨e⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf K hK σ hσ
  rw [← CFSG.HardMathSupport.Lang.Coordinator.card_fixedSubgroup_congr e α]
  refine twentySeven_dvd_fixedSubgroup_twistedE6RootGroup_of_diag hD hℓ hf K hK σ hσ
    (MulAut.congr e α) (by rw [← map_pow, hα3, map_one]) fun hin =>
      hα ((congr_mem_inner_iff e α).mp hin)

theorem twentySeven_dvd_fixedSubgroup_twistedE6_model_of_diag (hD : TwistedE6DiagCase)
    {ℓ f : ℕ} {G : Type} [Group G] (hG : ChevalleyExceptionalModel G .twistedE6 ℓ f)
    (α : MulAut G) (hα3 : α ^ 3 = 1) (hα : α ∉ inner G) :
    27 ∣ Nat.card (fixedSubgroup α) := by
  obtain ⟨hℓ, hf, -⟩ := hG.1
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_E6 hG
  rw [← CFSG.HardMathSupport.Lang.Coordinator.card_fixedSubgroup_congr e α]
  exact twentySeven_dvd_fixedSubgroup_twistedE6RootGroup_of_diag hD hℓ hf K hK σ hσ
    (MulAut.congr e α) (by rw [← map_pow, hα3, map_one]) fun hin =>
      hα ((congr_mem_inner_iff e α).mp hin)

end CFSG.HardMathSupport.Lang.Coordinator
