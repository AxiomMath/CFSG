module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionTransport
public import CFSG.ClassicalGroups.Orthogonal.Simple

public section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointAction

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Spin

universe w

section Witnesses

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {K : Type} [Field K]
variable {H : Type w} [Group H]
variable (Q : QuadraticForm K (ι → K)) {Q₀ : (ι → K) → K}

@[expose] def WitnessPointAction (hQ : ⇑Q = Q₀)
    (e : H ≃* StatedProj (StatedOmega Q₀)) : Prop :=
  Q ≠ 0 ∧ Q.polarBilin.Nondegenerate ∧
    (∃ T : Submodule K (ι → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) ∧
    ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q ∧
    StatedOmega Q₀ = (elementaryGroup Q).map (toLinEquiv ι K).symm.toMonoidHom ∧
    ActionProperties Q (statedPointAction hQ) ∧
    ActionProperties Q ((statedPointAction hQ).comp e.toMonoidHom) ∧
    (∀ (g : StatedOmega Q₀) (L : Points Q),
      (statedPointAction hQ (QuotientGroup.mk' _ g) L).val =
        L.val.map ((toLinEquiv ι K g.val) : (ι → K) →ₗ[K] (ι → K))) ∧
    (∀ L : Points Q,
      (actionStabilizer Q (statedPointAction hQ) L).comap e.toMonoidHom =
        actionStabilizer Q ((statedPointAction hQ).comp e.toMonoidHom) L) ∧
    ∃ eP : H ≃* ProjectiveGroup Q,
      (∀ g : H, statedPointAction hQ (e g) = projectivePointAction Q (eP g)) ∧
      ∀ p : ProjectiveGroup Q,
        projectivePointAction Q p = statedPointAction hQ (e (eP.symm p))

theorem witness_point_action_of_regular (hQ : ⇑Q = Q₀)
    (e : H ≃* StatedProj (StatedOmega Q₀))
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) (hnd : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (ι → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) :
    WitnessPointAction Q hQ e := by
  have hnz : Q ≠ 0 := by
    obtain ⟨T, hT3, hTs⟩ := hT
    obtain ⟨P₁, P₂, P₃, h₁₂, h₁₃, h₂₃⟩ := exists_three_hypPairs hnd (by omega) hTs
    have hv : Q (P₁.e + P₁.f) = 1 := by
      rw [QuadraticMap.map_add Q, P₁.Q_e, P₁.Q_f, P₁.polar_ef, zero_add, zero_add]
    intro hz
    simp [hz] at hv
  have ha := stated_action_properties hQ hE hnd hT
  let eP : H ≃* ProjectiveGroup Q := e.trans (statedActionEquiv hQ hE)
  have heP : ∀ g : H, statedPointAction hQ (e g) = projectivePointAction Q (eP g) :=
    fun g => statedPointAction_equiv hQ hE (e g)
  refine ⟨hnz, hnd, hT, hE, statedOmega_eq_map_elementaryGroup hQ hE, ha,
    actionProperties_equiv Q _ _ e (fun _ => rfl) ha,
    statedPointAction_mk_submodule hQ, ?_, eP, heP, ?_⟩
  · exact actionStabilizer_comap Q _ _ e (fun _ => rfl)
  · intro p
    have h := heP (eP.symm p)
    rw [eP.apply_symm_apply] at h
    exact h.symm

end Witnesses

section Models

variable {H : Type} [Group H] {n p f : ℕ}

@[expose] def ModelPointAction (H : Type) [Group H] (t : StatedLieTag) (n p f : ℕ) : Prop :=
  match t with
  | .POmegaOdd => ∀ (K : Type) [Field K] [Finite K], Nat.card K = p ^ f →
      ∀ e : H ≃* StatedProj (StatedOmega (StatedQuadOdd n K)),
        ringChar K = p ∧ WitnessPointAction (quadOdd n K) (coe_quadOdd n K) e
  | .POmegaPlus => ∀ (K : Type) [Field K] [Finite K], Nat.card K = p ^ f →
      ∀ e : H ≃* StatedProj (StatedOmega (StatedQuadPlus n K)),
        ringChar K = p ∧ WitnessPointAction (quadPlus n K) (coe_quadPlus n K) e
  | .POmegaMinus => ∀ (K : Type) [Field K] [Finite K], Nat.card K = p ^ f →
      ∀ (b c : K), (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
      ∀ e : H ≃* StatedProj (StatedOmega (StatedQuadMinus n K b c)),
        ringChar K = p ∧ WitnessPointAction (quadMinus n K b c) (coe_quadMinus n K b c) e
  | _ => False

theorem model_point_action_POmegaOdd (h : StatedClassicalModel H .POmegaOdd n p f) :
    ModelPointAction H .POmegaOdd n p f := by
  obtain ⟨hp, hf, hn, hp2⟩ := h.1
  intro K _ _ hK e
  have hchar := ringChar_eq_of_card_eq hp hf hK
  have hprime : (ringChar K).Prime := hchar ▸ hp
  have h2 : (2 : K) ≠ 0 := by
    rw [Ne, two_eq_zero_iff_ringChar_eq_two hprime, hchar]
    exact hp2
  have hreg := regular_quadOdd (K := K) h2 hn
  exact ⟨hchar, witness_point_action_of_regular (quadOdd n K) (coe_quadOdd n K) e
    (commutator_orthogonalGroup_quadOdd h2 hn) hreg.1 hreg.2⟩

theorem model_point_action_POmegaPlus (h : StatedClassicalModel H .POmegaPlus n p f) :
    ModelPointAction H .POmegaPlus n p f := by
  obtain ⟨hp, hf, hn⟩ := h.1
  intro K _ _ hK e
  have hreg := regular_quadPlus (K := K) (n := n) (by omega)
  exact ⟨ringChar_eq_of_card_eq hp hf hK,
    witness_point_action_of_regular (quadPlus n K) (coe_quadPlus n K) e
      (commutator_orthogonalGroup_quadPlus (by omega)) hreg.1 hreg.2⟩

theorem model_point_action_POmegaMinus (h : StatedClassicalModel H .POmegaMinus n p f) :
    ModelPointAction H .POmegaMinus n p f := by
  obtain ⟨hp, hf, hn⟩ := h.1
  intro K _ _ hK b c hirr e
  have hreg := regular_quadMinus (K := K) hn hirr
  exact ⟨ringChar_eq_of_card_eq hp hf hK,
    witness_point_action_of_regular (quadMinus n K b c) (coe_quadMinus n K b c) e
      (commutator_orthogonalGroup_quadMinus hn hirr) hreg.1 hreg.2⟩

theorem orthogonal_geometry_model_point_action (H : Type) [Group H]
    (t : StatedLieTag) (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus)
    (n p f : ℕ) (h : StatedClassicalModel H t n p f) :
    StatedLieAdmissible t n p f ∧ ModelPointAction H t n p f := by
  refine ⟨h.1, ?_⟩
  rcases ht with rfl | rfl | rfl
  · exact model_point_action_POmegaOdd h
  · exact model_point_action_POmegaPlus h
  · exact model_point_action_POmegaMinus h

end Models

end CFSG.ComponentClassification.CatalogueBOrthogonalPointAction
