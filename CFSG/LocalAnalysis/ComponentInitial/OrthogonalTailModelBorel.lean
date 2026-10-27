module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelTransport
public import CFSG.ClassicalGroups.Orthogonal.Simple
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelCoordinates

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal.Spin Module

@[expose] def tailModelFlag (r : ℕ) (K : Type*) [Field K] (κ : Type*) [DecidableEq κ] :
    Fin r → Submodule K (Fin r ⊕ Fin r ⊕ κ → K) :=
  fun i => Submodule.span K
    ((fun j : Fin r => (Pi.single (.inl j) 1 : Fin r ⊕ Fin r ⊕ κ → K)) '' {j | (j : ℕ) < i + 1})

theorem tailModelFlag_eq_map {K : Type*} [Field K] {r : ℕ} {κ : Type*} [DecidableEq κ]
    {q : QuadraticForm K (κ → K)} {Q : QuadraticForm K (Fin r ⊕ Fin r ⊕ κ → K)}
    (ψ : (quadTail r q).IsometryEquiv Q) (hψ : ∀ v, ψ v = tailModelEquiv r K κ v) (i : Fin r) :
    tailModelFlag r K κ i = (tailFlag K (κ → K) r (i + 1)).map ψ.toLinearMap := by
  rw [tailFlag, Submodule.map_span, ← Set.image_comp]
  refine congrArg (Submodule.span K) (Set.image_congr fun j _ => ?_)
  change Pi.single (.inl j) 1 = ψ (hypVec K (κ → K) (.inl j))
  rw [hψ, tailModelEquiv_hypVec_inl]

@[expose] def TailModelBorelInterface (t : StatedLieTag) (n p f : ℕ) : Prop :=
  match t with
  | .POmegaOdd => ∀ (K : Type) [Field K] [Finite K], Nat.card K = p ^ f →
      BorelInterface p (StatedQuadOdd n K) (tailModelFlag n K Unit)
  | .POmegaMinus => ∀ (K : Type) [Field K] [Finite K], Nat.card K = p ^ f →
      ∀ b c : K, (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
      BorelInterface p (StatedQuadMinus n K b c) (tailModelFlag (n - 1) K (Fin 2))
  | _ => False

theorem orthogonal_geometry_tail_model_Borel_overgroup_interface (G : Type) [Group G]
    (t : StatedLieTag) (ht : t = .POmegaOdd ∨ t = .POmegaMinus) (n p f : ℕ)
    (h : StatedClassicalModel G t n p f) : TailModelBorelInterface t n p f := by
  rcases ht with rfl | rfl
  · obtain ⟨hp, hf, hn, hp2⟩ := h.1
    intro K _ _ hK
    have hchar := ringChar_eq_of_card_eq hp hf hK
    have : Fact p.Prime := ⟨hp⟩
    have : CharP K p := hchar ▸ ringChar.charP K
    have h2 : (2 : K) ≠ 0 := by
      rw [Ne, two_eq_zero_iff_ringChar_eq_two (hchar ▸ hp), hchar]
      exact hp2
    exact borelInterface_of_tailIsometry (oddTailIsometry n K) (coe_quadOdd n K)
      (commutator_orthogonalGroup_quadOdd h2 hn) hn anisotropic_oddTailForm
      (nondegenerate_oddTailForm h2) (Or.inl finrank_unit_fun)
      (tailModelFlag_eq_map (oddTailIsometry n K) fun _ => rfl)
  · obtain ⟨hp, hf, hn⟩ := h.1
    intro K _ _ hK b c hirr
    have hchar := ringChar_eq_of_card_eq hp hf hK
    have : Fact p.Prime := ⟨hp⟩
    have : CharP K p := hchar ▸ ringChar.charP K
    exact borelInterface_of_tailIsometry (minusTailIsometry n K b c) (coe_quadMinus n K b c)
      (commutator_orthogonalGroup_quadMinus hn hirr) (by omega) (anisotropic_minusTailForm hirr)
      (nondegenerate_minusTailForm hirr) (Or.inr finrank_fin_two_fun)
      (tailModelFlag_eq_map (minusTailIsometry n K b c) fun _ => rfl)

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
