module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15Frame

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15

namespace T7O

open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalGroups.Orthogonal
  CFSG.ClassicalInvolution.Models.OrthogonalPairs QuadraticMap
open scoped MatrixGroups

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

section FrameLa

variable (fr : Frame Q)

theorem La_fix_perp (A : SL(2, F)) {r : V} (hr : r ∈ fr.perp) : fr.La A r = r :=
  Frame.La_apply_of_coords_eq_zero fr A ((Frame.mem_perp_iff fr).mp hr)

theorem La_mem_span (A : SL(2, F)) {s : V} (hs : s ∈ fr.span) : fr.La A s ∈ fr.span := by
  obtain ⟨X, rfl⟩ := hs
  rw [Frame.La_apply_incl]
  exact ⟨_, rfl⟩

theorem swap_La_fix_perp (A : SL(2, F)) {r : V} (hr : r ∈ fr.perp) : fr.swap.La A r = r :=
  La_fix_perp fr.swap A (by rwa [Frame.perp_swap])

theorem swap_La_mem_span (A : SL(2, F)) {s : V} (hs : s ∈ fr.span) :
    fr.swap.La A s ∈ fr.span := by
  have := La_mem_span fr.swap A (by rwa [Frame.span_eq_swap_span])
  rwa [Frame.span_eq_swap_span] at this

theorem mul_comm_of_fix_span {g w : V ≃ₗ[F] V} (hg : ∀ r ∈ fr.perp, g r = r)
    (hgs : ∀ s ∈ fr.span, g s ∈ fr.span) (hws : ∀ s ∈ fr.span, w s = s)
    (hwp : ∀ r ∈ fr.perp, w r ∈ fr.perp) : g * w = w * g := by
  refine LinearEquiv.ext fun x => ?_
  obtain ⟨hdec, hr⟩ := decomp_span_perp fr x
  have hs : fr.incl (fr.coords x) ∈ fr.span := ⟨_, rfl⟩
  conv_lhs => rw [hdec]
  conv_rhs => rw [hdec]
  simp only [LinearEquiv.mul_apply, map_add]
  rw [hws _ hs, hg _ hr, hg _ (hwp _ hr), hws _ (hgs _ hs)]

end FrameLa

section Hyp

variable [Finite F] [FiniteDimensional F V]

theorem commutator_orth_le_of_frame (hodd : Odd (Nat.card F)) (hQ : (polarBilin Q).Nondegenerate)
    (fr : Frame Q) (hV : 7 ≤ Module.finrank F V) :
    ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ≤
      elementaryGroup Q := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  have hperp3 : 3 ≤ Module.finrank F fr.perp := by
    have := finrank_perp_add_four fr
    omega
  obtain ⟨P₃, he₃, hf₃⟩ := exists_hypPair_le hodd (polarNondegOn_perp hQ fr) hperp3
  have h₁₃ : fr.P.Orth P₃ :=
    ⟨polar_perp_of_mem_span fr fr.e₁_mem_span he₃, polar_perp_of_mem_span fr fr.e₁_mem_span hf₃,
      polar_perp_of_mem_span fr fr.f₁_mem_span he₃, polar_perp_of_mem_span fr fr.f₁_mem_span hf₃⟩
  have h₂₃ : fr.P'.Orth P₃ :=
    ⟨polar_perp_of_mem_span fr fr.e₂_mem_span he₃, polar_perp_of_mem_span fr fr.e₂_mem_span hf₃,
      polar_perp_of_mem_span fr fr.f₂_mem_span he₃, polar_perp_of_mem_span fr fr.f₂_mem_span hf₃⟩
  exact (commutator_orthogonalGroup_eq_elementaryGroup_of_two_ne_zero h2 hQ fr.orth h₁₃ h₂₃).le

end Hyp

theorem not_central_of_sq_neg_one (h2 : (2 : F) ≠ 0) {a : SL(2, F)}
    (ha : (a : Matrix (Fin 2) (Fin 2) F) * a = -1) :
    ∃ b : SL(2, F), a * b ≠ b * a := by
  refine ⟨Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) 1, fun h => ?_⟩
  have hm : (a : Matrix (Fin 2) (Fin 2) F) * !![1, 1; 0, 1] =
      !![1, 1; 0, 1] * (a : Matrix (Fin 2) (Fin 2) F) := by
    have := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F)) h
    simpa [Frame.coe_transvection_zero_one] using this
  have hdet := a.2
  rw [Matrix.det_fin_two] at hdet
  have e1 := congrFun (congrFun hm 0) 0
  have e2 := congrFun (congrFun hm 0) 1
  have e3 := congrFun (congrFun ha 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e1 e2 e3
  have hr : (a : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := e1
  have hps : (a : Matrix (Fin 2) (Fin 2) F) 0 0 = (a : Matrix (Fin 2) (Fin 2) F) 1 1 := by
    linear_combination e2
  rw [hr, hps] at hdet e3
  apply h2
  linear_combination e3 - hdet

end T7O

end CFSG.ClassicalInvolution.ModelFacts.Orth15
