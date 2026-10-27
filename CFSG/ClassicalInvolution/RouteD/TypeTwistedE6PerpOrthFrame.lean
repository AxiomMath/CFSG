module

public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Fundamental
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Pairs
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthConj
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.ClassicalGroups.Orthogonal.Derived
public import CFSG.ClassicalGroups.Orthogonal.ProjectiveSimple
public import CFSG.Open.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.ClassicalInvolution.RouteD.NonClassical

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalGroups.Orthogonal QuadraticMap
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

section Basic

theorem frame_La_neg_one_eq_of_span_eq (h2 : (2 : K) ≠ 0) {F F' : OFrame Q}
    (h : F'.span = F.span) : F'.La (-1) = F.La (-1) := by
  refine LinearEquiv.ext fun x => ?_
  obtain ⟨s, hs, r, hr, rfl⟩ := Submodule.mem_sup.mp
    (F.isCompl_span_perp.sup_eq_top ▸ (Submodule.mem_top : x ∈ (⊤ : Submodule K V)))
  have hs' : s ∈ F'.span := h ▸ hs
  have hr' : r ∈ F'.perp := (Frame.perp_eq_of_span_eq h).symm ▸ hr
  rw [map_add, map_add, (Frame.mem_span_iff_inv F h2).mp hs,
    (Frame.mem_span_iff_inv F' h2).mp hs', (Frame.mem_perp_iff_fix F h2).mp hr,
    (Frame.mem_perp_iff_fix F' h2).mp hr']

theorem frame_polar_incl_incl (F : OFrame Q) (X Y : Matrix (Fin 2) (Fin 2) K) :
    polar Q (F.incl X) (F.incl Y) = polarDet X Y := by
  rw [Frame.polar_incl_right, Frame.coords_incl]
  simp [polarDet]
  ring

@[expose] noncomputable def frameOfIsometry (F : OFrame Q)
    (θ : Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K)
    (hθ : θ ∈ TauCeti.QuadraticMap.orthogonalGroup (detQ (K := K))) : OFrame Q where
  P := ⟨F.incl (θ !![1, 0; 0, 0]), F.incl (θ !![0, 0; 0, 1]), by
      rw [F.Q_incl, ← detQ_apply, map_of_mem hθ, detQ_apply]; simp,
    by rw [F.Q_incl, ← detQ_apply, map_of_mem hθ, detQ_apply]; simp,
    by
      rw [frame_polar_incl_incl F, ← polar_detQ, polar_map_of_mem hθ, polar_detQ]
      simp [polarDet]⟩
  P' := ⟨F.incl (θ !![0, -1; 0, 0]), F.incl (θ !![0, 0; 1, 0]), by
      rw [F.Q_incl, ← detQ_apply, map_of_mem hθ, detQ_apply]; simp,
    by rw [F.Q_incl, ← detQ_apply, map_of_mem hθ, detQ_apply]; simp,
    by
      rw [frame_polar_incl_incl F, ← polar_detQ, polar_map_of_mem hθ, polar_detQ]
      simp [polarDet]⟩
  orth :=
    ⟨by
      rw [frame_polar_incl_incl F, ← polar_detQ, polar_map_of_mem hθ, polar_detQ]
      simp [polarDet],
    by
      rw [frame_polar_incl_incl F, ← polar_detQ, polar_map_of_mem hθ, polar_detQ]
      simp [polarDet],
    by
      rw [frame_polar_incl_incl F, ← polar_detQ, polar_map_of_mem hθ, polar_detQ]
      simp [polarDet],
    by
      rw [frame_polar_incl_incl F, ← polar_detQ, polar_map_of_mem hθ, polar_detQ]
      simp [polarDet]⟩

end Basic

section Torsor

variable {F : OFrame Q}

theorem frameOfIsometry_incl (θ : Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K)
    (hθ : θ ∈ TauCeti.QuadraticMap.orthogonalGroup (detQ (K := K))) (X : Matrix (Fin 2) (Fin 2) K) :
    (frameOfIsometry F θ hθ).incl X = F.incl (θ X) := by
  have hX : X = X 0 0 • !![1, 0; 0, 0] + X 1 1 • !![0, 0; 0, 1] + (-X 0 1) • !![0, -1; 0, 0] +
      X 1 0 • !![0, 0; 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [Frame.incl_apply]
  show X 0 0 • F.incl (θ !![1, 0; 0, 0]) + X 1 1 • F.incl (θ !![0, 0; 0, 1]) +
    (-X 0 1) • F.incl (θ !![0, -1; 0, 0]) + X 1 0 • F.incl (θ !![0, 0; 1, 0]) = _
  conv_rhs => rw [hX]
  simp only [map_add, map_smul]

theorem frameOfIsometry_span (θ : Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K)
    (hθ : θ ∈ TauCeti.QuadraticMap.orthogonalGroup (detQ (K := K))) :
    (frameOfIsometry F θ hθ).span = F.span := by
  ext y
  constructor
  · rintro ⟨X, rfl⟩
    exact ⟨θ X, (frameOfIsometry_incl θ hθ X).symm⟩
  · rintro ⟨Z, rfl⟩
    exact ⟨θ.symm Z, by rw [frameOfIsometry_incl]; simp⟩

@[expose] noncomputable def frameSpanEquiv (F : OFrame Q) :
    {F' : OFrame Q // F'.span = F.span} ≃
      TauCeti.QuadraticMap.orthogonalGroup (detQ (K := K)) where
  toFun F' := ⟨Frame.comparisonEquiv F'.2, Frame.comparisonEquiv_mem_orthogonalGroup F'.2⟩
  invFun θ := ⟨frameOfIsometry F θ.1 θ.2, frameOfIsometry_span θ.1 θ.2⟩
  left_inv F' := by
    refine Subtype.ext (Frame.ext_vec ?_ ?_ ?_ ?_)
    · show F.incl (Frame.comparison F F'.1 _) = _
      rw [Frame.incl_comparison F'.2, Frame.e₁_eq_incl]
    · show F.incl (Frame.comparison F F'.1 _) = _
      rw [Frame.incl_comparison F'.2, Frame.f₁_eq_incl]
    · show F.incl (Frame.comparison F F'.1 _) = _
      rw [Frame.incl_comparison F'.2, Frame.e₂_eq_incl]
    · show F.incl (Frame.comparison F F'.1 _) = _
      rw [Frame.incl_comparison F'.2, Frame.f₂_eq_incl]
  right_inv θ := by
    refine Subtype.ext (LinearEquiv.ext fun X => ?_)
    show Frame.comparison F (frameOfIsometry F θ.1 θ.2) X = θ.1 X
    rw [Frame.comparison_apply, frameOfIsometry_incl, Frame.coords_incl]

theorem card_frames_span (F : OFrame Q) :
    Nat.card {F' : OFrame Q // F'.span = F.span} =
      Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := K))) :=
  Nat.card_congr (frameSpanEquiv F)

end Torsor

section Fibres

variable [Finite K]

theorem frame_La_neg_one_eq_of_range_eq (hodd : Odd (Nat.card K)) {F F' : OFrame Q}
    (h : F'.La.range = F.La.range) : F'.La (-1) = F.La (-1) :=
  IsFundamental.involution_unique hodd (IsFundamental.of_frame F')
    (h ▸ IsFundamental.of_frame F)

omit [Finite K] in
theorem frame_swap_swap (F : OFrame Q) : F.swap.swap = F :=
  Frame.ext_vec rfl rfl rfl rfl

variable [Finite V]

instance finite_frame : Finite (OFrame Q) := by
  refine Finite.of_injective (fun F : OFrame Q => (F.e₁, F.f₁, F.e₂, F.f₂)) ?_
  intro F F' h
  simp only [Prod.mk.injEq] at h
  exact Frame.ext_vec h.1 h.2.1 h.2.2.1 h.2.2.2

theorem two_mul_card_frames_range (hodd : Odd (Nat.card K)) (F : OFrame Q) :
    2 * Nat.card {F' : OFrame Q // F'.La.range = F.La.range} =
      Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := K))) := by
  classical
  have h2 : (2 : K) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  set B₁ : Set (OFrame Q) := {F' | F'.La.range = F.La.range} with hB₁
  set B₂ : Set (OFrame Q) := {F' | F'.La.range = F.swap.La.range} with hB₂
  have hswapneg : F.swap.La (-1) = F.La (-1) := Frame.La_swap_neg_one F
  have hA : {F' : OFrame Q | F'.span = F.span} = B₁ ∪ B₂ := by
    ext F'
    constructor
    · intro h
      exact Frame.La_range_eq_or_eq_swap h2 (frame_La_neg_one_eq_of_span_eq h2 h)
    · rintro (h | h)
      · exact Frame.span_eq_of_La_neg_one_eq h2 (frame_La_neg_one_eq_of_range_eq hodd h)
      · exact Frame.span_eq_of_La_neg_one_eq h2
          ((frame_La_neg_one_eq_of_range_eq hodd h).trans hswapneg)
  have hdisj : Disjoint B₁ B₂ := Set.disjoint_left.mpr fun F' h1 h2' =>
    Frame.La_range_ne_swap_La_range F (h1.symm.trans h2')
  have h1to2 : ∀ F' ∈ B₁, F'.swap ∈ B₂ := by
    intro F' hF'
    have hneg := frame_La_neg_one_eq_of_range_eq hodd hF'
    have hs : F'.swap.La (-1) = F.La (-1) := (Frame.La_swap_neg_one F').trans hneg
    rcases Frame.La_range_eq_or_eq_swap h2 hs with h | h
    · exact absurd (h.trans hF'.symm) (Frame.La_range_ne_swap_La_range F').symm
    · exact h
  have h2to1 : ∀ F' ∈ B₂, F'.swap ∈ B₁ := by
    intro F' hF'
    have hneg := (frame_La_neg_one_eq_of_range_eq hodd hF').trans hswapneg
    have hs : F'.swap.La (-1) = F.La (-1) := (Frame.La_swap_neg_one F').trans hneg
    rcases Frame.La_range_eq_or_eq_swap h2 hs with h | h
    · exact h
    · exact absurd (h.trans hF'.symm) (Frame.La_range_ne_swap_La_range F').symm
  have hcard : B₁.ncard = B₂.ncard :=
    Set.ncard_congr (fun F' _ => F'.swap) h1to2
      (fun a b _ _ h => by simpa [frame_swap_swap] using congrArg Frame.swap h)
      (fun b hb => ⟨b.swap, h2to1 b hb, frame_swap_swap b⟩)
  have hfin : ∀ S : Set (OFrame Q), S.Finite := fun S => Set.toFinite S
  have e1 : Nat.card {F' : OFrame Q // F'.La.range = F.La.range} = B₁.ncard :=
    Nat.card_coe_set_eq B₁
  have e2 : Nat.card {F' : OFrame Q // F'.span = F.span} =
      ({F' : OFrame Q | F'.span = F.span}).ncard := Nat.card_coe_set_eq _
  rw [← card_frames_span F, e1, e2, hA, Set.ncard_union_eq hdisj (hfin _) (hfin _), ← hcard]
  ring

end Fibres

end CFSG.ClassicalInvolution.RouteD.NonClassical
