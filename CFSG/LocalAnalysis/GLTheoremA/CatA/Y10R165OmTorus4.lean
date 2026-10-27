module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165OmTorus

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open QuadraticMap CFSG.Open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.SeitzGeneration.OrthBlk
open CFSG.RankThree.Classical2

namespace OmTorus

variable {F W : Type} [Field F] [CharP F 2] [AddCommGroup W] [Module F W]
  {Q : QuadraticForm F W}

theorem polar_plusPlaneA_gens (P P' : HypPair Q) (h : P.Orth P') (c : F) :
    polar Q (P.e + P.f) (P.e + c • P'.e + P'.f) = 1 := by
  simp only [QuadraticMap.map_add Q, QuadraticMap.map_smul Q, polar_add_left, polar_add_right,
    polar_smul_left_eq, polar_smul_right_eq, P.polar_ee, P.polar_ff, P'.polar_ee, P'.polar_ff,
    P.polar_ef, P'.polar_ef, P.polar_fe, P'.polar_fe, P.Q_e, P.Q_f, P'.Q_e, P'.Q_f, h.ee, h.ef,
    h.fe, h.ff]
  ring

theorem Q_plusPlaneA_snd (P P' : HypPair Q) (h : P.Orth P') (c : F) :
    Q (P.e + c • P'.e + P'.f) = c := by
  simp only [QuadraticMap.map_add Q, QuadraticMap.map_smul Q, polar_add_left, polar_add_right,
    polar_smul_left_eq, polar_smul_right_eq, P.polar_ee, P.polar_ff, P'.polar_ee, P'.polar_ff,
    P.polar_ef, P'.polar_ef, P.polar_fe, P'.polar_fe, P.Q_e, P.Q_f, P'.Q_e, P'.Q_f, h.ee, h.ef,
    h.fe, h.ff]
  ring

theorem Q_plusPlaneB_fst (P P' : HypPair Q) (h : P.Orth P') :
    Q (P.e + P.f + P'.e) = 1 := by
  simp only [QuadraticMap.map_add Q, QuadraticMap.map_smul Q, polar_add_left, polar_add_right,
    polar_smul_left_eq, polar_smul_right_eq, P.polar_ee, P.polar_ff, P'.polar_ee, P'.polar_ff,
    P.polar_ef, P'.polar_ef, P.polar_fe, P'.polar_fe, P.Q_e, P.Q_f, P'.Q_e, P'.Q_f, h.ee, h.ef,
    h.fe, h.ff]
  ring

theorem Q_plusPlaneB_snd (P P' : HypPair Q) (h : P.Orth P') (c : F) :
    Q (c • P'.e + P'.f) = c := by
  simp only [QuadraticMap.map_add Q, QuadraticMap.map_smul Q, polar_add_left, polar_add_right,
    polar_smul_left_eq, polar_smul_right_eq, P'.polar_ee, P'.polar_ff, P'.polar_ef,
    P'.Q_e, P'.Q_f, h.ee, h.ef, h.fe, h.ff]
  ring

theorem polar_plusPlaneB_gens (P P' : HypPair Q) (h : P.Orth P') (c : F) :
    polar Q (P.e + P.f + P'.e) (c • P'.e + P'.f) = 1 := by
  simp only [QuadraticMap.map_add Q, QuadraticMap.map_smul Q, polar_add_left, polar_add_right,
    polar_smul_left_eq, polar_smul_right_eq, P.polar_ee, P.polar_ff, P'.polar_ee, P'.polar_ff,
    P.polar_ef, P'.polar_ef, P.polar_fe, P'.polar_fe, P.Q_e, P.Q_f, P'.Q_e, P'.Q_f, h.ee, h.ef,
    h.fe, h.ff]
  ring

@[expose] noncomputable def plusPlaneA (P P' : HypPair Q) (h : P.Orth P') (c : F)
    (hc : ∀ s t : F, s ^ 2 + s * t + c * t ^ 2 = 0 → s = 0 ∧ t = 0) : PlaneFrame Q where
  A := Submodule.span F {P.e + P.f, P.e + c • P'.e + P'.f}
  u := P.e + P.f
  v := P.e + c • P'.e + P'.f
  hu := Submodule.subset_span (Set.mem_insert _ _)
  hv := Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  hQu := by
    rw [QuadraticMap.map_add Q, P.Q_e, P.Q_f, P.polar_ef]
    simp
  hbv := by
    rw [polar_plusPlaneA_gens P P' h c]
    exact one_ne_zero
  hirr := by
    intro s
    rw [polar_plusPlaneA_gens P P' h c, Q_plusPlaneA_snd P P' h c]
    exact fun hs => one_ne_zero (hc s 1 (by simpa using hs)).2
  hspan := rfl

@[expose] noncomputable def plusPlaneB (P P' : HypPair Q) (h : P.Orth P') (c : F)
    (hc : ∀ s t : F, s ^ 2 + s * t + c * t ^ 2 = 0 → s = 0 ∧ t = 0) : PlaneFrame Q where
  A := Submodule.span F {P.e + P.f + P'.e, c • P'.e + P'.f}
  u := P.e + P.f + P'.e
  v := c • P'.e + P'.f
  hu := Submodule.subset_span (Set.mem_insert _ _)
  hv := Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  hQu := by rw [Q_plusPlaneB_fst P P' h]
  hbv := by
    rw [polar_plusPlaneB_gens P P' h c]
    exact one_ne_zero
  hirr := by
    intro s
    rw [polar_plusPlaneB_gens P P' h c, Q_plusPlaneB_snd P P' h c]
    exact fun hs => one_ne_zero (hc s 1 (by simpa using hs)).2
  hspan := rfl

theorem plusPlane_orthogonal (P P' : HypPair Q) (h : P.Orth P') (c : F)
    (hc : ∀ s t : F, s ^ 2 + s * t + c * t ^ 2 = 0 → s = 0 ∧ t = 0) :
    (plusPlaneA P P' h c hc).A ≤ perp Q (plusPlaneB P P' h c hc).A := by
  intro x hx
  simp only [plusPlaneA, plusPlaneB] at hx ⊢
  rw [Submodule.mem_span_pair] at hx
  obtain ⟨α, β, rfl⟩ := hx
  rw [mem_perp]
  intro y hy
  rw [Submodule.mem_span_pair] at hy
  obtain ⟨γ, δ, rfl⟩ := hy
  have h1 : polar Q P'.e P.e = 0 := by rw [polar_comm]; exact h.ee
  have h2 : polar Q P'.e P.f = 0 := by rw [polar_comm]; exact h.fe
  have h3 : polar Q P'.f P.e = 0 := by rw [polar_comm]; exact h.ef
  have h4 : polar Q P'.f P.f = 0 := by rw [polar_comm]; exact h.ff
  simp only [QuadraticMap.map_add Q, QuadraticMap.map_smul Q, polar_add_left, polar_add_right,
    polar_smul_left_eq, polar_smul_right_eq, P.polar_ee, P.polar_ff, P'.polar_ee, P'.polar_ff,
    P.polar_ef, P'.polar_ef, P.polar_fe, P'.polar_fe, P.Q_e, P.Q_f, P'.Q_e, P'.Q_f,
    h.ee, h.ef, h.fe, h.ff, h1, h2, h3, h4]
  linear_combination (α * γ + γ * β + δ * c * β) * (CharTwo.two_eq_zero (R := F))

end OmTorus

end CFSG.LocalAnalysis.GLTheoremA.Y10F
