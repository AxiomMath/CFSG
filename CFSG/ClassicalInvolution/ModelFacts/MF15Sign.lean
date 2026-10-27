module

public import CFSG.ClassicalInvolution.ModelFacts.MF15Basic
public import CFSG.ClassicalInvolution.ModelFacts.Orth15Basic
public import CFSG.LieType.Universal.IrreducibleQuadratic
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders

public section

namespace CFSG.ClassicalInvolution.ModelFacts.MF15

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.GroupTheory.WeirSylow
open CFSG.LieType.Universal.Spin (quadPlus quadMinus)

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

omit [AddCommGroup V] [Module F V] in
theorem signPlus_iff {V : Type} [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}
    {U : Submodule F V} :
    SignPlus Q U ↔ ∃ T ≤ U, (∀ v ∈ T, Q v = 0) ∧
      Module.finrank F U = 2 * Module.finrank F T := by
  constructor
  · rintro ⟨W, hW, hWs⟩
    refine ⟨W.map U.subtype, Submodule.map_subtype_le U W, ?_, ?_⟩
    · rintro _ ⟨w, hw, rfl⟩
      exact hWs w hw
    · rw [Submodule.finrank_map_subtype_eq U W]; omega
  · rintro ⟨T, hTU, hTs, hT⟩
    refine ⟨T.comap U.subtype, ?_, fun x hx => hTs _ hx⟩
    have h1 : (T.comap U.subtype).map U.subtype = T := by
      rw [Submodule.map_comap_subtype]; exact inf_eq_right.mpr hTU
    have h2 := Submodule.finrank_map_subtype_eq U (T.comap U.subtype)
    rw [h1] at h2
    omega

theorem signPlus_plane_iff {U : Submodule F V} (hU : Module.finrank F U = 2) :
    SignPlus Q U ↔ ∃ v ∈ U, v ≠ 0 ∧ Q v = 0 := by
  constructor
  · rintro ⟨W, hW, hWs⟩
    have h1 : Module.finrank F W = 1 := by omega
    have hW0 : W ≠ ⊥ := by
      intro h
      rw [h, finrank_bot] at h1
      exact absurd h1 (by norm_num)
    obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
    exact ⟨(w : V), w.2, fun h => hw0 (Subtype.ext h), hWs w hwW⟩
  · rintro ⟨v, hvU, hv0, hvQ⟩
    have hv0' : (⟨v, hvU⟩ : U) ≠ 0 := fun h => hv0 (congrArg Subtype.val h)
    refine ⟨Submodule.span F {(⟨v, hvU⟩ : U)}, ?_, ?_⟩
    · rw [finrank_span_singleton hv0', hU]
    · intro w hw
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
      change Q (a • v) = 0
      rw [map_smul_eq_sq, hvQ, mul_zero]

theorem finrank_span_pair_two {u w : V} (h : LinearIndependent F ![u, w]) :
    Module.finrank F (Submodule.span F {u, w}) = 2 := by
  have h5 := finrank_span_eq_card h
  have hr : Set.range ![u, w] = {u, w} := by
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff, Fin.exists_fin_two]
    simp [eq_comm]
  rw [hr] at h5
  rw [h5]
  simp

section Four

variable [Finite F] [FiniteDimensional F V]

omit [Finite F] [FiniteDimensional F V] in
theorem polar_isometryEquiv {V₁ V₂ : Type} [AddCommGroup V₁] [Module F V₁] [AddCommGroup V₂]
    [Module F V₂] {Q₁ : QuadraticForm F V₁} {Q₂ : QuadraticForm F V₂}
    (e : Q₁.IsometryEquiv Q₂) (a b : V₁) : polar Q₂ (e a) (e b) = polar Q₁ a b := by
  have h : Q₂ (e a + e b) = Q₁ (a + b) := by
    rw [← map_add]; exact e.map_app _
  simp only [polar, h, e.map_app]

omit [Finite F] in
theorem exists_frame_of_four {U : Submodule F V} (hU : PolarNondegOn Q U)
    (hd : Module.finrank F U = 4) (hs : SignPlus Q U) : ∃ fr : Frame Q, fr.span ≤ U := by
  have hnd : (polarBilin (Q.restrict U)).Nondegenerate := nondegenerate_polarBilin_restrict hU
  obtain ⟨e⟩ := nonempty_isometry_quadPlus hnd (n := 2) (by omega) hs
  set P₀ := plusPair F (0 : Fin 2) with hP₀
  set P₁ := plusPair F (1 : Fin 2) with hP₁
  have horth : P₀.Orth P₁ := plusPair_orth (by decide)
  have hQe : ∀ p : Fin 2 ⊕ Fin 2 → F, quadPlus 2 F p = 0 → Q ((e.symm p : U) : V) = 0 := by
    intro p hp
    have := e.symm.map_app p
    exact this.trans hp
  have hpol : ∀ p p' : Fin 2 ⊕ Fin 2 → F, polar Q ((e.symm p : U) : V) ((e.symm p' : U) : V) =
      polar (quadPlus 2 F) p p' := fun p p' => by
    rw [← polar_restrict, polar_isometryEquiv e.symm]
  refine ⟨frameOfVectors ((e.symm P₀.e : U) : V) ((e.symm P₀.f : U) : V)
    ((e.symm P₁.e : U) : V) ((e.symm P₁.f : U) : V) (hQe _ P₀.Q_e) (hQe _ P₀.Q_f)
    (by rw [hpol]; exact P₀.polar_ef) (hQe _ P₁.Q_e) (hQe _ P₁.Q_f)
    (by rw [hpol]; exact P₁.polar_ef) (by rw [hpol]; exact horth.ee)
    (by rw [hpol]; exact horth.ef) (by rw [hpol]; exact horth.fe)
    (by rw [hpol]; exact horth.ff), ?_⟩
  rintro _ ⟨X, rfl⟩
  rw [incl_frameOfVectors]
  exact U.add_mem (U.add_mem (U.add_mem (U.smul_mem _ (e.symm P₀.e).2)
    (U.smul_mem _ (e.symm P₀.f).2)) (U.smul_mem _ (e.symm P₁.e).2))
    (U.smul_mem _ (e.symm P₁.f).2)

end Four

section Split

open CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.ModelFacts.Orth15

theorem nonempty_isometry_binForm_of_aniso [Finite F] {P : Submodule F V}
    (hP : PolarNondegOn Q P) (hd : Module.finrank F P = 2) (hnp : ¬ SignPlus Q P) {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    Nonempty ((Q.restrict P).IsometryEquiv (binForm b c)) := by
  have hnd := nondegenerate_polarBilin_restrict hP
  have : FiniteDimensional F P := Module.finite_of_finrank_pos (by omega)
  obtain ⟨e⟩ := nonempty_isometry_of_not_isPlusType hnd (n := 1) le_rfl (by omega) hnp hirr
  have e2 : (quadMinus 1 F b c).IsometryEquiv ((quadPlus 0 F).prod (binForm b c)) :=
    quadMinusIsometry 1 b c
  exact ⟨(e.trans e2).trans (QuadraticMap.IsometryEquiv.uniqueProd _ _)⟩

theorem exists_neg_similitude_of_aniso [Finite F] {P₁ P₂ : Submodule F V}
    (h₁ : PolarNondegOn Q P₁) (h₂ : PolarNondegOn Q P₂) (hd₁ : Module.finrank F P₁ = 2)
    (hd₂ : Module.finrank F P₂ = 2) (hn₁ : ¬ SignPlus Q P₁) (hn₂ : ¬ SignPlus Q P₂) :
    ∃ φ : P₁ ≃ₗ[F] P₂, ∀ p : P₁, Q (φ p : V) = - Q (p : V) := by
  obtain ⟨b, c, hirr⟩ := CFSG.LieType.Universal.exists_irreducible_quadratic F
  obtain ⟨e₁⟩ := nonempty_isometry_binForm_of_aniso h₁ hd₁ hn₁ hirr
  obtain ⟨e₂⟩ := nonempty_isometry_binForm_of_aniso h₂ hd₂ hn₂ hirr
  obtain ⟨ψ, hψ⟩ := exists_binForm_similitude hirr (d := (-1 : F)) (neg_ne_zero.mpr one_ne_zero)
  refine ⟨e₁.toLinearEquiv.trans (ψ.trans e₂.symm.toLinearEquiv), fun p => ?_⟩
  have h1 : Q (((e₁.toLinearEquiv.trans (ψ.trans e₂.symm.toLinearEquiv)) p : P₂) : V) =
      (Q.restrict P₂) (e₂.symm (ψ (e₁ p))) := rfl
  rw [h1, e₂.symm.map_app, hψ, e₁.map_app]
  simp

end Split

end CFSG.ClassicalInvolution.ModelFacts.MF15
