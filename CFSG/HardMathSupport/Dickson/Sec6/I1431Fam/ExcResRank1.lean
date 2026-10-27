module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResSL2Trace
public import CFSG.RankThree.Chevalley.SteinbergCFERootSL2Traces
public import CFSG.RankThree.Chevalley.SteinbergBIRootSL2Tools

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial Polynomial
open scoped MatrixGroups

section Trace


theorem excres_trace_rootSL2 {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {k : Type} [Field k]
    (β : Fin τ.rank → ℤ) (A : SL2 k) :
    LinearMap.trace k (RootModule τ k) (rootSL2 τ k β A : Module.End k (RootModule τ k)) =
      aeval (A : Matrix (Fin 2) (Fin 2) k).trace (eRootTracePoly τ) := by
  rw [rootSL2_apply, Units.val_mul, Units.val_mul, LinearMap.trace_conj,
    trace_simpleRootSL2_eq_aeval hτ]

@[expose] noncomputable def excresTheta (τ : Tag) {L : Type} [Field L] (K' : Subfield L)
    (β : Fin τ.rank → ℤ) (z : ModGL τ L) : SL2 K' →* ModGL τ L :=
  (MulAut.conj z).toMonoidHom.comp ((baseChangeGL K'.subtype).comp (rootSL2 τ K' β))

theorem excresTheta_apply (τ : Tag) {L : Type} [Field L] (K' : Subfield L)
    (β : Fin τ.rank → ℤ) (z : ModGL τ L) (g : SL2 K') :
    excresTheta τ K' β z g = z * baseChangeGL K'.subtype (rootSL2 τ K' β g) * z⁻¹ := rfl

theorem excresTheta_injective (τ : Tag) {L : Type} [Field L] (K' : Subfield L)
    (β : Fin τ.rank → ℤ) (z : ModGL τ L) : Function.Injective (excresTheta τ K' β z) := by
  intro g h hgh
  have h1 := (MulAut.conj z).injective hgh
  have h2 := baseChangeGL_injective _ h1
  exact rootSL2_injective_of_field β h2

theorem excres_trace_theta {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {L : Type} [Field L]
    (K' : Subfield L) (β : Fin τ.rank → ℤ) (z : ModGL τ L) (g : SL2 K') :
    LinearMap.trace L (RootModule τ L) (excresTheta τ K' β z g : Module.End L (RootModule τ L)) =
      K'.subtype (aeval (g : Matrix (Fin 2) (Fin 2) K').trace (eRootTracePoly τ)) := by
  rw [excresTheta_apply, Units.val_mul, Units.val_mul, LinearMap.trace_conj, trace_baseChangeGL,
    excres_trace_rootSL2 hτ]

theorem excres_inner_on_rankOne {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {L : Type}
    [Field L] (K' : Subfield L) [Finite K'] (β : Fin τ.rank → ℤ) (z : ModGL τ L)
    {P : Type} [Group P] [Finite P] (ι : P →* ModGL τ L) (hι : Function.Injective ι)
    (hθ : ∀ g : SL2 K', excresTheta τ K' β z g ∈ ι.range)
    {J : Subgroup P} (hJ : ∀ p : P, p ∈ J ↔ ι p ∈ (excresTheta τ K' β z).range)
    {y : P} (hy3 : y ^ 3 = 1) (hstab : ∀ p : P, y * p * y⁻¹ ∈ J ↔ p ∈ J) :
    ∃ w ∈ J, ∀ j ∈ J, y * j * y⁻¹ = w * j * w⁻¹ := by
  classical
  set θ := excresTheta τ K' β z with hθdef
  let e : P ≃* ι.range := MonoidHom.ofInjective hι
  let ρ : SL2 K' →* P := e.symm.toMonoidHom.comp (θ.codRestrict ι.range hθ)
  have hιρ : ∀ g, ι (ρ g) = θ g := by
    intro g
    have : e (ρ g) = ⟨θ g, hθ g⟩ := by
      change e (e.symm ⟨θ g, hθ g⟩) = _
      exact e.apply_symm_apply _
    exact congrArg Subtype.val this
  have hrange : ρ.range = J := by
    ext p
    constructor
    · rintro ⟨g, rfl⟩
      rw [hJ, hιρ]
      exact ⟨g, rfl⟩
    · intro hp
      obtain ⟨g, hg⟩ := (hJ p).1 hp
      exact ⟨g, hι (by rw [hιρ]; exact hg)⟩
  have hker : ∀ g : SL2 K', ρ g = 1 → ∃ l : K'ˣ, l ^ 2 = 1 ∧
      (g : Matrix (Fin 2) (Fin 2) K') = (l : K') • (1 : Matrix (Fin 2) (Fin 2) K') := by
    intro g hg
    have h1 : θ g = 1 := by rw [← hιρ, hg, map_one]
    have h2 : g = 1 := excresTheta_injective τ K' β z (by rw [h1, map_one])
    exact ⟨1, by simp, by rw [h2]; simp⟩
  have hχ : ∀ g h : P, LinearMap.trace L (RootModule τ L)
      (ι (h * g * h⁻¹) : Module.End L (RootModule τ L)) =
      LinearMap.trace L (RootModule τ L) (ι g : Module.End L (RootModule τ L)) := by
    intro g h
    rw [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul, LinearMap.trace_conj]
  obtain ⟨c, c₀, hcc⟩ : ∃ (c : ℕ) (c₀ : L), ∀ t : K'ˣ,
      LinearMap.trace L (RootModule τ L) (θ (sl2Diag K' t) : Module.End L (RootModule τ L)) =
        K'.subtype (((t : K') + (t : K')⁻¹) ^ 2 + (c : K') * ((t : K') + (t : K')⁻¹)) + c₀ := by
    rcases hτ with rfl | rfl | rfl
    · refine ⟨20, 34, fun t => ?_⟩
      rw [hθdef, excres_trace_theta (Or.inl rfl)]
      simp [eRootTracePoly, sl2Diag, Matrix.trace_fin_two, map_ofNat]
      first | rfl | norm_num | simp | exact_mod_cast rfl
    · refine ⟨32, 65, fun t => ?_⟩
      rw [hθdef, excres_trace_theta (Or.inr (Or.inl rfl))]
      simp [eRootTracePoly, sl2Diag, Matrix.trace_fin_two, map_ofNat]
      first | rfl | norm_num | simp | exact_mod_cast rfl
    · refine ⟨56, 132, fun t => ?_⟩
      rw [hθdef, excres_trace_theta (Or.inr (Or.inr rfl))]
      simp [eRootTracePoly, sl2Diag, Matrix.trace_fin_two, map_ofNat]
      first | rfl | norm_num | simp | exact_mod_cast rfl
  have hχd : ∀ t : K'ˣ, LinearMap.trace L (RootModule τ L) (ι (ρ (sl2Diag K' t)) : Module.End L
      (RootModule τ L)) = K'.subtype (((t : K') + (t : K')⁻¹) ^ 2 +
        (c : K') * ((t : K') + (t : K')⁻¹)) + c₀ := by
    intro t
    rw [hιρ]
    exact hcc t
  obtain ⟨w, hw, hwj⟩ := excres_normalizer_inner (ρ := ρ) hker K'.subtype c c₀
    (fun g => LinearMap.trace L (RootModule τ L) (ι g : Module.End L (RootModule τ L)))
    hχ hχd hy3 (by
      rw [hrange]
      ext p
      constructor
      · rintro ⟨q, hq, rfl⟩
        exact (hstab q).2 hq
      · intro hp
        refine ⟨y⁻¹ * p * y, (hstab _).1 ?_, ?_⟩
        · simpa [mul_assoc] using hp
        · simp [MulAut.conj_apply, mul_assoc])
  rw [hrange] at hw hwj
  exact ⟨w, hw, hwj⟩

end Trace

end CFSG.HardMathSupport.Dickson.Sec6.I1431
