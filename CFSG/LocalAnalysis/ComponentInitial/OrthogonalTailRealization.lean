module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailOpposite
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailShellConstancy
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailCoordinates

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin Module
  Submodule
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CFSG.ComponentClassification.CatalogueBOrthogonalPointAction
  (Points pointMk pointMk_submodule exists_eq_pointMk)

variable {K : Type*} [Field K] {A : Type*} [AddCommGroup A] [Module K A] {r : ℕ}

theorem map_symm_map_linearEquiv {V : Type*} [AddCommGroup V] [Module K V] (T : V ≃ₗ[K] V)
    (W : Submodule K V) : (W.map (T : V →ₗ[K] V)).map (T.symm : V →ₗ[K] V) = W := by
  ext v
  rw [Submodule.mem_map_equiv, LinearEquiv.symm_symm, Submodule.mem_map_equiv,
    LinearEquiv.symm_apply_apply]

theorem exists_semiSim_of_polarOrtho [FiniteDimensional K A] (hr : 3 ≤ r)
    {qA : QuadraticForm K A} (hani : qA.Anisotropic) (hreg : (polarBilin qA).Nondegenerate)
    (φ : Points (quadTail r qA) ≃ Points (quadTail r qA))
    (hφ : ∀ L M : Points (quadTail r qA),
      PolarOrtho (quadTail r qA) L.val M.val ↔ PolarOrtho (quadTail r qA) (φ L).val (φ M).val) :
    ∃ T : SemiSim (quadTail r qA) (quadTail r qA), ∀ L : Points (quadTail r qA),
      (φ L).val = T.mapSub L.val := by
  have h₁ := isInfOfMax_quadTail (r := r) hani hreg
  have hXs : ∀ x ∈ (flag r K r).prod (⊥ : Submodule K A), quadTail r qA x = 0 :=
    fun _ hx => quadTail_eq_zero_of_mem_xSpan hx
  have hYs : ∀ x ∈ (ySpan r K).prod (⊥ : Submodule K A), quadTail r qA x = 0 :=
    fun _ hx => quadTail_eq_zero_of_mem_ySpan hx
  obtain ⟨q₂, T₀, hq₂ani, hq₂reg, hT₀Q, hT₀X, hT₀Y⟩ := exists_tail_coordinates hani hreg
    (totSing_polarImage₂ φ hφ hXs) (totSing_polarImage₂ φ hφ hYs)
    (by rw [finrank_polarImage₂ φ hφ h₁ h₁ hXs, finrank_xSpan_tail])
    (by rw [finrank_polarImage₂ φ hφ h₁ h₁ hYs, finrank_ySpan_tail])
    (polarImage₂_inf_eq_bot h₁ h₁ φ hφ)
  have h₂ := isInfOfMax_quadTail (r := r) hq₂ani hq₂reg
  obtain ⟨T₀s, -, hT₀sm⟩ : ∃ T₀s : SemiSim (quadTail r q₂) (quadTail r qA),
      (∀ v, T₀s.e v = T₀ v) ∧
        ∀ W, T₀s.symm.mapSub W = W.map (T₀.symm : ((Fin r ⊕ Fin r → K) × A) →ₗ[K] _) :=
    ⟨SemiSim.ofLinear T₀ one_ne_zero fun v => by rw [hT₀Q, one_mul], fun v => rfl, fun W => by
      ext y
      rw [Submodule.mem_map_equiv]
      rfl⟩
  obtain ⟨φ₁, hφ₁⟩ : ∃ φ₁ : Points (quadTail r qA) ≃ Points (quadTail r q₂),
      φ₁ = φ.trans T₀s.pointEquiv.symm := ⟨_, rfl⟩
  have hφ₁o : ∀ L M : Points (quadTail r qA),
      PolarOrtho (quadTail r qA) L.val M.val ↔ PolarOrtho (quadTail r q₂) (φ₁ L).val (φ₁ M).val :=
    hφ₁ ▸ T₀s.polarOrtho_trans_symm φ hφ
  have hφ₁X : polarImage₂ φ₁ ((flag r K r).prod ⊥) = (flag r K r).prod ⊥ := by
    rw [hφ₁, T₀s.polarImage₂_trans_symm φ hφ h₁ hXs, hT₀sm, ← hT₀X, map_symm_map_linearEquiv]
  have hφ₁Y : polarImage₂ φ₁ ((ySpan r K).prod ⊥) = (ySpan r K).prod ⊥ := by
    rw [hφ₁, T₀s.polarImage₂_trans_symm φ hφ h₁ hYs, hT₀sm, ← hT₀Y, map_symm_map_linearEquiv]
  have hφ₁Y' : ∀ L : Points (quadTail r qA), L.val ≤ (ySpan r K).prod ⊥ →
      (φ₁ L).val ≤ (ySpan r K).prod ⊥ := fun L hL => by
    have h : φ₁ L ∈ φ₁ '' ptsIn (quadTail r qA) ((ySpan r K).prod ⊥) := ⟨L, hL, rfl⟩
    rw [← ptsIn_polarImage₂ φ₁ hφ₁o h₁ hYs, hφ₁Y] at h
    exact h
  obtain ⟨C, σ, hCσ⟩ := exists_semilinear_on_xSpan hr h₁ h₂ φ₁ hφ₁o hφ₁X
  have hs_add := basisCoord_add (A := A) σ
  have hs_smul := basisCoord_smul (A := A) σ
  have hq₃ani := anisotropic_twistForm hs_add hs_smul hq₂ani
  have hq₃reg := nondegenerate_twistForm hs_add hs_smul hq₂reg
  obtain ⟨φ₂, hφ₂⟩ : ∃ φ₂ : Points (quadTail r qA) ≃
      Points (quadTail r (twistForm hs_add hs_smul q₂)),
      φ₂ = φ₁.trans (twistSim hs_add hs_smul q₂ C).pointEquiv.symm := ⟨_, rfl⟩
  have hφ₂o : ∀ L M : Points (quadTail r qA),
      PolarOrtho (quadTail r qA) L.val M.val ↔
        PolarOrtho (quadTail r (twistForm hs_add hs_smul q₂)) (φ₂ L).val (φ₂ M).val :=
    hφ₂ ▸ (twistSim hs_add hs_smul q₂ C).polarOrtho_trans_symm φ₁ hφ₁o
  have hφ₂v : ∀ L : Points (quadTail r qA),
      (φ₂ L).val = (twistSim hs_add hs_smul q₂ C).symm.mapSub (φ₁ L).val := fun L => by
    rw [hφ₂]
    rfl
  have hφ₂X : ∀ L : Points (quadTail r qA), L.val ≤ (flag r K r).prod ⊥ → (φ₂ L).val = L.val := by
    intro L hL
    obtain ⟨v, hv0, hvQ, rfl⟩ := exists_eq_pointMk L
    have hvX : v ∈ (flag r K r).prod (⊥ : Submodule K A) := by
      rw [pointMk_submodule, span_singleton_le_iff_mem] at hL
      exact hL
    obtain ⟨x, rfl⟩ : ∃ x, xEmbT r K A x = v := by
      rw [← LinearMap.mem_range, range_xEmbT]
      exact hvX
    rw [hφ₂v, hCσ x hv0 hvQ, SemiSim.mapSub_span_singleton, ← twistSim_xEmbT hs_add hs_smul q₂ C,
      SemiSim.symm_e, Equiv.symm_apply_apply, pointMk_submodule]
  have hφ₂Y : ∀ L : Points (quadTail r qA), L.val ≤ (ySpan r K).prod ⊥ → (φ₂ L).val = L.val := by
    intro L hL
    refine eq_of_le_ySpan_tail φ₂ hφ₂o hφ₂X hL ?_
    rw [hφ₂v]
    intro y hy
    exact mem_ySpan_of_twistSim (v := y) hs_add hs_smul q₂ C
      (hφ₁Y' L hL ((SemiSim.mem_mapSub _).1 hy))
  obtain ⟨c, hc, hmix⟩ := orthogonal_geometry_tail_mixed_coordinates hr hani hq₃ani φ₂ hφ₂o hφ₂X
    hφ₂Y
  obtain ⟨F, ⟨-, hFq, hφF⟩, -⟩ :=
    orthogonal_geometry_tail_shell_constancy hr hani hq₃ani φ₂ hφ₂o hmix
  obtain ⟨-, -, -, g, hg, hgQ⟩ :=
    orthogonal_geometry_tail_linear_rigidity (by omega) hreg hq₃reg hc hFq φ₂ hφ₂o hφF
  refine ⟨(SemiSim.ofLinear g hc hgQ).trans ((twistSim hs_add hs_smul q₂ C).trans T₀s),
    fun L => ?_⟩
  obtain ⟨v, hv0, hvQ, rfl⟩ := exists_eq_pointMk L
  have h2 : (φ₂ (pointMk v hv0 hvQ)).val = K ∙ g v := by rw [hφF, hg]
  have h1 : φ₁ (pointMk v hv0 hvQ) =
      (twistSim hs_add hs_smul q₂ C).pointEquiv (φ₂ (pointMk v hv0 hvQ)) := by
    rw [hφ₂, Equiv.trans_apply, Equiv.apply_symm_apply]
  have h0 : φ (pointMk v hv0 hvQ) = T₀s.pointEquiv (φ₁ (pointMk v hv0 hvQ)) := by
    rw [hφ₁, Equiv.trans_apply, Equiv.apply_symm_apply]
  rw [h0, SemiSim.coe_pointEquiv, h1, SemiSim.coe_pointEquiv, h2, SemiSim.mapSub_span_singleton,
    SemiSim.mapSub_span_singleton, pointMk_submodule, SemiSim.mapSub_span_singleton]
  rfl

section Coord

variable {m : ℕ}

@[expose] def tailSCoord (σ : K ≃+* K) (v : (Fin r ⊕ Fin r → K) × (Fin m → K)) :
    (Fin r ⊕ Fin r → K) × (Fin m → K) :=
  (fun x => σ (v.1 x), fun j => σ (v.2 j))

theorem tailSCoord_symm_tailSCoord (σ : K ≃+* K) (v : (Fin r ⊕ Fin r → K) × (Fin m → K)) :
    tailSCoord σ.symm (tailSCoord σ v) = v := by
  simp [tailSCoord]

theorem tailSCoord_tailSCoord_symm (σ : K ≃+* K) (v : (Fin r ⊕ Fin r → K) × (Fin m → K)) :
    tailSCoord σ (tailSCoord σ.symm v) = v := by
  simp [tailSCoord]

theorem tailSCoord_add (σ : K ≃+* K) (v w : (Fin r ⊕ Fin r → K) × (Fin m → K)) :
    tailSCoord σ (v + w) = tailSCoord σ v + tailSCoord σ w :=
  Prod.ext (funext fun x => by simp [tailSCoord]) (funext fun j => by simp [tailSCoord])

theorem tailSCoord_smul (σ : K ≃+* K) (c : K) (v : (Fin r ⊕ Fin r → K) × (Fin m → K)) :
    tailSCoord σ (c • v) = σ c • tailSCoord σ v :=
  Prod.ext (funext fun x => by simp [tailSCoord]) (funext fun j => by simp [tailSCoord])

@[expose] noncomputable def SemiSim.linearPart
    {Q : QuadraticForm K ((Fin r ⊕ Fin r → K) × (Fin m → K))} (T : SemiSim Q Q) :
    ((Fin r ⊕ Fin r → K) × (Fin m → K)) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × (Fin m → K)) where
  toFun v := T.e (tailSCoord T.σ.symm v)
  invFun w := tailSCoord T.σ (T.e.symm w)
  map_add' v w := by rw [tailSCoord_add, T.map_add']
  map_smul' c v := by
    rw [tailSCoord_smul, T.map_smul', RingEquiv.apply_symm_apply, RingHom.id_apply]
  left_inv v := by
    simp only [Equiv.symm_apply_apply, tailSCoord_tailSCoord_symm]
  right_inv w := by
    simp only [tailSCoord_symm_tailSCoord, Equiv.apply_symm_apply]

theorem SemiSim.linearPart_tailSCoord {Q : QuadraticForm K ((Fin r ⊕ Fin r → K) × (Fin m → K))}
    (T : SemiSim Q Q) (v : (Fin r ⊕ Fin r → K) × (Fin m → K)) :
    T.linearPart (tailSCoord T.σ v) = T.e v := by
  change T.e (tailSCoord T.σ.symm (tailSCoord T.σ v)) = T.e v
  rw [tailSCoord_symm_tailSCoord]

end Coord

theorem orthogonal_geometry_tail_polar_realization {K : Type*} [Field K] {r m : ℕ} (hr : 3 ≤ r)
    {qA : QuadraticForm K (Fin m → K)} (hani : qA.Anisotropic)
    (hreg : (polarBilin qA).Nondegenerate)
    (φ : Points (quadTail r qA) ≃ Points (quadTail r qA))
    (hφ : ∀ L M : Points (quadTail r qA),
      PolarOrtho (quadTail r qA) L.val M.val ↔ PolarOrtho (quadTail r qA) (φ L).val (φ M).val) :
    ∃ (A₀ : ((Fin r ⊕ Fin r → K) × (Fin m → K)) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × (Fin m → K)))
      (σ : K ≃+* K) (μ : K), μ ≠ 0 ∧
      (∀ v, quadTail r qA (A₀ (tailSCoord σ v)) = μ * σ (quadTail r qA v)) ∧
      ∀ L : Points (quadTail r qA), ((φ L).val : Set ((Fin r ⊕ Fin r → K) × (Fin m → K))) =
        (fun v => A₀ (tailSCoord σ v)) '' (L.val : Set ((Fin r ⊕ Fin r → K) × (Fin m → K))) := by
  obtain ⟨T, hT⟩ := exists_semiSim_of_polarOrtho hr hani hreg φ hφ
  refine ⟨T.linearPart, T.σ, T.μ, T.μ_ne_zero, fun v => ?_, fun L => ?_⟩
  · rw [T.linearPart_tailSCoord, T.map_quad']
  · rw [hT L, T.coe_mapSub]
    congr 1
    funext v
    exact (T.linearPart_tailSCoord v).symm

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
