module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15Alpha
public import CFSG.ClassicalInvolution.Q3.Q3NMClass
public import CFSG.ClassicalInvolution.Q3.Q3NMLie
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3MFOD

open CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Q3.Q3NM CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.LieType.Universal.Spin

section Sim

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem conj_mem_orthogonalGroup_of_sim {g : V ≃ₗ[F] V} {μ : F}
    (hg : ∀ v, Q (g v) = μ * Q v) {x : V ≃ₗ[F] V}
    (hx : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q) :
    g * x * g⁻¹ ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff] at hx ⊢
  intro v
  have h1 : Q v = μ * Q (g.symm v) := by
    have := hg (g.symm v)
    rwa [LinearEquiv.apply_symm_apply] at this
  show Q (g (x (g.symm v))) = Q v
  rw [hg, hx, h1]

theorem conj_mem_elementaryGroup_of_sim (hE : elementaryGroup Q =
    ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    {g : V ≃ₗ[F] V} {μ : F} (hg : ∀ v, Q (g v) = μ * Q v) {x : V ≃ₗ[F] V}
    (hx : x ∈ elementaryGroup Q) : g * x * g⁻¹ ∈ elementaryGroup Q := by
  have hO : (TauCeti.QuadraticMap.orthogonalGroup Q).map (MulAut.conj g).toMonoidHom ≤
      TauCeti.QuadraticMap.orthogonalGroup Q := by
    rintro _ ⟨y, hy, rfl⟩
    exact conj_mem_orthogonalGroup_of_sim hg hy
  have hc : (⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆).map (MulAut.conj g).toMonoidHom ≤
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono hO hO
  rw [hE] at hx ⊢
  exact hc ⟨x, hx, rfl⟩

theorem sim_mem_normalizer_elementaryGroup (hE : elementaryGroup Q =
    ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    {g : V ≃ₗ[F] V} {μ : F} (hμ : μ ≠ 0) (hg : ∀ v, Q (g v) = μ * Q v) :
    g ∈ Subgroup.normalizer (elementaryGroup Q : Set (V ≃ₗ[F] V)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => conj_mem_elementaryGroup_of_sim hE hg hx, fun hx => ?_⟩
  have hg' : ∀ v, Q (g⁻¹ v) = μ⁻¹ * Q v := by
    intro v
    have h1 : Q v = μ * Q (g.symm v) := by
      have := hg (g.symm v)
      rwa [LinearEquiv.apply_symm_apply] at this
    show Q (g.symm v) = μ⁻¹ * Q v
    rw [h1]
    field_simp
  have := conj_mem_elementaryGroup_of_sim hE hg' hx
  simpa [mul_assoc] using this

variable (Q) in
@[expose] noncomputable def conjES (hE : elementaryGroup Q =
    ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    {g : V ≃ₗ[F] V} {μ : F} (hμ : μ ≠ 0) (hg : ∀ v, Q (g v) = μ * Q v) :
    MulAut ↥(elementaryGroup Q) :=
  Q3NM.conjAut (elementaryGroup Q) g (sim_mem_normalizer_elementaryGroup hE hμ hg)

theorem conjES_apply (hE : elementaryGroup Q =
    ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    {g : V ≃ₗ[F] V} {μ : F} (hμ : μ ≠ 0) (hg : ∀ v, Q (g v) = μ * Q v)
    (b : ↥(elementaryGroup Q)) :
    ((conjES Q hE hμ hg b : ↥(elementaryGroup Q)) : V ≃ₗ[F] V) = g * (b : V ≃ₗ[F] V) * g⁻¹ :=
  rfl

theorem mem_fixedSubgroup_conjES (hE : elementaryGroup Q =
    ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    {g : V ≃ₗ[F] V} {μ : F} (hμ : μ ≠ 0) (hg : ∀ v, Q (g v) = μ * Q v)
    (b : ↥(elementaryGroup Q)) :
    b ∈ fixedSubgroup (conjES Q hE hμ hg) ↔ (b : V ≃ₗ[F] V) * g = g * b := by
  rw [mem_fixedSubgroup_iff]
  constructor
  · intro h
    have h' : g * (b : V ≃ₗ[F] V) * g⁻¹ = b := congrArg Subtype.val h
    calc (b : V ≃ₗ[F] V) * g = (g * (b : V ≃ₗ[F] V) * g⁻¹) * g := by rw [h']
      _ = g * b := by group
  · intro h
    refine Subtype.ext ?_
    show g * (b : V ≃ₗ[F] V) * g⁻¹ = b
    rw [← h]
    group

end Sim

section Dict

variable {F : Type} [Field F] {ι : Type} [Fintype ι] [DecidableEq ι]
  {Q : QuadraticForm F (ι → F)} {X : Type} [Group X]

theorem oddCoreIn_fixed_of_lift_aut [Group.IsPerfect (spinGroup Q)]
    (hrange : (spinAction Q).range = elementaryGroup Q) {θ : spinGroup Q →* X}
    (hθs : Function.Surjective θ) (hθk : θ.ker ≤ Subgroup.center (spinGroup Q)) (τ : MulAut X)
    (αK : MulAut (spinGroup Q)) (hτ : ∀ s, θ (αK s) = τ (θ s))
    (κ : MulAut ↥(elementaryGroup Q))
    (hκ : ∀ s, (κ ⟨spinAction Q s, by rw [← hrange]; exact ⟨s, rfl⟩⟩ : ↥(elementaryGroup Q)) =
      ⟨spinAction Q (αK s), by rw [← hrange]; exact ⟨αK s, rfl⟩⟩)
    (hN : oddCoreIn (fixedSubgroup (autToCentralQuotient ↥(elementaryGroup Q) κ)) = ⊥) :
    oddCoreIn (fixedSubgroup (autToCentralQuotient X τ)) = ⊥ := by
  classical
  have hmem : ∀ s : spinGroup Q, spinAction Q s ∈ elementaryGroup Q := fun s => by
    rw [← hrange]
    exact ⟨s, rfl⟩
  set πE : spinGroup Q →* ↥(elementaryGroup Q) :=
    (spinAction Q).codRestrict (elementaryGroup Q) hmem with hπE
  have hπs : Function.Surjective πE := by
    intro e
    have h1 : (e : (ι → F) ≃ₗ[F] (ι → F)) ∈ (spinAction Q).range := by
      rw [hrange]
      exact e.2
    obtain ⟨s, hs⟩ := h1
    exact ⟨s, Subtype.ext hs⟩
  have hπk : πE.ker ≤ Subgroup.center (spinGroup Q) := by
    intro s hs
    exact ker_spinAction_le_center Q (by
      rw [MonoidHom.mem_ker] at hs ⊢
      exact congrArg Subtype.val hs)
  let ε : X ⧸ Subgroup.center X ≃* ↥(elementaryGroup Q) ⧸ Subgroup.center ↥(elementaryGroup Q) :=
    (centralQuotientIso θ hθs hθk).symm.trans (centralQuotientIso πE hπs hπk)
  have hε : ∀ s : spinGroup Q, ε (QuotientGroup.mk (θ s)) = QuotientGroup.mk (πE s) := by
    intro s
    have h1 : (centralQuotientIso θ hθs hθk).symm (QuotientGroup.mk (θ s)) =
        (QuotientGroup.mk s : spinGroup Q ⧸ Subgroup.center (spinGroup Q)) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show (centralQuotientIso πE hπs hπk)
      ((centralQuotientIso θ hθs hθk).symm (QuotientGroup.mk (θ s))) = _
    rw [h1]
    rfl
  have hcongr : MulAut.congr ε.symm (autToCentralQuotient ↥(elementaryGroup Q) κ) =
      autToCentralQuotient X τ := by
    refine MulEquiv.ext fun xb => ?_
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective xb
    obtain ⟨s, rfl⟩ := hθs y
    have h1 : (MulAut.congr ε.symm (autToCentralQuotient ↥(elementaryGroup Q) κ))
        (QuotientGroup.mk (θ s)) = ε.symm ((autToCentralQuotient ↥(elementaryGroup Q) κ)
          (ε (QuotientGroup.mk (θ s)))) := rfl
    rw [h1, hε, autToCentralQuotient_mk]
    have hπα : κ (πE s) = πE (αK s) := hκ s
    rw [hπα, ← hε, MulEquiv.symm_apply_apply, autToCentralQuotient_mk, hτ]
  rw [← hcongr]
  exact oddCoreIn_fixed_congr_eq_bot' ε.symm _ hN

end Dict

end CFSG.ClassicalInvolution.Q3.Q3MFOD
