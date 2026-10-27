module

public import CFSG.LieType.AlgebraicGroups.ClosedOrbitSolvable
public import CFSG.LieType.AlgebraicGroups.ClosedSubgroupComponent
public import CFSG.LieType.AlgebraicGroups.MaximalTorusQuotient
public import CFSG.LieType.AlgebraicGroups.SolvableTorusConjugacy

public noncomputable section

open WithConv TauCeti.Comodule CFSG.LieType.AlgebraicGroups.ClosedCone

namespace CFSG.LieType.AlgebraicGroups.TorusConjugacy

universe u

variable {k : Type u} [Field k]

section Stabilizer

variable {H : Type u} [CommRing H] [HopfAlgebra k H]
variable {W : Type u} [AddCommGroup W] [Module k W] [TauCeti.Comodule k H W]

theorem basePointsRepresentation_mem_span {w : W} {g : WithConv (H →ₐ[k] k)}
    (hg : basePointsRepresentation (H := H) W g w ∈ k ∙ w) {x : W} (hx : x ∈ k ∙ w) :
    basePointsRepresentation (H := H) W g x ∈ k ∙ w := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
  rw [map_smul]
  exact Submodule.smul_mem _ a hg

variable (k H) in
@[expose] def lineStabilizer (w : W) : Subgroup (WithConv (H →ₐ[k] k)) where
  carrier := {g | basePointsRepresentation (H := H) W g w ∈ k ∙ w ∧
    basePointsRepresentation (H := H) W g⁻¹ w ∈ k ∙ w}
  mul_mem' {g h} hg hh := by
    refine ⟨?_, ?_⟩
    · rw [map_mul, Module.End.mul_apply]
      exact basePointsRepresentation_mem_span hg.1 hh.1
    · rw [mul_inv_rev, map_mul, Module.End.mul_apply]
      exact basePointsRepresentation_mem_span hh.2 hg.2
  one_mem' := by
    refine ⟨?_, ?_⟩ <;> simp [Submodule.mem_span_singleton_self]
  inv_mem' {g} hg := ⟨hg.2, by simpa only [inv_inv] using hg.1⟩

theorem mem_lineStabilizer {w : W} {g : WithConv (H →ₐ[k] k)} :
    g ∈ lineStabilizer k H w ↔ basePointsRepresentation (H := H) W g w ∈ k ∙ w ∧
      basePointsRepresentation (H := H) W g⁻¹ w ∈ k ∙ w :=
  Iff.rfl

theorem mem_lineStabilizer_iff {w : W} (hw : w ≠ 0) (g : WithConv (H →ₐ[k] k)) :
    g ∈ lineStabilizer k H w ↔ basePointsRepresentation (H := H) W g w ∈ k ∙ w := by
  rw [mem_lineStabilizer]
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_smul] at ha
    apply hw
    have := congrArg (basePointsRepresentation (H := H) W g⁻¹) ha
    rwa [map_zero, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply, eq_comm] at this
  refine Submodule.mem_span_singleton.mpr ⟨a⁻¹, ?_⟩
  have := congrArg (basePointsRepresentation (H := H) W g⁻¹) ha
  rw [map_smul, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
    Module.End.one_apply] at this
  conv_lhs => rw [← this]
  rw [smul_smul, inv_mul_cancel₀ ha0, one_smul]

theorem mem_lineStabilizer_of_forall_mem_vanishingIdeal {w : W} (hw : w ≠ 0)
    {g : WithConv (H →ₐ[k] k)}
    (hg : ∀ x ∈ TauCeti.HopfIdeal.vanishingIdeal (lineStabilizer k H w), g.ofConv x = 0) :
    g ∈ lineStabilizer k H w := by
  rw [mem_lineStabilizer_iff hw]
  by_contra hgw
  obtain ⟨φ, hφg, hφw⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hgw inferInstance
  have hφ : ∀ x ∈ k ∙ w, φ x = 0 := fun x hx => by
    have hmem : φ x ∈ (k ∙ w).map φ := Submodule.mem_map_of_mem hx
    rwa [hφw, Submodule.mem_bot] at hmem
  refine hφg ?_
  rw [← apply_matrixCoefficient]
  refine hg _ ((TauCeti.HopfIdeal.mem_vanishingIdeal _ _).mpr fun s => ?_)
  rw [apply_matrixCoefficient]
  exact hφ _ (mem_lineStabilizer.mp s.2).1

end Stabilizer

variable [IsAlgClosed k]


theorem exists_conjugate_eq_of_isMaximalTorus_of_isSolvable
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) [IsDomain H]
    [Group.IsSolvable (WithConv (H →ₐ[k] k))] {I₁ I₂ : TauCeti.HopfIdeal k H}
    (h₁ : TauCeti.HopfIdeal.IsMaximalTorus k H.obj I₁)
    (h₂ : TauCeti.HopfIdeal.IsMaximalTorus k H.obj I₂) :
    ∃ g : WithConv (H →ₐ[k] k), I₁.conjugate g = I₂ := by
  obtain ⟨u, hu⟩ := unipotent_conjugacy_maximalTorusIdeals_of_isSolvable H ⟨I₁, h₁⟩ ⟨I₂, h₂⟩
  exact ⟨unipotentRadicalPointsHom H u, hu⟩

theorem exists_quotientPointsSubgroup_conjugate_le_lineStabilizer
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) [IsDomain H] {I : TauCeti.HopfIdeal k H}
    (hI : TauCeti.HopfIdeal.IsMaximalTorus k H.obj I)
    {W : Type u} [AddCommGroup W] [Module k W] [TauCeti.Comodule k H W] [FiniteDimensional k W]
    {w : W} (hw : w ≠ 0) (hclosed : IsZariskiClosed k (orbitCone k H w)) :
    ∃ g : WithConv (H →ₐ[k] k),
      TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj (I.conjugate g) (CommAlgCat.of k k) ≤
        lineStabilizer k H w := by
  have hcone : IsCone k (orbitCone k H w) := by
    rintro c _ ⟨g, d, rfl⟩
    exact ⟨g, c * d, by rw [smul_smul]⟩
  have hG : ∀ g : WithConv (H →ₐ[k] k), ∀ v ∈ orbitCone k H w,
      basePointsRepresentation (H := H) W g v ∈ orbitCone k H w := by
    rintro g _ ⟨h, d, rfl⟩
    exact ⟨g * h, d, by rw [map_smul, map_mul, Module.End.mul_apply]⟩
  have hne : ∃ v ∈ orbitCone k H w, v ≠ 0 := ⟨w, ⟨1, 1, by simp⟩, hw⟩
  obtain ⟨x, ⟨g, c, rfl⟩, hx0, hxT⟩ :=
    exists_ne_zero_mem_forall_mem_span_of_isMaximalTorus H hI hclosed hcone
      (fun s _ => hG s) hne
  have hc : c ≠ 0 := by
    rintro rfl
    exact hx0 (zero_smul k _)
  refine ⟨g⁻¹, fun y hy => ?_⟩
  have hmv : ∀ x : WithConv (H →ₐ[k] k),
      TauCeti.AlgHom.mapValue (H := H) (Algebra.ofId k k) x = x := fun x => by
    ext h
    simp
  have ht : g * y * g⁻¹ ∈
      TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k) := by
    refine (TauCeti.CommHopfAlgCat.pointConjugation_mem_conjugate_iff I g⁻¹ (CommAlgCat.of k k)
      (g * y * g⁻¹)).mp ?_
    rw [hmv, inv_inv, show g⁻¹ * (g * y * g⁻¹) * g = y by group]
    exact hy
  have h1 := hxT _ ht
  rw [map_smul, ← Module.End.mul_apply, ← map_mul, show g * y * g⁻¹ * g = g * y by group,
    map_mul, Module.End.mul_apply] at h1
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h1
  rw [mem_lineStabilizer_iff hw]
  refine Submodule.mem_span_singleton.mpr ⟨a, ?_⟩
  have h2 := congrArg (fun v => c⁻¹ • basePointsRepresentation (H := H) W g⁻¹ v) ha
  simp only [map_smul, smul_smul, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_left] at h2
  rwa [show c⁻¹ * (a * c) = a by field_simp, inv_mul_cancel₀ hc, one_smul, inv_mul_cancel,
    map_one, Module.End.one_apply] at h2

theorem exists_conjugate_eq_of_isMaximalTorus_of_ringKrullDim_le (n : ℕ) :
    ∀ (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) [IsDomain H], ringKrullDim H ≤ n →
      ∀ {I₁ I₂ : TauCeti.HopfIdeal k H}, TauCeti.HopfIdeal.IsMaximalTorus k H.obj I₁ →
        TauCeti.HopfIdeal.IsMaximalTorus k H.obj I₂ →
          ∃ g : WithConv (H →ₐ[k] k), I₁.conjugate g = I₂ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro H _ hdim I₁ I₂ h₁ h₂
  by_cases hsol : Group.IsSolvable (WithConv (H →ₐ[k] k))
  · exact exists_conjugate_eq_of_isMaximalTorus_of_isSolvable H h₁ h₂
  have hnot := mt (isSolvable_of_forall_isZariskiClosed_orbitCone (k := k) (H := H)) hsol
  simp only [not_forall, exists_prop] at hnot
  obtain ⟨W, _, _, _, _, w, hw0, hclosed, g₀, hg₀⟩ := hnot
  obtain ⟨g₁, hg₁⟩ := exists_quotientPointsSubgroup_conjugate_le_lineStabilizer H h₁ hw0 hclosed
  obtain ⟨g₂, hg₂⟩ := exists_quotientPointsSubgroup_conjugate_le_lineStabilizer H h₂ hw0 hclosed
  let S := lineStabilizer k H w
  let J := closureIdentityComponent H S
  have hdomJ : IsDomain (TauCeti.FiniteTypeCommHopfAlgCat.quotient H J) :=
    isDomain_quotient_closureIdentityComponent H S
  have hT₁ := h₁.conjugate g₁
  have hT₂ := h₂.conjugate g₂
  have hJ : ∀ {I : TauCeti.HopfIdeal k H}, TauCeti.HopfIdeal.IsMaximalTorus k H.obj I →
      TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k) ≤ S → J ≤ I := by
    intro I hI hIS
    have : IsDomain (TauCeti.FiniteTypeCommHopfAlgCat.quotient H I) :=
      isDomain_quotient_of_isMaximalTorus H hI
    have : ConnectedSpace (PrimeSpectrum (TauCeti.FiniteTypeCommHopfAlgCat.quotient H I)) :=
      connectedSpace_iff_univ.mpr (IrreducibleSpace.isIrreducible_univ _).isConnected
    exact closureIdentityComponent_le H hIS
  have hJ₁ : J ≤ I₁.conjugate g₁ := hJ hT₁ hg₁
  have hJ₂ : J ≤ I₂.conjugate g₂ := hJ hT₂ hg₂
  have hJbot : J ≠ ⊥ := by
    intro hJ0
    apply hg₀
    have hmem : g₀ ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj J (CommAlgCat.of k k) := by
      rw [TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff, hJ0]
      intro x hx
      rw [(TauCeti.HopfIdeal.mem_bot).mp hx, map_zero]
    have hmem' := quotientPointsSubgroup_closureIdentityComponent_le H S hmem
    rw [TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff] at hmem'
    exact (mem_lineStabilizer_iff hw0 g₀).mp
      (mem_lineStabilizer_of_forall_mem_vanishingIdeal hw0 hmem')
  have hlt := (ringKrullDim_quotient_lt H hJbot).trans_le hdim
  obtain ⟨m, hm, hdim'⟩ : ∃ m < n,
      ringKrullDim (TauCeti.FiniteTypeCommHopfAlgCat.quotient H J) ≤ (m : WithBot ℕ∞) := by
    have h0 : (0 : WithBot ℕ∞) ≤ ringKrullDim (TauCeti.FiniteTypeCommHopfAlgCat.quotient H J) :=
      ringKrullDim_nonneg_of_nontrivial
    generalize ringKrullDim (TauCeti.FiniteTypeCommHopfAlgCat.quotient H J) = x at hlt h0 ⊢
    induction x using WithBot.recBotCoe with
    | bot => exact absurd h0 (by simp)
    | coe y =>
      induction y using ENat.recTopCoe with
      | top => exact absurd hlt (by simp)
      | coe a =>
        refine ⟨a, ?_, le_rfl⟩
        exact_mod_cast hlt
  obtain ⟨h', hh'⟩ := ih m hm (TauCeti.FiniteTypeCommHopfAlgCat.quotient H J) hdim'
    (isMaximalTorus_map H hJ₁ hT₁) (isMaximalTorus_map H hJ₂ hT₂)
  have hconj := conjugate_eq_of_map_conjugate_eq H hJ₁ hJ₂ h' hh'
  refine ⟨g₂⁻¹ * TauCeti.CommHopfAlgCat.quotientPointsHom H.obj J (CommAlgCat.of k k) h' * g₁, ?_⟩
  rw [TauCeti.HopfIdeal.conjugate_mul, TauCeti.HopfIdeal.conjugate_mul, hconj,
    TauCeti.HopfIdeal.conjugate_inv_conjugate]

theorem exists_conjugate_eq_of_isMaximalTorus
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) [IsDomain H] {I₁ I₂ : TauCeti.HopfIdeal k H}
    (h₁ : TauCeti.HopfIdeal.IsMaximalTorus k H.obj I₁)
    (h₂ : TauCeti.HopfIdeal.IsMaximalTorus k H.obj I₂) :
    ∃ g : WithConv (H →ₐ[k] k), I₁.conjugate g = I₂ := by
  have : FiniteRingKrullDim H := TauCeti.finiteRingKrullDim_of_finiteType k H
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ringKrullDim H ≤ (n : WithBot ℕ∞) := by
    have htop : ringKrullDim H < ⊤ := ringKrullDim_lt_top
    generalize ringKrullDim H = x at htop ⊢
    induction x using WithBot.recBotCoe with
    | bot => exact ⟨0, bot_le⟩
    | coe y =>
      induction y using ENat.recTopCoe with
      | top => exact absurd htop (by simp)
      | coe a => exact ⟨a, le_rfl⟩
  exact exists_conjugate_eq_of_isMaximalTorus_of_ringKrullDim_le n H hn h₁ h₂

end CFSG.LieType.AlgebraicGroups.TorusConjugacy
