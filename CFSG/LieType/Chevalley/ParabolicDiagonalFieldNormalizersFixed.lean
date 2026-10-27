module

public import CFSG.LieType.Chevalley.ParabolicDiagonalFieldNormalizers
public import CFSG.LieType.Chevalley.GraphFixedParabolicPointwiseRigidity

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial

@[expose] def graphFixedParabolicRadicalIn
    (t : TwistTag) (K : Type) [Field K] (σ : K ≃+* K)
    (J : Set (Fin t.foldedTag.rank)) : Subgroup (graphFixedRootGroup t K σ.toRingHom) :=
  (graphFixedParabolicRadical t K σ.toRingHom J).subgroupOf (graphFixedRootGroup t K σ.toRingHom)

theorem mem_graphFixedParabolicRadicalIn
    {t : TwistTag} {K : Type} [Field K] {σ : K ≃+* K}
    {J : Set (Fin t.foldedTag.rank)} {x : graphFixedRootGroup t K σ.toRingHom} :
    x ∈ graphFixedParabolicRadicalIn t K σ J ↔
      (x : ModGL t.tag K) ∈ graphFixedParabolicRadical t K σ.toRingHom J :=
  Subgroup.mem_subgroupOf

theorem exact_parabolic_diagonal_field_normalizers_characteristic_p_fixed
    {p : ℕ}
    [Fact p.Prime] (t : TwistTag) (K : Type) [Field K] [Finite K] [CharP K p] (σ : K ≃+* K)
    (hσ : σ ^ t.order = 1) {J : Set (Fin t.foldedTag.rank)} (hJ : J ≠ Set.univ) :
    Subgroup.center (graphFixedRootGroup t K σ.toRingHom) = ⊥ ∧
    graphFixedParabolicRadicalIn t K σ J ≠ ⊥ ∧ IsPGroup p (graphFixedParabolicRadicalIn t K σ J) ∧
    (∀ α : MulAut (graphFixedRootGroup t K σ.toRingHom),
      (α ∈ fixedDiagonalFieldActors t K σ ∧ ∀ q ∈ graphFixedParabolicRadicalIn t K σ J, α q = q) ↔
        α ∈ ((Subgroup.center (graphFixedParabolicRadicalIn t K σ J)).map
          (graphFixedParabolicRadicalIn t K σ J).subtype).map MulAut.conj) ∧
    (∀ M : Subgroup (MulAut (graphFixedRootGroup t K σ.toRingHom)),
      (graphFixedParabolicRadicalIn t K σ J).map MulAut.conj ≤ M →
      M ≤ setwiseStabilizer (fixedDiagonalFieldActors t K σ)
        (graphFixedParabolicRadicalIn t K σ J) →
        IsCharacteristicP p M ∧ pPrimeCore p M = ⊥) ∧
    IsCharacteristicP p
      (setwiseStabilizer (fixedDiagonalFieldActors t K σ) (graphFixedParabolicRadicalIn t K σ J)) ∧
    pPrimeCore p
      (setwiseStabilizer (fixedDiagonalFieldActors t K σ) (graphFixedParabolicRadicalIn t K σ J)) =
        ⊥ := by
  have : Finite (ModGL t.tag K) := finite_modGL
  have hZ : Subgroup.center (graphFixedRootGroup t K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hQp, hQ1⟩ :=
    diagram_fixed_parabolic_root_radical_Levi_factors t K σ J
  have hQC := graphFixedParabolicRadical_le_graphFixedRootGroup t K σ.toRingHom J
  have e : graphFixedParabolicRadicalIn t K σ J ≃* graphFixedParabolicRadical t K σ.toRingHom J :=
    Subgroup.subgroupOfEquivOfLe hQC
  have hp : IsPGroup p (graphFixedParabolicRadicalIn t K σ J) := (hQp p).of_equiv e.symm
  have hne : graphFixedParabolicRadicalIn t K σ J ≠ ⊥ := by
    intro h
    apply hQ1 hJ
    rw [eq_bot_iff]
    intro x hx
    have h1 : (⟨x, hQC hx⟩ : graphFixedRootGroup t K σ.toRingHom) ∈
        graphFixedParabolicRadicalIn t K σ J := mem_graphFixedParabolicRadicalIn.2 hx
    rw [h, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val h1
  obtain ⟨-, hrig, -⟩ :=
    diagram_fixed_parabolic_radical_diagonal_field_pointwise_rigidity t K σ hσ hJ
  have hactor := Chevalley_diagonal_field_actor_data.2 t K σ
  obtain ⟨hall, hconj, hgen⟩ := normalizer_conclusions_of_pointwise_rigidity hZ hp hactor.2.2
    fun α hα hfix => by
      obtain ⟨g, hg, b, hb, δ, hδ, hαx⟩ := (hactor.1 α).1 hα
      obtain ⟨-, z, hz, hzC, rfl⟩ := hrig g hg b hb δ hδ α hαx
        fun x hx => hfix x (mem_graphFixedParabolicRadicalIn.2 hx)
      obtain ⟨⟨z, hzQ⟩, hzc, rfl⟩ := hz
      refine ⟨_, ⟨⟨⟨z, hzC⟩, mem_graphFixedParabolicRadicalIn.2 hzQ⟩,
        Subgroup.mem_center_iff.2 fun y => ?_, rfl⟩, rfl⟩
      have h1 := congrArg Subtype.val (Subgroup.mem_center_iff.1 hzc
        ⟨((y : graphFixedRootGroup t K σ.toRingHom) : ModGL t.tag K),
          mem_graphFixedParabolicRadicalIn.1 y.2⟩)
      exact Subtype.ext (Subtype.ext h1)
  exact ⟨hZ, hne, hp, hall, hconj, hgen⟩

theorem exact_parabolic_diagonal_field_normalizers_characteristic_p
    {p : ℕ} [Fact p.Prime]
    (K : Type) [Field K] [Finite K] [CharP K p] :
    (∀ (τ : Tag) (J : Set (Fin τ.rank)), J ≠ Set.univ →
      Subgroup.center (adjointGroup τ K) = ⊥ ∧
      parabolicRadicalIn τ K J ≠ ⊥ ∧ IsPGroup p (parabolicRadicalIn τ K J) ∧
      (∀ α : MulAut (adjointGroup τ K),
        (α ∈ diagonalFieldActors τ K ∧ ∀ q ∈ parabolicRadicalIn τ K J, α q = q) ↔
          α ∈ ((Subgroup.center (parabolicRadicalIn τ K J)).map
            (parabolicRadicalIn τ K J).subtype).map MulAut.conj) ∧
      (∀ M : Subgroup (MulAut (adjointGroup τ K)),
        (parabolicRadicalIn τ K J).map MulAut.conj ≤ M →
        M ≤ setwiseStabilizer (diagonalFieldActors τ K) (parabolicRadicalIn τ K J) →
          IsCharacteristicP p M ∧ pPrimeCore p M = ⊥) ∧
      IsCharacteristicP p
        (setwiseStabilizer (diagonalFieldActors τ K) (parabolicRadicalIn τ K J)) ∧
      pPrimeCore p (setwiseStabilizer (diagonalFieldActors τ K) (parabolicRadicalIn τ K J)) = ⊥) ∧
    (∀ (t : TwistTag) (σ : K ≃+* K), σ ^ t.order = 1 →
      ∀ J : Set (Fin t.foldedTag.rank), J ≠ Set.univ →
      Subgroup.center (graphFixedRootGroup t K σ.toRingHom) = ⊥ ∧
      graphFixedParabolicRadicalIn t K σ J ≠ ⊥ ∧
      IsPGroup p (graphFixedParabolicRadicalIn t K σ J) ∧
      (∀ α : MulAut (graphFixedRootGroup t K σ.toRingHom),
        (α ∈ fixedDiagonalFieldActors t K σ ∧
            ∀ q ∈ graphFixedParabolicRadicalIn t K σ J, α q = q) ↔
          α ∈ ((Subgroup.center (graphFixedParabolicRadicalIn t K σ J)).map
            (graphFixedParabolicRadicalIn t K σ J).subtype).map MulAut.conj) ∧
      (∀ M : Subgroup (MulAut (graphFixedRootGroup t K σ.toRingHom)),
        (graphFixedParabolicRadicalIn t K σ J).map MulAut.conj ≤ M →
        M ≤ setwiseStabilizer (fixedDiagonalFieldActors t K σ)
          (graphFixedParabolicRadicalIn t K σ J) →
          IsCharacteristicP p M ∧ pPrimeCore p M = ⊥) ∧
      IsCharacteristicP p (setwiseStabilizer (fixedDiagonalFieldActors t K σ)
        (graphFixedParabolicRadicalIn t K σ J)) ∧
      pPrimeCore p (setwiseStabilizer (fixedDiagonalFieldActors t K σ)
        (graphFixedParabolicRadicalIn t K σ J)) = ⊥) :=
  ⟨fun τ _ hJ => exact_parabolic_diagonal_field_normalizers_characteristic_p_ordinary τ K hJ,
    fun t σ hσ _ hJ =>
      exact_parabolic_diagonal_field_normalizers_characteristic_p_fixed t K σ hσ hJ⟩

end CFSG.LieType.Chevalley
