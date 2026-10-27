module

public import CFSG.LieType.Chevalley.ParabolicRadicalPointwiseRigidity
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.LocalAnalysis.ComponentInitial.AutomorphismRadicalRigidity

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial

section Generic

variable {C : Type*} [Group C]

@[expose] def setwiseStabilizer (A : Subgroup (MulAut C)) (Q : Subgroup C) :
    Subgroup (MulAut C) where
  carrier := {α | α ∈ A ∧ Q.map α.toMonoidHom = Q}
  one_mem' := ⟨A.one_mem, by
    ext x
    simp⟩
  mul_mem' {α β} hα hβ := ⟨A.mul_mem hα.1 hβ.1, by
    have e : (α * β).toMonoidHom = α.toMonoidHom.comp β.toMonoidHom := MonoidHom.ext fun x => rfl
    rw [e, ← Subgroup.map_map, hβ.2, hα.2]⟩
  inv_mem' {α} hα := ⟨A.inv_mem hα.1, by
    have h := congrArg (Subgroup.map α⁻¹.toMonoidHom) hα.2
    have e : α⁻¹.toMonoidHom.comp α.toMonoidHom = MonoidHom.id C :=
      MonoidHom.ext fun x => MulAut.inv_apply_self C α x
    rw [Subgroup.map_map, e, Subgroup.map_id] at h
    exact h.symm⟩

theorem mem_setwiseStabilizer {A : Subgroup (MulAut C)} {Q : Subgroup C} {α : MulAut C} :
    α ∈ setwiseStabilizer A Q ↔ α ∈ A ∧ Q.map α.toMonoidHom = Q :=
  Iff.rfl

theorem normalizer_conclusions_of_pointwise_rigidity [Finite C] (hZ : Subgroup.center C = ⊥)
    {p : ℕ} [Fact p.Prime] {Q : Subgroup C} (hQ : IsPGroup p Q) {A : Subgroup (MulAut C)}
    (hInn : (MulAut.conj : C →* MulAut C).range ≤ A)
    (hrig : ∀ α ∈ A, (∀ q ∈ Q, α q = q) →
      α ∈ ((Subgroup.center Q).map Q.subtype).map MulAut.conj) :
    (∀ α : MulAut C, (α ∈ A ∧ ∀ q ∈ Q, α q = q) ↔
      α ∈ ((Subgroup.center Q).map Q.subtype).map MulAut.conj) ∧
    (∀ M : Subgroup (MulAut C), Q.map MulAut.conj ≤ M → M ≤ setwiseStabilizer A Q →
      IsCharacteristicP p M ∧ pPrimeCore p M = ⊥) ∧
    IsCharacteristicP p (setwiseStabilizer A Q) ∧ pPrimeCore p (setwiseStabilizer A Q) = ⊥ := by
  have hQA : Q.map MulAut.conj ≤ A := fun α ⟨q, _, hq⟩ => hInn ⟨q, hq⟩
  have hCA : ∀ α ∈ A, (∀ u ∈ Q, α u = u) → α ∈ Q.map MulAut.conj := by
    intro α hα hfix
    obtain ⟨z, ⟨⟨y, hyQ⟩, -, rfl⟩, rfl⟩ := hrig α hα hfix
    exact ⟨y, hyQ, rfl⟩
  have hM : ∀ M : Subgroup (MulAut C), Q.map MulAut.conj ≤ M → M ≤ setwiseStabilizer A Q →
      IsCharacteristicP p M ∧ pPrimeCore p M = ⊥ := by
    intro M hQM hMN
    obtain ⟨h1, -, h3⟩ := automorphism_normalizer_from_pointwise_radical_rigidity hZ hQ hQA hCA hQM
      fun α hα => hMN hα
    exact ⟨h1, h3⟩
  have hQN : Q.map MulAut.conj ≤ setwiseStabilizer A Q := by
    rintro _ ⟨q, hq, rfl⟩
    refine ⟨hQA ⟨q, hq, rfl⟩, ?_⟩
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact Q.mul_mem (Q.mul_mem hq hy) (Q.inv_mem hq)
    · intro hx
      refine ⟨q⁻¹ * x * q, Q.mul_mem (Q.mul_mem (Q.inv_mem hq) hx) hq, ?_⟩
      change q * (q⁻¹ * x * q) * q⁻¹ = x
      group
  refine ⟨fun α => ⟨fun h => hrig α h.1 h.2, ?_⟩, hM, hM _ hQN le_rfl⟩
  rintro ⟨z, ⟨⟨y, hyQ⟩, hyc, rfl⟩, rfl⟩
  refine ⟨hInn ⟨y, rfl⟩, fun q hq => ?_⟩
  have h1 := congrArg Subtype.val (Subgroup.mem_center_iff.1 hyc ⟨q, hq⟩)
  change q * y = y * q at h1
  change y * q * y⁻¹ = q
  rw [← h1]
  group

end Generic

variable {τ : Tag} {K : Type} [Field K]

@[expose] def parabolicRadicalIn
    (τ : Tag) (K : Type) [Field K] (J : Set (Fin τ.rank)) :
    Subgroup (adjointGroup τ K) :=
  (parabolicRadical τ K J).subgroupOf (adjointGroup τ K)

theorem parabolicRadical_le_adjointGroup
    (J : Set (Fin τ.rank)) :
    parabolicRadical τ K J ≤ adjointGroup τ K :=
  (parabolicRadical_le_posUnipotent J).trans posUnipotent_le_adjointGroup

theorem mem_parabolicRadicalIn
    {J : Set (Fin τ.rank)} {x : adjointGroup τ K} :
    x ∈ parabolicRadicalIn τ K J ↔ (x : ModGL τ K) ∈ parabolicRadical τ K J :=
  Subgroup.mem_subgroupOf

theorem mem_map_center_parabolicRadicalIn
    {J : Set (Fin τ.rank)} {z : ModGL τ K}
    (hz : z ∈ (Subgroup.center (parabolicRadical τ K J)).map (parabolicRadical τ K J).subtype)
    (hzC : z ∈ adjointGroup τ K) :
    (⟨z, hzC⟩ : adjointGroup τ K) ∈
      (Subgroup.center (parabolicRadicalIn τ K J)).map (parabolicRadicalIn τ K J).subtype := by
  obtain ⟨⟨z, hzQ⟩, hzc, rfl⟩ := hz
  refine ⟨⟨⟨z, hzC⟩, mem_parabolicRadicalIn.2 hzQ⟩, Subgroup.mem_center_iff.2 fun y => ?_, rfl⟩
  have h1 := congrArg Subtype.val (Subgroup.mem_center_iff.1 hzc
    ⟨(y : adjointGroup τ K), mem_parabolicRadicalIn.1 y.2⟩)
  exact Subtype.ext (Subtype.ext h1)

theorem exact_parabolic_diagonal_field_normalizers_characteristic_p_ordinary
    {p : ℕ}
    [Fact p.Prime] (τ : Tag) (K : Type) [Field K] [Finite K] [CharP K p]
    {J : Set (Fin τ.rank)} (hJ : J ≠ Set.univ) :
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
    IsCharacteristicP p (setwiseStabilizer (diagonalFieldActors τ K) (parabolicRadicalIn τ K J)) ∧
    pPrimeCore p (setwiseStabilizer (diagonalFieldActors τ K) (parabolicRadicalIn τ K J)) = ⊥ := by
  have : Finite (ModGL τ K) := finite_modGL
  have hZ : Subgroup.center (adjointGroup τ K) = ⊥ := center_adjointGroup_eq_bot
  obtain ⟨-, hQp, hQ1⟩ := (parabolic_root_radical_Levi_factors τ K J).2.2.2.2.2.2.2.2.2.2.2.2 p
  have hQC := parabolicRadical_le_adjointGroup (K := K) J
  have e : parabolicRadicalIn τ K J ≃* parabolicRadical τ K J :=
    Subgroup.subgroupOfEquivOfLe hQC
  have hp : IsPGroup p (parabolicRadicalIn τ K J) := hQp.of_equiv e.symm
  have hne : parabolicRadicalIn τ K J ≠ ⊥ := by
    intro h
    apply hQ1 hJ
    rw [eq_bot_iff]
    intro x hx
    have h1 : (⟨x, hQC hx⟩ : adjointGroup τ K) ∈ parabolicRadicalIn τ K J :=
      mem_parabolicRadicalIn.2 hx
    rw [h, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val h1
  have hrig := (Chevalley_parabolic_radical_diagonal_field_pointwise_rigidity τ K hJ).1
  have hactor := (Chevalley_diagonal_field_actor_data.1 τ K)
  obtain ⟨hall, hconj, hgen⟩ := normalizer_conclusions_of_pointwise_rigidity hZ hp hactor.2.2
    fun α hα hfix => by
      obtain ⟨g, hg, a, δ, hαx⟩ := (hactor.1 α).1 hα
      obtain ⟨-, z, hz, hzC, rfl⟩ := hrig g hg a δ α hαx
        fun x hx => hfix x (mem_parabolicRadicalIn.2 hx)
      exact ⟨_, mem_map_center_parabolicRadicalIn hz hzC, rfl⟩
  exact ⟨hZ, hne, hp, hall, hconj, hgen⟩

end CFSG.LieType.Chevalley
