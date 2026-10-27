module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431D4Aux.FieldPart.Semilinear

public noncomputable section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431.FieldPart

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

set_option linter.unusedSectionVars false


variable {K : Type} [Field K] [Finite K]

theorem mem_normalizer_of_conj_mem_StabU {x : adjointGroup Tag.D4 K}
    (hx : MulAut.conj x ∈ StabU K) : x ∈ Subgroup.normalizer
      ((UP K : Subgroup (adjointGroup Tag.D4 K)) : Set (adjointGroup Tag.D4 K)) := by
  have h : (UP K).map (MulAut.conj x).toMonoidHom = UP K := hx
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    have : x * u * x⁻¹ ∈ (UP K).map (MulAut.conj x).toMonoidHom :=
      Subgroup.mem_map.2 ⟨u, hu, by simp [MulAut.conj_apply]⟩
    rwa [h] at this
  · intro hu
    rw [← h] at hu
    obtain ⟨u', hu', hu'e⟩ := Subgroup.mem_map.1 hu
    have : u' = u := by
      simpa [MulAut.conj_apply] using hu'e
    exact this ▸ hu'

theorem exists_decomp (α : MulAut (adjointGroup Tag.D4 K)) :
    ∃ (c : adjointGroup Tag.D4 K) (β : MulAut (adjointGroup Tag.D4 K)), β ∈ StabU K ∧
      α = MulAut.conj c * β := by
  have : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K _⟩
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem Tag.D4).length
  obtain ⟨c, β, hU, -, rfl⟩ :=
    (exceptional_ordinary_Sylow_opposition Tag.D4 K (ringChar K) w₀ hw₀).2.2.2.2.2 α
  exact ⟨c, β, hU, rfl⟩

@[expose] def sigmaOf (β : StabU K) : K ≃+* K :=
  (exists_semilin β.2).choose_spec.choose

theorem semilin_sigmaOf (β : StabU K) : ∃ a : Kˣ, Semilin (β : MulAut (adjointGroup Tag.D4 K)) a
    (sigmaOf β) := by
  have := (exists_semilin β.2).choose_spec.choose_spec
  exact ⟨(exists_semilin β.2).choose, this⟩

theorem sigmaOf_eq {β : StabU K} {a : Kˣ} {σ : K ≃+* K}
    (h : Semilin (β : MulAut (adjointGroup Tag.D4 K)) a σ) : sigmaOf β = σ := by
  obtain ⟨a', ha'⟩ := semilin_sigmaOf β
  exact (h.unique ha').2.symm

theorem sigmaOf_one : sigmaOf (1 : StabU K) = 1 := by
  apply sigmaOf_eq
  exact Semilin.one

theorem sigmaOf_mul (β β' : StabU K) : sigmaOf (β * β') = sigmaOf β * sigmaOf β' := by
  obtain ⟨a, ha⟩ := semilin_sigmaOf β
  obtain ⟨a', ha'⟩ := semilin_sigmaOf β'
  exact sigmaOf_eq (ha.mul ha')

theorem sigmaOf_conj {x : adjointGroup Tag.D4 K}
    (hx : x ∈ Subgroup.normalizer ((UP K : Subgroup (adjointGroup Tag.D4 K)) :
      Set (adjointGroup Tag.D4 K))) : sigmaOf ⟨MulAut.conj x, conj_mem_StabU hx⟩ = 1 := by
  obtain ⟨a, ha⟩ := semilin_conj hx
  exact sigmaOf_eq ha

noncomputable def decompOf (α : MulAut (adjointGroup Tag.D4 K)) :
    adjointGroup Tag.D4 K × StabU K :=
  ((exists_decomp α).choose, ⟨(exists_decomp α).choose_spec.choose,
    (exists_decomp α).choose_spec.choose_spec.1⟩)

theorem decompOf_spec (α : MulAut (adjointGroup Tag.D4 K)) :
    α = MulAut.conj (decompOf α).1 * ((decompOf α).2 : MulAut (adjointGroup Tag.D4 K)) :=
  (exists_decomp α).choose_spec.choose_spec.2

@[expose] def fieldPartFn (α : MulAut (adjointGroup Tag.D4 K)) : K ≃+* K :=
  sigmaOf (decompOf α).2

theorem fieldPartFn_eq {α : MulAut (adjointGroup Tag.D4 K)} {c : adjointGroup Tag.D4 K}
    {β : StabU K} (h : α = MulAut.conj c * (β : MulAut (adjointGroup Tag.D4 K))) :
    fieldPartFn α = sigmaOf β := by
  set c₁ := (decompOf α).1
  set β₁ := (decompOf α).2
  have h1 : α = MulAut.conj c₁ * (β₁ : MulAut (adjointGroup Tag.D4 K)) := decompOf_spec α
  have h2 : (β₁ : MulAut (adjointGroup Tag.D4 K)) =
      MulAut.conj (c₁⁻¹ * c) * (β : MulAut (adjointGroup Tag.D4 K)) := by
    have : MulAut.conj c₁ * (β₁ : MulAut (adjointGroup Tag.D4 K)) =
        MulAut.conj c * (β : MulAut (adjointGroup Tag.D4 K)) := h1.symm.trans h
    calc (β₁ : MulAut (adjointGroup Tag.D4 K))
        = (MulAut.conj c₁)⁻¹ * (MulAut.conj c₁ * (β₁ : MulAut (adjointGroup Tag.D4 K))) := by
          group
      _ = (MulAut.conj c₁)⁻¹ * (MulAut.conj c * (β : MulAut (adjointGroup Tag.D4 K))) := by
          rw [this]
      _ = MulAut.conj (c₁⁻¹ * c) * (β : MulAut (adjointGroup Tag.D4 K)) := by
          rw [map_mul, map_inv, mul_assoc]
  have hconj : MulAut.conj (c₁⁻¹ * c) ∈ StabU K := by
    have : MulAut.conj (c₁⁻¹ * c) = (β₁ : MulAut (adjointGroup Tag.D4 K)) *
        (β : MulAut (adjointGroup Tag.D4 K))⁻¹ := by
      rw [h2]; group
    rw [this]
    exact mul_mem β₁.2 (inv_mem β.2)
  have hx := mem_normalizer_of_conj_mem_StabU hconj
  have hβ₁ : β₁ = ⟨MulAut.conj (c₁⁻¹ * c), hconj⟩ * β := Subtype.ext h2
  show sigmaOf β₁ = sigmaOf β
  rw [hβ₁, sigmaOf_mul, sigmaOf_conj hx, one_mul]

@[expose] def fieldPart : MulAut (adjointGroup Tag.D4 K) →* (K ≃+* K) where
  toFun := fieldPartFn
  map_one' := by
    have := fieldPartFn_eq (α := (1 : MulAut (adjointGroup Tag.D4 K))) (c := 1) (β := 1)
      (by simp)
    rw [this, sigmaOf_one]
  map_mul' := by
    intro α α'
    set c := (decompOf α).1
    set β := (decompOf α).2
    set c' := (decompOf α').1
    set β' := (decompOf α').2
    have h1 : α = MulAut.conj c * (β : MulAut (adjointGroup Tag.D4 K)) := decompOf_spec α
    have h1' : α' = MulAut.conj c' * (β' : MulAut (adjointGroup Tag.D4 K)) := decompOf_spec α'
    have h : α * α' = MulAut.conj (c * (β : MulAut (adjointGroup Tag.D4 K)) c') *
        ((β * β' : StabU K) : MulAut (adjointGroup Tag.D4 K)) := by
      rw [h1, h1']
      ext x
      simp [MulAut.mul_apply, MulAut.conj_apply, mul_assoc]
    show fieldPartFn (α * α') = fieldPartFn α * fieldPartFn α'
    rw [fieldPartFn_eq h]
    exact sigmaOf_mul β β'

theorem fieldPart_apply (α : MulAut (adjointGroup Tag.D4 K)) : fieldPart α = fieldPartFn α := rfl

theorem fieldPart_of_mem_StabU {β : MulAut (adjointGroup Tag.D4 K)} (hβ : β ∈ StabU K) :
    fieldPart β = sigmaOf ⟨β, hβ⟩ := by
  refine fieldPartFn_eq (c := 1) ?_
  simp

theorem fieldPart_conj (g : adjointGroup Tag.D4 K) : fieldPart (MulAut.conj g) = 1 := by
  have := fieldPartFn_eq (α := MulAut.conj g) (c := g) (β := 1) (by simp)
  rw [fieldPart_apply, this, sigmaOf_one]

theorem fieldPart_eq_one_of_mem_commutator {η : MulAut (adjointGroup Tag.D4 K)}
    (hη : η ∈ commutator (MulAut (adjointGroup Tag.D4 K))) : fieldPart η = 1 := by
  haveI : IsCyclic (K ≃+* K) := ringAut_isCyclic
  letI : CommGroup (K ≃+* K) := IsCyclic.commGroup
  have h := Abelianization.commutator_subset_ker (fieldPart : MulAut (adjointGroup Tag.D4 K) →*
    (K ≃+* K)) hη
  exact h

end CFSG.HardMathSupport.Dickson.Sec6.I1431.FieldPart
