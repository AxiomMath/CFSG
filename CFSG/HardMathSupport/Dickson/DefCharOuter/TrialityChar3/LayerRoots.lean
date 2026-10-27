module

public import CFSG.HardMathSupport.Lang.E27Lie.TrialityThreeLayers
public import CFSG.LieType.Chevalley.OddTrialityAutomorphismNormalForm

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Lang.Triality CFSG.HardMathSupport.Lang.E27Lie

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3


section Delta0

variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K)

theorem cocycleData_delta0 :
    CocycleData (fieldActor (t := TwistTag.D4) σ σ) (layerN σ) (maxHeight TwistTag.D4.tag).toNat
      (layerPhi σ) (layerTau σ)
      (fun k => Nat.card {a : LayerCoord (K := K) k // a ∈ (layerPhi σ k).range ∧
        a * layerTau σ k a * layerTau σ k (layerTau σ k a) = 1}) := by
  have h := cocycleData_layers σ (u := 1) (Subgroup.one_mem _)
    (fun k => Nat.card {a : LayerCoord (K := K) k // a ∈ (layerPhi σ k).range ∧
      a * layerTau σ k a * layerTau σ k (layerTau σ k a) = 1}) (fun k _ => le_rfl)
  have hβ : betaAut σ 1 = fieldActor (t := TwistTag.D4) σ σ := by
    unfold betaAut
    rw [map_one, one_mul]
  rw [hβ] at h
  exact h

end Delta0

abbrev rootB : Fin TwistTag.D4.tag.rank → ℤ := ![0, 0, 1, 0]
abbrev rootC : Fin TwistTag.D4.tag.rank → ℤ := ![1, 1, 1, 1]
abbrev rootD : Fin TwistTag.D4.tag.rank → ℤ := ![1, 1, 2, 1]

theorem isRoot_rootB : IsRoot TwistTag.D4.tag rootB :=
  mem_rootFinset.1 (by decide +kernel)
theorem isRoot_rootC : IsRoot TwistTag.D4.tag rootC :=
  mem_rootFinset.1 (by decide +kernel)
theorem isRoot_rootD : IsRoot TwistTag.D4.tag rootD :=
  mem_rootFinset.1 (by decide +kernel)
theorem height_rootB : height rootB = 1 := by decide
theorem height_rootC : height rootC = 4 := by decide
theorem height_rootD : height rootD = 5 := by decide

private theorem diagramMap_conj_pinnedX_fixed {K : Type} [Field K]
    {β : Fin TwistTag.D4.tag.rank → ℤ}
    (hβ : IsRoot TwistTag.D4.tag β) (hfix : permLattice TwistTag.D4.perm β = β) (c : K) :
    diagramMap TwistTag.D4 K * pinnedX TwistTag.D4.tag K β c * (diagramMap TwistTag.D4 K)⁻¹ =
      pinnedX TwistTag.D4.tag K β c := by
  obtain ⟨ε, hε, hP⟩ := diagramMap_conj_pinnedX (K := K) TwistTag.D4 hβ
  rw [hfix] at hP
  have hP3 : diagramMap TwistTag.D4 K ^ 3 = 1 := diagramMap_pow_order TwistTag.D4 K
  have e : ∀ k : ℕ, ∀ d : K, diagramMap TwistTag.D4 K ^ k * pinnedX TwistTag.D4.tag K β d *
      (diagramMap TwistTag.D4 K ^ k)⁻¹ = pinnedX TwistTag.D4.tag K β (ε ^ k * d) := by
    intro k d
    induction k generalizing d with
    | zero => simp
    | succ k ih =>
      have hstep : diagramMap TwistTag.D4 K ^ (k + 1) * pinnedX TwistTag.D4.tag K β d *
          (diagramMap TwistTag.D4 K ^ (k + 1))⁻¹ =
          diagramMap TwistTag.D4 K * (diagramMap TwistTag.D4 K ^ k * pinnedX TwistTag.D4.tag K β d *
            (diagramMap TwistTag.D4 K ^ k)⁻¹) * (diagramMap TwistTag.D4 K)⁻¹ := by
        rw [pow_succ', mul_inv_rev]
        group
      rw [hstep, ih, hP]
      congr 1
      ring
  have h1 := e 3 1
  simp only [hP3, inv_one, one_mul, mul_one] at h1
  have h2 := pinnedX_injective TwistTag.D4.tag K β h1
  have h3 : ε ^ 3 = ε := by linear_combination ε * hε
  have hε1 : ε = 1 := by
    rw [h3] at h2
    exact h2.symm
  rw [hP, hε1, one_mul]

variable {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] [CharP K 3]
  (hK : Nat.card K = (3 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (3 ^ f))
include hf hK hσ

theorem twistHom_pinnedX_of_fixedRoot {γ : Fin TwistTag.D4.tag.rank → ℤ}
    (hγ : IsRoot TwistTag.D4.tag γ) (hρ : permLattice TwistTag.D4.perm γ = γ) (c : K) :
    twistHom TwistTag.D4 K σ.toRingHom (pinnedX TwistTag.D4.tag K γ c) =
      pinnedX TwistTag.D4.tag K γ (σ c) := by
  have h1 : twistHom TwistTag.D4 K σ.toRingHom (pinnedX TwistTag.D4.tag K γ c) =
      diagramMap TwistTag.D4 K * Units.map (entrywiseHom σ.toRingHom)
        (pinnedX TwistTag.D4.tag K γ c) * (diagramMap TwistTag.D4 K)⁻¹ := rfl
  rw [h1, show Units.map (entrywiseHom σ.toRingHom) (pinnedX TwistTag.D4.tag K γ c) =
    pinnedX TwistTag.D4.tag K γ (σ c) from Units.ext (entrywise_pinnedX σ.toRingHom γ c)]
  exact diagramMap_conj_pinnedX_fixed hγ hρ (σ c)

theorem pinnedX_mem_graphFixedPosUnipotent {γ : Fin TwistTag.D4.tag.rank → ℤ}
    (hγ : γ = rootB ∨ γ = rootC ∨ γ = rootD) {c : K} (hc : σ c = c) :
    pinnedX TwistTag.D4.tag K γ c ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom := by
  have hroot : IsRoot TwistTag.D4.tag γ ∧ 0 < height γ ∧ permLattice TwistTag.D4.perm γ = γ := by
    rcases hγ with rfl | rfl | rfl
    · exact ⟨isRoot_rootB, by rw [height_rootB]; norm_num, by decide⟩
    · exact ⟨isRoot_rootC, by rw [height_rootC]; norm_num, by decide⟩
    · exact ⟨isRoot_rootD, by rw [height_rootD]; norm_num, by decide⟩
  obtain ⟨hr, hp, hρ⟩ := hroot
  refine Subgroup.mem_inf.2 ⟨pinnedX_mem_rootSpan
    (S := {α | IsRoot TwistTag.D4.tag α ∧ 0 < height α}) ⟨hr, hp⟩ c, ?_⟩
  refine (mem_twistedFixedGroup_iff_twistHom _ _ _).2 ⟨pinnedX_mem_adjointGroup γ c, ?_⟩
  rw [twistHom_pinnedX_of_fixedRoot hf hK σ hσ hr hρ c, hc]

@[expose] noncomputable def longElt {γ : Fin TwistTag.D4.tag.rank → ℤ}
    (hγ : γ = rootB ∨ γ = rootC ∨ γ = rootD) (c : K) (hc : σ c = c) :
    graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
  ⟨pinnedX TwistTag.D4.tag K γ c,
    le_sup_left (a := graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom)
      (pinnedX_mem_graphFixedPosUnipotent hf hK σ hσ hγ hc)⟩

theorem coe_longElt {γ : Fin TwistTag.D4.tag.rank → ℤ} (hγ : γ = rootB ∨ γ = rootC ∨ γ = rootD)
    (c : K) (hc : σ c = c) :
    ((longElt hf hK σ hσ hγ c hc : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
      ModGL TwistTag.D4.tag K) = pinnedX TwistTag.D4.tag K γ c := rfl

theorem longElt_zero {γ : Fin TwistTag.D4.tag.rank → ℤ} (hγ : γ = rootB ∨ γ = rootC ∨ γ = rootD)
    (h0 : σ 0 = 0) : longElt hf hK σ hσ hγ 0 h0 = 1 := by
  apply Subtype.ext
  exact pinnedX_zero TwistTag.D4.tag K γ

theorem cocycleProd_eq_one_of_pow_three (u : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hu : (MulAut.conj u * fieldActor (t := TwistTag.D4) σ σ) ^ 3 = 1) :
    cocycleProd (fieldActor (t := TwistTag.D4) σ σ) u = 1 := by
  have hσ3 : σ ^ 3 = 1 := by
    ext c
    exact ringEquiv_cube_apply_eq hK hσ c
  have hδ3 : fieldActor (t := TwistTag.D4) σ σ ^ 3 = 1 := by
    have h2 : (CFSG.LieType.Chevalley.fieldActorHom (t := TwistTag.D4) σ) (σ ^ 3) = 1 := by
      rw [hσ3, map_one]
    rw [map_pow] at h2
    exact h2
  set δ := fieldActor (t := TwistTag.D4) σ σ with hδ
  have hpow : (MulAut.conj u * δ) ^ 3 = MulAut.conj (cocycleProd δ u) * δ ^ 3 := by
    ext x
    simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.conj_apply, map_mul,
      map_inv, cocycleProd]
  have hc1 : MulAut.conj (cocycleProd δ u) = 1 := by
    rw [hpow, hδ3, mul_one] at hu
    exact hu
  have hmem : cocycleProd δ u ∈ Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h := congrArg (fun φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) => φ g) hc1
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h.symm
  have hbot := center_graphFixedRootGroup_eq_bot (t := TwistTag.D4) (K := K)
    (σ := σ.toRingHom) σ.surjective
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hmem

theorem cocycleProd_eq_one_of_fixed_cube (m : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hm : fieldActor (t := TwistTag.D4) σ σ m = m) (hm3 : m ^ 3 = 1) :
    cocycleProd (fieldActor (t := TwistTag.D4) σ σ) m = 1 := by
  simp only [cocycleProd, hm]
  rw [← pow_three']
  exact hm3

theorem conj_mul_twisted (δ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (u w : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
    MulAut.conj w⁻¹ * (MulAut.conj u * δ) * (MulAut.conj w⁻¹)⁻¹ =
      MulAut.conj (w⁻¹ * u * δ w) * δ := by
  rw [← map_inv MulAut.conj, inv_inv]
  ext x
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, inv_inv]

end CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3
