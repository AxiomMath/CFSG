module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4MaxEntry

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.RankThree.PartOne.CTP CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.ExcOuterLeOne CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

section EntryF2


section Criterion

variable {τ : Tag} {K : Type} [Field K]

private theorem d4F2_cartan_eq {z : RootModule τ K}
    (hz : ∀ (β : Fin τ.rank → ℤ) (hβ : IsRoot τ β), z (rootLabel hβ) = 0) :
    z = ∑ j : Fin τ.rank, z (Sum.inl j) • hVec τ K j := by
  classical
  ext a
  rcases a with j | ⟨β, hβ⟩
  · simp [hVec, Finsupp.finset_sum_apply, Finsupp.single_apply]
  · have h : z (Sum.inr ⟨β, hβ⟩) = 0 := hz β hβ
    simp [hVec, Finsupp.finset_sum_apply, Finsupp.single_apply, h]

private theorem d4F2_fix_of_coord (op : K → Module.End K (RootModule τ K)) (A : Fin τ.rank → K)
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) {z : RootModule τ K}
    (hdec : z = ∑ j : Fin τ.rank, z (Sum.inl j) • hVec τ K j)
    (hop : ∀ (c : K) (j : Fin τ.rank), op c (hVec τ K j) = hVec τ K j + (A j * c) • rootVec τ K β)
    (hw0 : (op 1 z - z) (rootLabel hβ) = 0) (c : K) : op c z = z := by
  have hsum : ∀ (t : Fin τ.rank → K) (c : K), op c (∑ j, t j • hVec τ K j) =
      (∑ j, t j • hVec τ K j) + (∑ j, t j * (A j * c)) • rootVec τ K β := by
    intro t c
    simp only [map_sum, map_smul, hop, smul_add, smul_smul, Finset.sum_add_distrib, Finset.sum_smul]
  have hopz : ∀ c : K, op c z = z + (∑ j, z (Sum.inl j) * (A j * c)) • rootVec τ K β := by
    intro c
    have h : op c (∑ j, z (Sum.inl j) • hVec τ K j) = (∑ j, z (Sum.inl j) • hVec τ K j) +
        (∑ j, z (Sum.inl j) * (A j * c)) • rootVec τ K β := hsum (fun j => z (Sum.inl j)) c
    rwa [← hdec] at h
  have hT : ∀ c : K, (∑ j, z (Sum.inl j) * (A j * c)) = (∑ j, z (Sum.inl j) * (A j * 1)) * c := by
    intro c
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hT1 : (∑ j, z (Sum.inl j) * (A j * 1)) = 0 := by
    have h1 : op 1 z - z = (∑ j, z (Sum.inl j) * (A j * 1)) • rootVec τ K β := by
      rw [hopz 1]
      abel
    rw [h1, rootVec_of_isRoot' hβ] at hw0
    simpa using hw0
  rw [hopz c, hT c, hT1, zero_mul, zero_smul, add_zero]

theorem d4F2_vanishSub_le_top {k : Subfield K} {R : Subgroup ↥(adjointGroup Tag.D4 K)}
    (hrat : ∀ γ : Fin Tag.D4.rank → ℤ, IsRoot Tag.D4 γ → ∀ c ∈ k,
      xPar (rootOperatorFamily Tag.D4) γ c ∈ R)
    {θ : Fin Tag.D4.rank → ℤ} (hθ : IsMaxHeightRoot Tag.D4 θ) :
    vanishSub R (negLabel hθ.1) ≤
      vanishSub (⊤ : Subgroup ↥(adjointGroup Tag.D4 K)) (negLabel hθ.1) := by
  intro z hz
  have hcoord : ∀ {w : RootModule Tag.D4 K}, w ∈ vanishSub R (negLabel hθ.1) →
      ∀ {β : Fin Tag.D4.rank → ℤ} (hβ : IsRoot Tag.D4 β), w (rootLabel hβ) = 0 :=
    fun hw _ hβ => vanishSub_rootCoord_sl d4SimplyLaced hrat hθ hw hβ
      ((d4SimplyLaced.norm_two _ hβ).trans (d4SimplyLaced.norm_two _ hθ.1).symm)
  have hdec := d4F2_cartan_eq fun _ hβ => hcoord hz hβ
  have hsub : ∀ {γ : Fin Tag.D4.rank → ℤ}, IsRoot Tag.D4 γ →
      endHom K (xPar (rootOperatorFamily Tag.D4) γ (1 : K)) z - z ∈
        vanishSub R (negLabel hθ.1) := by
    intro γ hγ
    refine Submodule.sub_mem _ (mem_vanishSub.2 fun r hr => ?_) hz
    rw [← Module.End.mul_apply, ← map_mul]
    exact mem_vanishSub.1 hz _ (R.mul_mem hr (hrat γ hγ 1 k.one_mem))
  have hxfix : ∀ (i : Fin Tag.D4.rank) (c : K), xOp Tag.D4 K i c z = z := by
    intro i c
    have hw := hsub (isRoot_single Tag.D4 i)
    rw [xPar_simple, endHom_eltElement, (rootOperatorFamily Tag.D4).elt_simple] at hw
    exact d4F2_fix_of_coord (xOp Tag.D4 K i) (fun j => ((Tag.D4.cartan j i).natAbs : K))
      (isRoot_single Tag.D4 i) hdec (fun c j => xOp_apply_hVec i j c)
      (hcoord hw (isRoot_single Tag.D4 i)) c
  have hyfix : ∀ (i : Fin Tag.D4.rank) (c : K), yOp Tag.D4 K i c z = z := by
    intro i c
    have hw := hsub (isRoot_neg_single Tag.D4 i)
    rw [xPar_neg_simple, endHom_eltElement, (rootOperatorFamily Tag.D4).elt_neg_simple] at hw
    exact d4F2_fix_of_coord (yOp Tag.D4 K i) (fun j => ((Tag.D4.cartan j i).natAbs : K))
      (isRoot_neg_single Tag.D4 i) hdec (fun c j => yOp_apply_hVec i j c)
      (hcoord hw (isRoot_neg_single Tag.D4 i)) c
  let Stab : Subgroup ↥(adjointGroup Tag.D4 K) :=
    { carrier := {g | endHom K g z = z}
      one_mem' := by
        show endHom K 1 z = z
        rw [map_one, Module.End.one_apply]
      mul_mem' := fun {g₁ g₂} (h1 : endHom K g₁ z = z) (h2 : endHom K g₂ z = z) => by
        show endHom K (g₁ * g₂) z = z
        rw [map_mul, Module.End.mul_apply, h2, h1]
      inv_mem' := fun {g} (h : endHom K g z = z) => by
        show endHom K g⁻¹ z = z
        conv_lhs => rw [← h]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have htop : Stab = ⊤ := by
    set S : Set (ModGL Tag.D4 K) := {g | ∃ (i : Fin Tag.D4.rank) (c : K),
      (g : Module.End K (RootModule Tag.D4 K)) = xOp Tag.D4 K i c ∨
        (g : Module.End K (RootModule Tag.D4 K)) = yOp Tag.D4 K i c}
    have hcl : Subgroup.closure (((↑) : ↥(adjointGroup Tag.D4 K) → ModGL Tag.D4 K) ⁻¹' S) = ⊤ :=
      Subgroup.closure_closure_coe_preimage
    rw [eq_top_iff, ← hcl, Subgroup.closure_le]
    rintro g ⟨i, c, hg | hg⟩
    · show endHom K g z = z
      rw [show endHom K g = xOp Tag.D4 K i c from hg]
      exact hxfix i c
    · show endHom K g z = z
      rw [show endHom K g = yOp Tag.D4 K i c from hg]
      exact hyfix i c
  refine mem_vanishSub.2 fun g _ => ?_
  have hg : g ∈ Stab := htop ▸ Subgroup.mem_top g
  rw [show endHom K g z = z from hg]
  simpa using mem_vanishSub.1 hz 1 R.one_mem

theorem d4F2_mem_subfieldGroup_of_entries [Finite K] (σ : K ≃+* K) (hK3 : 3 ≤ Nat.card K)
    {θ : Fin Tag.D4.rank → ℤ} (hθ : IsMaxHeightRoot Tag.D4 θ) (g : ↥(adjointGroup Tag.D4 K))
    (hall : ∀ r ∈ subfieldGroup Tag.D4 σ, ∀ r' ∈ subfieldGroup Tag.D4 σ,
      entry (r * g * r') (negLabel hθ.1) (rootLabel hθ.1) ∈ fixSubfield σ) :
    g ∈ subfieldGroup Tag.D4 σ := by
  set R := subfieldGroup Tag.D4 σ with hR
  have hrat : ∀ γ : Fin Tag.D4.rank → ℤ, IsRoot Tag.D4 γ → ∀ c ∈ fixSubfield σ,
      xPar (rootOperatorFamily Tag.D4) γ c ∈ R :=
    fun γ _ c hc => xPar_mem_subfieldGroup Tag.D4 σ γ hc
  set g₂ : ↥(adjointGroup Tag.D4 K) := entrywiseAdjointAut Tag.D4 σ g
  have hRfix : ∀ r ∈ R, entrywiseAdjointAut Tag.D4 σ r = r := fun r hr => mem_fixedSubgroup.1 hr
  have hent : ∀ r ∈ R, ∀ r' ∈ R, entry (r * g₂ * r') (negLabel hθ.1) (rootLabel hθ.1) =
      entry (r * g * r') (negLabel hθ.1) (rootLabel hθ.1) := by
    intro r hr r' hr'
    have e : r * g₂ * r' = entrywiseAdjointAut Tag.D4 σ (r * g * r') := by
      rw [map_mul, map_mul, hRfix r hr, hRfix r' hr']
    rw [e, entry_entrywiseAdjointAut]
    exact (mem_fixSubfield σ).1 (hall r hr r' hr')
  set Z := vanishSub R (negLabel hθ.1)
  have hDmem : ∀ r' ∈ R, (endHom K g₂ - endHom K g) (endHom K r' (rootVec Tag.D4 K θ)) ∈ Z := by
    intro r' hr'
    refine mem_vanishSub.2 fun r hr => ?_
    have hv : rootVec Tag.D4 K θ = Finsupp.single (rootLabel hθ.1) 1 := rootVec_of_isRoot' hθ.1
    have h1 := hent r hr r' hr'
    unfold entry at h1
    rw [hv]
    simp only [LinearMap.sub_apply, map_sub, Finsupp.sub_apply, ← Module.End.mul_apply,
      ← map_mul] at h1 ⊢
    rw [sub_eq_zero]
    simpa [mul_assoc, Module.End.mul_apply] using h1
  have hle : Submodule.span K {x | ∃ r ∈ R, x = endHom K r (rootVec Tag.D4 K θ)} ≤
      Z.comap (endHom K g₂ - endHom K g) := by
    refine Submodule.span_le.2 ?_
    rintro x ⟨r', hr', rfl⟩
    exact hDmem r' hr'
  rw [span_orbit_eq_top_sl d4SimplyLaced hrat hθ] at hle
  have hx : ∀ v : RootModule Tag.D4 K, endHom K (g₂ * g⁻¹) v - v ∈
      vanishSub (⊤ : Subgroup ↥(adjointGroup Tag.D4 K)) (negLabel hθ.1) := by
    intro v
    have h1 : (endHom K g₂ - endHom K g) (endHom K g⁻¹ v) ∈ Z := hle Submodule.mem_top
    have e1 : endHom K g (endHom K g⁻¹ v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [LinearMap.sub_apply, e1] at h1
    rw [map_mul, Module.End.mul_apply]
    exact d4F2_vanishSub_le_top hrat hθ h1
  have h3 : 3 ≤ Nat.card (⊤ : Subfield K) := by
    rw [Nat.card_congr (Subfield.topEquiv : (⊤ : Subfield K) ≃+* K).toEquiv]
    exact hK3
  have h1 := eq_one_of_sub_mem_vanishSub_sl d4SimplyLaced h3
    (R := (⊤ : Subgroup ↥(adjointGroup Tag.D4 K))) (fun _ _ _ _ => Subgroup.mem_top _) hθ
    (g₂ * g⁻¹) hx
  rw [hR, subfieldGroup, mem_fixedSubgroup]
  exact mul_inv_eq_one.1 h1

end Criterion

theorem d4F2_exists_bad_entry {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (hK3 : 3 ≤ Nat.card K) {θ : Fin Tag.D4.rank → ℤ}
    (hθ : IsMaxHeightRoot Tag.D4 θ) (g : ↥(adjointGroup Tag.D4 K)) (hg : g ∉ subfieldGroup Tag.D4 σ) :
    ∃ r ∈ subfieldGroup Tag.D4 σ, ∃ r' ∈ subfieldGroup Tag.D4 σ,
      entry (r * g * r') (negLabel hθ.1) (rootLabel hθ.1) ∉ fixSubfield σ := by
  by_contra h
  push Not at h
  exact hg (d4F2_mem_subfieldGroup_of_entries σ hK3 hθ g h)

end EntryF2

end CFSG.LieType.SeitzGeneration.ExcWideThree
