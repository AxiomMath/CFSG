module

public import CFSG.LieType.Chevalley.GraphFixedRootNormal
public import CFSG.LieType.Chevalley.RankOneBruhat

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley

section Commute

variable {t : TwistTag} {K : Type} [Field K]

theorem commute_torusElt_xUnit_of_mem_orbit
    {a : Fin t.foldedTag.rank} {i j : Fin t.tag.rank}
    (hi : i ∈ t.orbit a) (hj : j ∈ t.orbit a) (hij : i ≠ j) (u : Kˣ) (c : K) :
    Commute (torusElt t.tag K i u) (xUnit t.tag K j c) := by
  have h := (simple_torus_root_conjugation t.tag K i j u c).1
  rw [t.cartan_eq_zero_of_mem_orbit hi hj hij, zpow_zero, Units.val_one, one_mul] at h
  exact mul_inv_eq_iff_eq_mul.1 h

theorem commute_torusElt_yUnit_of_mem_orbit
    {a : Fin t.foldedTag.rank} {i j : Fin t.tag.rank}
    (hi : i ∈ t.orbit a) (hj : j ∈ t.orbit a) (hij : i ≠ j) (u : Kˣ) (c : K) :
    Commute (torusElt t.tag K i u) (yUnit t.tag K j c) := by
  have h := (simple_torus_root_conjugation t.tag K i j u c).2
  rw [t.cartan_eq_zero_of_mem_orbit hi hj hij, neg_zero, zpow_zero, Units.val_one, one_mul] at h
  exact mul_inv_eq_iff_eq_mul.1 h

end Commute

section Identity

variable (t : TwistTag) {K : Type} [Field K] (σ : K →+* K)

theorem orbitParam_inv {a : Fin t.foldedTag.rank} (c : K) {j : Fin t.tag.rank}
    (hj : j ∈ t.orbit a) : orbitParam t σ a c⁻¹ j = (orbitParam t σ a c j)⁻¹ := by
  obtain ⟨k, hk, rfl⟩ := t.exists_eq_perm_pow_orbitMin hj
  rw [orbitParam_pow t σ _ hk, orbitParam_pow t σ _ hk, map_inv₀]

theorem orbitParam_neg {a : Fin t.foldedTag.rank} (c : K) {j : Fin t.tag.rank}
    (hj : j ∈ t.orbit a) : orbitParam t σ a (-c) j = -orbitParam t σ a c j := by
  obtain ⟨k, hk, rfl⟩ := t.exists_eq_perm_pow_orbitMin hj
  rw [orbitParam_pow t σ _ hk, orbitParam_pow t σ _ hk, map_neg]

theorem orbitH_mem_graphFixedRootTorus
    (a : Fin t.foldedTag.rank) (u : (orbitField t K σ a)ˣ) :
    (orbitH t K σ a u : ModGL t.tag K) ∈ graphFixedRootTorus t K σ := by
  have hC := orbitH_mem_graphFixedRootGroup t σ a u
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨?_, graphFixedRootGroup_le t K σ hC⟩, hC⟩
  rw [coe_orbitH_eq]
  exact Subgroup.list_prod_mem _ fun x hx => by
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
    exact torusElt_mem_torusGroup j _

theorem canonicalRep_orbitReflection_mul_orbitX
    (a : Fin t.foldedTag.rank)
    (u : (orbitField t K σ a)ˣ) :
    canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) *
        (orbitX t K σ a u : ModGL t.tag K) =
      (orbitX t K σ a (-((u⁻¹ : (orbitField t K σ a)ˣ) : orbitField t K σ a)) :
          ModGL t.tag K) * (orbitH t K σ a (-u⁻¹) : ModGL t.tag K) *
        (orbitY t K σ a ((u⁻¹ : (orbitField t K σ a)ˣ) : orbitField t K σ a) :
          ModGL t.tag K) := by
  have hω := t.nodup_orbitWord a
  have hmem : ∀ j ∈ t.orbitWord a, j ∈ t.orbit a := fun j hj => (t.mem_orbitWord).1 hj
  set U := orbitUnitParam t σ a (orbitFieldUnit t σ u) with hU
  have hUj : ∀ j ∈ t.orbit a, (U j : K) = orbitParam t σ a ((u : orbitField t K σ a) : K) j :=
    fun j hj => coe_orbitUnitParam t σ _ hj
  have hinv : ∀ j ∈ t.orbit a, (((U j)⁻¹ : Kˣ) : K) =
      orbitParam t σ a (((u⁻¹ : (orbitField t K σ a)ˣ) : orbitField t K σ a) : K) j := by
    intro j hj
    rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, Subfield.coe_inv,
      orbitParam_inv t σ _ hj, hUj j hj]
  have hX : (orbitX t K σ a u : ModGL t.tag K) =
      ((t.orbitWord a).map fun j => xUnit t.tag K j (U j)).prod := by
    rw [coe_orbitX_eq_orbitXProd]
    exact orbitXProd_congr t fun j hj => (hUj j hj).symm
  have hX' : (orbitX t K σ a (-((u⁻¹ : (orbitField t K σ a)ˣ) : orbitField t K σ a)) :
      ModGL t.tag K) =
      ((t.orbitWord a).map fun j => xUnit t.tag K j (-(((U j)⁻¹ : Kˣ) : K))).prod := by
    rw [coe_orbitX_eq_orbitXProd]
    refine orbitXProd_congr t fun j hj => ?_
    rw [Subfield.coe_neg, orbitParam_neg t σ _ hj, hinv j hj]
  have hH : (orbitH t K σ a (-u⁻¹) : ModGL t.tag K) =
      ((t.orbitWord a).map fun j => torusElt t.tag K j (-(U j)⁻¹)).prod := by
    rw [coe_orbitH_eq]
    refine congrArg List.prod (List.map_congr_left fun j hj => congrArg _ (Units.ext ?_))
    rw [coe_orbitUnitParam t σ _ (hmem j hj), coe_orbitFieldUnit, Units.val_neg, Units.val_neg,
      Subfield.coe_neg, orbitParam_neg t σ _ (hmem j hj), hinv j (hmem j hj)]
  have hY : (orbitY t K σ a ((u⁻¹ : (orbitField t K σ a)ˣ) : orbitField t K σ a) :
      ModGL t.tag K) =
      ((t.orbitWord a).map fun j => yUnit t.tag K j (((U j)⁻¹ : Kˣ) : K)).prod := by
    rw [coe_orbitY_eq_orbitYProd, orbitYProd]
    exact congrArg List.prod (List.map_congr_left fun j hj => by rw [hinv j (hmem j hj)])
  rw [canonicalRep_orbitReflection, hX, hX', hH, hY,
    ← list_prod_map_mul_of_commute_of_ne hω (fun j => weylElt t.tag K j 1)
      (fun j => xUnit t.tag K j (U j)) (fun x hx y hy hxy =>
        (commute_weylElt_xUnit' K (hmem y hy) (hmem x hx) (Ne.symm hxy) 1 _).symm),
    ← list_prod_map_mul_of_commute_of_ne hω (fun j => xUnit t.tag K j (-(((U j)⁻¹ : Kˣ) : K)))
      (fun j => torusElt t.tag K j (-(U j)⁻¹)) (fun x hx y hy hxy =>
        commute_torusElt_xUnit_of_mem_orbit (hmem x hx) (hmem y hy) hxy _ _),
    ← list_prod_map_mul_of_commute_of_ne hω
      (fun j => xUnit t.tag K j (-(((U j)⁻¹ : Kˣ) : K)) * torusElt t.tag K j (-(U j)⁻¹))
      (fun j => yUnit t.tag K j (((U j)⁻¹ : Kˣ) : K)) (fun x hx y hy hxy =>
        ((commute_xUnit_yUnit K (hmem y hy) (hmem x hx) (Ne.symm hxy) _ _).symm.mul_right
          (commute_torusElt_yUnit_of_mem_orbit (hmem y hy) (hmem x hx) (Ne.symm hxy) _ _).symm))]
  exact congrArg List.prod (List.map_congr_left fun j _ => weylElt_one_mul_xUnit j (U j))

end Identity

theorem fixed_simple_rank_one_Bruhat_identity
    (t : TwistTag) (K : Type) [Field K]
    (σ : K →+* K) :
    (∀ a, (orbitN t K σ a 1 : ModGL t.tag K) =
      canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a)) ∧
    ∀ a (u : (orbitField t K σ a)ˣ),
      (orbitH t K σ a u : ModGL t.tag K) ∈ graphFixedRootTorus t K σ ∧
      canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) *
          (orbitX t K σ a u : ModGL t.tag K) =
        (orbitX t K σ a (-((u⁻¹ : (orbitField t K σ a)ˣ) : orbitField t K σ a)) :
            ModGL t.tag K) * (orbitH t K σ a (-u⁻¹) : ModGL t.tag K) *
          (orbitY t K σ a ((u⁻¹ : (orbitField t K σ a)ˣ) : orbitField t K σ a) :
            ModGL t.tag K) ∧
      ∃ b ∈ graphFixedRootBorel t K σ,
        canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) *
            (orbitX t K σ a u : ModGL t.tag K) =
          b * (orbitY t K σ a ((u⁻¹ : (orbitField t K σ a)ˣ) : orbitField t K σ a) :
            ModGL t.tag K) := by
  refine ⟨fun a => (canonicalRep_orbitReflection_eq_orbitN t σ a).symm, fun a u =>
    ⟨orbitH_mem_graphFixedRootTorus t σ a u, canonicalRep_orbitReflection_mul_orbitX t σ a u,
      _, ?_, canonicalRep_orbitReflection_mul_orbitX t σ a u⟩⟩
  have hx := orbitX_mem_graphFixedPosUnipotent t σ a
    (-((u⁻¹ : (orbitField t K σ a)ˣ) : orbitField t K σ a))
  obtain ⟨hhH, hhC⟩ := Subgroup.mem_inf.1 (orbitH_mem_graphFixedRootTorus t σ a (-u⁻¹))
  exact Subgroup.mem_inf.2 ⟨mul_mem (graphFixedPosUnipotent_le_graphFixedBorel hx)
    (graphFixedTorus_le_graphFixedBorel hhH),
    mul_mem (graphFixedPosUnipotent_le_graphFixedRootGroup t K σ hx) hhC⟩

end CFSG.LieType.Chevalley
