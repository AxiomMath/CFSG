module

public import CFSG.LieType.Chevalley.EvenCartanRootDiagonals

public noncomputable section

namespace CFSG.ComponentClassification.Foote5.OddLieCore.Exc

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Pointwise

variable {τ : Tag}

theorem det_transpose_cartan_eq_one (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E8) :
    τ.cartan.transpose.det = 1 := by
  rw [Matrix.det_transpose]
  rcases hτ with rfl | rfl | rfl
  · exact det_cartan_G2
  · exact det_cartan_F4
  · exact det_cartan_E8

theorem rootDiagUnit_mem_torusGroup_of_det_one
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E8) {K : Type} [Field K]
    (a : Fin τ.rank → Kˣ) : rootDiagUnit τ a ∈ torusGroup τ K := by
  rw [rootDiagUnit_eq_list_prod_torusElt_adjugate (u := a) fun i => by
    rw [det_transpose_cartan_eq_one hτ, zpow_one]]
  exact list_prod_torusElt_mem_torusGroup _

theorem fixed_torusGroup_eq_map_of_det_one
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E8) {K : Type} [Field K] [Finite K] (σ : K ≃+* K) :
    torusGroup τ K ⊓ (Units.map (entrywiseHom σ.toRingHom)).eqLocus (MonoidHom.id _) =
      (torusGroup τ (fixSubfield σ)).map (baseChangeGL (fixSubfield σ).subtype) := by
  set k := fixSubfield σ
  set ι := k.subtype
  have hn := det_transpose_cartan_eq_one hτ
  refine le_antisymm ?_ ?_
  · rintro h ⟨hh, hfix⟩
    obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
    have hσa : ∀ i, σ (a i : K) = a i := by
      have hF : Units.map (entrywiseHom σ.toRingHom) (rootDiagUnit τ a) = rootDiagUnit τ a := hfix
      have h0 : Units.map (entrywiseHom σ.toRingHom) (rootDiagUnit τ a) =
          rootDiagUnit τ (fun i => Units.map σ.toRingHom.toMonoidHom (a i)) :=
        Units.ext (entrywise_rootDiag σ.toRingHom a)
      have h1 := rootDiagUnit_injective (h0.symm.trans hF)
      intro i
      exact congrArg Units.val (congrFun h1 i)
    set a' : Fin τ.rank → kˣ := fun i =>
      Units.mk0 ⟨a i, hσa i⟩ fun h => (a i).ne_zero (congrArg Subtype.val h)
    have ha' : ∀ i, Units.map ι.toMonoidHom (a' i) = a i := fun i => Units.ext rfl
    refine ⟨((List.finRange τ.rank).map fun j =>
      torusElt τ k j (∏ i, a' i ^ τ.cartan.transpose.adjugate j i)).prod,
      list_prod_torusElt_mem_torusGroup _, ?_⟩
    rw [map_list_prod, List.map_map]
    rw [rootDiagUnit_eq_list_prod_torusElt_adjugate (u := fun i => Units.map ι.toMonoidHom (a' i))
      fun i => by rw [hn, zpow_one, ha']]
    refine congrArg List.prod (List.map_congr_left fun j _ => ?_)
    rw [Function.comp_apply, baseChangeGL_torusElt, map_prod]
    simp only [map_zpow]
  · have hle : torusGroup τ k ≤ (torusGroup τ K).comap (baseChangeGL ι) := by
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨⟨i, s⟩, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, baseChangeGL_torusElt]
      exact torusElt_mem_torusGroup i _
    rintro _ ⟨g, hg, rfl⟩
    refine ⟨hle hg, ?_⟩
    change baseChangeGL σ.toRingHom (baseChangeGL ι g) = baseChangeGL ι g
    rw [baseChangeGL_baseChangeGL,
      show σ.toRingHom.comp ι = ι from RingHom.ext fun c => (mem_fixSubfield σ).1 c.2]

theorem entrywiseFixedGroup_eq_fixedFieldImage_of_det_one
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E8) {K : Type} [Field K] [Finite K] (σ : K ≃+* K) :
    entrywiseFixedGroup τ σ = fixedFieldImage τ σ := by
  obtain ⟨-, -, -, hJΓ, hprod, -, -⟩ := Chevalley_coordinate_field_fixed_normal_subgroup τ K σ
  refine le_antisymm (fun g hg => ?_) hJΓ
  have hg' : g ∈ (entrywiseFixedTorus τ σ : Set (ModGL τ K)) *
      (fixedFieldImage τ σ : Set (ModGL τ K)) := by
    rw [← hprod]
    exact hg
  obtain ⟨h, hh, j, hj, rfl⟩ := Set.mem_mul.1 hg'
  refine mul_mem ?_ hj
  have hh' : h ∈ torusGroup τ K ⊓ (Units.map (entrywiseHom σ.toRingHom)).eqLocus
      (MonoidHom.id _) :=
    mem_inf.2 ⟨(mem_inf.1 hh).1, (mem_inf.1 (mem_inf.1 hh).2).2⟩
  rw [fixed_torusGroup_eq_map_of_det_one hτ σ] at hh'
  obtain ⟨t, ht, rfl⟩ := hh'
  have hTG : torusGroup τ (fixSubfield σ) ≤ adjointGroup τ (fixSubfield σ) :=
    (Subgroup.closure_le _).2 fun _ ⟨q, hq⟩ => hq ▸ torusElt_mem_adjointGroup q.1 q.2
  exact ⟨t, hTG ht, rfl⟩

end CFSG.ComponentClassification.Foote5.OddLieCore.Exc
