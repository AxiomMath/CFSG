module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResTLPsl

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG.Open CFSG.Open.StatedAPI
open scoped commutatorElement

set_option linter.unusedSectionVars false

theorem excOth_psl2_pigeon {F : Type} [Field F] {K : Type*} [Group K]
    {g : StatedProj (StatedSL 2 F)} (hg : g ≠ 1) (f : K →* StatedProj (StatedSL 2 F))
    (h : ∀ a, Commute (f a) g) :
    ∃ K₀ : Subgroup K, (∀ u v w : K, u⁻¹ * v ∈ K₀ ∨ u⁻¹ * w ∈ K₀ ∨ v⁻¹ * w ∈ K₀) ∧
      ∀ a ∈ K₀, ∀ b ∈ K₀, Commute (f a) (f b) := by
  obtain ⟨ĝ, rfl⟩ := QuotientGroup.mk'_surjective ((StatedScalars (Fin 2) F).subgroupOf
    (StatedSL 2 F)) g
  have hĝ : ĝ ∉ (StatedScalars (Fin 2) F).subgroupOf (StatedSL 2 F) := fun hh =>
    hg ((QuotientGroup.eq_one_iff ĝ).2 hh)
  have hnon := excTL_not_scalar hĝ
  obtain ⟨l, ε, hl, hε, hZ⟩ := excTL_exists_comm_hom
    ((StatedScalars (Fin 2) F).subgroupOf (StatedSL 2 F))
    (statedScalars_subgroupOf_le_center _) f ĝ h
  refine ⟨ε.ker, ?_, ?_⟩
  · intro u v w
    rcases excTL_scalar_three (hZ u) (hZ v) (hZ w) with huv | huw | hvw
    · left
      rw [MonoidHom.mem_ker, map_mul, map_inv, huv, inv_mul_cancel]
    · right; left
      rw [MonoidHom.mem_ker, map_mul, map_inv, huw, inv_mul_cancel]
    · right; right
      rw [MonoidHom.mem_ker, map_mul, map_inv, hvw, inv_mul_cancel]
  · intro a ha b hb
    rw [MonoidHom.mem_ker] at ha hb
    rw [← hl a, ← hl b]
    refine Commute.map ?_ _
    have ca : l a * ĝ = ĝ * l a := by
      have := hε a
      rw [ha] at this
      exact commutatorElement_eq_one_iff_mul_comm.1 this.symm
    have cb : l b * ĝ = ĝ * l b := by
      have := hε b
      rw [hb] at this
      exact commutatorElement_eq_one_iff_mul_comm.1 this.symm
    have toMat : ∀ x y : ↥(StatedSL 2 F), x * y = y * x →
        ((x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * ((y : GL (Fin 2) F) : Matrix _ _ F) =
          ((y : GL (Fin 2) F) : Matrix _ _ F) * ((x : GL (Fin 2) F) : Matrix _ _ F) := by
      intro x y hxy
      have := congrArg (fun t : ↥(StatedSL 2 F) => ((t : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))
        hxy
      simpa using this
    have hm := excTL_commute_of_commute_nonscalar hnon (toMat _ _ ca) (toMat _ _ cb)
    exact Subtype.ext (Units.ext hm)

theorem excOth_index_two {G : Type*} [Group G] {F : Type} [Field F]
    (φ : (G ⧸ Subgroup.center G) ≃* StatedProj (StatedSL 2 F)) {K : Type*} [Group K]
    (k : K →* G) (c : G) (hc : c ∉ Subgroup.center G) (hk : ∀ a, Commute (k a) c) :
    ∃ K₀ : Subgroup K, (∀ u v w : K, u⁻¹ * v ∈ K₀ ∨ u⁻¹ * w ∈ K₀ ∨ v⁻¹ * w ∈ K₀) ∧
      ∀ a ∈ K₀, ∀ b ∈ K₀, ⁅k a, k b⁆ ∈ Subgroup.center G := by
  have hg : φ (QuotientGroup.mk' (Subgroup.center G) c) ≠ 1 := fun h => hc
    ((QuotientGroup.eq_one_iff c).1 (φ.injective (h.trans (map_one φ).symm)))
  obtain ⟨K₀, hK₀, hcomm⟩ := excOth_psl2_pigeon hg
    ((φ : (G ⧸ Subgroup.center G) →* _).comp ((QuotientGroup.mk' (Subgroup.center G)).comp k))
    (fun a => ((hk a).map (QuotientGroup.mk' (Subgroup.center G))).map φ.toMonoidHom)
  refine ⟨K₀, hK₀, fun a ha b hb => ?_⟩
  have hab := hcomm a ha b hb
  rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement]
  refine commutatorElement_eq_one_iff_mul_comm.2 (φ.injective ?_)
  simpa using hab.eq

end CFSG.HardMathSupport.Dickson.Sec6.I1431
