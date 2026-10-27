module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Fi23Lift
public import CFSG.Sporadic.FischerOddCore.Fi24Cent

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.YS14

open CFSG.Sporadic.Fi24 (R J JR jR tR)
open CFSG.Sporadic.FischerOddCore (fi24D fi24U2 fi24U3 fi23ToR fi23ToR_apply fi24_involution_class)

theorem map_centralizer_singleton_eq_inf_range {T M : Type*} [Group T] [Group M] {f : T →* M}
    (hf : Function.Injective f) (t : T) :
    (Subgroup.centralizer ({t} : Set T)).map f =
      Subgroup.centralizer ({f t} : Set M) ⊓ f.range := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    MonoidHom.mem_range]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨by rw [← map_mul, hx, map_mul], x, rfl⟩
  · rintro ⟨hy, x, rfl⟩
    refine ⟨x, hf ?_, rfl⟩
    rw [map_mul, map_mul, hy]

theorem map_conj_centralizer_inf {G : Type*} [Group G] {N : Subgroup G} (hN : N.Normal)
    (c u : G) :
    (Subgroup.centralizer ({u} : Set G) ⊓ N).map (MulAut.conj c).toMonoidHom =
      Subgroup.centralizer ({c * u * c⁻¹} : Set G) ⊓ N := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨x, ⟨hx, hxN⟩, rfl⟩
    refine ⟨?_, hN.conj_mem x hxN c⟩
    calc c * x * c⁻¹ * (c * u * c⁻¹) = c * (x * u) * c⁻¹ := by group
      _ = c * (u * x) * c⁻¹ := by rw [hx]
      _ = c * u * c⁻¹ * (c * x * c⁻¹) := by group
  · rintro ⟨hy, hyN⟩
    refine ⟨c⁻¹ * y * c, ⟨?_, ?_⟩, by group⟩
    · calc c⁻¹ * y * c * u = c⁻¹ * (y * (c * u * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * u * c⁻¹) * y) * c := by rw [hy]
        _ = u * (c⁻¹ * y * c) := by group
    · have h := hN.conj_mem y hyN c⁻¹
      rwa [inv_inv] at h

theorem fourClassesLarge_conj_inf {G : Type*} [Group G] {N : Subgroup G} (hN : N.Normal)
    {c u v : G} (hv : c * u * c⁻¹ = v)
    (h : CFSG.ComponentClassification.M12Cover.FourClassesLarge
      ↥(Subgroup.centralizer ({u} : Set G) ⊓ N)) :
    CFSG.ComponentClassification.M12Cover.FourClassesLarge
      ↥(Subgroup.centralizer ({v} : Set G) ⊓ N) := by
  subst hv
  exact CFSG.ComponentClassification.M12Cover.FourClassesLarge.of_mulEquiv
    (((Subgroup.centralizer ({u} : Set G) ⊓ N).equivMapOfInjective (MulAut.conj c).toMonoidHom
      (MulAut.conj c).injective).trans (MulEquiv.subgroupCongr
        (map_conj_centralizer_inf hN c u))).symm h

theorem fourClassesLarge_of_injective_map {G H : Type*} [Group G] [Group H] {f : G →* H}
    (hf : Function.Injective f) {N : Subgroup H} (hN : f.range = N) (t : G)
    (h : CFSG.ComponentClassification.M12Cover.FourClassesLarge
      ↥(Subgroup.centralizer ({f t} : Set H) ⊓ N)) :
    CFSG.ComponentClassification.M12Cover.FourClassesLarge
      ↥(Subgroup.centralizer ({t} : Set G)) := by
  subst hN
  exact CFSG.ComponentClassification.M12Cover.FourClassesLarge.of_mulEquiv
    (((Subgroup.centralizer ({t} : Set G)).equivMapOfInjective f hf).trans
      (MulEquiv.subgroupCongr (map_centralizer_singleton_eq_inf_range hf t))) h

theorem mul_self_eq_one_and_ne_one_of_orderOf_two {G : Type*} [Group G] {t : G}
    (ht : orderOf t = 2) : t * t = 1 ∧ t ≠ 1 := by
  refine ⟨?_, ?_⟩
  · have h1 : t ^ orderOf t = 1 := pow_orderOf_eq_one t
    rw [ht, sq] at h1
    exact h1
  · intro h1
    rw [h1, orderOf_one] at ht
    exact absurd ht (by norm_num)

theorem mem_of_mul_mem_of_mem {G : Type*} [Group G] {H : Subgroup G} {x y : G} (hx : x ∈ H)
    (h : x * y ∈ H) : y ∈ H := by
  simpa using H.mul_mem (H.inv_mem hx) h

theorem fi23ToR_mem_JR (u : CFSG.Sporadic.Fi23.J) : fi23ToR u ∈ JR := by
  rw [fi23ToR_apply]
  exact CFSG.Sporadic.Fi24.jR_mem_JR _

theorem fi24D_mem_JR : fi24D ∈ JR := fi23ToR_mem_JR _

theorem fi24U2_mem_JR : fi24U2 ∈ JR := fi23ToR_mem_JR _

theorem fi24U3_mem_JR : fi24U3 ∈ JR := fi23ToR_mem_JR _

theorem tR_notMem_JR : tR ∉ JR := CFSG.Sporadic.Fi24.tR_not_mem_JR

theorem fi24D_mul_tR_notMem_JR : fi24D * tR ∉ JR := fun h =>
  tR_notMem_JR (mem_of_mul_mem_of_mem fi24D_mem_JR h)

theorem fi24U2_mul_tR_notMem_JR : fi24U2 * tR ∉ JR := fun h =>
  tR_notMem_JR (mem_of_mul_mem_of_mem fi24U2_mem_JR h)

theorem fi24U3_mul_tR_notMem_JR : fi24U3 * tR ∉ JR := fun h =>
  tR_notMem_JR (mem_of_mul_mem_of_mem fi24U3_mem_JR h)

theorem fourClassesLarge_R_of_reps
    (h : ∀ r ∈ ({fi24D, fi24U2, fi24U3, tR, fi24D * tR, fi24U2 * tR, fi24U3 * tR} : Set R),
      CFSG.ComponentClassification.M12Cover.FourClassesLarge
        ↥(Subgroup.centralizer ({r} : Set R))) :
    ∀ t : R, orderOf t = 2 →
      CFSG.ComponentClassification.M12Cover.FourClassesLarge
        ↥(Subgroup.centralizer ({t} : Set R)) := by
  intro t ht
  obtain ⟨ht2, ht1⟩ := mul_self_eq_one_and_ne_one_of_orderOf_two ht
  obtain ⟨r, hr, hc⟩ := fi24_involution_class ht2 ht1
  exact CFSG.EvenSporadicStandard.HypOne.Fi23.fourClassesLarge_of_isConj hc (h r hr)

theorem fourClassesLarge_J_of_reps
    (h : ∀ r ∈ ({fi24D, fi24U2, fi24U3} : Set R),
      CFSG.ComponentClassification.M12Cover.FourClassesLarge
        ↥(Subgroup.centralizer ({r} : Set R) ⊓ JR)) :
    ∀ j : J, orderOf j = 2 →
      CFSG.ComponentClassification.M12Cover.FourClassesLarge
        ↥(Subgroup.centralizer ({j} : Set J)) := by
  intro j hj
  have hr2 : orderOf (jR j) = 2 := (orderOf_injective jR CFSG.Sporadic.Fi24.jR_injective j).trans hj
  obtain ⟨hr2', hr1'⟩ := mul_self_eq_one_and_ne_one_of_orderOf_two hr2
  obtain ⟨r0, hr0, hc⟩ := fi24_involution_class hr2' hr1'
  obtain ⟨c, hc'⟩ := isConj_iff.1 hc
  have hr0JR : r0 ∈ JR := by
    have e : r0 = c⁻¹ * jR j * c⁻¹⁻¹ := by
      rw [← hc']
      group
    rw [e]
    exact CFSG.Sporadic.Fi24.normal_JR.conj_mem _ (CFSG.Sporadic.Fi24.jR_mem_JR j) _
  have hr0set : r0 ∈ ({fi24D, fi24U2, fi24U3} : Set R) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr0
    rcases hr0 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · simp
    · simp
    · exact absurd hr0JR tR_notMem_JR
    · exact absurd hr0JR fi24D_mul_tR_notMem_JR
    · exact absurd hr0JR fi24U2_mul_tR_notMem_JR
    · exact absurd hr0JR fi24U3_mul_tR_notMem_JR
  have h1 : CFSG.ComponentClassification.M12Cover.FourClassesLarge
      ↥(Subgroup.centralizer ({jR j} : Set R) ⊓ JR) :=
    fourClassesLarge_conj_inf CFSG.Sporadic.Fi24.normal_JR hc' (h r0 hr0set)
  exact fourClassesLarge_of_injective_map CFSG.Sporadic.Fi24.jR_injective
    CFSG.Sporadic.Fi24.range_jR j h1

end CFSG.EvenSporadicStandard.YS14
