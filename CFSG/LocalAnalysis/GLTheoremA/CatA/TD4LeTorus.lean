module

public import CFSG.Timmesfeld.Orders.ExceptionalTwistedUnipotent
public import CFSG.Timmesfeld.Orders.ExceptionalTwistedBruhat
public import CFSG.LocalAnalysis.GLTheoremA.CatA.TD4LeRoot
public import CFSG.LocalAnalysis.GLTheoremA.CatA.TD4LeField

public section

namespace CFSG.LocalAnalysis.GLTheoremA.TD4Le

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.Timmesfeld.ExceptionalOrders


variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {e : ℕ}

theorem exists_rootDiagUnit_of_mem_torus (hσs : Function.Surjective σ.toRingHom)
    {x : ModGL TwistTag.D4.tag K} (hx : x ∈ graphFixedRootTorus TwistTag.D4 K σ.toRingHom) :
    ∃ a : Fin TwistTag.D4.tag.rank → Kˣ, x = rootDiagUnit TwistTag.D4.tag a ∧
      ∀ i, a (TwistTag.D4.perm i) = Units.map σ.toRingHom.toMonoidHom (a i) := by
  rw [graphFixedRootTorus_eq_compatTorus hσs] at hx
  obtain ⟨c, hc, rfl⟩ := (mem_compatTorus σ.toRingHom).1 hx
  refine ⟨cartanChar c, ?_, cartanChar_perm hc⟩
  rw [coe_torusCoordHom, List.ofFn_eq_map]
  exact list_prod_torusElt_eq_rootDiagUnit c

theorem exists_cube_root_diag (h : Std e K σ) (hQ : 2 ^ e % 3 = 1)
    {x : ModGL TwistTag.D4.tag K} (hx : x ∈ graphFixedRootTorus TwistTag.D4 K σ.toRingHom)
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    ∃ a : Fin TwistTag.D4.tag.rank → Kˣ, x = rootDiagUnit TwistTag.D4.tag a ∧
      (∀ i, a i ^ 3 = 1) ∧ (∀ i, a (TwistTag.D4.perm i) = a i) ∧ a ≠ 1 := by
  obtain ⟨a, rfl, hcompat⟩ := exists_rootDiagUnit_of_mem_torus σ.surjective hx
  have hpow : rootDiagUnit TwistTag.D4.tag (a ^ 3) = 1 := by
    have : rootDiagUnit TwistTag.D4.tag (a ^ 3) = rootDiagUnit TwistTag.D4.tag a ^ 3 :=
      (rootDiagUnitHom TwistTag.D4.tag K).map_pow a 3
    rw [this, hx3]
  have ha3 : a ^ 3 = 1 := by
    apply rootDiagUnit_injective
    rw [hpow, rootDiagUnit_one]
  have ha3' : ∀ i, a i ^ 3 = 1 := fun i => congrFun ha3 i
  refine ⟨a, rfl, ha3', fun i => ?_, ?_⟩
  · rw [hcompat i]
    refine Units.ext ?_
    have hc : ((a i : Kˣ) : K) ^ 3 = 1 := by
      have := congrArg (fun u : Kˣ => (u : K)) (ha3' i)
      simpa using this
    exact h.apply_eq_of_pow_three hQ hc
  · rintro rfl
    exact hx1 (by rw [rootDiagUnit_one])

theorem card_posUnipotent_inf_centralizer_le (h : Std e K σ) (hQ : 2 ^ e % 3 = 1)
    {x : ModGL TwistTag.D4.tag K} (hx : x ∈ graphFixedRootTorus TwistTag.D4 K σ.toRingHom)
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    Nat.card ↥(graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ⊓
      Subgroup.centralizer ({x} : Set (ModGL TwistTag.D4.tag K))) ≤ (2 ^ e) ^ 3 := by
  obtain ⟨a, rfl, ha3, haρ, ha1⟩ := exists_cube_root_diag h hQ hx hx3 hx1
  set S : Set (Fin TwistTag.D4.tag.rank → ℤ) :=
    rootCharKernel a ∩ {α | IsRoot TwistTag.D4.tag α ∧ 0 < height α} with hS
  have hcard : Nat.card ↥(rootSpan TwistTag.D4.tag K S ⊓
      twistedFixedGroup TwistTag.D4 K σ.toRingHom) = (2 ^ e) ^ 3 := by
    rw [card_rootSpan_inf_twistedFixedGroup (t := TwistTag.D4) σ.surjective (card_orbitField_std h)
      (fun α hα => hα.2) (posKernel_perm a haρ) (posKernel_closed a),
      ncard_posKernel a ha3 haρ ha1]
  rw [← hcard]
  refine Subgroup.card_le_of_le ?_
  intro y hy
  obtain ⟨hyU, hyc⟩ := Subgroup.mem_inf.1 hy
  obtain ⟨hyP, hyΓ⟩ := Subgroup.mem_inf.1 hyU
  refine Subgroup.mem_inf.2 ⟨?_, hyΓ⟩
  have hfix : rootDiagUnit TwistTag.D4.tag a * y * (rootDiagUnit TwistTag.D4.tag a)⁻¹ = y := by
    have := (Subgroup.mem_centralizer_singleton_iff).1 hyc
    rw [mul_inv_eq_iff_eq_mul]
    exact this.symm
  have hposfin :
      {β : Fin TwistTag.D4.tag.rank → ℤ | IsRoot TwistTag.D4.tag β ∧ 0 < height β}.Finite :=
    (finite_setOf_isRoot TwistTag.D4.tag).subset fun β hβ => hβ.1
  exact mem_rootSpan_inter_of_conj_eq a hposfin (fun β hβ => hβ.1)
    (fun α hα hr => (positive_root_collection TwistTag.D4.tag K).2 α hα hr) hyP hfix

end CFSG.LocalAnalysis.GLTheoremA.TD4Le

end
