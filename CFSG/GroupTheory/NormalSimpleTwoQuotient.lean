module

public import CFSG.GroupTheory.PCore.SolvableRadical
import CFSG.Quasithin.Background.A3ComponentsQuotient

public section

namespace CFSG.GroupTheory

open scoped commutatorElement

variable {K : Type*} [Group K] [Finite K]

theorem eq_one_of_mem_solvableRadical_of_isSimpleGroup {J : Subgroup K}
    (hJ : IsSimpleGroup J) (hnab : ∃ x y : J, x * y ≠ y * x)
    {x : K} (hxJ : x ∈ J) (hxR : x ∈ CFSG.solvableRadical K) : x = 1 := by
  classical
  have hRs : Group.IsSolvable (CFSG.solvableRadical K) :=
    CFSG.Quasithin.A3.solvableRadical_isSolvable
  have hRn : (CFSG.solvableRadical K).Normal := inferInstance
  have : ((CFSG.solvableRadical K).subgroupOf J).Normal := hRn.subgroupOf J
  let f : ↥((CFSG.solvableRadical K).subgroupOf J) →* ↥(CFSG.solvableRadical K) :=
    { toFun := fun y => ⟨y.1.1, y.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := fun y z h =>
    Subtype.ext (Subtype.ext (congrArg (fun w : ↥(CFSG.solvableRadical K) => (w : K)) h))
  have : Group.IsSolvable ((CFSG.solvableRadical K).subgroupOf J) :=
    Group.isSolvable_of_isSolvable_injective (f := f) hf
  rcases hJ.eq_bot_or_eq_top_of_normal ((CFSG.solvableRadical K).subgroupOf J) with h0 | h0
  · have hmem : (⟨x, hxJ⟩ : J) ∈ (CFSG.solvableRadical K).subgroupOf J := hxR
    rw [h0] at hmem
    exact Subtype.ext_iff.mp (Subgroup.mem_bot.mp hmem)
  · exfalso
    rw [Subgroup.subgroupOf_eq_top] at h0
    have hJs : Group.IsSolvable J :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion h0)
        (Subgroup.inclusion_injective _)
    obtain ⟨a, b, hab⟩ := hnab
    exact hab ((IsSimpleGroup.comm_iff_isSolvable).mpr hJs a b)

theorem isPGroup_two_solvableRadical_of_isSimpleGroup {J : Subgroup K}
    (hJ : IsSimpleGroup J) (hnab : ∃ x y : J, x * y ≠ y * x)
    (hK2 : ∀ x : K, ∃ k : ℕ, x ^ 2 ^ k ∈ J) :
    IsPGroup 2 (CFSG.solvableRadical K) := by
  rw [isPGroup_iff_pow_pow_eq_one]
  intro r
  obtain ⟨k, hk⟩ := hK2 (r : K)
  refine ⟨k, ?_⟩
  apply Subtype.ext
  have hxR : (r : K) ^ 2 ^ k ∈ CFSG.solvableRadical K :=
    (CFSG.solvableRadical K).pow_mem r.2 _
  have hone := eq_one_of_mem_solvableRadical_of_isSimpleGroup hJ hnab hk hxR
  simpa using hone

theorem exists_commutator_not_mem_solvableRadical_of_relIndex_two {G : Type*} [Group G]
    [Finite G] {A K J : Subgroup G}
    (hAN : A ≤ Subgroup.normalizer (J : Set G)) (hJK : J ≤ K)
    (hs : IsSimpleGroup ↥J) (hna : ∃ x y : ↥J, x * y ≠ y * x)
    (hidx : (A ⊓ Subgroup.centralizer (J : Set G)).relIndex A = 2) :
    ∃ a ∈ A, ∃ x ∈ J, ⁅a, x⁆ ∉ (CFSG.solvableRadical ↥K).map K.subtype := by
  classical
  have hne : A ⊓ Subgroup.centralizer (J : Set G) ≠ A := by
    intro heq
    rw [heq, Subgroup.relIndex_self] at hidx
    omega
  by_contra hcon
  push Not at hcon
  apply hne
  refine le_antisymm inf_le_left ?_
  intro a haA
  refine ⟨haA, ?_⟩
  show a ∈ Subgroup.centralizer (J : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hmem : ⁅a, x⁆ ∈ (CFSG.solvableRadical ↥K).map K.subtype := hcon a haA x hx
  obtain ⟨y, hyR, hy⟩ := Subgroup.mem_map.mp hmem
  have haxJ : ⁅a, x⁆ ∈ J := by
    rw [commutatorElement_def]
    exact J.mul_mem ((Subgroup.mem_normalizer_iff.mp (hAN haA) x).mp hx) (J.inv_mem hx)
  have hyJ : y ∈ J.subgroupOf K := by
    rw [Subgroup.mem_subgroupOf]
    rw [show (y : G) = K.subtype y from rfl, hy]
    exact haxJ
  let e : ↥(J.subgroupOf K) ≃* ↥J := Subgroup.subgroupOfEquivOfLe hJK
  have hJ' : IsSimpleGroup (J.subgroupOf K) := e.isSimpleGroup
  have hna' : ∃ u v : ↥(J.subgroupOf K), u * v ≠ v * u := by
    obtain ⟨u, v, huv⟩ := hna
    refine ⟨e.symm u, e.symm v, ?_⟩
    intro huv'
    exact huv (by simpa using congrArg e huv')
  have hone := eq_one_of_mem_solvableRadical_of_isSimpleGroup hJ' hna' hyJ hyR
  have hxeq : ⁅a, x⁆ = 1 := by
    rw [← hy]
    exact congrArg Subtype.val hone
  rw [commutatorElement_eq_one_iff_mul_comm] at hxeq
  exact hxeq.symm

theorem pCore_two_le_centralizer_of_normal_simple {J : Subgroup K} [J.Normal]
    (hJ : IsSimpleGroup J) (hnab : ∃ x y : J, x * y ≠ y * x) :
    CFSG.pCore 2 K ≤ Subgroup.centralizer (J : Set K) := by
  classical
  set O : Subgroup K := CFSG.pCore 2 K with hO
  have hOinfJ : O ⊓ J = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxR : x ∈ CFSG.solvableRadical K := CFSG.pCore_le_solvableRadical 2 K hx.1
    exact Subgroup.mem_bot.mpr
      (eq_one_of_mem_solvableRadical_of_isSimpleGroup hJ hnab hx.2 hxR)
  have hcomm : ⁅O, J⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_of_disjoint (disjoint_iff.mpr hOinfJ)
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm

end CFSG.GroupTheory
