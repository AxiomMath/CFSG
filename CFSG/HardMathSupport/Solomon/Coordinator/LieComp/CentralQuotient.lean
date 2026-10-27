module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerBridge
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Glue

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

variable {X T : Type*} [Group X] [Group T]

private theorem normal_map_subgroupOf_map (π : X →* T) {A L : Subgroup X}
    (hL : ∀ c ∈ A, ∀ g ∈ L, c * g * c⁻¹ ∈ L) :
    ((L.map π).subgroupOf (A.map π)).Normal := by
  refine ⟨fun x hx g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  obtain ⟨f, hf, hfx⟩ := hx
  obtain ⟨c, hc, hcg⟩ := g.2
  refine ⟨c * f * c⁻¹, hL c hc f hf, ?_⟩
  simp only [map_mul, map_inv, hcg, hfx, Subgroup.coe_mul, Subgroup.coe_inv]

private theorem conj_mem_iSup {ι : Type*} {A : Subgroup X} (F : ι → Subgroup X)
    (hF : ∀ i, ∀ c ∈ A, ∀ g ∈ F i, c * g * c⁻¹ ∈ F i) :
    ∀ c ∈ A, ∀ g ∈ ⨆ i, F i, c * g * c⁻¹ ∈ ⨆ i, F i := by
  intro c hc g hg
  refine Subgroup.iSup_induction F (C := fun x => c * x * c⁻¹ ∈ ⨆ i, F i) hg
    (fun i x hx => Subgroup.mem_iSup_of_mem i (hF i c hc x hx)) (by simp) fun x y hx hy => ?_
  have e : c * (x * y) * c⁻¹ = (c * x * c⁻¹) * (c * y * c⁻¹) := by group
  rw [e]
  exact Subgroup.mul_mem _ hx hy

private theorem isSolvable_of_surjective_of_ker_le {A G Q : Type*} [Group A] [Group G] [Group Q]
    [Group.IsSolvable Q] (ψ : A →* Q) (φ : A →* G) (hφ : Function.Surjective φ)
    (hker : ψ.ker ≤ φ.ker) : Group.IsSolvable G := by
  haveI : Group.IsSolvable (A ⧸ ψ.ker) :=
    Group.isSolvable_of_isSolvable_injective (QuotientGroup.kerLift_injective ψ)
  exact Group.isSolvable_of_surjective
    (QuotientGroup.lift_surjective_of_surjective ψ.ker φ hφ hker)

private theorem not_le_ker_of_isQuasisimple (π : X →* T) (hker : π.ker ≤ Subgroup.center X)
    {K : Subgroup X} (hK : CFSG.IsQuasisimple K) : ¬ K ≤ π.ker := by
  intro hKπ
  obtain ⟨-, -, a, b, hab⟩ := hK
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  refine hab ?_
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (Subgroup.mem_center_iff.1 (hker (hKπ x.2)) y).symm

private theorem perfect_le_iSup_map (π : X →* T) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center X) (α : MulAut X) (β : MulAut T)
    (hαβ : ∀ x, π (α x) = β (π x)) {ι : Type*} (F : ι → Subgroup X)
    (hFα : ∀ i, F i ≤ fixSubgroup α)
    (hFn : ∀ i, ∀ c ∈ fixSubgroup α, ∀ g ∈ F i, c * g * c⁻¹ ∈ F i)
    {Q : Type*} [Group Q] [Group.IsSolvable Q]
    (ψ : ↥(fixSubgroup α) →* Q) (hψ : ∀ x : ↥(fixSubgroup α), ψ x = 1 → (x : X) ∈ ⨆ i, F i)
    {P : Subgroup T} (hPC : P ≤ fixSubgroup β) (hP : ⁅P, P⁆ = P) :
    P ≤ ⨆ i, (F i).map π := by
  have hDα : (⨆ i, F i) ≤ fixSubgroup α := iSup_le hFα
  have hMN : (⨆ i, F i).map π ≤ (fixSubgroup α).map π := Subgroup.map_mono hDα
  haveI : (((⨆ i, F i).map π).subgroupOf ((fixSubgroup α).map π)).Normal :=
    normal_map_subgroupOf_map π (conj_mem_iSup F hFn)
  have hNM : Group.IsSolvable (↥((fixSubgroup α).map π) ⧸
      ((⨆ i, F i).map π).subgroupOf ((fixSubgroup α).map π)) := by
    refine isSolvable_of_surjective_of_ker_le ψ
      ((QuotientGroup.mk' (((⨆ i, F i).map π).subgroupOf ((fixSubgroup α).map π))).comp
        (π.subgroupMap (fixSubgroup α)))
      ((QuotientGroup.mk'_surjective _).comp (π.subgroupMap_surjective _)) fun x hx => ?_
    rw [MonoidHom.mem_ker] at hx ⊢
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]
    exact ⟨x, hψ x hx, rfl⟩
  rw [← Subgroup.map_iSup]
  exact perfect_le_of_solvable_quotient hMN hNM
    (le_map_fixSubgroup_of_perfect π hker α β hαβ hπ hPC hP) hP

private theorem isComponentOf_map_fixSubgroup (π : X →* T) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center X) (α : MulAut X) (β : MulAut T)
    (hαβ : ∀ x, π (α x) = β (π x)) {F : Subgroup X} (hFα : F ≤ fixSubgroup α)
    (hFn : ∀ c ∈ fixSubgroup α, ∀ g ∈ F, c * g * c⁻¹ ∈ F) (hFq : CFSG.IsQuasisimple F) :
    IsComponentOf (F.map π) (fixSubgroup β) := by
  have hNC : (fixSubgroup α).map π ≤ fixSubgroup β := map_fixSubgroup_le π hker α β hαβ
  haveI hNn : (((fixSubgroup α).map π).subgroupOf (fixSubgroup β)).Normal :=
    normal_map_fixSubgroup π hker α β hαβ hπ
  haveI : ((F.map π).subgroupOf ((fixSubgroup α).map π)).Normal :=
    normal_map_subgroupOf_map π hFn
  exact isComponentOf_of_normal_normal (Subgroup.map_mono hFα) hNC inferInstance hNn
    (CFSG.LocalCores.isQuasisimple_map hFq π (not_le_ker_of_isQuasisimple π hker hFq))

theorem components_of_centralQuotient [Finite T] (π : X →* T) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center X) (α : MulAut X) (β : MulAut T)
    (hαβ : ∀ x, π (α x) = β (π x)) {ι : Type*} (F : ι → Subgroup X)
    (hFα : ∀ i, F i ≤ fixSubgroup α)
    (hFn : ∀ i, ∀ c ∈ fixSubgroup α, ∀ g ∈ F i, c * g * c⁻¹ ∈ F i)
    (hFq : ∀ i, CFSG.IsQuasisimple (F i)) {Q : Type*} [Group Q] [Group.IsSolvable Q]
    (ψ : ↥(fixSubgroup α) →* Q) (hψ : ∀ x : ↥(fixSubgroup α), ψ x = 1 → (x : X) ∈ ⨆ i, F i) :
    ∀ K : Subgroup T, IsComponentOf K (fixSubgroup β) → ∃ i, K = (F i).map π := by
  intro K hK
  haveI : Finite (Subgroup T) := Finite.of_injective _ SetLike.coe_injective
  let R : Set (Subgroup T) := Set.range fun i => (F i).map π
  obtain ⟨⟨_, i, rfl⟩, hKi⟩ := component_mem_named_factors (ι := R) (fun r => (r : Subgroup T))
    (fun ⟨_, i, hi⟩ => hi ▸ isComponentOf_map_fixSubgroup π hπ hker α β hαβ (hFα i) (hFn i) (hFq i))
    (fun P hPC hP => (perfect_le_iSup_map π hπ hker α β hαβ F hFα hFn ψ hψ hPC
      (Subgroup.isPerfect_iff.1 ⟨hP⟩)).trans
        (iSup_le fun i => le_iSup (fun r : R => (r : Subgroup T)) ⟨_, i, rfl⟩)) hK
  exact ⟨i, hKi⟩

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
