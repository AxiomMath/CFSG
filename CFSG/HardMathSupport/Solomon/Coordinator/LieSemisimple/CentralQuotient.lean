module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerBridge

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

open CFSG.Open
open scoped commutatorElement

variable {X T : Type*} [Group X] [Group T]

private theorem isSolvable_quotient_of_commutatorElement_mem {G : Type*} [Group G]
    (N : Subgroup G) [N.Normal] (h : ∀ x y : G, ⁅x, y⁆ ∈ N) : Group.IsSolvable (G ⧸ N) := by
  refine Group.isSolvable_of_comm fun a b => ?_
  induction a using QuotientGroup.induction_on with
  | H x =>
    induction b using QuotientGroup.induction_on with
    | H y =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      have hxy : (x * y)⁻¹ * (y * x) = ⁅y⁻¹, x⁻¹⁆ := by
        rw [commutatorElement_def]
        group
      rw [hxy]
      exact h _ _

private theorem isSolvable_of_surjective_of_ker_le {A G Q : Type*} [Group A] [Group G] [Group Q]
    [Group.IsSolvable Q] (ψ : A →* Q) (φ : A →* G) (hφ : Function.Surjective φ)
    (hker : ψ.ker ≤ φ.ker) : Group.IsSolvable G := by
  haveI : Group.IsSolvable (A ⧸ ψ.ker) :=
    Group.isSolvable_of_isSolvable_injective (QuotientGroup.kerLift_injective ψ)
  exact Group.isSolvable_of_surjective
    (QuotientGroup.lift_surjective_of_surjective ψ.ker φ hφ hker)

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

theorem perfectInLayer_of_centralQuotient (π : X →* T) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center X) (α : MulAut X) (β : MulAut T)
    (hαβ : ∀ x, π (α x) = β (π x)) {ι : Type*} (F : ι → Subgroup X)
    (hFα : ∀ i, F i ≤ fixSubgroup α)
    (hFn : ∀ i, ∀ c ∈ fixSubgroup α, ∀ g ∈ F i, c * g * c⁻¹ ∈ F i)
    (hFq : ∀ i, CFSG.IsQuasisimple (F i)) {Q : Type*} [Group Q] [Group.IsSolvable Q]
    (ψ : ↥(fixSubgroup α) →* Q) (hψ : ∀ x : ↥(fixSubgroup α), ψ x = 1 → (x : X) ∈ ⨆ i, F i) :
    PerfectInLayer β := by
  have hNC : (fixSubgroup α).map π ≤ fixSubgroup β := map_fixSubgroup_le π hker α β hαβ
  haveI hNn : (((fixSubgroup α).map π).subgroupOf (fixSubgroup β)).Normal :=
    normal_map_fixSubgroup π hker α β hαβ hπ
  have hDα : (⨆ i, F i) ≤ fixSubgroup α := iSup_le hFα
  have hMN : (⨆ i, F i).map π ≤ (fixSubgroup α).map π := Subgroup.map_mono hDα
  haveI : (((⨆ i, F i).map π).subgroupOf ((fixSubgroup α).map π)).Normal :=
    normal_map_subgroupOf_map π (conj_mem_iSup F hFn)
  have hCN : Group.IsSolvable (↥(fixSubgroup β) ⧸
      ((fixSubgroup α).map π).subgroupOf (fixSubgroup β)) := by
    refine isSolvable_quotient_of_commutatorElement_mem _ fun x y => ?_
    obtain ⟨kx, hkx⟩ := hπ (x : T)
    obtain ⟨ky, hky⟩ := hπ (y : T)
    rw [Subgroup.mem_subgroupOf]
    refine ⟨⁅kx, ky⁆, comm_mem_fixSubgroup π hker α β hαβ (by rw [hkx]; exact x.2)
      (by rw [hky]; exact y.2), ?_⟩
    rw [map_commutatorElement, hkx, hky]
    rfl
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
  have hM : (⨆ i, F i).map π ≤ GLALayer (fixSubgroup β) := by
    rw [Subgroup.map_iSup]
    refine iSup_le fun i => ?_
    have hq : CFSG.IsQuasisimple ((F i).map π) :=
      CFSG.LocalCores.isQuasisimple_map (hFq i) π
        (not_le_ker_of_isQuasisimple π hker (hFq i))
    haveI : (((F i).map π).subgroupOf ((fixSubgroup α).map π)).Normal :=
      normal_map_subgroupOf_map π (hFn i)
    exact le_sSup (isComponentOf_of_normal_normal (Subgroup.map_mono (hFα i)) hNC inferInstance
      hNn hq)
  exact perfectInLayer_of_series hNC hCN hMN hNM hM

end CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
