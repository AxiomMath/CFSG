module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Component
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.CentralQuotient

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped commutatorElement

section Helpers

variable {X T : Type*} [Group X] [Group T]

theorem up34_isSolvable_of_surjective_of_ker_le {A G Q : Type*} [Group A] [Group G] [Group Q]
    [Group.IsSolvable Q] (ψ : A →* Q) (φ : A →* G) (hφ : Function.Surjective φ)
    (hker : ψ.ker ≤ φ.ker) : Group.IsSolvable G := by
  haveI : Group.IsSolvable (A ⧸ ψ.ker) :=
    Group.isSolvable_of_isSolvable_injective (QuotientGroup.kerLift_injective ψ)
  exact Group.isSolvable_of_surjective
    (QuotientGroup.lift_surjective_of_surjective ψ.ker φ hφ hker)

theorem up34_normal_map_subgroupOf_map (π : X →* T) {A L : Subgroup X}
    (hL : ∀ c ∈ A, ∀ g ∈ L, c * g * c⁻¹ ∈ L) :
    ((L.map π).subgroupOf (A.map π)).Normal := by
  refine ⟨fun x hx g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  obtain ⟨f, hf, hfx⟩ := hx
  obtain ⟨c, hc, hcg⟩ := g.2
  refine ⟨c * f * c⁻¹, hL c hc f hf, ?_⟩
  simp only [map_mul, map_inv, hcg, hfx, Subgroup.coe_mul, Subgroup.coe_inv]

theorem up34_conj_mem_iSup {ι : Type*} {A : Subgroup X} (F : ι → Subgroup X)
    (hF : ∀ i, ∀ c ∈ A, ∀ g ∈ F i, c * g * c⁻¹ ∈ F i) :
    ∀ c ∈ A, ∀ g ∈ ⨆ i, F i, c * g * c⁻¹ ∈ ⨆ i, F i := by
  intro c hc g hg
  refine Subgroup.iSup_induction F (C := fun x => c * x * c⁻¹ ∈ ⨆ i, F i) hg
    (fun i x hx => Subgroup.mem_iSup_of_mem i (hF i c hc x hx)) (by simp) fun x y hx hy => ?_
  have e : c * (x * y) * c⁻¹ = (c * x * c⁻¹) * (c * y * c⁻¹) := by group
  rw [e]
  exact Subgroup.mul_mem _ hx hy

theorem up34_not_le_ker_of_isQuasisimple (π : X →* T) (hker : π.ker ≤ Subgroup.center X)
    {K : Subgroup X} (hK : CFSG.IsQuasisimple K) : ¬ K ≤ π.ker := by
  intro hKπ
  obtain ⟨-, -, a, b, hab⟩ := hK
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  refine hab ?_
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (Subgroup.mem_center_iff.1 (hker (hKπ x.2)) y).symm

end Helpers

variable {X T : Type} [Group X] [Group T] [Finite X] [Finite T]

theorem perfect_le_map_iSup_of_centralQuotient (π : X →* T) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center X) (α : MulAut X) (β : MulAut T)
    (hαβ : ∀ x, π (α x) = β (π x)) {ι : Type*} (F : ι → Subgroup X)
    (hFα : ∀ i, F i ≤ fixSubgroup α)
    (hFn : ∀ i, ∀ c ∈ fixSubgroup α, ∀ g ∈ F i, c * g * c⁻¹ ∈ F i)
    {Q : Type*} [Group Q] [Group.IsSolvable Q]
    (ψ : ↥(fixSubgroup α) →* Q) (hψ : ∀ x : ↥(fixSubgroup α), ψ x = 1 → (x : X) ∈ ⨆ i, F i)
    {P : Subgroup T} (hPC : P ≤ fixSubgroup β) (hP : ⁅P, P⁆ = P) :
    P ≤ (⨆ i, F i).map π := by
  have hPN : P ≤ (fixSubgroup α).map π :=
    le_map_fixSubgroup_of_perfect π hker α β hαβ hπ hPC hP
  have hDα : (⨆ i, F i) ≤ fixSubgroup α := iSup_le hFα
  have hMN : (⨆ i, F i).map π ≤ (fixSubgroup α).map π := Subgroup.map_mono hDα
  haveI : (((⨆ i, F i).map π).subgroupOf ((fixSubgroup α).map π)).Normal :=
    up34_normal_map_subgroupOf_map π (up34_conj_mem_iSup F hFn)
  have hNM : Group.IsSolvable (↥((fixSubgroup α).map π) ⧸
      ((⨆ i, F i).map π).subgroupOf ((fixSubgroup α).map π)) := by
    refine up34_isSolvable_of_surjective_of_ker_le ψ
      ((QuotientGroup.mk' (((⨆ i, F i).map π).subgroupOf ((fixSubgroup α).map π))).comp
        (π.subgroupMap (fixSubgroup α)))
      ((QuotientGroup.mk'_surjective _).comp (π.subgroupMap_surjective _)) fun x hx => ?_
    rw [MonoidHom.mem_ker] at hx ⊢
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]
    exact ⟨x, hψ x hx, rfl⟩
  exact perfect_le_of_solvable_quotient hMN hNM hPN hP

theorem noL34Layer_of_centralQuotient (π : X →* T) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center X) (α : MulAut X) (β : MulAut T)
    (hαβ : ∀ x, π (α x) = β (π x)) {ι : Type*} (F : ι → Subgroup X)
    (hFα : ∀ i, F i ≤ fixSubgroup α)
    (hFn : ∀ i, ∀ c ∈ fixSubgroup α, ∀ g ∈ F i, c * g * c⁻¹ ∈ F i)
    (hFq : ∀ i, CFSG.IsQuasisimple (F i)) {Q : Type*} [Group Q] [Group.IsSolvable Q]
    (ψ : ↥(fixSubgroup α) →* Q) (hψ : ∀ x : ↥(fixSubgroup α), ψ x = 1 → (x : X) ∈ ⨆ i, F i)
    (hno : ∀ i, ¬ IsLThreeFour (↥(F i) ⧸ Subgroup.center ↥(F i))) : NoL34Layer β := by
  have hPIL : PerfectInLayer β :=
    perfectInLayer_of_centralQuotient π hπ hker α β hαβ F hFα hFn hFq ψ hψ
  intro I hI hT
  obtain ⟨hcomp, hIT⟩ := exists_component_of_isLThreeFour hPIL hI hT
  have hIM : I ≤ (⨆ i, F i).map π :=
    perfect_le_map_iSup_of_centralQuotient π hπ hker α β hαβ F hFα hFn ψ hψ hI.1
      (glaPComponent_perfect hI)
  have hNC : (fixSubgroup α).map π ≤ fixSubgroup β := map_fixSubgroup_le π hker α β hαβ
  haveI hNn : (((fixSubgroup α).map π).subgroupOf (fixSubgroup β)).Normal :=
    normal_map_fixSubgroup π hker α β hαβ hπ
  have hGcomp : ∀ i, IsComponentOf ((F i).map π) (fixSubgroup β) := by
    intro i
    have hq : CFSG.IsQuasisimple ((F i).map π) :=
      CFSG.LocalCores.isQuasisimple_map (hFq i) π (up34_not_le_ker_of_isQuasisimple π hker (hFq i))
    haveI : (((F i).map π).subgroupOf ((fixSubgroup α).map π)).Normal :=
      up34_normal_map_subgroupOf_map π (hFn i)
    exact isComponentOf_of_normal_normal (Subgroup.map_mono (hFα i)) hNC inferInstance hNn hq
  have hIq : CFSG.Open.IsQuasisimple ↥I := hcomp.2.2
  have hex : ∃ i, (F i).map π ≤ I := by
    by_contra hcon
    push Not at hcon
    have hcomm : ∀ i, ⁅(F i).map π, I⁆ = ⊥ := fun i =>
      (b3Lie_comp_le_or_comm (hGcomp i) hI.1 hI.2.1).resolve_left (hcon i)
    have hMcI : (⨆ i, (F i).map π) ≤ Subgroup.centralizer (I : Set T) :=
      iSup_le fun i => Subgroup.commutator_eq_bot_iff_le_centralizer.1 (hcomm i)
    have hIcI : I ≤ Subgroup.centralizer (I : Set T) := by
      refine le_trans ?_ hMcI
      rw [← Subgroup.map_iSup]
      exact hIM
    have hab : ∀ a ∈ I, ∀ b ∈ I, a * b = b * a := fun a ha b hb =>
      (Subgroup.mem_centralizer_iff.1 (hIcI hb)) a ha
    obtain ⟨-, -, a, b, hab'⟩ := isQuasisimple_of_open_up34 hIq
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    refine hab' ?_
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (hab a a.2 b b.2)
  obtain ⟨i, hiI⟩ := hex
  have hGsn : IsSubnormal ((F i).map π) I :=
    isSubnormal_of_le_of_le (hGcomp i).2.1 hiI hI.1
  have hGq : CFSG.Open.IsQuasisimple ↥((F i).map π) := (hGcomp i).2.2
  have hGp : ⁅(F i).map π, (F i).map π⁆ = (F i).map π := Subgroup.isPerfect_iff.1 ⟨hGq.1⟩
  have hGne : (F i).map π ≠ ⊥ := by
    haveI := CFSG.LocalCores.isQuasisimple_nontrivial (isQuasisimple_of_open_up34 hGq)
    exact (Subgroup.nontrivial_iff_ne_bot _).1 this
  have hGeq : (F i).map π = I :=
    Lemma510Ns.eq_of_isSubnormal_of_quasisimple hIq hGsn hGp hGne
  subst hGeq
  let φ : ↥(F i) →* ↥((F i).map π) := π.subgroupMap (F i)
  have hφ : Function.Surjective φ := π.subgroupMap_surjective (F i)
  have hkc : φ.ker ≤ Subgroup.center ↥(F i) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hπx : π (x : X) = 1 := by simpa [φ] using congrArg Subtype.val hx
    have hxz : (x : X) ∈ Subgroup.center X := hker hπx
    rw [Subgroup.mem_center_iff] at hxz ⊢
    intro g
    exact Subtype.ext (hxz g)
  obtain ⟨e⟩ := CFSG.Goldschmidt.G37.nonempty_centerQuotientEquiv (hFq i).1 φ hφ hkc
  exact hno i (IsLThreeFour.of_mulEquiv e.symm hIT)

end CFSG.HardMathSupport.Dickson.Sec6
