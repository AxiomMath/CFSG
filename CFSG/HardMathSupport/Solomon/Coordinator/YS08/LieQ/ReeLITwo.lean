module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Ree
public import CFSG.LieType.Ree.LargeReeInvolutionTCentralizer

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LieType.ChevTwo.Semi CFSG.LieType.Ree.LargeReeInvolution

set_option linter.unusedSectionVars false

section ReeTwo


variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}

theorem reeLIAt_one (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ReeLIAt K a ⟨1, by decide⟩ := by
  obtain ⟨-, -, hcent, -, -⟩ := centralizerZ_kernel (K := K) (a := a) ha hK
  intro x hx
  have hzV : centralZ K a 1 ∈ ReeTag.F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩ :=
    centralZ_mem_complement ha hK 1
  have hzΓ : centralZ K a 1 ∈ ReeTag.F4.reeGamma K a := (Subgroup.mem_inf.1 hzV).2
  have hz : (⟨centralZ K a 1, hzΓ⟩ : ↥(ReeTag.F4.reeGamma K a)) ∈
      reeQJ ReeTag.F4 K a (some ⟨1, by decide⟩) := by
    rw [reeQJ_some]
    exact Subgroup.mem_subgroupOf.2 hzV
  have hxz : (x : ModGL ReeTag.F4.tag K) * centralZ K a 1 = centralZ K a 1 * x := by
    have h1 := congrArg (fun y : ↥(ReeTag.F4.reeGamma K a) => (y : ModGL ReeTag.F4.tag K))
      (hx _ hz)
    simp only [Subgroup.coe_mul] at h1
    exact h1
  have hxC : (x : ModGL ReeTag.F4.tag K) ∈ centralizerZ K a := by
    rw [← reeGamma_inf_centralizer_eq ha hK]
    refine Subgroup.mem_inf.2 ⟨x.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    rw [hg]
    exact hxz.symm
  have hx' : (⟨x, hxC⟩ : ↥(centralizerZ K a)) ∈
      (ReeTag.F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩).subgroupOf
        (centralizerZ K a) := by
    refine hcent (Subgroup.mem_centralizer_iff.2 ?_)
    intro r hr
    have hrV : (r : ModGL ReeTag.F4.tag K) ∈
        ReeTag.F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩ :=
      Subgroup.mem_subgroupOf.1 hr
    have hrΓ : (r : ModGL ReeTag.F4.tag K) ∈ ReeTag.F4.reeGamma K a := (Subgroup.mem_inf.1 hrV).2
    have hrQ : (⟨r, hrΓ⟩ : ↥(ReeTag.F4.reeGamma K a)) ∈
        reeQJ ReeTag.F4 K a (some ⟨1, by decide⟩) := by
      rw [reeQJ_some]
      exact Subgroup.mem_subgroupOf.2 hrV
    have h1 := congrArg (fun y : ↥(ReeTag.F4.reeGamma K a) => (y : ModGL ReeTag.F4.tag K))
      (hx _ hrQ)
    simp only [Subgroup.coe_mul] at h1
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul]
    exact h1.symm
  rw [reeQJ_some]
  exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.1 hx')

end ReeTwo

section ReeOne


variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}

theorem reeLIAt_zero (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ReeLIAt K a ⟨0, by decide⟩ := by
  obtain ⟨-, -, hcent, -, -⟩ := centralizerT_kernel (K := K) (a := a) ha hK
  intro x hx
  have hQ1 : sylowL a K 1 ∈ tKernel K a := sylowL_mem_tKernel hK 1
  have hV : sylowL a K 1 ∈ ReeTag.F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩ :=
    (Subgroup.mem_inf.1 hQ1).1
  have hΓ : sylowL a K 1 ∈ ReeTag.F4.reeGamma K a := tKernel_le_reeGamma hQ1
  have hz : (⟨sylowL a K 1, hΓ⟩ : ↥(ReeTag.F4.reeGamma K a)) ∈
      reeQJ ReeTag.F4 K a (some ⟨0, by decide⟩) := by
    rw [reeQJ_some]
    exact Subgroup.mem_subgroupOf.2 hV
  have hxz : (x : ModGL ReeTag.F4.tag K) * sylowL a K 1 = sylowL a K 1 * x := by
    have h1 := congrArg (fun y : ↥(ReeTag.F4.reeGamma K a) => (y : ModGL ReeTag.F4.tag K))
      (hx _ hz)
    simp only [Subgroup.coe_mul] at h1
    exact h1
  have hxC : (x : ModGL ReeTag.F4.tag K) ∈ centralizerT K a := by
    rw [← reeGamma_inf_centralizer_tOne_eq hK]
    refine Subgroup.mem_inf.2 ⟨x.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    rw [hg]
    exact hxz.symm
  have hx' : (⟨x, hxC⟩ : ↥(centralizerT K a)) ∈ (tKernel K a).subgroupOf (centralizerT K a) := by
    refine hcent (Subgroup.mem_centralizer_iff.2 ?_)
    intro r hr
    have hrQ : (r : ModGL ReeTag.F4.tag K) ∈ tKernel K a := Subgroup.mem_subgroupOf.1 hr
    have hrV : (r : ModGL ReeTag.F4.tag K) ∈
        ReeTag.F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩ := (Subgroup.mem_inf.1 hrQ).1
    have hrΓ : (r : ModGL ReeTag.F4.tag K) ∈ ReeTag.F4.reeGamma K a := tKernel_le_reeGamma hrQ
    have hrQJ : (⟨r, hrΓ⟩ : ↥(ReeTag.F4.reeGamma K a)) ∈
        reeQJ ReeTag.F4 K a (some ⟨0, by decide⟩) := by
      rw [reeQJ_some]
      exact Subgroup.mem_subgroupOf.2 hrV
    have h1 := congrArg (fun y : ↥(ReeTag.F4.reeGamma K a) => (y : ModGL ReeTag.F4.tag K))
      (hx _ hrQJ)
    simp only [Subgroup.coe_mul] at h1
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul]
    exact h1.symm
  rw [reeQJ_some]
  exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hx')).1

end ReeOne

section ReeAll


variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}

theorem reeLI_of_one_le (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) : ReeLI K a := by
  intro j
  obtain ⟨j, hj⟩ := j
  have hj2 : j < 2 := hj
  interval_cases j
  · exact reeLIAt_zero ha hK
  · exact reeLIAt_one ha hK

end ReeAll

end CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ
