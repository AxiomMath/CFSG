module

public import CFSG.ClassicalInvolution.Q3.Q3PlanParamsComp
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalToral

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Open (IsSubnormal)
open CFSG.ClassicalInvolution.ModelFacts
  (isQuasisimple_componentRootSpan_of_five_le open_isQuasisimple)
open scoped commutatorElement

variable {τ : Tag} {K : Type} [Field K]

section Quotient

theorem weylQuotient_sq (hK : ringChar K ≠ 2) {a : Fin τ.rank → Kˣ}
    (ha : ∀ i, a i = 1 ∨ a i = -1)
    (q : rootCharStabilizerSubgroup a ⧸
      (kernelReflectionGroup a).subgroupOf (rootCharStabilizerSubgroup a)) : q ^ 2 = 1 := by
  obtain ⟨⟨w, hw⟩, rfl⟩ := QuotientGroup.mk_surjective q
  have h := orderOf_dvd_iff_pow_eq_one.mp (orderOf_dvd_two_of_charQuotient
    (maskChar (signTupleBits a))
    (QuotientGroup.mk ⟨w, (mem_rootCharStabilizer_iff hK ha).1 hw⟩ :
      CharQuotient (maskChar (signTupleBits a))))
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
    kernelReflectionGroup_eq_kernelWeylGroup hK ha]
  exact h

theorem toralQuotient_sq (hK : ringChar K ≠ 2) {a : Fin τ.rank → Kˣ}
    (ha : ∀ i, a i = 1 ∨ a i = -1)
    (x : toralCentralizer τ K a ⧸ (toralRootGroup τ K a).subgroupOf (toralCentralizer τ K a)) :
    x ^ 2 = 1 := by
  obtain ⟨-, -, -, -, φ, hφ, -⟩ := Chevalley_toral_centralizer_root_generated_quotient τ K a
  obtain ⟨q, rfl⟩ := hφ x
  rw [← map_pow, weylQuotient_sq hK ha, map_one]

theorem mem_toralRootGroup_of_odd_orderOf (hK : ringChar K ≠ 2) {a : Fin τ.rank → Kˣ}
    (ha : ∀ i, a i = 1 ∨ a i = -1) {x : ModGL τ K} (hx : x ∈ toralCentralizer τ K a)
    (hodd : Odd (orderOf x)) : x ∈ toralRootGroup τ K a := by
  obtain ⟨-, hn, -⟩ := Chevalley_toral_centralizer_root_generated_quotient τ K a
  have : ((toralRootGroup τ K a).subgroupOf (toralCentralizer τ K a)).Normal := hn
  set q : toralCentralizer τ K a ⧸ (toralRootGroup τ K a).subgroupOf (toralCentralizer τ K a) :=
    QuotientGroup.mk ⟨x, hx⟩ with hq
  have h2 : q ^ 2 = 1 := toralQuotient_sq hK ha q
  have hm : q ^ orderOf x = 1 := by
    rw [hq, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    have : (⟨x, hx⟩ : toralCentralizer τ K a) ^ orderOf x = 1 :=
      Subtype.ext (by simp)
    rw [this]
    exact one_mem _
  obtain ⟨k, hk⟩ := hodd
  have hq1 : q = 1 := by
    calc q = q ^ (2 * k + 1) * (q ^ 2) ^ (-(k : ℤ)) := by
          rw [h2, one_zpow, mul_one, pow_succ, pow_mul, h2, one_pow, one_mul]
      _ = 1 := by rw [← hk, hm, h2, one_zpow, mul_one]
  rw [hq, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hq1
  exact hq1

end Quotient

section Commutator

theorem commutator_toralRootGroup_le (a : Fin τ.rank → Kˣ) :
    ∀ x ∈ toralRootGroup τ K a, ∀ y ∈ toralRootGroup τ K a,
      ⁅x, y⁆ ∈ rootSpan τ K (rootCharKernel a) := by
  set M := toralRootGroup τ K a with hM
  set S := rootSpan τ K (rootCharKernel a) with hS
  have hSM : S ≤ M := le_sup_right
  have hTM : torusGroup τ K ≤ M := le_sup_left
  have hMn : M ≤ Subgroup.normalizer (S : Set (ModGL τ K)) :=
    sup_le (torusGroup_le_normalizer_rootSpan fun _ hα => hα.1) Subgroup.le_normalizer
  have hN : (S.subgroupOf M).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hSM).mpr hMn
  have hsup : S.subgroupOf M ⊔ (torusGroup τ K).subgroupOf M = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hSM hTM]
    have : S ⊔ torusGroup τ K = M := by rw [hM, toralRootGroup, sup_comm]
    rw [this, Subgroup.subgroupOf_self]
  have hTc : ∀ g ∈ torusGroup τ K, ∀ g' ∈ torusGroup τ K, g * g' = g' * g :=
    (triangular_borel_structure.{0, 0} τ K).1
  have hcomm : IsMulCommutative ↥((torusGroup τ K).subgroupOf M) :=
    ⟨⟨fun u v => Subtype.ext (Subtype.ext (hTc _ (Subgroup.mem_subgroupOf.mp u.2) _
      (Subgroup.mem_subgroupOf.mp v.2)))⟩⟩
  have hle := Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup hcomm
  intro x hx y hy
  have hmem : ⁅(⟨x, hx⟩ : M), (⟨y, hy⟩ : M)⁆ ∈ _root_.commutator ↥M := by
    rw [commutator_def]
    exact Subgroup.commutator_mem_commutator trivial trivial
  exact Subgroup.mem_subgroupOf.mp (hle hmem)

end Commutator

section Solvable

variable [Finite K]

theorem commute_of_mem_inf_rootSpan (hK : ringChar K ≠ 2) (h5 : 5 ≤ Nat.card K)
    {a : Fin τ.rank → Kˣ} (ha : ∀ i, a i = 1 ∨ a i = -1) {J : Subgroup (ModGL τ K)}
    (hJs : IsSubnormal J (toralCentralizer τ K a)) (hsolv : Group.IsSolvable J) :
    ∀ n ∈ J ⊓ rootSpan τ K (rootCharKernel a), ∀ s ∈ rootSpan τ K (rootCharKernel a),
      n * s = s * n := by
  set χ := maskChar (signTupleBits a) with hχ
  have hSeq : rootSpan τ K (rootCharKernel a) = rootSpan τ K (kernelRoots χ) := by
    rw [rootCharKernel_eq_kernelRoots hK ha]
  have hSC : rootSpan τ K (rootCharKernel a) ≤ toralCentralizer τ K a :=
    rootSpan_rootCharKernel_le_toralCentralizer a
  have hSn : IsSubnormal (J ⊓ rootSpan τ K (kernelRoots χ)) (rootSpan τ K (kernelRoots χ)) := by
    rw [← hSeq]
    exact CFSG.ClassicalInvolution.ModelFacts.isSubnormal_inf hJs hSC
  have hsolv' : Group.IsSolvable ↥(J ⊓ rootSpan τ K (kernelRoots χ)) :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion (inf_le_left))
      (Subgroup.inclusion_injective inf_le_left)
  rw [hSeq]
  obtain ⟨-, -, -, hnorm, -, -⟩ := root_character_kernel_orthogonal_central_product τ K χ
  intro n hn s hs
  have hnS := hn.2
  rw [← iSup_componentRootSpan K] at hs
  have hZ : ⨆ i, componentRootSpan K χ i ≤ Subgroup.centralizer ({n} : Set (ModGL τ K)) := by
    refine iSup_le fun i => fun x hx => ?_
    have hq : CFSG.Open.IsQuasisimple (componentRootSpan K χ i) :=
      open_isQuasisimple (isQuasisimple_componentRootSpan_of_five_le hK h5 χ i)
    have hle := (hnorm i).1
    have hnormal : rootSpan τ K (kernelRoots χ) ≤
        Subgroup.normalizer (componentRootSpan K χ i : Set (ModGL τ K)) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mp (hnorm i).2
    have := commute_of_isSubnormal_of_isSolvable hq hle hnormal hSn hsolv' n hn x hx
    exact Subgroup.mem_centralizer_singleton_iff.mpr this.symm
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hZ hs)).symm

theorem derivedSeries_two_eq_bot_of_toral (hK : ringChar K ≠ 2) (h5 : 5 ≤ Nat.card K)
    {a : Fin τ.rank → Kˣ} (ha : ∀ i, a i = 1 ∨ a i = -1) {J : Subgroup (ModGL τ K)}
    (hJC : J ≤ toralCentralizer τ K a) (hJs : IsSubnormal J (toralCentralizer τ K a))
    (hsolv : Group.IsSolvable J)
    (hodd : J ≤ Subgroup.closure {x : ModGL τ K | x ∈ J ∧ Odd (orderOf x)}) :
    derivedSeries ↥J 2 = ⊥ := by
  have hJM : J ≤ toralRootGroup τ K a :=
    hodd.trans ((Subgroup.closure_le _).mpr fun x hx =>
      mem_toralRootGroup_of_odd_orderOf hK ha (hJC hx.1) hx.2)
  refine derivedSeries_two_eq_bot_of_commutator_mem (B := J ⊓ rootSpan τ K (rootCharKernel a))
    (fun u hu v hv => commute_of_mem_inf_rootSpan hK h5 ha hJs hsolv u hu v hv.2) ?_
  intro x hx y hy
  exact ⟨J.mul_mem (J.mul_mem (J.mul_mem hx hy) (J.inv_mem hx)) (J.inv_mem hy),
    commutator_toralRootGroup_le a x (hJM hx) y (hJM hy)⟩

end Solvable

end CFSG.ClassicalInvolution.Q3
