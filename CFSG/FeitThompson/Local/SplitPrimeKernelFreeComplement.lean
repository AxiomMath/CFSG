module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Complement
import CFSG.FeitThompson.Local.SplitKernelRemovalExponentAbelianSylow

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Pointwise Subgroup

variable {G : Type*} [Group G] {p : ℕ} {H U A V : Subgroup G}

theorem isMulCommutative_of_natCard_eq_prime (hp : p.Prime) (hA : Nat.card A = p) :
    IsMulCommutative A :=
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsCyclic A := isCyclic_of_prime_card hA
  inferInstance

theorem natCard_subgroupOf_eq (h : A ≤ U) : Nat.card (A.subgroupOf U) = Nat.card A :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

structure IsSplitCentralizingPrimeKernel (p : ℕ) (H U A V : Subgroup G) : Prop where
  prime : p.Prime
  H_ne_bot : H ≠ ⊥
  U_le_normalizer : U ≤ normalizer (H : Set G)
  A_le_U : A ≤ U
  V_le_U : V ≤ U
  A_normal : (A.subgroupOf U).Normal
  natCard_A : Nat.card A = p
  sup_eq : A ⊔ V = U
  inf_eq : A ⊓ V = ⊥
  A_le_centralizer : A ≤ centralizer (H : Set G)
  dvd_natCard_V : p ∣ Nat.card V
  exists_sylow_isMulCommutative : ∃ S : Sylow p U, IsMulCommutative (S : Subgroup U)
  centralizer_inf_eq_bot : ∀ v ∈ V, v ≠ 1 → H ⊓ centralizer ({v} : Set G) = ⊥

namespace IsSplitCentralizingPrimeKernel

variable (hk : IsSplitCentralizingPrimeKernel p H U A V)

include hk

theorem subgroupOf_sup_eq_top : A.subgroupOf U ⊔ V.subgroupOf U = ⊤ := by
  rw [← Subgroup.subgroupOf_sup hk.A_le_U hk.V_le_U, hk.sup_eq, Subgroup.subgroupOf_self]

theorem subgroupOf_inf_eq_bot : A.subgroupOf U ⊓ V.subgroupOf U = ⊥ := by
  have hc : (A ⊓ V).subgroupOf U = A.subgroupOf U ⊓ V.subgroupOf U :=
    Subgroup.comap_inf A V U.subtype
  rw [← hc, hk.inf_eq, Subgroup.bot_subgroupOf]

theorem isComplement' : (A.subgroupOf U).IsComplement' (V.subgroupOf U) := by
  have := hk.A_normal
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr
    hk.subgroupOf_inf_eq_bot) ?_
  rw [← Subgroup.normal_mul, hk.subgroupOf_sup_eq_top, Subgroup.coe_top]

theorem V_le_normalizer_A : V ≤ normalizer (A : Set G) :=
  haveI := hk.A_normal
  hk.V_le_U.trans (Subgroup.le_normalizer_of_normal_subgroupOf hk.A_le_U)

theorem coe_eq_mul : (U : Set G) = (A : Set G) * (V : Set G) := by
  rw [← hk.sup_eq, Subgroup.coe_mul_of_right_le_normalizer_left A V hk.V_le_normalizer_A]

theorem isMulCommutative : IsMulCommutative A :=
  isMulCommutative_of_natCard_eq_prime hk.prime hk.natCard_A

theorem inf_centralizer_eq {h : G} (hh : h ∈ H) (hh1 : h ≠ 1) :
    U ⊓ centralizer ({h} : Set G) = A := by
  refine le_antisymm (fun u hu => ?_) (le_inf hk.A_le_U fun a ha => ?_)
  · obtain ⟨huU, huc⟩ := hu
    obtain ⟨a, ha, v, hv, rfl⟩ := Set.mem_mul.mp (hk.coe_eq_mul ▸ huU)
    have hac : a * h = h * a := Subgroup.mem_centralizer_singleton_iff.mp
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hh) (hk.A_le_centralizer ha))
    have huc' : a * v * h = h * (a * v) := Subgroup.mem_centralizer_singleton_iff.mp huc
    have hvc : v * h = h * v :=
      mul_left_cancel (a := a) (by rw [← mul_assoc, huc', ← mul_assoc, ← hac, mul_assoc])
    have hv1 : v = 1 := by
      by_contra hv1
      have hmemi : h ∈ H ⊓ centralizer ({v} : Set G) :=
        ⟨hh, Subgroup.mem_centralizer_singleton_iff.mpr hvc.symm⟩
      rw [hk.centralizer_inf_eq_bot v hv hv1] at hmemi
      exact hh1 (by simpa using hmemi)
    simpa [hv1] using ha
  · exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hh) (hk.A_le_centralizer ha)

theorem exponent_eq [Finite G] : Monoid.exponent V = Monoid.exponent U := by
  have := hk.A_normal
  have : Fact p.Prime := ⟨hk.prime⟩
  obtain ⟨S, hS⟩ := hk.exists_sylow_isMulCommutative
  have hAcard : Nat.card (A.subgroupOf U) = p := by
    rw [natCard_subgroupOf_eq hk.A_le_U, hk.natCard_A]
  have hpV : p ∣ Nat.card (V.subgroupOf U) := by
    rw [natCard_subgroupOf_eq hk.V_le_U]; exact hk.dvd_natCard_V
  have key := exponent_eq_of_sylow_isMulCommutative S hAcard hk.subgroupOf_sup_eq_top
    hk.subgroupOf_inf_eq_bot hpV hS
  rwa [Monoid.exponent_eq_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hk.V_le_U)] at key

theorem isMulCommutative_and_normal_and_inf_centralizer_eq_and_exponent_eq [Finite G] :
    IsMulCommutative A ∧ (A.subgroupOf U).Normal ∧
      (∀ h ∈ H, h ≠ 1 → U ⊓ centralizer ({h} : Set G) = A) ∧
      Monoid.exponent V = Monoid.exponent U :=
  ⟨hk.isMulCommutative, hk.A_normal, fun _ hh hh1 => hk.inf_centralizer_eq hh hh1, hk.exponent_eq⟩

end IsSplitCentralizingPrimeKernel

end

end CFSG.FeitThompson
