module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerNonsolv1
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerCore
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerNilp
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.QuasithinUnique.Setup.Layer

open CFSG.QuasithinUnique.Setup.Offender CFSG.Quasithin.B6 CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Setup
open scoped commutatorElement

universe v

variable {k : Type*} [Field k] {V : Type v} [AddCommGroup V] [Module k V]
variable [CharP k 2] [Finite V]

theorem offender_centralizes_core {H M : Subgroup (V ≃ₗ[k] V)} (hMH : M ≤ H)
    (hCrad : kerIn (M.subgroupOf H) ⊤ = CFSG.solvableRadical ↥H)
    (hCnil : Group.IsNilpotent ↥(kerIn (M.subgroupOf H) ⊤))
    (hCodd : Odd (Nat.card ↥(kerIn (M.subgroupOf H) ⊤))) :
    ∀ A : Subgroup (V ≃ₗ[k] V), IsMinOffender H A → ⁅kerIn M H, A⁆ = ⊥ := by
  intro A hA
  by_contra hcomm
  have : Finite (V ≃ₗ[k] V) := finite_linearEquiv
  have hFH : kerIn M H ≤ H := kerIn_le_of_le hMH
  have hsub : (kerIn M H).subgroupOf H = kerIn (M.subgroupOf H) ⊤ :=
    (kerIn_subgroupOf_top M H).symm
  have hFnorm : ((kerIn M H).subgroupOf H).Normal := by
    rw [hsub]
    exact kerIn_top_normal _
  have e : ↥((kerIn M H).subgroupOf H) ≃* ↥(kerIn M H) := Subgroup.subgroupOfEquivOfLe hFH
  have : Group.IsNilpotent ↥(kerIn M H) := by
    refine (Group.isNilpotent_congr e).1 ?_
    rw [hsub]
    exact hCnil
  have hFodd : Odd (Nat.card ↥(kerIn M H)) := by
    rw [← Nat.card_congr e.toEquiv, hsub]
    exact hCodd
  obtain ⟨-, -, -, -, -, -, -, -, -, -, ⟨ι, hfin, g, Fg⟩, hmain⟩ :=
    nilpotent_offender_natural_S3_factors hFH hFnorm hFodd hA.1 hA.2.2.1 hA.2.1 hA.2.2.2.1
      hA.2.2.2.2 hcomm
  have hN := (hmain g Fg).toNatural
  have hAB : A ≤ natB H (kerIn M H) A :=
    (le_sup_right : A ≤ ⁅kerIn M H, A⁆ ⊔ A).trans hN.LA_le_B
  have hsolv : Group.IsSolvable ↥(natB H (kerIn M H) A) := by
    refine isSolvable_of_commutator_comm _ ?_
    rw [hN.B_derived]
    intro x hx y hy
    have := hN.D_elem.toIsMulCommutative.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
    exact congrArg Subtype.val this
  have e' : ↥((natB H (kerIn M H) A).subgroupOf H) ≃* ↥(natB H (kerIn M H) A) :=
    Subgroup.subgroupOfEquivOfLe hN.B_le
  have hsolv' : Group.IsSolvable ↥((natB H (kerIn M H) A).subgroupOf H) :=
    Group.isSolvable_of_isSolvable_injective (f := e'.toMonoidHom) e'.injective
  have hle : (natB H (kerIn M H) A).subgroupOf H ≤ CFSG.solvableRadical ↥H :=
    le_sSup ⟨hN.B_normal, hsolv'⟩
  rw [← hCrad] at hle
  have hAle : A.subgroupOf H ≤ kerIn (M.subgroupOf H) ⊤ :=
    fun x hx => hle (hAB hx)
  have h1 : Nat.card ↥(A.subgroupOf H) ∣ Nat.card ↥(kerIn (M.subgroupOf H) ⊤) :=
    Subgroup.card_dvd_of_le hAle
  have h2 : Nat.card ↥(A.subgroupOf H) = Nat.card ↥A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA.1).toEquiv
  have hel : CFSG.IsElementaryAbelian 2 ↥A := hA.2.2.1
  have h3 : 2 ∣ Nat.card ↥A := by
    rcases (CFSG.IsElementaryAbelian.isPGroup 2 A).card_eq_or_dvd with h4 | h4
    · exact absurd ((Subgroup.card_eq_one).1 h4) hA.2.1
    · exact h4
  rw [h2] at h1
  exact (Nat.not_even_iff_odd.2 hCodd) (even_iff_two_dvd.2 (h3.trans h1))

end CFSG.QuasithinUnique.Setup.Layer
