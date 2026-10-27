module

public import CFSG.GH74.GLS.Stage1.Thm4.Defs
import CFSG.GH74.GLS.NT44.RigidExhaustion
import CFSG.GH74.GLS.Bg.Pu5.BalBBasic
import CFSG.GH74.GLS.Stage1.Thm4.P92Pump
import CFSG.GH74.GLS.NT44.RigidFamily
public import CFSG.GH74.GLS.TwoThin.Basic
public import CFSG.GH74.GLS.TwoThin.Struct

public section

namespace CFSG.GH74.GLS.NT44

open Subgroup CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm4
  CFSG.GH74.GLS.Stage1.Thm4.P92 CFSG.GH74.GLS.C3.Layer1.PumpCalc
  CFSG.GH74.GLS.C3.Layer1.PumpRigid CFSG.GH74.GLS.TwoThin

theorem rigid_product_coverage
    {G : Type} [Group G] [Finite G] {fullQ : Type} [Group fullQ] {x t : G}
    (J : Subgroup G → Subgroup G)
    (hxY : x ∈ centralizer ({t} : Set G))
    (hJ : ∀ K ∈ RigidSet fullQ x, PumpUpLT 2 x K t (J K))
    (hcard : (RigidSet fullQ t).ncard ≤ (RigidSet fullQ x).ncard) :
    ((Kz fullQ x ⊓ Kz fullQ t) ⊔ pPrimeCoreOf 2 (Kz fullQ x) = Kz fullQ x) ∧
      ((Kz fullQ x ⊓ Kz fullQ t) ⊔ pPrimeCoreOf 2 (Kz fullQ t) = Kz fullQ t) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hrig, hEq, hex⟩ := rigid_pump_exhaustion J hxY hJ hcard
  have hstep : ∀ K ∈ RigidSet fullQ x,
      (K ≤ (Kz fullQ x ⊓ Kz fullQ t) ⊔ pPrimeCoreOf 2 (Kz fullQ x)) ∧
        (J K ≤ (Kz fullQ x ⊓ Kz fullQ t) ⊔ pPrimeCoreOf 2 (Kz fullQ t)) := by
    intro K hK
    obtain ⟨Λ, hΛ⟩ := exists_stepData' hK.1 (hJ K hK) hxY
    have hΛlam : IsLam x t K Λ := hΛ.lam
    obtain ⟨hΛJK, hbar⟩ := (hex K hK).2 Λ hΛlam
    have hKleP : K ≤ Kz fullQ x := le_sSup hK
    have hPleCx : Kz fullQ x ≤ centralizer ({x} : Set G) := kz_le_centralizer
    have hRleCt : Kz fullQ t ≤ centralizer ({t} : Set G) := kz_le_centralizer
    have hJKrig : IsRigidOfType fullQ t (J K) := hrig K hK
    have hJKleR : J K ≤ Kz fullQ t := le_sSup hJKrig
    have hJKleCt : J K ≤ centralizer ({t} : Set G) := hJKrig.1.1.2.2.1
    have hΛleK : Λ ≤ K := fun a ha => (hΛlam.le ha).1
    have hΛD : Λ ≤ Kz fullQ x ⊓ Kz fullQ t :=
      le_inf (hΛleK.trans hKleP) (hΛJK.trans hJKleR)
    have hOKleOP : pPrimeCoreOf 2 K ≤ pPrimeCoreOf 2 (Kz fullQ x) :=
      Bg.Pu5.pPrimeCoreOf_le_of_isPCompIn
        ⟨hKleP, CFSG.ComponentClassification.CatalogueBPrimeJoin.pComponent_subgroupOf_of_le
          hKleP hPleCx hK.1.1.2.2.2⟩
    have hOJKleOR : pPrimeCoreOf 2 (J K) ≤ pPrimeCoreOf 2 (Kz fullQ t) :=
      Bg.Pu5.pPrimeCoreOf_le_of_isPCompIn
        ⟨hJKleR, CFSG.ComponentClassification.CatalogueBPrimeJoin.pComponent_subgroupOf_of_le
          hJKleR hRleCt hJKrig.1.1.2.2.2⟩
    refine ⟨?_, ?_⟩
    · intro k hk
      obtain ⟨l, hl, o, ho, hko⟩ := hΛlam.cover k hk
      rw [hko]
      exact Subgroup.mul_mem_sup (hΛD hl) (hOKleOP ho)
    · intro j hj
      have hjY : j ∈ centralizer ({t} : Set G) := hJKleCt hj
      have hmem : barMk ↥(centralizer ({t} : Set G)) ⟨j, hjY⟩ ∈ bar t (J K) :=
        ⟨⟨j, hjY⟩, Subgroup.mem_subgroupOf.mpr hj, rfl⟩
      rw [← hbar] at hmem
      obtain ⟨l, hl, hlj⟩ := hmem
      have hlΛ : (l : G) ∈ Λ := Subgroup.mem_subgroupOf.mp hl
      have hlJK : (l : G) ∈ J K := hΛJK hlΛ
      let o : G := (l : G)⁻¹ * j
      have hoJK : o ∈ J K := (J K).mul_mem ((J K).inv_mem hlJK) hj
      have hoY : o ∈ centralizer ({t} : Set G) :=
        (centralizer ({t} : Set G)).mul_mem ((centralizer ({t} : Set G)).inv_mem l.2) hjY
      have hpi : barMk ↥(centralizer ({t} : Set G)) ⟨o, hoY⟩ = 1 := by
        have h1 : (⟨o, hoY⟩ : ↥(centralizer ({t} : Set G))) =
            l⁻¹ * ⟨j, hjY⟩ := by
          apply Subtype.ext
          rfl
        rw [h1, map_mul, map_inv, hlj, inv_mul_cancel]
      have hoO : o ∈ pPrimeCoreOf 2 (J K) :=
        mem_pPrimeCoreOf_of_barMk_eq_one' hJKleCt hoJK hoY hpi
      have hjo : j = (l : G) * o := by
        show j = (l : G) * ((l : G)⁻¹ * j)
        group
      rw [hjo]
      exact Subgroup.mul_mem_sup (hΛD hlΛ) (hOJKleOR hoO)
  refine ⟨le_antisymm ?_ ?_, le_antisymm ?_ ?_⟩
  · exact sup_le inf_le_left (TwoThin.pPrimeCoreOf_le _)
  · conv_lhs => rw [show Kz fullQ x = sSup (RigidSet fullQ x) from rfl]
    exact sSup_le fun K hK => (hstep K hK).1
  · exact sup_le inf_le_right (TwoThin.pPrimeCoreOf_le _)
  · conv_lhs => rw [show Kz fullQ t = sSup (RigidSet fullQ t) from rfl]
    exact sSup_le fun L hL => by
      rw [hEq] at hL
      obtain ⟨K, hK, rfl⟩ := hL
      exact (hstep K hK).2

end CFSG.GH74.GLS.NT44

end
