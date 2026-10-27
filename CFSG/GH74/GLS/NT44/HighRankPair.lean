module

public import CFSG.GH74.GLS.Stage1.Thm4.Defs
public import CFSG.GH74.GLS.C3.Layer1.Th2Defs
import CFSG.GH74.GLS.NT44.InvolutionCore
import CFSG.GH74.GLS.NT44.CoreBalance

set_option autoImplicit false

public section

namespace CFSG.GH74.GLS.NT44

open CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm4

theorem isKBal_two_and_isWeakKBal_one_of_le_rigid_center_sylow
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    {fullQ : Type} [Group fullQ]
    {x : G} {W : Subgroup G} {A : Subgroup G}
    (hnonab : ∃ u v : G, u * v ≠ v * u)
    (hx2 : orderOf x = 2)
    (hmax : ∀ z : G, orderOf z = 2 →
      (RigidSet fullQ z).ncard ≤ (RigidSet fullQ x).ncard)
    (hW : CFSG.ABGLocalTools.IsSylowOf 2 W (zStar (Kz fullQ x)))
    (hA : CFSG.IsElementaryAbelian 2 A)
    (hAW : A ≤ W) :
    CFSG.GH74.GLS.IsKBal 2 A ∧ CFSG.GH74.GLS.IsWeakKBal 1 A := by
  classical
  have hcore : ∀ a ∈ A, a ≠ 1 →
      A ≤ (CFSG.Op_p'p 2 ↥(Subgroup.centralizer ({a} : Set G))).map
        (Subgroup.centralizer ({a} : Set G)).subtype := by
    intro a ha ha1
    have hfact2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hapow : a ^ 2 = 1 :=
      @CFSG.elemPow_eq_one_of_isElementaryAbelian 2 G _ A hA a ha
    have ha2 : orderOf a = 2 := orderOf_eq_prime (p := 2) (hp := hfact2) hapow ha1
    have hWcore :=
      CFSG.GH74.GLS.NT44.le_core_centralizer_of_mem_rigid_center_sylow
        (G := G) (fullQ := fullQ) (x := x) (W := W) (a := a)
        hnonab hx2 hmax hW (hAW ha) ha2
    exact hAW.trans hWcore
  have hstrong : CFSG.GH74.GLS.IsKBal 1 A :=
    CFSG.GH74.GLS.NT44.isKBal_one_of_le_core_centralizers hcore
  refine ⟨?_, ?_⟩
  · intro D hD a ha ha1
    have hD1 : IsE 1 A D :=
      ⟨hD.1, hD.2.1, le_trans (by norm_num : 1 ≤ 2) hD.2.2⟩
    exact hstrong D hD1 a ha ha1
  · intro D hD a ha ha1 c hc b hb
    let C : Subgroup G := Subgroup.centralizer ({a} : Set G)
    let O : Subgroup G := (CFSG.pPrimeCore 2 C).map C.subtype
    have hcO : c ∈ O := hstrong D hD a ha ha1 hc
    have hbOp : b ∈ (CFSG.Op_p'p 2 ↥C).map C.subtype := hcore a ha ha1 hb
    have hbC : b ∈ C := by
      obtain ⟨b', -, rfl⟩ := Subgroup.mem_map.mp hbOp
      exact b'.2
    have hcinv : c⁻¹ ∈ O := O.inv_mem hcO
    obtain ⟨y, hy, hyc⟩ := Subgroup.mem_map.mp hcinv
    change (y : G) = c⁻¹ at hyc
    let b' : C := ⟨b, hbC⟩
    have hconjCore : b' * y * b'⁻¹ ∈ CFSG.pPrimeCore 2 C :=
      CFSG.pPrimeCore_normal.conj_mem y hy b'
    have hconj : b * c⁻¹ * b⁻¹ ∈ O := by
      refine ⟨b' * y * b'⁻¹, hconjCore, ?_⟩
      simp [b', hyc]
    have hprod : c * (b * c⁻¹ * b⁻¹) ∈ O := O.mul_mem hcO hconj
    change c * b * c⁻¹ * b⁻¹ ∈ O
    simpa only [mul_assoc] using hprod

end CFSG.GH74.GLS.NT44

end
