module

public import CFSG.GF2Type.Smith1979.WidthFourKP.Swap.Stab
public import CFSG.GF2Type.Smith1979.WidthFourKP.Swap.Orbits

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4Swap

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S5
  CFSG.Open Subgroup Module

theorem exists_thompsonInput (hHS : HermStabFacts) (hCE : S4.CentralExtInput.{0})
    {G : Type} [Group G] [Finite G] {S : Setting G} {g : G} (hw : S.width = 4)
    (hno : S11.NoA2All S) (H : S4.Hyp4 S g) (C : S4.Cons311 S g) (D : S5.SwapData S g) :
    ∃ x : G, ∃ K Y : Subgroup S.O, ThompsonInput S g x K Y := by
  have W : SwapW4 D := SwapW4.mk' hCE hw hno H C D
  obtain ⟨Q, hQ, hR, hsing, hmin⟩ := SwapW4.exists_form_minus D W
  obtain ⟨x, hxX, hord, hxz, hcl, hxV, hQx, hnotX⟩ :=
    SwapW4.exists_x D W Q hQ hR hsing hmin
  let A : StabData W :=
    { Q := Q
      hQ := hQ
      hR := hR
      hmin := hmin
      v := ⟨S.cl x, hxV⟩
      hv := hQx
      CX := D.Xhat ⊓ SwapW4.stab (S.cl x)
      hCX := fun m => by rw [Subgroup.mem_inf, SwapW4.mem_stab]
      K := (D.Z ⊔ D.W) ⊓ SwapW4.stab (S.cl x)
      hK := fun m => by rw [Subgroup.mem_inf, SwapW4.mem_stab] }
  have h60 : 60 ≤ Nat.card A.K := SwapW4.card_K_ge D W hxX hxV hnotX A.K A.hK
  refine ⟨x, A.K, S.Mbar ⊓ SwapW4.stab (S.cl x), ?_⟩
  exact
    { mem_QG := hxX.1
      mem_Qa := hxX.2
      orderOf_eq := hord
      ne_z := hxz
      cl_ne := hcl
      mem_Y := fun m => by rw [Subgroup.mem_inf, SwapW4.mem_stab]
      quasisimple := SwapW4.isQuasisimple_K W A hHS h60
      subnormal := CFSG.ClassicalInvolution.isSubnormal_inf
        (isSubnormal_sup_of_isComponentOf D.isComponentOf D.isComponentOf_W) _
      le_closure := SwapW4.le_closure_pow_five W A hHS h60
      finrank_le := SwapW4.finrank_le_two W A hHS
      eq_one := SwapW4.eq_one_of_mem_Lbar_of_commute W A hHS h60 }

end CFSG.GF2Type.Smith1979.W4Swap
