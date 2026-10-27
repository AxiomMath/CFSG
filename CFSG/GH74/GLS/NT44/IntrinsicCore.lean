module

public import CFSG.GH74.GLS.Basic

import CFSG.GH74.GLS.Stage1.Thm4.Alt51Q1

public section

set_option autoImplicit false

namespace CFSG.GH74.GLS.NT44

theorem le_Op_p'p_of_le_zStar {G : Type} [Group G] {W R : Subgroup G}
    (hW2 : IsPGroup 2 W) (hWZ : W ≤ CFSG.GH74.GLS.zStar R) :
    W ≤ (CFSG.Op_p'p 2 ↥R).map R.subtype := by
  intro w hw
  have hWR : W ≤ R := fun x hx => (hWZ hx).1
  let A : Subgroup R := W.subgroupOf R
  let q : R →* (R ⧸ CFSG.pPrimeCore 2 R) :=
    QuotientGroup.mk' (CFSG.pPrimeCore 2 R)
  let U : Subgroup (R ⧸ CFSG.pPrimeCore 2 R) := A.map q
  have hA2 : IsPGroup 2 A := hW2.comap_subtype
  have hU2 : IsPGroup 2 U := hA2.map q
  have hUc : U ≤ Subgroup.center (R ⧸ CFSG.pPrimeCore 2 R) := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    have hz : (a : G) ∈ CFSG.GH74.GLS.zStar R :=
      hWZ (Subgroup.mem_subgroupOf.mp ha)
    have hc :=
      (CFSG.GH74.GLS.Stage1.Thm4.Alt51.mem_zStar_iff_hat_mem_center (K := R) a).1 hz
    change QuotientGroup.mk' (CFSG.pPrimeCore 2 R) a ∈
      Subgroup.center (R ⧸ CFSG.pPrimeCore 2 R)
    simpa only [CFSG.GH74.GLS.Stage1.Thm2.Recip.hatMk,
      CFSG.GH74.GLS.Stage1.Thm3.Sec5.HatT] using hc
  have hUn : U.Normal := Subgroup.normal_of_le_center hUc
  have hUp : U ≤ CFSG.pCore 2 (R ⧸ CFSG.pPrimeCore 2 R) := by
    rw [CFSG.pCore]
    exact le_sSup ⟨hUn, hU2⟩
  let r : R := ⟨w, hWR hw⟩
  have hrA : r ∈ A := by
    change (r : G) ∈ W
    exact hw
  have hmemU : q r ∈ U := Subgroup.mem_map.mpr ⟨r, hrA, rfl⟩
  have hcore : q r ∈ CFSG.pCore 2 (R ⧸ CFSG.pPrimeCore 2 R) := hUp hmemU
  have hr : r ∈ CFSG.Op_p'p 2 R := by
    rw [CFSG.Op_p'p]
    change q r ∈ CFSG.pCore 2 (R ⧸ CFSG.pPrimeCore 2 R)
    exact hcore
  exact Subgroup.mem_map.mpr ⟨r, hr, rfl⟩

end CFSG.GH74.GLS.NT44

end
