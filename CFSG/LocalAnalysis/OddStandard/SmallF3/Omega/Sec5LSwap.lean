module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5InputsB5
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BSwCore
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BSwCtx
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BSwXfer
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5XSwFin
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5XSwSound
public import Certificates.Certificate442265

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.LieType.Multipliers.U43 CFSG.Quasithin.H13.U43

theorem asc82FactSwap6_of_certs :
    Asc82FactSwap6 := by
  intro G _ _ L z K₁ K₂ hL hO h₁ h₂ hne hcomm hprod
  obtain ⟨τ, hτ⟩ := sw_exists_tau hL hO
  have hchk := Certificates.certificate442265
  have hx : orderOf xElt = 2 := sw_orderOf_xElt_of_check hchk.1
  have hF : SwFinite := swFinite_of_tables hx (sw_tables_of_check hchk.1)
  have hOddC : SwOddCent := sw_oddCent_of_check hchk.2
  have hK₁L : K₁ ≤ L := fun k hk => (h₁.2.1 hk).1
  have hK₂L : K₂ ≤ L := fun k hk => (h₂.2.1 hk).1
  have hzL : z ∈ L := (h₁.2.1 h₁.1).1
  have S : SwSetup (K₁.subgroupOf L) (K₂.subgroupOf L) (⟨z, hzL⟩ : ↥L) :=
    swSetup_of_pockets h₁ h₂ hcomm hprod
  obtain ⟨c, hc, hconj⟩ := sw_core hτ x0OneClass hx hF hOddC S
  exact ⟨(c : G), sw_mem_cent_coe hzL hc, sw_conj_coe hK₁L hK₂L hconj⟩

end CFSG.OddStandard.SmallF3.Omega
