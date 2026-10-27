module

public import CFSG.CGT.M24R.WrapTop
public import CFSG.CGT.M24R.N8Cert
public import CFSG.CGT.M24R.L2Cert
public import CFSG.CGT.M24R.R3
public import CFSG.CGT.M24R.M24PresCert

public section

namespace CFSG.CGT.M24R

open CFSG.CGT.Timmesfeld75 CFSG.CGT.M24S CFSG.Blueprint

theorem r24Statement : R24Statement :=
  r24Statement_of_card_le ⟨finite_pg_relsN8Ten, card_pg_relsN8Ten_le⟩

theorem isSporadic_m24_of_type4_of_holt
    (hHolt : CFSG.Holt.H78.HoltTheorem1) {G : Type} [Group G]
    [Finite G] [IsSimpleGroup G] {T H : Subgroup G} (h : Hyp T H) (hL : LocalFacts T H)
    (hC : Subgroup.centralizer (T : Set G) = T) (hcompl : HasComplement T H) {x g : G}
    (hxN : x ∈ Subgroup.normalizer (T : Set G)) (hxT : x ∉ T) (hxg : x ∈ conjSubgroup g T)
    (hcx : Nat.card ↥(T ⊓ Subgroup.centralizer ({x} : Set G)) = 4) :
    NativeSporadic.IsSporadic G .M24 :=
  isSporadic_m24_of_type4 n8Statement l2Statement8_of_n8 r3Statement r24Statement hHolt h hL hC
    hcompl hxN hxT hxg hcx

end CFSG.CGT.M24R
