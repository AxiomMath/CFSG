module

public import CFSG.GH74.GLS.Stage1.Thm4.Defs
public import CFSG.GH74.GLS.C3.Layer1.Defs

import CFSG.GH74.GLS.NT44.RigidFamily
import CFSG.LocalAnalysis.ComponentClassification.PComponentNormalizerEnlargement
import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalCorrespondenceTools

set_option autoImplicit false

public section

namespace CFSG.GH74.GLS.NT44

theorem pLayer_kz_eq_top_and_kBar {G : Type} [Group G] [Finite G] {fullQ : Type}
    [Group fullQ] (x : G) :
    CFSG.pLayer (CFSG.GH74.GLS.Stage1.Thm4.Kz fullQ x) 2 = ⊤ ∧
      CFSG.pLayer (CFSG.GH74.GLS.kBar (CFSG.GH74.GLS.Stage1.Thm4.Kz fullQ x)) 2 = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P : Subgroup G := CFSG.GH74.GLS.Stage1.Thm4.Kz fullQ x
  let C : Subgroup G := Subgroup.centralizer ({x} : Set G)
  have : Finite ↥P := Subtype.finite
  change CFSG.pLayer P 2 = ⊤ ∧ CFSG.pLayer (CFSG.GH74.GLS.kBar P) 2 = ⊤
  have hPC : P ≤ C := by
    dsimp only [P, C]
    exact CFSG.GH74.GLS.NT44.kz_le_centralizer (Q := fullQ) (G := G) (z := x)
  let L : Subgroup G := (CFSG.pLayer P 2).map P.subtype
  have hPL : P ≤ L := by
    dsimp only [P]
    unfold CFSG.GH74.GLS.Stage1.Thm4.Kz
    refine sSup_le fun K hK => ?_
    have hKP : K ≤ P := by
      change K ≤ sSup (CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ x)
      exact le_sSup hK
    have hKsub : CFSG.IsPComponent 2 (K.subgroupOf P) :=
      CFSG.ComponentClassification.CatalogueBPrimeJoin.pComponent_subgroupOf_of_le
        (p := 2) hKP hPC hK.1.1.2.2.2
    have hKle : K.subgroupOf P ≤ CFSG.pLayer P 2 := le_sSup hKsub
    have hmap := Subgroup.map_mono (f := P.subtype) hKle
    rw [Subgroup.map_subgroupOf_eq_of_le hKP] at hmap
    change K ≤ (CFSG.pLayer P 2).map P.subtype
    exact hmap
  have hlayer_top : CFSG.pLayer P 2 = ⊤ := by
    rw [eq_top_iff]
    intro u _
    have huL : (u : G) ∈ L := hPL u.2
    dsimp only [L] at huL
    obtain ⟨v, hv, hvu⟩ := huL
    have hvu' : v = u := Subtype.ext hvu
    simpa [hvu'] using hv
  constructor
  · exact hlayer_top
  · let q : ↥P →* CFSG.GH74.GLS.kBar P :=
      QuotientGroup.mk' (CFSG.pPrimeCore 2 ↥P)
    have hq_surj : Function.Surjective q := by
      dsimp only [q]
      exact QuotientGroup.mk'_surjective (CFSG.pPrimeCore 2 ↥P)
    have hq_ker : q.ker = CFSG.pPrimeCore 2 ↥P := by
      dsimp only [q]
      exact QuotientGroup.ker_mk' (CFSG.pPrimeCore 2 ↥P)
    have hq_odd : ¬ 2 ∣ Nat.card q.ker := by
      rw [hq_ker]
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp
        (CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥P))
    have : Finite (CFSG.GH74.GLS.kBar P) := Finite.of_surjective q hq_surj
    have hmap :=
      CFSG.ComponentClassification.UnbalancingLocal.Correspondence.map_pLayer_of_coprime_kernel
        (p := 2) q hq_surj hq_odd
    have htopmap : (CFSG.pLayer P 2).map q = ⊤ := by
      rw [hlayer_top]
      exact Subgroup.map_top_of_surjective q hq_surj
    exact hmap.symm.trans htopmap

end CFSG.GH74.GLS.NT44

end
