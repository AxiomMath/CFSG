module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Basic
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171Trans2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171Facts

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.S171
open scoped commutatorElement

theorem i171_of_facts (G : Type) [Group G] [Finite G] (hType : T171SmallTypeFact)
    (hU42 : I171SmallIsU42Fact) : I171At G := by
  intro B x L hS h4 hchev hKG hid _hcent hTa hex hsmall
  have hcfg : Cfg G 3 B x L := cfg_of_sStar hS h4 hchev hid
  have hmax : MaxG 3 B := maxG_of_isBmax Nat.prime_three hS.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hS.2.2.2.1.1
  obtain ⟨T, hTL, hT2, hBT, hne⟩ := hTa
  have hTC : T ≤ Subgroup.centralizer ({x} : Set G) := hTL.trans hLx
  have hTN : T ≤ Subgroup.normalizer (L : Set G) := hTL.trans Subgroup.le_normalizer
  have hBx : B ≤ Subgroup.centralizer ({x} : Set G) := fun b hb => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact isElemAbelian_commute hS.1.1 hb hS.2.1
  have hLX : L ≤ (L ⊔ B) ⊔ T := le_sup_left.trans le_sup_left
  have hBX : B ≤ (L ⊔ B) ⊔ T := le_sup_right.trans le_sup_left
  have hTX : T ≤ (L ⊔ B) ⊔ T := le_sup_right
  have hxX : x ∈ (L ⊔ B) ⊔ T := hBX hS.2.1
  have hXC : (L ⊔ B) ⊔ T ≤ Subgroup.centralizer ({x} : Set G) := sup_le (sup_le hLx hBx) hTC
  have hXN : (L ⊔ B) ⊔ T ≤ Subgroup.normalizer (L : Set G) :=
    sup_le (sup_le Subgroup.le_normalizer (normalizer_of_innerDiagMarking hid)) hTN
  have hKX : CFSG.Open.IsKGroup ↥((L ⊔ B) ⊔ T) := CFSG.Open.IsKGroup.of_le hKG hXC
  have hLn : (L.subgroupOf ((L ⊔ B) ⊔ T)).Normal := normal_subgroupOf_of_le_normalizer _ hLX hXN
  have hcfgX := cfg_subgroupOf _ hBX hLX hxX hcfg
  have hmaxX := maxG_subgroupOf _ hBX hmax
  have hexX := exists_glaStdSubPre_subgroupOf _ hxX hBX hLX (p := 3) hex
  have hsmallX := small_subgroupOf _ hxX hBX hLX (p := 3) hsmall
  have hTX' := exists_T_subgroupOf _ hxX hTX hBX hLX hTN hTC hT2 hBT hne
  have hi : catalogIs (↥L ⧸ Subgroup.center ↥L) (fun i => S9.isU5two i ∨ S9.isU6two i ∨ S9.isD4two i) :=
    (catalogIs_center_subgroupOf_iff _ hLX).1
      (hType ↥((L ⊔ B) ⊔ T) (B.subgroupOf ((L ⊔ B) ⊔ T)) ⟨x, hxX⟩ (L.subgroupOf ((L ⊔ B) ⊔ T)) hKX hcfgX hLn
        hmaxX hexX hsmallX hTX')
  refine ⟨hi, fun D K hpre => ?_⟩
  obtain ⟨y, hyD, hyx⟩ := exists_y Nat.prime_three hcfg.ne_one hpre
  have hcomp : IsComponentOf K (L ⊓ Subgroup.centralizer ({y} : Set G)) := by
    rw [← L_cs_eq Nat.prime_three hcfg.ne_one hpre hyD hyx hLx]
    exact hpre.2.2.2.2.2.1
  have hy3 : y ^ 3 = 1 := hpre.2.1.2 y hyD
  have hidy : InnerDiagMarking (Subgroup.zpowers y) L :=
    innerDiagMarking_mono hid (Subgroup.zpowers_le.2 (hpre.1 hyD))
  exact (hU42 G L K y hcfg.qs hi hidy hy3 hcomp (hsmall D K hpre)).1

end CFSG.LocalAnalysis.GLTheoremA.T171

end
