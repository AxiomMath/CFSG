module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.GH73.ComponentSplit
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.GH73.PerfectGroups
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.GH73.SylowData

public section

namespace CFSG.EvenSporadicStandard.HNRecog.GH73

open CFSG.LocalAnalysis.ComponentInitial

theorem caseB {X : Type} [Group X] [Finite X] [Group.IsPerfect X]
    (hK : CFSG.SectionRank.IsKGroupCat X) (hS : SchreierFor CFSG.Blueprint.Catalog)
    (hZ : Subgroup.center X = ⊥) (D : A8SylowData X) (hE : CFSG.layer X ≠ ⊥) :
    IsSimpleGroup X := by
  classical
  obtain ⟨L, hL⟩ : ∃ L : Subgroup X, CFSG.IsComponent L := by
    by_contra h
    push Not at h
    exact hE (CFSG.LocalCores.layer_eq_bot_of_forall h)
  obtain ⟨hLnorm, hLsimple, C, hCnorm, hdisj, hsup, hcomm⟩ :=
    component_splits hK hS D.gen_four hZ L hL
  haveI : L.Normal := hLnorm
  haveI : C.Normal := hCnorm
  haveI : IsSimpleGroup ↥L := hLsimple
  haveI : Group.IsPerfect ↥L := hL.1.1
  have hLCbot : L ⊓ C = ⊥ := disjoint_iff.mp hdisj
  have hLC : ⁅L, C⁆ = ⊥ := Subgroup.commutator_eq_bot_of_disjoint hdisj
  have hCL : ⁅C, L⁆ = ⊥ := Subgroup.commutator_comm L C ▸ hLC
  have hcommtop : (⊤ : Subgroup X) = ⁅L, L⁆ ⊔ ⁅C, C⁆ := by
    have hperf : ⁅(⊤ : Subgroup X), ⊤⁆ = ⊤ := Group.IsPerfect.commutator_eq_top
    rw [← hsup] at hperf
    rw [Subgroup.commutator_sup_right L C (L ⊔ C)] at hperf
    rw [Subgroup.commutator_sup_left L L C, Subgroup.commutator_sup_left C L C,
      hLC, hCL] at hperf
    have h1 : L ⊔ C = ⁅L, L⁆ ⊔ ⁅C, C⁆ := by simpa using hperf.symm
    rwa [hsup] at h1
  have hsup2 : L ⊔ ⁅C, C⁆ = ⊤ := by
    apply le_antisymm le_top
    rw [hcommtop]
    refine sup_le ?_ le_sup_right
    exact le_trans (Subgroup.commutator_le_left L L) le_sup_left
  have hDleC : ⁅C, C⁆ ≤ C := Subgroup.commutator_le_left C C
  have hCleD : C ≤ ⁅C, C⁆ := by
    intro c hc
    have hcmem : c ∈ L ⊔ ⁅C, C⁆ := by rw [hsup2]; trivial
    obtain ⟨l, hl, d, hd, hld⟩ :=
      (Subgroup.mem_sup_of_normal_left (s := L) (t := ⁅C, C⁆)).mp hcmem
    have hlC : l ∈ C := by
      have hl_eq : l = c * d⁻¹ := by rw [← hld]; group
      rw [hl_eq]
      exact C.mul_mem hc (C.inv_mem (hDleC hd))
    have hlbot : l = 1 := by
      have : l ∈ L ⊓ C := ⟨hl, hlC⟩
      rw [hLCbot] at this
      exact Subgroup.mem_bot.mp this
    rw [hlbot, one_mul] at hld
    rwa [← hld]
  have hCperfect : Group.IsPerfect ↥C :=
    Subgroup.isPerfect_iff.mpr (le_antisymm hDleC hCleD)
  have hCbot : C = ⊥ := by
    by_contra hCne
    haveI : Group.IsPerfect ↥C := hCperfect
    haveI : Nontrivial ↥C := (Subgroup.nontrivial_iff_ne_bot C).mpr hCne
    have hL4 : 4 ∣ Nat.card ↥L := perfect_four_dvd_card
    have hC4 : 4 ∣ Nat.card ↥C := perfect_four_dvd_card
    have hL2 : 2 ∣ Nat.card ↥L := dvd_trans (by norm_num : 2 ∣ 4) hL4
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 2 hL2
    have hgX : orderOf (g : X) = 2 := (Subgroup.orderOf_coe g).trans hg
    have hgne : g ≠ 1 := by
      intro h1; rw [h1, orderOf_one] at hg; norm_num at hg
    let PL : Subgroup X := Subgroup.zpowers (g : X)
    have hPLpg : IsPGroup 2 PL :=
      IsPGroup.iff_card.mpr ⟨1, by rw [Nat.card_zpowers, hgX, pow_one]⟩
    have hPL_le_L : PL ≤ L := Subgroup.zpowers_le.mpr g.2
    have hC2 : 2 ∣ Nat.card ↥C := dvd_trans (by norm_num : 2 ∣ 4) hC4
    obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' (G := ↥C) 2 hC2
    have hkX : orderOf (k : X) = 2 := (Subgroup.orderOf_coe k).trans hk
    let PC : Subgroup X := Subgroup.zpowers (k : X)
    have hPCpg : IsPGroup 2 PC :=
      IsPGroup.iff_card.mpr ⟨1, by rw [Nat.card_zpowers, hkX, pow_one]⟩
    have hPC_le_C : PC ≤ C := Subgroup.zpowers_le.mpr k.2
    have hPLnorm : PL ≤ Subgroup.normalizer PC := by
      calc PL ≤ L := hPL_le_L
        _ ≤ Subgroup.centralizer C := by
              intro l hl
              rw [Subgroup.mem_centralizer_iff]
              intro c hc
              exact (hcomm l hl c hc).symm
        _ ≤ Subgroup.centralizer PC :=
              Subgroup.centralizer_le (show (PC : Set X) ⊆ C from hPC_le_C)
        _ ≤ Subgroup.normalizer PC := Subgroup.centralizer_le_normalizer (PC : Set X)
    have hPpg : IsPGroup 2 (PL ⊔ PC : Subgroup X) :=
      IsPGroup.to_sup_of_normal_right' hPLpg hPCpg hPLnorm
    obtain ⟨S, hPS⟩ := hPpg.exists_le_sylow
    have hgS : (g : X) ∈ (S : Subgroup X) :=
      hPS (Subgroup.mem_sup_left (Subgroup.mem_zpowers (g : X)))
    have hhS : (k : X) ∈ (S : Subgroup X) :=
      hPS (Subgroup.mem_sup_right (Subgroup.mem_zpowers (k : X)))
    haveI : Group.IsNilpotent ↥(S : Subgroup X) :=
      IsPGroup.isNilpotent (show IsPGroup 2 (S : Subgroup X) from S.isPGroup')
    have hLSL : L.subgroupOf (S : Subgroup X) ≠ ⊥ := by
      refine Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨⟨⟨(g : X), hgS⟩, g.2⟩, ?_⟩
      intro hEq
      have h1 : (⟨(g : X), hgS⟩ : ↥(S : Subgroup X)) = 1 := Subtype.ext_iff.mp hEq
      have h2 : (g : X) = 1 := Subtype.ext_iff.mp h1
      exact hgne (Subtype.ext h2)
    have hCSL : C.subgroupOf (S : Subgroup X) ≠ ⊥ := by
      refine Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨⟨⟨(k : X), hhS⟩, k.2⟩, ?_⟩
      intro hEq
      have hkne : k ≠ 1 := by
        intro h1; rw [h1, orderOf_one] at hk; norm_num at hk
      have h1 : (⟨(k : X), hhS⟩ : ↥(S : Subgroup X)) = 1 := Subtype.ext_iff.mp hEq
      have h2 : (k : X) = 1 := Subtype.ext_iff.mp h1
      exact hkne (Subtype.ext h2)
    have hAL : (L.subgroupOf (S : Subgroup X) ⊓ Subgroup.center ↥(S : Subgroup X)) ≠ ⊥ :=
      Group.IsNilpotent.inf_center_ne_bot_of_normal hLSL
    have hAC : (C.subgroupOf (S : Subgroup X) ⊓ Subgroup.center ↥(S : Subgroup X)) ≠ ⊥ :=
      Group.IsNilpotent.inf_center_ne_bot_of_normal hCSL
    obtain ⟨zL, hzL⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hAL
    obtain ⟨zC, hzC⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hAC
    have hzLc : (zL : ↥(S : Subgroup X)) ∈ Subgroup.center ↥(S : Subgroup X) := zL.2.2
    have hzCc : (zC : ↥(S : Subgroup X)) ∈ Subgroup.center ↥(S : Subgroup X) := zC.2.2
    have hzLL : ((zL : ↥(S : Subgroup X)) : X) ∈ L := zL.2.1
    have hzCC : ((zC : ↥(S : Subgroup X)) : X) ∈ C := zC.2.1
    let zLc : Subgroup.center ↥(S : Subgroup X) := ⟨(zL : ↥(S : Subgroup X)), hzLc⟩
    let zCc : Subgroup.center ↥(S : Subgroup X) := ⟨(zC : ↥(S : Subgroup X)), hzCc⟩
    have hzLne1 : zLc ≠ 1 := by
      intro hEq
      apply hzL
      have h1 : (zL : ↥(S : Subgroup X)) = 1 := Subtype.ext_iff.mp hEq
      exact Subtype.ext h1
    have hzCne1 : zCc ≠ 1 := by
      intro hEq
      apply hzC
      have h1 : (zC : ↥(S : Subgroup X)) = 1 := Subtype.ext_iff.mp hEq
      exact Subtype.ext h1
    have hzLneC : zLc ≠ zCc := by
      intro hEq
      have hv : (zL : ↥(S : Subgroup X)) = (zC : ↥(S : Subgroup X)) :=
        Subtype.ext_iff.mp hEq
      have hx : ((zL : ↥(S : Subgroup X)) : X) = ((zC : ↥(S : Subgroup X)) : X) :=
        congrArg Subtype.val hv
      have hmem : ((zL : ↥(S : Subgroup X)) : X) ∈ L ⊓ C := ⟨hzLL, hx ▸ hzCC⟩
      have hx1 : ((zL : ↥(S : Subgroup X)) : X) = 1 := by
        have hbot : ((zL : ↥(S : Subgroup X)) : X) ∈ (⊥ : Subgroup X) := by
          rw [← hLCbot]; exact hmem
        exact Subgroup.mem_bot.mp hbot
      exact hzLne1 (Subtype.ext (Subtype.ext hx1))
    let f : Fin 3 → Subgroup.center ↥(S : Subgroup X) := ![zLc, zCc, 1]
    have hfinj : Function.Injective f := by
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp_all [f, hzLne1, hzCne1, hzLneC, Ne.symm hzLneC]
    have h3 : 3 ≤ Nat.card (Subgroup.center ↥(S : Subgroup X)) := by
      have := Nat.card_le_card_of_injective f hfinj
      simpa using this
    have h2 : Nat.card (Subgroup.center ↥(S : Subgroup X)) = 2 := D.card_center S
    omega
  have hLtop : L = ⊤ := by rw [← hsup, hCbot, sup_bot_eq]
  have e : ↥L ≃* X := (MulEquiv.subgroupCongr hLtop).trans Subgroup.topEquiv
  exact e.symm.isSimpleGroup

end CFSG.EvenSporadicStandard.HNRecog.GH73
