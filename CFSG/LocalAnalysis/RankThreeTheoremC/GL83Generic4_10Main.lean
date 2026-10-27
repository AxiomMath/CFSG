module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_10Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_10Group
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_10Lemmas
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_10Core
import CFSG.GH74.Uniqueness.SU.SU1Basic
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1Red

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem genericRedAt_of_plane {S : ℕ → ∀ (K : Type) [Group K], Prop} (hS : Setting G)
    (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G) (hK : KFactInvolution S)
    (hP : GL83GenericPlane S G) : GenericRedAt G S := by
  intro p hp P M hM hfail hIH x hgen h5 J hJC hCJ hperf hlt hmin hnot Q _ ψ hψ hker hSpQ hFi
  exfalso
  have hprime : p.Prime := sigmaA_prime p hp
  have : Fact p.Prime := ⟨hprime⟩
  have hp2 : p ≠ 2 := sigmaA_odd p hp
  have : Finite Q := Finite.of_surjective ψ hψ
  obtain ⟨hOJ, -, hOcop⟩ := CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec p J
  obtain ⟨hOM, hOodd⟩ := u3main_core_facts hS hD1 hp hM hgen hJC hCJ
  have hOcop' : ¬ p ∣ Nat.card (rankThreePrimeCore p J) :=
    (Nat.Prime.coprime_iff_not_dvd hprime).mp hOcop
  have hcardker : Nat.card ψ.ker = Nat.card (rankThreePrimeCore p J) := by
    rw [hker]
    exact Nat.card_congr (subgroupOfEquivOfLe hOJ).toEquiv
  have hkerodd : Odd (Nat.card ψ.ker) := hcardker ▸ hOodd
  have hkercop : ¬ p ∣ Nat.card ψ.ker := hcardker ▸ hOcop'
  obtain ⟨hxP, ⟨-, hx1, hxp, -, -⟩, hsyl, -⟩ := id hgen
  have hPM : (P : Subgroup G) ≤ M := (sylow_le_of_isCoreMaxLocal hS hp hM).1
  have hxJ : x ∉ J := u3main_not_mem hx1 hxp hJC hOcop' ψ hψ hker
    (u3main_center_bot hOJ hperf hlt hmin ψ hψ hker)
  obtain ⟨T, hT⟩ := (hsyl.inf_of_le_normalizer hJC hCJ).exists_sylow_eq_subgroupOf
  set QJ : Subgroup G := (P : Subgroup G) ⊓ centralizer ({x} : Set G) ⊓ J with hQJ
  have hQJp : IsPGroup p QJ := (hsyl.inf_of_le_normalizer hJC hCJ).isPGroup
  have hQJP : QJ ≤ (P : Subgroup G) := inf_le_left.trans inf_le_left
  have hQJJ : QJ ≤ J := inf_le_right
  have hTQJ : (T : Subgroup ↥J).map J.subtype = QJ := by
    rw [hT, map_subgroupOf_eq_of_le hQJJ]
  have hinjT : ∀ t ∈ (T : Subgroup ↥J), ψ t = 1 → t = 1 :=
    u3main_eq_one_of_ker ψ hkercop T.isPGroup'
  have hTb := Sylow.coe_mapSurjective hψ T
  obtain ⟨h2rk, u, hu, huord, zb, hzb1, hzb2, hzbu, hgenK⟩ :=
    hK p h5 Q hSpQ (Sylow.mapSurjective hψ T)
  rw [hTb] at h2rk hu hgenK
  obtain ⟨w, hw, hwu⟩ := hu
  have hu_mem : u ∈ (T : Subgroup ↥J).map ψ := hwu ▸ w.2
  have huc : ∀ y ∈ (T : Subgroup ↥J).map ψ, y * u = u * y := fun y hy => by
    have := congrArg Subtype.val (mem_center_iff.mp hw ⟨y, hy⟩)
    rwa [← hwu]
  have hup : u ^ p = 1 := huord ▸ pow_orderOf_eq_one u
  have hu1 : u ≠ 1 := by
    intro h
    rw [h, orderOf_one] at huord
    exact hprime.one_lt.ne huord
  obtain ⟨c, hcT, hcu, hcp, hcc⟩ := u3main_exists_central_lift ψ hinjT hu_mem hup huc
  have hc1 : c ≠ 1 := fun h => hu1 (by rw [← hcu, h, map_one])
  have hZ₀ : IsPGroup p (zpowers c) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hcp hc1, pow_one])
  have hzbc : ∀ c' ∈ zpowers c, zb * ψ c' = ψ c' * zb := by
    intro c' hc'
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hc'
    rw [map_zpow, hcu]
    exact (Commute.zpow_right hzbu k).eq
  have hcQJ : (c : G) ∈ QJ := mem_subgroupOf.mp (hT ▸ hcT)
  have hrk2 : 2 ≤ CFSG.Open.pRank p QJ := by
    have h1 := u3main_pRank_map hprime ψ hinjT
    have h2 := CFSG.SectionRank.pRank_le_map hprime.one_lt J.subtype J.subtype_injective
      (T : Subgroup ↥J)
    rw [hTQJ] at h2
    exact h2rk.trans (h1.le.trans h2)
  obtain ⟨E₂, hE₂QJ, hE₂e, hE₂c⟩ :=
    CFSG.GH74.Uniqueness.SU.SU1.exists_isElemAbelian_of_le_pRank hprime hrk2
  have hcE : ∀ e ∈ E₂, e * (c : G) = (c : G) * e := by
    intro e he
    have heT : (⟨e, (hE₂QJ he).2⟩ : ↥J) ∈ (T : Subgroup ↥J) := by
      rw [hT]
      exact mem_subgroupOf.mpr (hE₂QJ he)
    exact (congrArg Subtype.val (hcc _ heT)).symm
  have hc1G : (c : G) ≠ 1 := fun h => hc1 (Subtype.ext h)
  have hcpG : (c : G) ^ p = 1 := by
    have := congrArg Subtype.val hcp
    simpa using this
  obtain ⟨R, E, hRP, hRe, hRc, hxR, hRz, hEP, hEe, hEc, hER⟩ := u3main_plane_cube hxP
    (hQJP hcQJ) (hE₂QJ.trans hQJP) hxp hc1G hcpG hcQJ.2 (hE₂QJ.trans hQJJ) hxJ hJC hE₂e hE₂c hcE
  have hC : ∀ z : ↥J, z ≠ 1 → z ^ 2 = 1 → (∀ c' ∈ zpowers c, z * c' = c' * z) →
      centralizer ({z} : Set ↥J) ≤ (M ⊓ J).subgroupOf J := by
    intro z hz1 hz2 hzc g hg
    have hzG1 : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext h)
    have hzG2 : (z : G) ^ 2 = 1 := by
      have := congrArg Subtype.val hz2
      simpa using this
    have hRz' := hRz (z : G) z.2 (congrArg Subtype.val (hzc c (mem_zpowers c)))
    have hCz : centralizer ({(z : G)} : Set G) ≤ M :=
      u3main_centralizer_le hS hD1 hU0 hp hM hRe hRc hEe hEc (hEP.trans hPM) hER hzG1 hzG2 hRz'
        (hP p hp P M hM hfail hIH x hgen h5 J hJC hCJ hperf hlt hmin hnot Q ψ hψ hker hSpQ hFi
          (z : G) z.2 hzG1 hzG2 R hRP hRe hRc hxR hRz')
    refine mem_subgroupOf.mpr ⟨hCz ?_, g.2⟩
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hg))
  have hN : normalizer ((T : Subgroup ↥J) : Set ↥J) ≤ (M ⊓ J).subgroupOf J := by
    intro g hg
    have h1 := u3main_mem_normalizer_map hg
    rw [hTQJ] at h1
    exact mem_subgroupOf.mpr
      ⟨normalizer_le_of_le_of_two_le_pRank hS hU0 hp hM hQJp (hQJP.trans hPM) hrk2 h1, g.2⟩
  have hker' : ψ.ker ≤ (M ⊓ J).subgroupOf J := by
    rw [hker]
    intro g hg
    exact mem_subgroupOf.mpr ⟨hOM (mem_subgroupOf.mp hg), g.2⟩
  have htop := eq_top_of_involution_generation hp2 ψ hψ hkerodd hkercop T hZ₀ hzb1 hzb2 hzbc
    hgenK hker' hN hC
  apply hnot
  intro j hj
  have : (⟨j, hj⟩ : ↥J) ∈ (M ⊓ J).subgroupOf J := htop ▸ mem_top _
  exact (mem_subgroupOf.mp this).1

theorem genericListExclusionRedU3_of_plane (hS : Setting G) (hD1 : TheoremD1 G)
    (hU0 : FullCoreLocal G) (hK : KFactU3Involution) (hP : GL83GenericU3Plane G) :
    GL83GenericListExclusionRedU3 G :=
  genericRedAt_of_plane hS hD1 hU0 hK hP

end CFSG.LocalAnalysis.RankThreeTheoremC
