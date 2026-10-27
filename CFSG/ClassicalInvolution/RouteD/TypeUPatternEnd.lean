module

public import CFSG.ClassicalInvolution.RouteD.TypeUPatternPartner

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Phan CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType.BorelTits CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

theorem UCtx.end_relation_four (c : UCtx p f 4 Ω K z) (nd : UNodes c) (hMFZ : FundNoncentral p)
    (hshape : LocalShapeU p f 4 Ω z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    {β : Subgroup G} (hβ : β ∈ Ω) {t : G} (hwβ : IsClassicalMember p f β t) (hnK : ¬ Commutes K β)
    (hpair : ∃ W : Subgroup G, UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W K β)
    (hfirst : ¬ Commutes β (nd.j 0)) (hmid : Commutes β (nd.j 1)) (hlast : Commutes β (nd.j 3)) :
    Commutes β (nd.j 2) := by
  classical
  have h2 : (2 : GaloisField p f) ≠ 0 := two_ne_zero_of_charP_ne_two c.hp2
  have hfixed : ∀ (a : ℕ) (ha : a < 4), partnerFixed 4 ⟨a, ha⟩ → Commutes β (nd.j a) := by
    intro a ha hfx
    have h3 : a = 3 ∨ a = 1 := by
      rcases hfx with hfx | ⟨h1, h2'⟩
      · left
        simp only at hfx
        omega
      · right
        simp only at h1 h2'
        omega
    rcases h3 with rfl | rfl
    · exact hlast
    · exact hmid
  obtain ⟨htz, w, hpat, hw0, -⟩ := c.partner_pattern (by norm_num) nd hMFZ hshape hsingle hβ hwβ
    hnK hpair hfixed hfirst
  by_cases hw : w = 0
  · exact hw0 hw
  exfalso
  have hw1 : w = 1 := by
    have : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
    exact (this w).resolve_left hw
  subst hw1
  obtain ⟨_htz', _, _, _, hfixiff⟩ := c.partner_setup nd hMFZ hshape hsingle hβ hwβ hnK hpair
  have hconj := c.hΩ.conjInvariant
  have hex := c.hex
  have hzt : z * t = t * z := by
    have := htz
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  have hj1Ω : nd.j 1 ∈ Ω := (nd.mem 1 (by norm_num)).1
  obtain ⟨g, hg⟩ := hsingle _ hj1Ω
  have hx_eq : nd.w 1 = g * z * g⁻¹ :=
    unique_involution_of_isClassicalMember h2 (hex _ hj1Ω) (nd.isCl 1 (by norm_num))
      (by rw [hg]; exact c.hz.conj g)
  have hψu : c.d.ψ (zEltU (GaloisField p (2 * f)) p f (nodePair 4 1 (by norm_num))) =
      locElt Ω z (nd.w 1) (le_centralizingLayer (nd.mem 1 (by norm_num))
        (nd.isCl 1 (by norm_num)).mem) :=
    psiU_root_inv c.hp2 c.hq c.hm c.d (isLongRootSU2_LcU c.h2 c.hn _) (nd.img 1 (by norm_num))
      (le_centralizingLayer (nd.mem 1 (by norm_num))) (nd.isCl 1 (by norm_num)).mem
      (nd.isCl 1 (by norm_num)).orderOf_eq_two
  have hKne : K ≠ nd.j 1 := (nd.ne_K 1 (by norm_num)).symm
  have hβne : β ≠ nd.j 1 := fun e => hnK (e ▸ nd.commK 1 (by norm_num))
  have hKβ : K ≠ β := fun e => hfirst (e ▸ nd.commK 0 (by norm_num))
  obtain ⟨hKcm, -, R₀, i₀', hR₀, hKR₀, hy₀, hi₀⟩ :=
    c.exists_rootData_conj hg c.hK (nd.commK 1 (by norm_num)) hKne c.hz
  obtain ⟨hbcm, -, Rb, ib, hRb, hβRb, hyb, hib⟩ := c.exists_rootData_conj hg hβ hmid hβne hwβ
  have hcommz : (g⁻¹ * z * g) * (g⁻¹ * t * g) = (g⁻¹ * t * g) * (g⁻¹ * z * g) := by
    calc (g⁻¹ * z * g) * (g⁻¹ * t * g) = g⁻¹ * (z * t) * g := by group
      _ = g⁻¹ * (t * z) * g := by rw [hzt]
      _ = (g⁻¹ * t * g) * (g⁻¹ * z * g) := by group
  have hc12 := c.commute_of_locElt hKcm hbcm (fun e => hKβ (conjSub_injective g⁻¹ e)) hR₀ hRb
    hKR₀ hβRb hy₀ hyb hi₀ hib hcommz
  have hnc_root : ¬ Commutes R₀ Rb := by
    rw [← c.commutes_iff_root hKcm hbcm hR₀ hKR₀ hβRb, commutes_conjSub_iff]
    exact hnK
  obtain ⟨R, i, hRi, hRc, hRn⟩ := exists_perp_not_commutes_su c.card_eq c.hp2
    (by norm_num : 4 ≤ 4 + 1) hR₀ hRb hc12.1 hc12.2 hnc_root
  obtain ⟨L, hL, hLK, hLR⟩ := typeU_exists_member_of_root c.hp2 c.hq c.hm c.hΩ c.hK c.hz c.hP1
    c.d (⟨i, hRi⟩ : R ∈ longRootSetU c.hn)
  have hLKc : Commutes L (conjSub g⁻¹ K) := (c.commutes_iff_root hL hKcm hRi hLR hKR₀).mpr hRc
  have hLbc : ¬ Commutes L (conjSub g⁻¹ β) := fun h =>
    hRn ((c.commutes_iff_root hL hbcm hRi hLR hβRb).mp h)
  have hN'Ω : conjSub g L ∈ Ω := hconj g L hL.1
  have hN'K : Commutes (conjSub g L) K := by
    have := (commutes_conjSub_iff g).mpr hLKc
    rwa [conjSub_conjSub_inv] at this
  have hN'β : ¬ Commutes (conjSub g L) β := fun h => hLbc (by
    have := (commutes_conjSub_iff g⁻¹).mpr h
    rwa [conjSub_inv_conjSub] at this)
  have hN'x : conjSub g L ∈ centralizingMembers Ω {nd.w 1} := by
    rw [hx_eq, centralizingMembers_conj hconj]
    exact ⟨L, hL, rfl⟩
  have hN'z : conjSub g L ∈ centralizingMembers Ω {z} :=
    ⟨hN'Ω, fun n hn => Subgroup.mem_centralizer_singleton_iff.mpr (hN'K n hn z c.hz.mem)⟩
  have hN'ne : conjSub g L ≠ K := fun e =>
    not_commutes_self_of_isClassicalMember c.hz (e ▸ hN'K)
  obtain ⟨R', -, hR'⟩ := typeU_exists_root_of_ne c.hp2 c.hq c.hm c.hΩ c.hex c.hK c.hz c.hP1 c.d
    hN'z hN'ne
  have hfixN : ∀ a ∈ locImg Ω z (conjSub g L), locAut hconj htz a = a := by
    intro a ha
    have ha' := ha
    rw [hR'] at ha'
    obtain ⟨y, -, rfl⟩ := ha'
    rw [hpat y, conjSign_partnerSigns_four, map_mul, map_mul, hψu, map_inv, hψu]
    obtain ⟨b, hb, hba⟩ := ha
    have hxb : locElt Ω z (nd.w 1) (le_centralizingLayer (nd.mem 1 (by norm_num))
        (nd.isCl 1 (by norm_num)).mem) * c.d.ψ y = c.d.ψ y * locElt Ω z (nd.w 1)
        (le_centralizingLayer (nd.mem 1 (by norm_num)) (nd.isCl 1 (by norm_num)).mem) := by
      rw [← hba]
      unfold locElt
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_singleton_iff.mp
        (hN'x.2 (Subgroup.mem_subgroupOf.mp hb))).symm
    rw [hxb, mul_inv_cancel_right]
  exact hN'β ((hfixiff _ hN'z hN'K).mp hfixN)

theorem not_uEndObstruction_four (hMFZ : FundNoncentral p) {Ω : Set (Subgroup G)}
    {K : Subgroup G} {z : G} (hshape : LocalShapeU p f 4 Ω z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) : ¬ UEndObstruction p f 4 Ω K z := by
  rintro ⟨c, nd, β, hβΩ, ⟨t, hwβ⟩, hnK, hpair, hfirst, -, hlast, hmid, hnot⟩
  exact hnot (c.end_relation_four nd hMFZ hshape hsingle hβΩ hwβ hnK hpair hfirst
    (hmid 1 le_rfl (by norm_num)) hlast)

theorem routeD_typeU_four (hMFZ : FundNoncentral p) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) (hex : ExactMembers Ω) {K : Subgroup G}
    (hK : K ∈ Ω) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hconn : DeltaConnected Ω)
    {z : G} (hz : IsClassicalMember p f K z) (hshape : LocalShapeU p f 4 Ω z)
    (hP1 : LocalOddCentral Ω {z}) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .PSU ∧ D.rank i = 4 + 3 :=
  (routeD_typeU_dichotomy hp2 hq (le_refl 4) hΩ hex hK hsingle hconn hz hshape hP1).resolve_right
    (not_uEndObstruction_four hMFZ hshape hsingle)

end CFSG.ClassicalInvolution.RouteD
