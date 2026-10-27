module

public import CFSG.ClassicalInvolution.RouteD.GapsEnd4Aux
public import CFSG.ClassicalInvolution.RouteD.GapsD4AAmbient
public import CFSG.ClassicalInvolution.RouteD.GapsAut

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.RouteD CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

theorem ACtx.commutes_beta_second_last_four (c : ACtx p f 4 Ω K z) (nd : Nodes c)
    (hMFZ : FundNoncentral p) (hcl : LinearAutClassification (GaloisField p f) 5)
    (hshape : LocalShapeA p f 4 Ω z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    {β : Subgroup G} (hβ : β ∈ Ω) {t : G} (hwβ : IsClassicalMember p f β t)
    (hnK : ¬ Commutes K β) (hpair : ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W K β)
    (hfirst : ¬ Commutes β (nd.j 0)) (hmid : Commutes β (nd.j 1)) (hlast : Commutes β (nd.j 3)) :
    Commutes β (nd.j 2) := by
  classical
  have h2 := c.two_ne_zero
  have hΩ := c.hΩ
  have hex := c.hex
  have hconj := hΩ.conjInvariant
  obtain ⟨W, hW⟩ := hpair
  have hz2 : orderOf z = 2 := c.hz.orderOf_eq_two
  have ht2 : orderOf t = 2 := hwβ.orderOf_eq_two
  have hzt : z * t = t * z := standardPair_involutions_commute h2 hW c.hz.mem hwβ.mem hz2 ht2
  have htz : t * z * t⁻¹ = z := by rw [mul_inv_eq_iff_eq_mul]; exact hzt.symm
  have htt : t * t = 1 := by
    rw [← pow_two]
    have := pow_orderOf_eq_one t
    rwa [ht2] at this
  obtain ⟨D, hDcard, i₀, i₁, hne01, ht₀, hr₀, ht₁, hr₁⟩ := hshape
  obtain ⟨h, hh⟩ := hsingle β hβ
  have ht_eq : t = h * z * h⁻¹ :=
    unique_involution_of_isClassicalMember h2 (hex β hβ) hwβ (hh ▸ c.hz.conj h)
  have hP1t : LocalOddCentral Ω {t} := by
    rw [ht_eq]; exact localOddCentral_conj hconj h z c.hP1
  obtain ⟨Dt, -⟩ := exists_lieSystemData_conj hconj h z D
  have attach : ∀ N : Subgroup G, N ∈ Ω → Commutes N K →
      (Commutes N β ↔ N ≤ Subgroup.centralizer ({t} : Set G)) := by
    intro N hN hNK
    rw [ht_eq] at hwβ ⊢
    exact commutes_iff_le_centralizer hMFZ hΩ hex (by rw [← ht_eq]; exact hP1t) Dt hβ hwβ hN hNK hnK
  have hconj_t : centralizingMembers Ω {z} = conjSub t '' centralizingMembers Ω {z} := by
    have := centralizingMembers_conj hconj t z
    rwa [htz] at this
  have hmemΩz : ∀ L ∈ centralizingMembers Ω {z}, conjSub t L ∈ centralizingMembers Ω {z} := by
    intro L hL
    have : conjSub t L ∈ conjSub t '' centralizingMembers Ω {z} := ⟨L, hL, rfl⟩
    rwa [← hconj_t] at this
  set σ := locAut hconj htz with hσdef
  have hσ2 : ∀ y, σ (σ y) = y := locAut_locAut hconj htz htt
  set ψ := c.d.ψ with hψ
  have hKz : K ∈ centralizingMembers Ω {z} := ⟨c.hK, le_centralizer_of_isClassicalMember c.hz⟩
  have hi₀ : ∀ i : Fin D.card, D.tag i = .PSL → D.rank i = 2 → i = i₀ := by
    intro i hti hri
    by_contra hne
    have hi : i = i₁ := by
      have h1 := i.isLt
      have h2' := i₀.isLt
      have h3 := i₁.isLt
      have h4 : i.val ≠ i₀.val := fun e => hne (Fin.ext e)
      have h5 : i₀.val ≠ i₁.val := fun e => hne01 (Fin.ext e)
      exact Fin.ext (by omega)
    rw [hi, hr₁] at hri
    omega
  have hKt : conjSub t K = K := by
    have hcK : IsClassicalMember p f (conjSub t K) z := by
      have := c.hz.conj t
      rwa [htz] at this
    have hmem : conjSub t K ∈ centralizingMembers Ω {z} :=
      ⟨hconj t K c.hK, le_centralizer_of_isClassicalMember hcK⟩
    obtain ⟨ia, hta, hra, hia⟩ := locImg_eq_range_of_involution hMFZ D hKz c.hz
    obtain ⟨ib, htb, hrb, hib⟩ := locImg_eq_range_of_involution hMFZ D hmem hcK
    have e1 := hi₀ ia hta hra
    have e2 := hi₀ ib htb hrb
    subst e1 e2
    exact locImg_injOn hΩ c.hP1 hmem hKz (hib.trans hia.symm)
  have hKt' : conjSub t⁻¹ K = K := by
    have := congrArg (conjSub t⁻¹) hKt
    rw [conjSub_inv_conjSub] at this
    exact this.symm
  have hconjne : ∀ L, conjSub t L ≠ K ↔ L ≠ K := by
    intro L
    constructor
    · intro hne heq
      apply hne
      rw [heq, hKt]
    · intro hne heq
      apply hne
      have := congrArg (conjSub t⁻¹) heq
      rwa [conjSub_inv_conjSub, hKt'] at this
  have hstab : ∀ x, σ (ψ x) ∈ ψ.range := by
    have hS : (⨆ R ∈ longRootSet (K := GaloisField p f) c.hn, R) ≤
        (ψ.range).comap (σ.toMonoidHom.comp ψ) := by
      refine iSup₂_le fun R hR y hy => ?_
      obtain ⟨L, hL, hLK, hLR⟩ :=
        exists_member_of_root c.hm c.hodd hΩ c.hK c.hz c.hP1 c.d hR
      have hyL : ψ y ∈ locImg Ω z L := by rw [hLR]; exact ⟨y, hy, rfl⟩
      have h1 : σ (ψ y) ∈ locImg Ω z (conjSub t L) := by
        rw [← locAut_locImg hconj htz L]; exact ⟨_, hyL, rfl⟩
      obtain ⟨R', -, hR'⟩ := exists_root_of_ne c.hm c.hodd hΩ hex c.hK c.hz c.hP1 c.d
        (hmemΩz L hL) ((hconjne L).mpr hLK)
      rw [hR'] at h1
      obtain ⟨y', -, hy'⟩ := h1
      exact ⟨y', hy'⟩
    intro x
    have hx : x ∈ ⨆ R ∈ longRootSet (K := GaloisField p f) c.hn, R := by
      rw [iSup_longRootSet_eq_top h2 c.hn]; exact Subgroup.mem_top x
    exact hS hx
  have himg : ∀ a (ha : a < 4), locImg Ω z (nd.j a) =
      (blockSL2 (GaloisField p f) 4 ⟨a, ha⟩).range.map ψ := fun a ha => by
    rw [nd.img a ha, blockSL2_range_eq_Lc h2 ha]
  have hfixed : ∀ a (ha : a < 4), Commutes β (nd.j a) → ∀ A : SL(2, GaloisField p f),
      σ (ψ (blockSL2 (GaloisField p f) 4 ⟨a, ha⟩ A)) =
        ψ (blockSL2 (GaloisField p f) 4 ⟨a, ha⟩ A) := by
    intro a ha hcomm A
    have hle : nd.j a ≤ Subgroup.centralizer ({t} : Set G) := fun n hn => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hcomm t hwβ.mem n hn).symm
    exact (locAut_fixed_iff hΩ c.hP1 htz (nd.mem a ha)).mp hle _
      (by rw [himg a ha]; exact ⟨_, ⟨A, rfl⟩, rfl⟩)
  have hfix : ∀ a : Fin 4, partnerFixed 4 a → ∀ A : SL(2, GaloisField p f),
      σ (ψ (blockSL2 (GaloisField p f) 4 a A)) = ψ (blockSL2 (GaloisField p f) 4 a A) := by
    intro a ha A
    have h3 : a.val = 3 ∨ a.val = 1 := by
      rcases ha with ha | ⟨ha1, ha2⟩ <;> omega
    rcases h3 with h3 | h3
    · have : a = ⟨3, (by norm_num : 3 < 4)⟩ := Fin.ext h3
      subst this
      exact hfixed 3 (by norm_num) hlast A
    · have : a = ⟨1, (by norm_num : 1 < 4)⟩ := Fin.ext h3
      subst this
      exact hfixed 1 (by norm_num) hmid A
  have hmove : ∃ A : SL(2, GaloisField p f),
      σ (ψ (blockSL2 (GaloisField p f) 4 ⟨0, by omega⟩ A)) ≠
        ψ (blockSL2 (GaloisField p f) 4 ⟨0, by omega⟩ A) := by
    by_contra hcon
    push Not at hcon
    have hfx : ∀ a ∈ locImg Ω z (nd.j 0), σ a = a := by
      intro a ha
      rw [himg 0 (by omega)] at ha
      obtain ⟨_, ⟨A, rfl⟩, rfl⟩ := ha
      exact hcon A
    have hle := (locAut_fixed_iff hΩ c.hP1 htz (nd.mem 0 (by omega))).mpr hfx
    exact hfirst (commutes_symm
      ((attach (nd.j 0) (nd.mem 0 (by omega)).1 (commutes_symm (nd.commK 0 (by omega)))).mpr hle))
  obtain ⟨μ, hμ, hpat, hiff⟩ := partner_pattern_amb c.hodd c.h5 (le_refl 4) hcl ψ c.d.ker_le σ hσ2
    hstab hfix hmove
  rcases hμ with hμ1 | hμ1
  ·
    have hf2 := hiff.mp hμ1
    have hle : nd.j 2 ≤ Subgroup.centralizer ({t} : Set G) := by
      refine (locAut_fixed_iff hΩ c.hP1 htz (nd.mem 2 (by norm_num))).mpr ?_
      intro a ha
      rw [himg 2 (by norm_num)] at ha
      obtain ⟨_, ⟨A, rfl⟩, rfl⟩ := ha
      exact hf2 A
    exact commutes_symm ((attach (nd.j 2) (nd.mem 2 (by norm_num)).1
      (commutes_symm (nd.commK 2 (by norm_num)))).mpr hle)
  ·
    exfalso
    subst hμ1
    have hj1Ω : nd.j 1 ∈ Ω := (nd.mem 1 (by norm_num)).1
    obtain ⟨g, hg⟩ := hsingle _ hj1Ω
    have hx_eq : nd.w 1 = g * z * g⁻¹ :=
      unique_involution_of_isClassicalMember h2 (hex _ hj1Ω) (nd.isCl 1 (by norm_num))
        (by rw [hg]; exact c.hz.conj g)
    have hψu : ψ (zElt (GaloisField p f) (nodePair 4 1 (by norm_num))) =
        locElt Ω z (nd.w 1) (le_centralizingLayer (nd.mem 1 (by norm_num))
          (nd.isCl 1 (by norm_num)).mem) :=
      psi_root_inv c.hm c.hodd c.d (isLongRootSL2_Lc h2 c.hn _) (nd.img 1 (by norm_num))
        (le_centralizingLayer (nd.mem 1 (by norm_num))) (nd.isCl 1 (by norm_num)).mem
        (nd.isCl 1 (by norm_num)).orderOf_eq_two
    have hKne : K ≠ nd.j 1 := (nd.ne_K 1 (by norm_num)).symm
    have hβne : β ≠ nd.j 1 := fun e => hnK (e ▸ nd.commK 1 (by norm_num))
    have hKβ : K ≠ β := fun e => hfirst (e ▸ nd.commK 0 (by norm_num))
    obtain ⟨hKcm, -, R₀, i₀', hR₀, hKR₀, hy₀, hi₀⟩ :=
      c.exists_rootData_conj hg c.hK (nd.commK 1 (by norm_num)) hKne c.hz
    obtain ⟨hbcm, -, Rb, ib, hRb, hβRb, hyb, hib⟩ :=
      c.exists_rootData_conj hg hβ hmid hβne hwβ
    have hcommz : (g⁻¹ * z * g) * (g⁻¹ * t * g) = (g⁻¹ * t * g) * (g⁻¹ * z * g) := by
      calc (g⁻¹ * z * g) * (g⁻¹ * t * g) = g⁻¹ * (z * t) * g := by group
        _ = g⁻¹ * (t * z) * g := by rw [hzt]
        _ = (g⁻¹ * t * g) * (g⁻¹ * z * g) := by group
    have hc12 := c.commute_of_locElt hKcm hbcm (fun e => hKβ (conjSub_injective g⁻¹ e)) hR₀ hRb
      hKR₀ hβRb hy₀ hyb hi₀ hib hcommz
    have hnc_root : ¬ Commutes R₀ Rb := by
      rw [← c.commutes_iff_root hKcm hbcm hR₀ hKR₀ hβRb, commutes_conjSub_iff]
      exact hnK
    obtain ⟨R, i, hRi, hRc, hRn⟩ := exists_perp_not_commutes h2 (by norm_num : 4 ≤ 4 + 1) hR₀ hRb
      hc12.1 hc12.2 hnc_root
    obtain ⟨L, hL, hLK, hLR⟩ :=
      exists_member_of_root c.hm c.hodd hΩ c.hK c.hz c.hP1 c.d (⟨i, hRi⟩ : R ∈ longRootSet c.hn)
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
    obtain ⟨R', -, hR'⟩ := exists_root_of_ne c.hm c.hodd hΩ hex c.hK c.hz c.hP1 c.d hN'z hN'ne
    have hfixN : ∀ a ∈ locImg Ω z (conjSub g L), σ a = a := by
      intro a ha
      have ha' := ha
      rw [hR'] at ha'
      obtain ⟨y, -, rfl⟩ := ha'
      rw [hpat y, conj_partnerDiag_four_neg, map_mul, map_mul, hψu, map_inv, hψu]
      obtain ⟨b, hb, hba⟩ := ha
      have hxb : locElt Ω z (nd.w 1) (le_centralizingLayer (nd.mem 1 (by norm_num))
          (nd.isCl 1 (by norm_num)).mem) * ψ y = ψ y * locElt Ω z (nd.w 1)
          (le_centralizingLayer (nd.mem 1 (by norm_num)) (nd.isCl 1 (by norm_num)).mem) := by
        rw [← hba]
        unfold locElt
        rw [← map_mul, ← map_mul]
        congr 1
        apply Subtype.ext
        exact (Subgroup.mem_centralizer_singleton_iff.mp (hN'x.2 (Subgroup.mem_subgroupOf.mp hb))).symm
      rw [hxb, mul_inv_cancel_right]
    have hle := (locAut_fixed_iff hΩ c.hP1 htz hN'z).mpr hfixN
    exact hN'β ((attach _ hN'Ω hN'K).mpr hle)

end CFSG.ClassicalInvolution.RouteD.Gaps
