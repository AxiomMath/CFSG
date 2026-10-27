module

public import CFSG.ClassicalInvolution.Q3.Q3WASNorm
public import CFSG.ClassicalInvolution.Q3.Q3WARow

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair blockSL2)
open scoped MatrixGroups

section End4

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem ACtx3.end_relation_four {ι : Type} (c : ACtx3 4 Ω K z) (nd : Nodes3 c)
    (hMFZ : RouteD.Gaps.FundNoncentral 3)
    (hcl : LinearAutClassification (GaloisField 3 1) 5)
    (D : LieSystemData3 ι (locQuot Ω z) (locFamily Ω z))
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    {β : Subgroup G} (hβ : β ∈ Ω) {t : G} (hwβ : IsClassicalMember3 β t)
    (hnK : ¬ Commutes K β)
    (hpair : ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W K β)
    (hfirst : ¬ Commutes β (nd.j 0)) (hmid : Commutes β (nd.j 1))
    (hlast : Commutes β (nd.j 3)) : Commutes β (nd.j 2) := by
  classical
  have h2 := two_ne_zero_gf3
  have hΩ := c.hΩ
  have hex := c.hex
  have hconj := hΩ.conjInvariant
  have htz : t * z * t⁻¹ = z := fix_of_stdpair3 c.hz hwβ hpair
  have hzt : z * t = t * z := (mul_inv_eq_iff_eq_mul.mp htz).symm
  have attach := fun (N : Subgroup G) (hN : N ∈ Ω) (hNK : Commutes N K) =>
    c.commutes_partner_iff hMFZ D hsingle hβ hwβ hnK hN hNK
  have hfixed : ∀ (a : ℕ) (ha : a < 4), partnerFixed 4 ⟨a, ha⟩ → Commutes β (nd.j a) := by
    intro a ha hfx
    have h3 : a = 3 ∨ a = 1 := by
      rcases hfx with hfx | ⟨ha1, ha2⟩
      · left
        simp only at hfx
        omega
      · right
        simp only at ha1 ha2
        omega
    rcases h3 with rfl | rfl
    · exact hlast
    · exact hmid
  obtain ⟨μ, hμ, hpat, hiff⟩ := c.partner_pattern (le_refl 4) nd hMFZ hcl D hsingle hβ hwβ hnK htz
    hfixed hfirst
  rcases hμ with hμ1 | hμ1
  ·
    have hf2 := hiff.mp hμ1
    have hle : nd.j 2 ≤ Subgroup.centralizer ({t} : Set G) := by
      refine (locAut_fixed_iff3 hΩ hex c.hP1 c.hO3 htz (nd.mem 2 (by norm_num))).mpr ?_
      intro a ha
      rw [nd.locImg_eq (by norm_num)] at ha
      obtain ⟨_, ⟨A, rfl⟩, rfl⟩ := ha
      exact hf2 A
    exact Gaps.commutes_symm ((attach (nd.j 2) (nd.mem 2 (by norm_num)).1
      (Gaps.commutes_symm (nd.commK 2 (by norm_num)))).mpr hle)
  ·
    exfalso
    subst hμ1
    have hj1Ω : nd.j 1 ∈ Ω := (nd.mem 1 (by norm_num)).1
    obtain ⟨g, hg⟩ := hsingle _ hj1Ω
    have hx_eq : nd.w 1 = g * z * g⁻¹ :=
      involution_unique3 (nd.isCl 1 (by norm_num)) (by rw [hg]; exact c.hz.conj g)
    have hψu : c.d.ψ (zElt (GaloisField 3 1) (nodePair 4 1 (by norm_num))) =
        locElt Ω z (nd.w 1) (le_centralizingLayer (nd.mem 1 (by norm_num))
          (nd.isCl 1 (by norm_num)).mem) :=
      psi_root_inv c.hm odd_gf3 c.d (isLongRootSL2_Lc h2 c.hn _) (nd.img 1 (by norm_num))
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
    obtain ⟨L, hL, hLK, hLR⟩ := exists_member_of_root3 c.hm hΩ hex c.hK c.hz c.hP1 c.hO3 c.d
      (⟨i, hRi⟩ : R ∈ longRootSet c.hn)
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
    have hN'ne : conjSub g L ≠ K := fun e => not_commutes_self3 c.hz (e ▸ hN'K)
    obtain ⟨R', -, hR'⟩ := exists_root_of_ne3 c.hm hΩ hex c.hK c.hz c.hP1 c.hO3 c.d hN'z hN'ne
    have hfixN : ∀ a ∈ locImg Ω z (conjSub g L), locAut hconj htz a = a := by
      intro a ha
      have ha' := ha
      rw [hR'] at ha'
      obtain ⟨y, -, rfl⟩ := ha'
      rw [hpat y, conj_partnerDiag_four_neg, map_mul, map_mul, hψu, map_inv, hψu]
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
    have hle := (locAut_fixed_iff3 hΩ hex c.hP1 c.hO3 htz hN'z).mpr hfixN
    exact hN'β ((attach _ hN'Ω hN'K).mpr hle)

end End4

section Row

@[expose] def ChainRow3 (m : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteD3Setup K z →
      LocalShapeC3 1 (CompData.model .PSL (m + 1)) (conjClass3 K) z →
      ∃ U : Fin (m + 2) → Subgroup G, (∀ i, U i ∈ conjClass3 K) ∧
        (∀ i j : Fin (m + 2), (i : ℕ) + 1 < j → Commutes (U i) (U j)) ∧
        ∀ i j : Fin (m + 2), (j : ℕ) = i + 1 →
          ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (U i) (U j)

theorem chainRow3_four (h3 : OddThreeFreeInput) : ChainRow3 4 := by
  intro G _ _ _ hnab K z hR hshape
  have hsingle : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g K := by
    rintro L ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  obtain ⟨hex, hP1⟩ := hR.setup
  have hK : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  have hshape' := hshape
  obtain ⟨d⟩ := LocalShapeC3.nonempty_dict (m := 4) (by norm_num) hR.inClass hK hR.cls hshape
  let c : ACtx3 4 (conjClass3 K) K z :=
    { hm := by norm_num, hΩ := hR.inClass, hex := hex, hK := hK, hz := hR.cls, hP1 := hP1,
      hO3 := h3 G K z hR, d := d, hlift := Or.inl (by norm_num) }
  obtain ⟨nd⟩ := c.nonempty_nodes
  obtain ⟨ι, -, D, -⟩ := hshape'
  obtain ⟨β, hβΩ, ⟨t, hβcl⟩, hnK, hpair, hnβ0, ⟨W2, hW2⟩, hlast, hmid⟩ :=
    c.exists_partner nd (by norm_num) hsingle
  have hm1 : Commutes β (nd.j 1) := hmid 1 le_rfl (by norm_num)
  have hsecond : Commutes β (nd.j 2) :=
    c.end_relation_four nd (RouteD.Gaps.fundNoncentral 3) (linearAutClassification3 (by norm_num))
      D hsingle hβΩ hβcl hnK hpair hnβ0 hm1 hlast
  obtain ⟨W1, hW1⟩ := hpair
  refine ⟨![K, β, nd.j 0, nd.j 1, nd.j 2, nd.j 3], ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact hK
    · exact hβΩ
    · exact (nd.mem 0 (by norm_num)).1
    · exact (nd.mem 1 (by norm_num)).1
    · exact (nd.mem 2 (by norm_num)).1
    · exact (nd.mem 3 (by norm_num)).1
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first | (exfalso; exact absurd hij (by decide)) | skip
    · exact nd.commK 0 (by norm_num)
    · exact nd.commK 1 (by norm_num)
    · exact nd.commK 2 (by norm_num)
    · exact nd.commK 3 (by norm_num)
    · exact hm1
    · exact hsecond
    · exact hlast
    · exact nd.far 0 (by norm_num) 2 (by norm_num) (by norm_num)
    · exact nd.far 0 (by norm_num) 3 (by norm_num) (by norm_num)
    · exact nd.far 1 (by norm_num) 3 (by norm_num) (by norm_num)
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first | (exfalso; exact absurd hij (by decide)) | skip
    · exact ⟨W1, hW1⟩
    · exact ⟨W2, hW2⟩
    · exact nd.pair 0 (by norm_num)
    · exact nd.pair 1 (by norm_num)
    · exact nd.pair 2 (by norm_num)

end Row

end CFSG.ClassicalInvolution.Q3.Q3W
