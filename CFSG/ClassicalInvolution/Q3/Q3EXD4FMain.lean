module

public import CFSG.ClassicalInvolution.Q3.Q3EXD4FCaseI
public import CFSG.ClassicalInvolution.Q3.Q3EXD4FCA
public import CFSG.ClassicalInvolution.Q3.Q3EXMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W.EX

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD.Exotic CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.RouteD.Gaps (locMk)


section Main

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}

theorem false_of_d4_four3 (hnab : ∃ x y : G, x * y ≠ y * x) (S : D4Ctx3 G K z 4) : False := by
  classical
  set Ω := conjClass3 K with hΩdef
  have hΩ : InClass3 Ω := S.setup.inClass
  obtain ⟨hex, -⟩ := S.setup.setup
  have hKΩ : K ∈ Ω := ⟨1, conjSub_one K⟩
  have hcen := center_eq_bot_of_simple hnab
  obtain ⟨M, hM⟩ := outerSet_nonempty_of_shape3 S hKΩ
  obtain ⟨z₀, hz₀⟩ := hΩ.classical K hKΩ
  obtain ⟨Ta, Tb, ya, yb, P, x, hTaΩ, hTbΩ, hcTa, hcTb, hTaN, hTbN, hTab, hyaT, hybT, hya2,
    hyb2, hyanc, hybnc, hne1, hPΩ, hxP, hPcomm, ht4, htne⟩ :=
    exists_lift_data3 hnab S hKΩ hM hz₀
  set u : G := ya * yb with hu
  have hnc : ¬ ({u} : Set G) ⊆ Subgroup.center G := fun h => by
    have h1 : u ∈ Subgroup.center G := h (Set.mem_singleton u)
    rw [hcen, Subgroup.mem_bot] at h1
    exact hne1 h1
  have hcu : ∀ L : Subgroup G, Commutes L Ta → Commutes L Tb →
      L ≤ Subgroup.centralizer ({u} : Set G) := by
    intro L h1 h2 g hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    have e1 := h1 g hg ya hyaT
    have e2 := h2 g hg yb hybT
    rw [hu, ← mul_assoc, e1, mul_assoc, e2, ← mul_assoc]
  have hKTa : Commutes K Ta := commutes_of_twin hcTa (self_mem_cnbhd hKΩ) (Ne.symm hTaN)
  have hKTb : Commutes K Tb := commutes_of_twin hcTb (self_mem_cnbhd hKΩ) (Ne.symm hTbN)
  have hKC : K ≤ Subgroup.centralizer ({u} : Set G) := hcu K hKTa hKTb
  have H1 : ∀ L ∈ outerSet Ω K, L ≤ Subgroup.centralizer ({u} : Set G) := fun L hL =>
    hcu L (commutes_of_twin hcTa hL.1 (ne_of_mem_outerSet hcTa hL))
      (commutes_of_twin hcTb hL.1 (ne_of_mem_outerSet hcTb hL))
  have H3 : ∃ T ∈ Ω, cnbhd Ω T = cnbhd Ω K ∧ ∃ g ∈ T, u * g ≠ g * u := by
    refine ⟨Ta, hTaΩ, hcTa, ?_⟩
    by_contra hcon
    push Not at hcon
    apply hyanc
    intro g hg
    have h1 := hcon g hg
    have hTbTa : Commutes Tb Ta := commutes_of_twins hTbΩ hcTb hcTa hTab.symm
    have e : yb * g = g * yb := hTbTa yb hybT g hg
    have h2 : ya * g * yb = g * ya * yb := by
      calc ya * g * yb = ya * (g * yb) := by group
        _ = ya * (yb * g) := by rw [e]
        _ = u * g := by rw [hu]; group
        _ = g * u := h1
        _ = g * ya * yb := by rw [hu]; group
    exact mul_right_cancel h2
  obtain ⟨ι, hι, ⟨Du⟩⟩ := S.setup.ih {u} hnc
  have hKu : K ∈ centralizingMembers Ω {u} := ⟨hKΩ, hKC⟩
  obtain ⟨iK, hKi, -⟩ := exists_unique_comp_u hΩ hex Du hKu
  have hPu : P ∈ centralizingMembers Ω {u} :=
    ⟨hPΩ, fun g hg => Subgroup.mem_centralizer_singleton_iff.mpr (hPcomm g hg)⟩
  have hPi : P ∈ compMembers3 Ω u Du iK := by
    obtain ⟨iP, hPi, -⟩ := exists_unique_comp_u hΩ hex Du hPu
    by_cases h : iP = iK
    · subst h
      exact hPi
    · exact absurd (eq_one_of_mem_oddCoreIn_of_pow_four
        (comm_mem_oddCoreIn_of_ne_comp3 hΩ.conjInvariant h hPi hKi hxP hz₀.mem) ht4) htne
  have hxY : x ∈ locLayer Ω u := le_centralizingLayer hPu hxP
  have hNi : conjSub x K ∈ compMembers3 Ω u Du iK :=
    conjSub_mem_compMembers_of_mem_layer3 hΩ.conjInvariant hKi hxY
  have hCaseI : ∀ M'' ∈ outerSet Ω K, M'' ∉ compMembers3 Ω u Du iK := fun M'' hM'' =>
    not_mem_comp_of_outer3 S hKΩ hz₀ Du hKi H1 H3 hM''
  have hΘ : ∀ X, X ∈ compMembers3 Ω u Du iK → outerGen Ω K ≤ commModOdd u X := by
    intro X hX
    refine le_commModOdd_of_ne_comp3 hΩ.conjInvariant hX (𝒮 := outerSet Ω K) ?_ ?_
    · intro L hL
      exact ⟨⟨hL.1.1, H1 L hL⟩, fun j hj hji => hCaseI L hL (hji ▸ hj)⟩
    · intro L hL
      obtain ⟨j, hj, -⟩ := exists_unique_comp_u hΩ hex Du ⟨hL.1.1, H1 L hL⟩
      exact ⟨j, hj⟩
  obtain ⟨Mk, zk, hMk, hzk, hzkcomm, hMkgen⟩ := exists_node_members3 S hKΩ
  have hMkK : ∀ k, Commutes (Mk k) K := fun k =>
    ((hMk k).1.2).resolve_left fun h => (hMk k).2 (by rw [h])
  have hz₀2 : z₀ * z₀ = 1 := mul_self_of_isClassicalMember3 hz₀
  set zz : Option (Fin 4) → G := fun o => o.elim z₀ zk with hzz
  have hzz2 : ∀ o, zz o * zz o = 1 := by
    rintro (_ | k)
    · exact hz₀2
    · exact mul_self_of_isClassicalMember3 (hzk k)
  have hzzcomm : ∀ o o', zz o * zz o' = zz o' * zz o := by
    rintro (_ | k) (_ | k')
    · rfl
    · exact (hMkK k' (zk k') (hzk k').mem z₀ hz₀.mem).symm
    · exact hMkK k (zk k) (hzk k).mem z₀ hz₀.mem
    · exact hzkcomm k k'
  have hF₀p : IsPGroup 2 (Subgroup.closure (Set.range zz)) :=
    isPGroup_closure_of_commuting_involutions zz hzz2 hzzcomm
  have hzkΘ : ∀ k, zk k ∈ outerGen Ω K := fun k => le_outerGen (hMk k) (hzk k).mem
  have key : ∀ (Ns : Subgroup G) (zs : G), Ns ∈ compMembers3 Ω u Du iK →
      IsClassicalMember3 Ns zs → zs * z₀ = z₀ * zs →
      (zs * z₀⁻¹ ∈ oddCoreIn (Subgroup.centralizer ({u} : Set G)) → False) → False := by
    intro Ns zs hNs hzs hcs hfin
    have hΘN : outerGen Ω K ≤ commModOdd u Ns := hΘ Ns hNs
    have hzs2 : zs * zs = 1 := mul_self_of_isClassicalMember3 hzs
    have hzsinv : zs⁻¹ = zs := inv_eq_of_mul_eq_one_right hzs2
    have hNsC : Ns ≤ Subgroup.centralizer ({u} : Set G) := hNs.1.2
    have hzsC : zs ∈ Subgroup.centralizer ({u} : Set G) := hNsC hzs.mem
    have hF₀C : ∀ g ∈ Subgroup.closure (Set.range zz), g ∈ Subgroup.centralizer ({u} : Set G) := by
      intro g hg
      have hle : Subgroup.closure (Set.range zz) ≤ Subgroup.centralizer ({u} : Set G) := by
        rw [Subgroup.closure_le]
        rintro _ ⟨o, rfl⟩
        rcases o with _ | k
        · exact hKC hz₀.mem
        · exact (hΘN (hzkΘ k)).1
      exact hle hg
    have hF₀le : Subgroup.closure (Set.range zz) ≤ commModOdd u (Subgroup.zpowers zs) := by
      rw [Subgroup.closure_le]
      rintro _ ⟨o, rfl⟩
      rcases o with _ | k
      · refine ⟨hKC hz₀.mem, fun y hy => ?_⟩
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        have hc : z₀ * zs ^ m = zs ^ m * z₀ := ((Commute.zpow_left hcs m).eq).symm
        show z₀ * zs ^ m * z₀⁻¹ * (zs ^ m)⁻¹ ∈
          oddCoreIn (Subgroup.centralizer ({u} : Set G))
        rw [hc, mul_inv_cancel_right, mul_inv_cancel]
        exact Subgroup.one_mem _
      · have h := hΘN (hzkΘ k)
        exact ⟨h.1, fun y hy => h.2 y (Subgroup.zpowers_le.mpr hzs.mem hy)⟩
    have hzA : ∀ g ∈ Subgroup.closure (Set.range zz),
        zs * (g * zs * g⁻¹) ∈ oddCoreIn (Subgroup.centralizer ({u} : Set G)) := by
      intro g hg
      have h1 := (oddCoreIn _).inv_mem ((hF₀le hg).2 zs (Subgroup.mem_zpowers zs))
      have e : zs * (g * zs * g⁻¹) = (g * zs * g⁻¹ * zs⁻¹)⁻¹ := by
        have h2 : (g * zs * g⁻¹ * zs⁻¹)⁻¹ = zs * g * zs⁻¹ * g⁻¹ := by group
        rw [h2, hzsinv]
        group
      rw [e]
      exact h1
    obtain ⟨n, hnO, hfix⟩ := Bootstrap.exists_conj_fixed_of_isPGroup
      (A := Subgroup.closure (Set.range zz))
      (N := oddCoreIn (Subgroup.centralizer ({u} : Set G))) hF₀p (odd_card_oddCoreIn _)
      (fun g hg m hm => conj_mem_oddCoreIn (hF₀C g hg) hm) hzs2
      (fun m hm => conj_mem_oddCoreIn hzsC hm) hzA
    have hN'Ω : conjSub n Ns ∈ Ω := hΩ.conjInvariant n _ hNs.1.1
    have hN'i : conjSub n Ns ∈ compMembers3 Ω u Du iK :=
      conjSub_mem_compMembers_of_oddCoreIn3 hΩ.conjInvariant hNs hnO
    have hN'C : conjSub n Ns ≤ Subgroup.centralizer ({u} : Set G) := hN'i.1.2
    have hz' : IsClassicalMember3 (conjSub n Ns) (n * zs * n⁻¹) := hzs.conj n
    have hΘ' : outerGen Ω K ≤ commModOdd u (conjSub n Ns) :=
      hΘN.trans (commModOdd_le_conjSub hNsC hnO)
    have hFle : Subgroup.closure (Set.range zk) ≤ Subgroup.closure (Set.range zz) :=
      Subgroup.closure_mono (by rintro _ ⟨k, rfl⟩; exact ⟨some k, rfl⟩)
    have hFΘ : Subgroup.closure (Set.range zk) ≤ outerGen Ω K := by
      rw [Subgroup.closure_le]
      rintro _ ⟨k, rfl⟩
      exact hzkΘ k
    have hFcent : ∀ g ∈ Subgroup.closure (Set.range zk), ∀ y ∈ conjSub n Ns,
        g * y = y * g := fun g hg =>
      centralizes_of_exact_of_comm_mem_oddCoreIn3 S hN'Ω hN'C hz' (hfix g (hFle hg))
        (hΘ' (hFΘ hg)).2
    have hcentMk : ∀ k, ∀ g ∈ conjSub n Ns, ∀ y ∈ Mk k, g * y = y * g := by
      intro k g hg y hy
      have hzkF : zk k ∈ Subgroup.closure (Set.range zk) := Subgroup.subset_closure ⟨k, rfl⟩
      have hgz : g * zk k * g⁻¹ = zk k := by
        rw [← hFcent (zk k) hzkF g hg]
        group
      obtain ⟨j, hj, -⟩ := exists_unique_comp_u hΩ hex Du ⟨(hMk k).1.1, H1 _ (hMk k)⟩
      have hij : iK ≠ j := fun h => hCaseI _ (hMk k) (h ▸ hj)
      exact centralizes_of_exact_of_comm_mem_oddCoreIn3 S (hMk k).1.1 (H1 _ (hMk k)) (hzk k) hgz
        (fun y' hy' => comm_mem_oddCoreIn_of_ne_comp3 hΩ.conjInvariant hij hN'i hj hg hy') y hy
    have hJc : ∀ L ∈ outerSet Ω K, Commutes (conjSub n Ns) L := by
      intro L hL g hg l hl
      have hle : (⨆ k, Mk k) ≤ Subgroup.centralizer ({g} : Set G) :=
        iSup_le fun k y hy =>
          Subgroup.mem_centralizer_singleton_iff.mpr (hcentMk k g hg y hy).symm
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hle (hMkgen L hL hl))).symm
    have hz₀F : z₀ ∈ Subgroup.closure (Set.range zz) := Subgroup.subset_closure ⟨none, rfl⟩
    have hcz₀ : z₀ * (n * zs * n⁻¹) = (n * zs * n⁻¹) * z₀ := by
      have h := hfix z₀ hz₀F
      calc z₀ * (n * zs * n⁻¹) = z₀ * (n * zs * n⁻¹) * z₀⁻¹ * z₀ := by group
        _ = (n * zs * n⁻¹) * z₀ := by rw [h]
    have hcn : cnbhd Ω (conjSub n Ns) = cnbhd Ω K :=
      ca_of_cliques_comm3 hnab S hKΩ hN'Ω hJc hz₀ hz' hcz₀
    have hz'K : IsClassicalMember3 (conjSub n Ns) z₀ :=
      isClassicalMember_of_twin3 hnab S hKΩ hN'Ω hcn hz₀
    have hz'eq : n * zs * n⁻¹ = z₀ := involution_unique3 hz' hz'K
    have hz₀C : z₀ ∈ Subgroup.centralizer ({u} : Set G) := hKC hz₀.mem
    have htO : zs * z₀⁻¹ ∈ oddCoreIn (Subgroup.centralizer ({u} : Set G)) := by
      have hzse : zs = n⁻¹ * z₀ * n := by rw [← hz'eq]; group
      have e : zs * z₀⁻¹ = n⁻¹ * (z₀ * n * z₀⁻¹) := by rw [hzse]; group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hnO) (conj_mem_oddCoreIn hz₀C hnO)
    exact hfin htO
  obtain ⟨zN, hzN⟩ : ∃ zN : G, zN = x * z₀ * x⁻¹ := ⟨_, rfl⟩
  have hzNcl : IsClassicalMember3 (conjSub x K) zN := hzN ▸ hz₀.conj x
  have ht4' : (zN * z₀⁻¹) ^ 4 = 1 := by rw [hzN]; exact ht4
  have htne' : zN * z₀⁻¹ ≠ 1 := by rw [hzN]; exact htne
  have hzN2 : zN * zN = 1 := mul_self_of_isClassicalMember3 hzNcl
  have hz₀inv : z₀⁻¹ = z₀ := inv_eq_of_mul_eq_one_right hz₀2
  have hzNinv : zN⁻¹ = zN := inv_eq_of_mul_eq_one_right hzN2
  by_cases hcomm : zN * z₀ = z₀ * zN
  ·
    refine key (conjSub x K) zN hNi hzNcl hcomm fun hO => htne' ?_
    exact eq_one_of_mem_oddCoreIn_of_pow_four hO ht4'
  ·
    have hzNY : zN ∈ locLayer Ω u := le_centralizingLayer hNi.1 hzNcl.mem
    have hKz : conjSub zN K ∈ compMembers3 Ω u Du iK :=
      conjSub_mem_compMembers_of_mem_layer3 hΩ.conjInvariant hKi hzNY
    have hcl : IsClassicalMember3 (conjSub zN K) (zN * z₀ * zN⁻¹) := hz₀.conj zN
    have ha4 : (zN * z₀ * zN * z₀) * (zN * z₀ * zN * z₀) = 1 := by
      have h4 : (zN * z₀) ^ 4 = 1 := by rw [hz₀inv] at ht4'; exact ht4'
      calc (zN * z₀ * zN * z₀) * (zN * z₀ * zN * z₀) = (zN * z₀) ^ 4 := by
            simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        _ = 1 := h4
    have hinvz : (zN * z₀ * zN * z₀)⁻¹ = z₀ * zN * z₀ * zN := by
      rw [mul_inv_rev, mul_inv_rev, mul_inv_rev, hzNinv, hz₀inv]
      group
    have hcs : (zN * z₀ * zN⁻¹) * z₀ = z₀ * (zN * z₀ * zN⁻¹) := by
      have h := eq_inv_of_mul_eq_one_left ha4
      rw [hinvz] at h
      rw [hzNinv]
      calc zN * z₀ * zN * z₀ = z₀ * zN * z₀ * zN := h
        _ = z₀ * (zN * z₀ * zN) := by group
    refine key (conjSub zN K) (zN * z₀ * zN⁻¹) hKz hcl hcs fun hO => hcomm ?_
    have hsame : zN * z₀ * zN⁻¹ * z₀⁻¹ = zN * z₀ * zN * z₀ := by rw [hzNinv, hz₀inv]
    rw [hsame] at hO
    have h1 : zN * z₀ * zN * z₀ = 1 := by
      refine eq_one_of_mem_oddCoreIn_of_pow_four hO ?_
      calc (zN * z₀ * zN * z₀) ^ 4 = ((zN * z₀ * zN * z₀) * (zN * z₀ * zN * z₀)) *
            ((zN * z₀ * zN * z₀) * (zN * z₀ * zN * z₀)) := by
            simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        _ = 1 := by rw [ha4, one_mul]
    have h2 : (zN * z₀) * (zN * z₀) = 1 := by
      rw [← h1]
      group
    have h3 := eq_inv_of_mul_eq_one_left h2
    rw [mul_inv_rev, hzNinv, hz₀inv] at h3
    exact h3

end Main

end CFSG.ClassicalInvolution.Q3.Q3W.EX

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank


theorem rowShapeExoticD43 (h3 : OddThreeFreeInput) : RowPiece3 ShapeExoticD43 := by
  rintro a t n ⟨rfl, rfl, rfl⟩ G _ _ _ hnab K z hR hshape
  exact (EX.false_of_d4_four3 hnab ⟨hR, h3 G K z hR, hshape⟩).elim

end CFSG.ClassicalInvolution.Q3.Q3W
