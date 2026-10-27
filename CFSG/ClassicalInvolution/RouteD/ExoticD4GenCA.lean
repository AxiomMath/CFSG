module

public import CFSG.ClassicalInvolution.RouteD.ExoticD4GenModel
public import CFSG.ClassicalInvolution.RouteD.ExoticD4FourTwins
public import CFSG.ClassicalInvolution.RouteD.ExoticD4FourPair
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import CFSG.ClassicalInvolution.RouteD.ExoticD4FourLift

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin QuadraticMap CFSG.ClassicalGroups.Orthogonal
  CFSG.ClassicalInvolution.ModelFacts

section Model

variable {p f : ℕ} [Fact p.Prime]

theorem generate_of_comm_of_eq (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {t : StatedLieTag} {n e : ℕ}
    (ht : t = .POmegaPlus) (hn : n = 4) (he : e = f)
    {R R' : Subgroup (Generic.modelUniv t n p e Fact.out).K}
    (hR : R ∈ Generic.fundamentalSubgroups t (Generic.modelUniv t n p e Fact.out).D)
    (hR' : R' ∈ Generic.fundamentalSubgroups t (Generic.modelUniv t n p e Fact.out).D)
    (hne : R' ≠ R) (hnc : ¬ Commutes R R') {c c' : (Generic.modelUniv t n p e Fact.out).K}
    (hc : c ∈ R) (hcz : ∀ r ∈ R, c * r = r * c) (hc1 : c ≠ 1) (hc' : c' ∈ R')
    (hcz' : ∀ r ∈ R', c' * r = r * c') (hc1' : c' ≠ 1)
    (hcomm : c * c' * c⁻¹ * c'⁻¹ ∈ Subgroup.center (Generic.modelUniv t n p e Fact.out).K) :
    (⨆ S ∈ {S : Subgroup (Generic.modelUniv t n p e Fact.out).K |
      S ∈ Generic.fundamentalSubgroups t (Generic.modelUniv t n p e Fact.out).D ∧
        (S = R ∨ Commutes S R ∨ S = R' ∨ Commutes S R')}, S) = ⊤ := by
  subst ht hn he
  have hn3 : 3 ≤ 4 := by norm_num
  have hF := D4Facts.of_galoisField (p := p) (f := e) hp2 hq
  have hM : Generic.modelUniv .POmegaPlus 4 p e Fact.out =
      ⟨spinGroup (quadPlus 4 (GaloisField p e)), plusDatum 4 (GaloisField p e) hn3⟩ :=
    (rfl : Generic.modelUniv .POmegaPlus 4 p e Fact.out =
      ModelFacts.modelUniv .POmegaPlus 4 p e Fact.out).trans (modelUniv_POmegaPlus hn3)
  have key : ∀ M : LieUniversal, M =
      ⟨spinGroup (quadPlus 4 (GaloisField p e)), plusDatum 4 (GaloisField p e) hn3⟩ →
      ∀ R R' : Subgroup M.K, R ∈ Generic.fundamentalSubgroups .POmegaPlus M.D →
        R' ∈ Generic.fundamentalSubgroups .POmegaPlus M.D → R' ≠ R → ¬ Commutes R R' →
        ∀ c c' : M.K, c ∈ R → (∀ r ∈ R, c * r = r * c) → c ≠ 1 → c' ∈ R' →
          (∀ r ∈ R', c' * r = r * c') → c' ≠ 1 →
          c * c' * c⁻¹ * c'⁻¹ ∈ Subgroup.center M.K →
        (⨆ S ∈ {S : Subgroup M.K | S ∈ Generic.fundamentalSubgroups .POmegaPlus M.D ∧
          (S = R ∨ Commutes S R ∨ S = R' ∨ Commutes S R')}, S) = ⊤ := by
    intro M hM
    subst hM
    intro R R' hR hR' hne hnc c c' hc hcz hc1 hc' hcz' hc1' hcomm
    exact hF.generate_of_comm hR hR' hne hnc hc hcz hc1 hc' hcz' hc1' hcomm
  exact key _ hM R R' hR hR' hne hnc c c' hc hcz hc1 hc' hcz' hc1' hcomm

end Model

section Corr

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {x : G}
  {D : LieSystemData p f (locQuot Ω x) (locFamily Ω x)} {i : Fin D.card}

theorem exists_central_corr
    (hperf : FundPerfect (D.tag i) (Generic.modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D)
    {N : Subgroup G} {R : Subgroup (Generic.modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K}
    (h : Corr Ω x D i N R) {z : G} (hz : IsClassicalMember p f N z) :
    ∃ c ∈ R, (∀ r ∈ R, c * r = r * c) ∧ c ≠ 1 ∧
      D.hom i c = locMk Ω x ⟨z, le_centralizingLayer h.1 hz.mem⟩ := by
  have hzY : z ∈ locLayer Ω x := le_centralizingLayer h.1 hz.mem
  have hmem : locMk Ω x ⟨z, hzY⟩ ∈ R.map (D.hom i) := by
    rw [← h.2.2]
    exact ⟨⟨z, hzY⟩, Subgroup.mem_subgroupOf.mpr hz.mem, rfl⟩
  obtain ⟨c, hcR, hcimg⟩ := hmem
  have hzc : ∀ y ∈ N, y * z = z * y := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mp (le_centralizer_of_isClassicalMember hz hy)
  have hperf' : ⁅R, R⁆ = R :=
    le_antisymm (Subgroup.commutator_le.mpr fun a ha b hb =>
      R.mul_mem (R.mul_mem (R.mul_mem ha hb) (R.inv_mem ha)) (R.inv_mem hb)) (hperf R h.2.1)
  refine ⟨c, hcR, ?_, ?_, hcimg⟩
  · have hcent : c ∈ Subgroup.centralizer (R : Set _) :=
      Models.Transfer.mem_centralizer_of_map (D.ker_le_center i) hperf' (g := c) (by
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        rw [← h.2.2] at ha
        obtain ⟨y, hy, rfl⟩ := ha
        rw [hcimg]
        show locMk Ω x y * locMk Ω x ⟨z, hzY⟩ = locMk Ω x ⟨z, hzY⟩ * locMk Ω x y
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (hzc y (Subgroup.mem_subgroupOf.mp hy)))
    intro r hr
    exact (Subgroup.mem_centralizer_iff.mp hcent r hr).symm
  · rintro rfl
    rw [map_one] at hcimg
    have hker : (⟨z, hzY⟩ : ↥(locLayer Ω x)) ∈ classicalInvolutionOddCore ↥(locLayer Ω x) := by
      rw [← QuotientGroup.eq_one_iff (N := classicalInvolutionOddCore ↥(locLayer Ω x))]
      exact hcimg.symm
    have hodd : Odd (Nat.card (classicalInvolutionOddCore ↥(locLayer Ω x))) :=
      CFSG.ComponentClassification.OddCore.odd_card ↥(locLayer Ω x)
    have hd := Subgroup.orderOf_dvd_natCard (classicalInvolutionOddCore ↥(locLayer Ω x)) hker
    have h2 : orderOf (⟨z, hzY⟩ : ↥(locLayer Ω x)) = 2 := by
      rw [← Subgroup.orderOf_coe]
      exact hz.orderOf_eq_two
    rw [h2] at hd
    have := Nat.odd_iff.mp hodd
    omega

end Corr

section CA

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {K : Subgroup G} {z : G}

theorem ca_of_cliques_comm (hnab : ∃ x y : G, x * y ≠ y * x)
    (S : RouteDSetup p f K z) (hloc : LocalShapeT p f 4 .POmegaPlus 4 (conjClass K) z)
    {N J : Subgroup G} (hN : N ∈ conjClass K) (hJ : J ∈ conjClass K)
    (hJc : ∀ L ∈ outerSet (conjClass K) N, Commutes J L) {zN zJ : G}
    (hzN : IsClassicalMember p f N zN) (hzJ : IsClassicalMember p f J zJ)
    (hzcomm : zN * zJ = zJ * zN) :
    cnbhd (conjClass K) J = cnbhd (conjClass K) N := by
  classical
  by_contra hne
  set Ω := conjClass K with hΩdef
  have hΩ : InClass p f Ω := S.inClass
  have hex : ExactMembers Ω := S.exact
  have hf : 0 < f := routeD_f_pos S
  have hq4 : 4 ≤ p ^ f := by
    have := S.five
    omega
  obtain ⟨M, hM⟩ := outerSet_nonempty_of_shape S hloc hN
  have hMΩ : M ∈ Ω := hM.1.1
  have hNM : N ∈ outerSet Ω M := mem_outerSet_symm hN hM
  have hJN : J ≠ N := fun h => hne (by rw [h])
  have hnotcomm : ¬ Commutes J N := by
    intro hc
    have hJin : J ∈ outerSet Ω N := ⟨⟨hJ, Or.inr hc⟩, hne⟩
    obtain ⟨L, hL, -, hnc⟩ := exists_noncommuting_outer S hloc hN hJin
    exact hnc (hJc L hL)
  have hJM : J ∈ outerSet Ω M := by
    refine ⟨⟨hJ, Or.inr (hJc M hM)⟩, fun h => ?_⟩
    obtain ⟨L, hL, hLM, hnc⟩ := exists_noncommuting_outer S hloc hN hM
    have hLJ : L ∈ cnbhd Ω J := ⟨hL.1.1, Or.inr (commutes_symm (hJc L hL))⟩
    rw [h] at hLJ
    exact hnc (commutes_symm (hLJ.2.resolve_left hLM))
  obtain ⟨w, hw, hP1, D, i₁, hcard, ht, hr, hrest⟩ := exists_D4At S hloc hMΩ
  have hout := outerSet_eq_compMembers S.odd hf S.five hΩ hex hw hMΩ hP1
    (single_class_of_mem hMΩ) D ht hr hrest
  have hperf := D.fundPerfect S.odd hq4
    (trialityD4_vacuous D (by decide : StatedLieTag.POmegaPlus ≠ .trialityD4) ht hrest) i₁
  have hexp : D.exp i₁ = f := by
    rcases D.exp_eq i₁ with h | ⟨h, -⟩
    · exact h
    · rw [ht] at h
      exact absurd h (by decide)
  have hsc := fundamentalSingleClass_of_ne D i₁ (by rw [ht]; decide) (by rw [ht]; decide)
  have hNc : N ∈ compMembers Ω w D i₁ := hout ▸ hNM
  have hJc' : J ∈ compMembers Ω w D i₁ := hout ▸ hJM
  obtain ⟨RN, hRN⟩ := exists_corr_left hΩ hex D hNc
  obtain ⟨RJ, hRJ⟩ := exists_corr_left hΩ hex D hJc'
  have hne' : RJ ≠ RN := fun h => hJN (corr_unique_right hΩ hP1 hRJ (h ▸ hRN))
  have hnc' : ¬ Commutes RN RJ := fun h =>
    hnotcomm (commutes_symm ((corr_commutes hΩ hP1 hperf hRN hRJ).mpr h))
  obtain ⟨cN, hcNR, hcNz, hcN1, hcNimg⟩ := exists_central_corr hperf hRN hzN
  obtain ⟨cJ, hcJR, hcJz, hcJ1, hcJimg⟩ := exists_central_corr hperf hRJ hzJ
  have hcomm : cN * cJ * cN⁻¹ * cJ⁻¹ ∈
      Subgroup.center (Generic.modelUniv (D.tag i₁) (D.rank i₁) p (D.exp i₁) Fact.out).K := by
    refine D.ker_le_center i₁ ?_
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hcNimg, hcJimg]
    have hab : locMk Ω w ⟨zN, le_centralizingLayer hRN.1 hzN.mem⟩ *
        locMk Ω w ⟨zJ, le_centralizingLayer hRJ.1 hzJ.mem⟩ =
        locMk Ω w ⟨zJ, le_centralizingLayer hRJ.1 hzJ.mem⟩ *
          locMk Ω w ⟨zN, le_centralizingLayer hRN.1 hzN.mem⟩ := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hzcomm
    rw [hab, mul_inv_cancel_right, mul_inv_cancel]
  have hgen := generate_of_comm_of_eq S.odd S.five ht hr hexp hRN.2.1 hRJ.2.1 hne' hnc'
    hcNR hcNz hcN1 hcJR hcJz hcJ1 hcomm
  set 𝒮 := {S' : Subgroup (Generic.modelUniv (D.tag i₁) (D.rank i₁) p (D.exp i₁) Fact.out).K |
    S' ∈ Generic.fundamentalSubgroups (D.tag i₁)
      (Generic.modelUniv (D.tag i₁) (D.rank i₁) p (D.exp i₁) Fact.out).D ∧
      (S' = RN ∨ Commutes S' RN ∨ S' = RJ ∨ Commutes S' RJ)} with h𝒮
  have hgen' : (⨆ s : ↥𝒮, s.1) = ⊤ := by
    rw [← hgen]
    exact (iSup_subtype' (p := fun S' => S' ∈ 𝒮) (f := fun S' _ => S')).symm
  choose T hT using fun s : ↥𝒮 => exists_corr_right hΩ D hsc s.2.1
  have hTout : ∀ s : ↥𝒮, T s ∈ outerSet Ω M := fun s => by
    rw [hout]
    exact ⟨(hT s).1, (hT s).2.2 ▸ Subgroup.map_le_range _ _⟩
  have hTB : ∀ s : ↥𝒮, ∀ L ∈ outerSet Ω N, Commutes (T s) L := by
    intro s L hL
    have hLne : ∀ Y, cnbhd Ω Y = cnbhd Ω N → L ≠ Y := fun Y hY h => hL.2 (by rw [h, hY])
    rcases s.2.2 with h | h | h | h
    · have hTN : T s = N := corr_unique_right hΩ hP1 (hT s) (h ▸ hRN)
      rw [hTN]
      exact commutes_symm (hL.1.2.resolve_left (hLne N rfl))
    · have hc : Commutes (T s) N := (corr_commutes hΩ hP1 hperf (hT s) hRN).mpr h
      have htw := commutes_outer_eq_twin S hloc hN hM (hTout s) hc
      have hLmem : L ∈ cnbhd Ω (T s) := by
        rw [htw]
        exact hL.1
      exact commutes_symm (hLmem.2.resolve_left (hLne (T s) htw))
    · have hTJ : T s = J := corr_unique_right hΩ hP1 (hT s) (h ▸ hRJ)
      rw [hTJ]
      exact hJc L hL
    · have hc : Commutes (T s) J := (corr_commutes hΩ hP1 hperf (hT s) hRJ).mpr h
      have hMJ : M ∈ outerSet Ω J := mem_outerSet_symm hMΩ hJM
      have htw := commutes_outer_eq_twin S hloc hJ hMJ (hTout s) hc
      have hLmem : L ∈ cnbhd Ω (T s) := by
        rw [htw]
        exact ⟨hL.1.1, Or.inr (commutes_symm (hJc L hL))⟩
      refine commutes_symm (hLmem.2.resolve_left fun hLT => ?_)
      have hNmem : N ∈ cnbhd Ω (T s) := by
        rw [← hLT]
        exact mem_cnbhd_symm hN hL.1
      rw [htw] at hNmem
      rcases hNmem.2 with hNJ | hNJ
      · exact hJN hNJ.symm
      · exact hnotcomm (commutes_symm hNJ)
  set Θ := outerGen Ω N with hΘ
  have hTle : ∀ s : ↥𝒮, T s ≤ Subgroup.centralizer (Θ : Set G) := by
    intro s g hg
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hΘg : Θ ≤ Subgroup.centralizer ({g} : Set G) := iSup₂_le fun L hL y hy =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hTB s L hL g hg y hy).symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hΘg hh)
  have hΞ : outerGen Ω M ≤ Subgroup.centralizer (Θ : Set G) := by
    refine iSup₂_le fun L hL => ?_
    have hLc : L ∈ compMembers Ω w D i₁ := hout ▸ hL
    have := le_iSup_of_model_generates hΩ hP1 T (fun s => s.1) hT hgen' hLc
    exact this.trans (iSup_le hTle)
  have htop : Subgroup.normalizer (Θ : Set G) = ⊤ :=
    eq_top_of_outerGen_le S hloc hN hM Subgroup.le_normalizer
      (hΞ.trans (Subgroup.centralizer_le_normalizer _))
  have hnormal : Θ.Normal := Subgroup.normalizer_eq_top_iff.mp htop
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Θ with hbot | htop'
  · obtain ⟨zM, hzM⟩ := hΩ.classical M hMΩ
    have hmem : zM ∈ Θ := le_outerGen hM hzM.mem
    rw [hbot, Subgroup.mem_bot] at hmem
    have h2 := hzM.orderOf_eq_two
    rw [hmem, orderOf_one] at h2
    omega
  · obtain ⟨zN, hzN⟩ := hΩ.classical N hN
    have hzc : zN ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro h
      have hΘg : Θ ≤ Subgroup.centralizer ({zN} : Set G) := iSup₂_le fun L hL y hy =>
        Subgroup.mem_centralizer_singleton_iff.mpr
          ((hL.1.2.resolve_left (fun h' => hL.2 (by rw [h']))) y hy zN hzN.mem)
      exact Subgroup.mem_centralizer_singleton_iff.mp (hΘg (htop' ▸ Subgroup.mem_top h))
    rw [center_eq_bot_of_simple hnab, Subgroup.mem_bot] at hzc
    have h2 := hzN.orderOf_eq_two
    rw [hzc, orderOf_one] at h2
    omega

end CA

end CFSG.ClassicalInvolution.RouteD.Exotic
