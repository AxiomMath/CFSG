module

public import CFSG.ClassicalInvolution.Asc77.AscT7AProved

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic AscE184Sect ExactLayer
open scoped commutatorElement

section Sections

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {A : Subgroup G}

theorem section_connected_or_orbit (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hA : IsPGroup 2 ↥A) (hY : sectionHull Ω A ≠ ⊤) (hBelow : CITBelowU p f (Nat.card G))
    (h3s : T3.Thm3SectBelow p f (Nat.card G)) {B : Subgroup G} (hB : B ∈ sectionMembers Ω A) :
    T3.DStarConnected (quotFamily (restrictFamily (sectionFamily Ω A) (sectionHull Ω A))
        (classicalInvolutionOddCore ↥(sectionHull Ω A))) ∨
      ∀ M ∈ quotFamily (restrictFamily (sectionFamily Ω A) (sectionHull Ω A))
          (classicalInvolutionOddCore ↥(sectionHull Ω A)),
        ∃ y : ↥(sectionHull Ω A) ⧸ classicalInvolutionOddCore ↥(sectionHull Ω A),
          conjSub y (((secMember A B).subgroupOf (sectionHull Ω A)).map
            (QuotientGroup.mk' (classicalInvolutionOddCore ↥(sectionHull Ω A)))) = M := by
  set Y := sectionHull Ω A with hYdef
  set Λ : Set (Subgroup ↥Y) := restrictFamily (sectionFamily Ω A) Y with hΛdef
  set N₀ : Subgroup ↥Y := classicalInvolutionOddCore ↥Y with hN₀def
  have hN₀odd : Odd (Nat.card N₀) := CFSG.ComponentClassification.OddCore.odd_card ↥Y
  have hΛ : HypOmegaMod p f Λ := hypOmegaMod_sectionFamily hp hq hΩ hA
  have hΛ' : HypOmegaMod p f (quotFamily Λ N₀) := oddQuotHyp p f hp hq ↥Y Λ hΛ N₀ hN₀odd
  have hltY := natCard_lt_of_ne_top hY
  have hlt : Nat.card (↥Y ⧸ N₀) < Nat.card G := by
    have h1 : Nat.card (↥Y ⧸ N₀) ≤ Nat.card ↥Y :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card N₀)
    omega
  have hOq : classicalInvolutionOddCore (↥Y ⧸ N₀) = ⊥ :=
    CFSG.ComponentClassification.OddCore.quotient_corefree ↥Y
  have hBΛ : (secMember A B).subgroupOf Y ∈ Λ := subgroupOf_secMember_mem hB
  by_cases hconn : T3.DStarConnected (quotFamily Λ N₀)
  · exact Or.inl hconn
  · right
    have hΛA : ∀ L ∈ Λ, AEmpty Λ L := h3s hp hq ↥Y hltY Λ hΛ hconn
    have hAΛ' := aEmpty_quotFamily hp hq hΛ hΛ' hN₀odd hΛA
    rcases dichotomy_of_thm4 hp hq (thm4Below_of_citBelow hBelow) hlt hΛ' hOq hAΛ'
      (map_mem_quotFamily hBΛ) with hc | horb
    · exact absurd (T3.dstarConnected_of_pivot (map_mem_quotFamily hBΛ) hc) hconn
    · exact horb

theorem exists_mem_sectionHull_conj_of_orbit (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) (hA : IsPGroup 2 ↥A) {B : Subgroup G} (hB : B ∈ sectionMembers Ω A)
    (horb : ∀ M ∈ quotFamily (restrictFamily (sectionFamily Ω A) (sectionHull Ω A))
          (classicalInvolutionOddCore ↥(sectionHull Ω A)),
        ∃ y : ↥(sectionHull Ω A) ⧸ classicalInvolutionOddCore ↥(sectionHull Ω A),
          conjSub y (((secMember A B).subgroupOf (sectionHull Ω A)).map
            (QuotientGroup.mk' (classicalInvolutionOddCore ↥(sectionHull Ω A)))) = M)
    {J₁ : Subgroup G} (hJ₁ : J₁ ∈ sectionMembers Ω A) :
    ∃ g ∈ sectionHull Ω A, J₁ = conjSub g B := by
  set Y := sectionHull Ω A with hYdef
  set Λ : Set (Subgroup ↥Y) := restrictFamily (sectionFamily Ω A) Y with hΛdef
  set N₀ : Subgroup ↥Y := classicalInvolutionOddCore ↥Y with hN₀def
  have hN₀odd : Odd (Nat.card N₀) := CFSG.ComponentClassification.OddCore.odd_card ↥Y
  have hΛ : HypOmegaMod p f Λ := hypOmegaMod_sectionFamily hp hq hΩ hA
  have hBΛ : (secMember A B).subgroupOf Y ∈ Λ := subgroupOf_secMember_mem hB
  have hJ₁Λ : (secMember A J₁).subgroupOf Y ∈ Λ := subgroupOf_secMember_mem hJ₁
  obtain ⟨yb, hyb⟩ := horb _ (map_mem_quotFamily hJ₁Λ)
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N₀ yb
  have hKy : conjSub y ((secMember A B).subgroupOf Y) ∈ Λ := hΛ.conjInvariant y _ hBΛ
  have himg : (conjSub y ((secMember A B).subgroupOf Y)).map (QuotientGroup.mk' N₀) =
      ((secMember A J₁).subgroupOf Y).map (QuotientGroup.mk' N₀) := by
    rw [AscQuot.map_conjSub]
    exact hyb
  obtain ⟨n, -, hn⟩ := exists_conj_of_map_eq hp hq hΛ hN₀odd hKy hJ₁Λ himg
  refine ⟨((n * y : ↥Y) : G), (n * y).2, ?_⟩
  have hnyC : ((n * y : ↥Y) : G) ∈ Subgroup.centralizer (A : Set G) :=
    sectionHull_le_centralizer Ω A (n * y).2
  have h1 : (secMember A J₁).subgroupOf Y =
      (secMember A (conjSub ((n * y : ↥Y) : G) B)).subgroupOf Y := by
    rw [hn, ← conjSub_mul, ← conjSub_secMember hnyC]
    exact conjSub_subgroupOf Y (n * y) (secMember A B)
  have h2 : secMember A J₁ = secMember A (conjSub ((n * y : ↥Y) : G) B) := by
    have hle1 : secMember A J₁ ≤ Y := le_sectionHull hJ₁
    have hle2 : secMember A (conjSub ((n * y : ↥Y) : G) B) ≤ Y :=
      le_sectionHull (conjSub_mem_sectionMembers hΩ hnyC hB)
    have := congrArg (Subgroup.map Y.subtype) h1
    rwa [Subgroup.map_subgroupOf_eq_of_le hle1, Subgroup.map_subgroupOf_eq_of_le hle2] at this
  exact eq_of_secMember_eq hp hΩ hA hJ₁ (conjSub_mem_sectionMembers hΩ hnyC hB) h2

omit [Finite G] in
theorem sectionHull_le_rLayer (Ω : Set (Subgroup G)) (c : G) :
    sectionHull Ω (Subgroup.zpowers c) ≤ rLayer Ω c := by
  refine iSup₂_le fun L hL => ?_
  obtain ⟨J, hJ, rfl⟩ := hL
  refine iSup₂_le fun T hT => ?_
  have hTc : T ≤ Subgroup.centralizer ({c} : Set G) := by
    have := hT.2
    rwa [CFSG.ClassicalInvolution.Balance.Bootstrap.centralizer_zpowers_eq_singleton'] at this
  exact le_iSup₂_of_le T (mem_RSet_of_isSylow2In hJ.1 hT.1) (le_iSup_of_le hTc le_rfl)

end Sections

section Frame

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem exists_mem_tqMembers_u (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {K K' J : Subgroup G} {z u t : G} (hK : K ∈ Ω) (hz : IsUniqueInvolution K z)
    (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K) (hu : u ∈ K ⊔ K') (hu2 : u * u = 1) (hu1 : u ≠ 1)
    (hJ : J ∈ omegaOfSet Ω (twinSet Ω K)) (_ht : IsUniqueInvolution J t) :
    ∃ g ∈ K ⊔ K', conjSub g J ∈ omegaOfSet Ω (twinSet Ω K) ∧ conjSub g J ∈ tqMembers Ω u := by
  have hK'Ω : K' ∈ Ω := hK'.1
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hK'
  have hJΩ : J ∈ Ω := hJ.1
  obtain ⟨R₁, R₂, hR₁, hR₂, hc, huR⟩ :=
    T7A.exists_sylow_pair_of_mem hp hΩ hK hK'Ω hne hz hzK' hu hu2 hu1
  obtain ⟨S₀, R₀, R₀', T₀, hR₀, hR₀', hT₀, hR₀S, hR₀'S, hT₀S, hc₀, hRT₀, hR'T₀⟩ :=
    exists_twinSylow hp hq hΩ hK hz hK' hne hJ
  obtain ⟨g, hgQ, hgR, hgR'⟩ :=
    T7A.exists_conj_sylow_pair hp hΩ hK hK'Ω hne hz hzK' hR₁ hR₂ hc hR₀ hR₀' hc₀
  have hKN : K' ≤ Subgroup.normalizer (K : Set G) := hΩ.le_normalizer_of_twin hK'Ω hK hne hzK' hz
  have hgiK : conjSub g⁻¹ K = K :=
    mem_normalizer_iff_conjSub_eq.mp (Subgroup.inv_mem _ ((sup_le Subgroup.le_normalizer hKN) hgQ))
  have hJ' : conjSub g J ∈ omegaOfSet Ω (twinSet Ω K) := by
    refine ⟨hΩ.conjInvariant g J hJΩ, fun L hL => ?_⟩
    have hL' : conjSub g⁻¹ L ∈ twinSet Ω K := by
      have := twinSet_conj hΩ.conjInvariant hL g⁻¹
      rwa [hgiK] at this
    have := omegaNbr_conj hΩ.conjInvariant (hJ.2 _ hL') g
    rwa [conjSub_conjSub_inv] at this
  refine ⟨g, hgQ, hJ', ?_⟩
  have hTsyl : IsSylow2In (conjSub g T₀) (conjSub g J) := hT₀.conj g
  have hcRT : Commutes R₁ (conjSub g T₀) := by
    have := hRT₀.conjSub g
    rwa [hgR] at this
  have hcR'T : Commutes R₂ (conjSub g T₀) := by
    have := hR'T₀.conjSub g
    rwa [hgR'] at this
  obtain ⟨x, hx, y, hy, hxy⟩ := AscE186.exists_mul_of_mem_sup_of_commutes hc huR
  have hTc : conjSub g T₀ ≤ Subgroup.centralizer ({u} : Set G) := by
    intro s hs
    rw [Subgroup.mem_centralizer_singleton_iff, ← hxy]
    have h1 : x * s = s * x := hcRT x hx s hs
    have h2 : y * s = s * y := hcR'T y hy s hs
    calc s * (x * y) = (s * x) * y := by group
      _ = (x * s) * y := by rw [h1]
      _ = x * (s * y) := by group
      _ = x * (y * s) := by rw [h2]
      _ = (x * y) * s := by group
  exact (mem_tqMembers_iff_exists_sylow hp hq hΩ (isPGroup_zpowers_of_sq_eq_one hu2)).mpr
    ⟨hΩ.conjInvariant g J hJΩ, conjSub g T₀, hTsyl, hTc⟩

theorem sigmaGen_le_sigmaStarNorm (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω) {K : Subgroup G}
    (hK : K ∈ Ω) : sigmaGen Ω K ≤ sigmaStarNorm Ω K := by
  refine iSup₂_le fun M hM g hg => ?_
  have hMd : M ∈ dstarComp Ω K := T7A.mem_dstarComp_of_mem_dComp hp hΩ hM
  have hMΩ : M ∈ Ω := (T3.mem_dstarComp_symm hK hMd).1
  have hgM : conjSub g M = M := mem_normalizer_iff_conjSub_eq.mp (Subgroup.le_normalizer hg)
  have h1 : g ∈ sigmaStarNorm Ω M :=
    T7A.mem_sigmaStarNorm_of_conj hΩ.conjInvariant hMΩ
      (by rw [hgM]; exact Relation.ReflTransGen.refl)
  rwa [sigmaStarNorm_congr (T7A.dstarComp_eq_of_mem hK hMd)] at h1

end Frame

section Main

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' J W : Subgroup G} {z u t : G}

omit [IsSimpleGroup G] in
theorem Hyp21.oddCore_centralizer_u_comm (h : Hyp21 p f Ω K K' z u J t W)
    (hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥) {n : G}
    (hn : n ∈ oddCoreOf (Subgroup.centralizer ({u} : Set G))) : n * z = z * n := by
  have hzA : z ∈ Subgroup.closure ({u, z} : Set G) := Subgroup.subset_closure (by simp)
  have huA : u ∈ Subgroup.closure ({u, z} : Set G) := Subgroup.subset_closure (by simp)
  have hmem : ⁅n, z⁆ ∈ ⁅oddCoreOf (Subgroup.centralizer ({u} : Set G)),
      Subgroup.closure ({u, z} : Set G)⁆ := Subgroup.commutator_mem_commutator hn hzA
  have hle : ⁅oddCoreOf (Subgroup.centralizer ({u} : Set G)),
      Subgroup.closure ({u, z} : Set G)⁆ ≤ alphaOf (Subgroup.closure ({u, z} : Set G)) := by
    unfold alphaOf
    exact le_sup_of_le_left (le_iSup₂_of_le u huA (le_iSup_of_le h.hu1 le_rfl))
  rw [hα] at hle
  exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp (hle hmem))

variable (p f) in
theorem c21_YSigma_of_sections (h3s : ∀ n, CITBelowU p f n → T3.Thm3SectBelow p f n) :
    C21_YSigma p f := by
  intro G _ _ _ Ω K K' z u J t W h hα hY _
  have hp : p ≠ 2 := h.std.stand.odd
  have hq : 5 ≤ p ^ f := h.std.stand.five
  have hΩ : HypOmegaMod p f Ω := h.std.stand.hyp
  have hK : K ∈ Ω := h.std.stand.mem
  have hz : IsUniqueInvolution K z := h.std.hz
  have hBelow : CITBelowU p f (Nat.card G) := h.std.stand.below f hq
  have hu2 : u * u = 1 := h.hu2
  have hu1 : u ≠ 1 := h.hu1
  have hcA : IsPGroup 2 (Subgroup.zpowers u) := isPGroup_zpowers_of_sq_eq_one hu2
  set A : Subgroup G := Subgroup.zpowers u with hAdef
  obtain ⟨g₀, -, hJ₀nbr, hJ₀t⟩ := exists_mem_tqMembers_u hp hq hΩ hK hz h.std.hK' h.std.hne h.hu
    hu2 hu1 h.hJ h.ht
  set J₀ : Subgroup G := conjSub g₀ J with hJ₀def
  have hJ₀Ω : J₀ ∈ Ω := hΩ.conjInvariant g₀ J h.hJ.1
  have hJ₀d : J₀ ∈ dstarComp Ω K :=
    Relation.ReflTransGen.single ⟨hJ₀Ω, Or.inl (T3.omegaNbr_subset_omegaStarNbr hp hΩ K
      (hJ₀nbr.2 K (mem_twinSet_self hK hz)))⟩
  have hJ₀m : J₀ ∈ sectionMembers Ω A := by rw [hAdef, sectionMembers_zpowers]; exact hJ₀t
  have hcent : Subgroup.centralizer ((A : Subgroup G) : Set G) =
      Subgroup.centralizer ({u} : Set G) := by
    rw [hAdef, CFSG.ClassicalInvolution.Balance.Bootstrap.centralizer_zpowers_eq_singleton']
  set Y : Subgroup G := sectionHull Ω A with hYdef
  have hYtop : Y ≠ ⊤ := by
    intro htop
    have hle : Y ≤ Subgroup.centralizer ({u} : Set G) := by
      have := sectionHull_le_centralizer Ω A
      rwa [hcent] at this
    rw [htop, top_le_iff] at hle
    have hcomm : ∀ g : G, g * u = u * g := fun g =>
      Subgroup.mem_centralizer_singleton_iff.mp (hle ▸ Subgroup.mem_top g)
    obtain ⟨V, hV, -⟩ := IsSylow2In.exists_ge (isPGroup_two_bot (G := G)) (bot_le : ⊥ ≤ K)
    have hVR : V ∈ RSet Ω := mem_RSet_of_isSylow2In hK hV
    obtain ⟨x, -, y, -, hxy⟩ := (hΩ.isQuatSub_of_mem_RSet hp hVR).exists_not_commute
    exact hu1 (T7A.eq_one_of_central ⟨x, y, hxy⟩ hcomm)
  have hinv : ∀ n : ↥Y, n ∈ classicalInvolutionOddCore ↥Y → (n : G) ∈ sigmaStarNorm Ω K := by
    intro n hn
    have hnO : (n : G) ∈ oddCoreOf Y := ⟨n, hn, rfl⟩
    have hnC := oddCoreOf_sectionHull_le hΩ A hnO
    rw [hcent] at hnC
    have hnz : (n : G) * z = z * (n : G) := h.oddCore_centralizer_u_comm hα hnC
    have hnzn : (n : G) * z * (n : G)⁻¹ = z := by
      calc (n : G) * z * (n : G)⁻¹ = (z * (n : G)) * (n : G)⁻¹ := by rw [hnz]
        _ = z := by group
    have hKn : conjSub (n : G) K ∈ twinSet Ω K :=
      ⟨hΩ.conjInvariant n K hK, z, hz, hnzn ▸ hz.conj (n : G)⟩
    exact T7A.mem_sigmaStarNorm_of_conj hΩ.conjInvariant hK
      (AscE186.mem_dstarComp_of_twin hp hΩ hK hKn)
  have hYN : ∀ g ∈ Y, g ∈ sigmaStarNorm Ω K := fun g hg =>
    sigmaGen_le_sigmaStarNorm hp hΩ hK ((sectionHull_le_rLayer Ω u).trans hY hg)
  have hall : ∀ M ∈ tqMembers Ω u, M ∈ dstarComp Ω K := by
    intro M hM
    have hMs : M ∈ sectionMembers Ω A := by rw [hAdef, sectionMembers_zpowers]; exact hM
    rcases section_connected_or_orbit hp hq hΩ hcA hYtop hBelow (h3s _ hBelow) hJ₀m with
      hconn | horb
    · obtain ⟨n, hn, J', hJ', hJ'd, rfl⟩ :=
        exists_conj_mem_dstarComp_of_conn hp hq hΩ hcA hJ₀m hconn hMs
      exact ((mem_sigmaStarNorm_iff.mp (hinv n hn)) J').mp (hJ₀d.trans hJ'd)
    · obtain ⟨g, hg, rfl⟩ := exists_mem_sectionHull_conj_of_orbit hp hq hΩ hcA hJ₀m horb hMs
      exact ((mem_sigmaStarNorm_iff.mp (hYN g hg)) J₀).mp hJ₀d
  intro c hc
  have h1 : conjSub c J₀ ∈ tqMembers Ω u := conjSub_mem_tqMembers hΩ.conjInvariant hc hJ₀t
  have hJJ : conjSub c J₀ ∈ dstarComp Ω J₀ :=
    (T3.mem_dstarComp_symm hK hJ₀d).2.trans (hall _ h1)
  have hcn : c ∈ sigmaStarNorm Ω J₀ := T7A.mem_sigmaStarNorm_of_conj hΩ.conjInvariant hJ₀Ω hJJ
  rwa [sigmaStarNorm_congr (T7A.dstarComp_eq_of_mem hK hJ₀d)] at hcn

variable (p f) in
theorem c21_2_final_sections (hE : ThmEWithSylow p f) (hHz : TwinFrameHyp51z p f)
    (hHt : TwinFrameHyp51t p f) (hHu : TwinFrameHyp51u p f) (hMF : DStarConnectedTwin p f)
    (h3s : ∀ n, CITBelowU p f n → T3.Thm3SectBelow p f n) (h13N : C21_13_N p f)
    (h14N : C21_14_N p f) (h14a : C21_14_alt p f) (h15 : C21_15 p f)
    (hWyl : C21_WylTrans' p f) : C21_2 p f :=
  c21_2_final_proved p f hE hHz hHt hHu hMF h3s h13N h14N h14a h15 hWyl
    (c21_YSigma_of_sections p f h3s)

end Main

end CFSG.ClassicalInvolution.Asc77
