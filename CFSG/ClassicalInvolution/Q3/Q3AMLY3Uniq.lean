module

public import CFSG.ClassicalInvolution.Q3.Q3AMLY3Gen
public import CFSG.ClassicalInvolution.Q3.Q3AMLYEdge

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped MatrixGroups commutatorElement

section Uniq

variable {G : Type} [Group G] [Finite G]

theorem inf_le_exactCore3_of_mem_two_group {z : G} {N W₀ : Subgroup G} (hzW : z ∈ W₀)
    (hW₀ : IsPGroup 2 W₀) (hzN : z ∈ trivialOnQuot N) : N ⊓ W₀ ≤ exactCore3 z N := by
  rintro x ⟨hxN, hxW⟩
  refine ⟨hxN, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
  have h1 : ⁅z, x⁆ ∈ oddCoreOf N := hzN.2 x hxN
  have h2 : ⁅z, x⁆ ∈ W₀ := by
    rw [commutatorElement_def]
    exact W₀.mul_mem (W₀.mul_mem (W₀.mul_mem hzW hxW) (W₀.inv_mem hzW)) (W₀.inv_mem hxW)
  have h3 : IsPGroup 2 (Subgroup.zpowers ⁅z, x⁆) := hW₀.to_le (Subgroup.zpowers_le.mpr h2)
  have h4 := eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard N) h1 h3
  exact (commutatorElement_eq_one_iff_mul_comm.mp h4).symm

theorem eq_of_modOddIn_exactCore3_eq {Ω : Set (Subgroup G)}
    (hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M) {Y N N' : Subgroup G} {z : G}
    (hN : N ∈ Ω) (hN' : N' ∈ Ω) (hzN : z ∈ Subgroup.normalizer (N : Set G))
    (hzN' : z ∈ Subgroup.normalizer (N' : Set G)) (hNY : exactCore3 z N ≤ Y)
    (hN'Y : exactCore3 z N' ≤ Y) {u u' : G} (hu : IsUniqueInvolution N u)
    (hu' : IsUniqueInvolution N' u') {W₀ : Subgroup G} (hW₀ : IsPGroup 2 W₀) (huW : u ∈ W₀)
    (hu'W : u' ∈ W₀) (h : modOddIn Y (exactCore3 z N) = modOddIn Y (exactCore3 z N')) :
    N = N' := by
  set O : Subgroup ↥Y := classicalInvolutionOddCore ↥Y with hOdef
  have hO : Odd (Nat.card O) := CFSG.ComponentClassification.OddCore.odd_card _
  have huc : IsUniqueInvolution (exactCore3 z N) u :=
    Q3T8.Layer.isUniqueInvolution_exactCore3 hzN hu
  have hu'c : IsUniqueInvolution (exactCore3 z N') u' :=
    Q3T8.Layer.isUniqueInvolution_exactCore3 hzN' hu'
  have hz1 := isUniqueInvolution_map_mk_of_odd
    (odd_natCard_inf hO ((exactCore3 z N).subgroupOf Y)) (isUniqueInvolution_subgroupOf huc hNY)
  have hz2 := isUniqueInvolution_map_mk_of_odd
    (odd_natCard_inf hO ((exactCore3 z N').subgroupOf Y))
    (isUniqueInvolution_subgroupOf hu'c hN'Y)
  have h' : ((exactCore3 z N).subgroupOf Y).map (QuotientGroup.mk' O) =
      ((exactCore3 z N').subgroupOf Y).map (QuotientGroup.mk' O) := h
  rw [h'] at hz1
  have hmk : QuotientGroup.mk' O (⟨u, hNY huc.mem⟩ : ↥Y) =
      QuotientGroup.mk' O ⟨u', hN'Y hu'c.mem⟩ := hz1.eq hz2
  have hw : (⟨u, hNY huc.mem⟩ : ↥Y)⁻¹ * ⟨u', hN'Y hu'c.mem⟩ ∈ O := by
    have : QuotientGroup.mk' O ((⟨u, hNY huc.mem⟩ : ↥Y)⁻¹ * ⟨u', hN'Y hu'c.mem⟩) = 1 := by
      rw [map_mul, map_inv, hmk, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff _).mp this
  have h2 : IsPGroup 2 (Subgroup.zpowers ((⟨u, hNY huc.mem⟩ : ↥Y)⁻¹ * ⟨u', hN'Y hu'c.mem⟩)) := by
    rw [← isPGroup_zpowers_coe_iff]
    refine hW₀.to_le (Subgroup.zpowers_le.mpr ?_)
    exact W₀.mul_mem (W₀.inv_mem huW) hu'W
  have h1 := eq_one_of_isPGroup_of_mem_odd hO hw h2
  have huu : u = u' := by
    have h3 : u⁻¹ * u' = 1 := congrArg Subtype.val h1
    exact inv_mul_eq_one.mp h3
  have hN'twin : N' ∈ twinSet Ω N := ⟨hN', u, hu, huu ▸ hu'⟩
  exact (hnt N hN N' hN'twin).symm

theorem exists_involution_mem_of_inf_mem_USet {Ω : Set (Subgroup G)} (hΩG : HypOmegaGen Ω)
    {M W₀ : Subgroup G} (hM : M ∈ Ω) (hUM : M ⊓ W₀ ∈ USet Ω) :
    ∃ u, IsUniqueInvolution M u ∧ u ∈ W₀ := by
  obtain ⟨u, hu⟩ := Sec6Gen.exists_uniqueInvolution hΩG hM
  have hU2 : IsPGroup 2 ↥(M ⊓ W₀) := Sec6Gen.isPGroup_of_mem_USet hΩG hUM
  obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := Sec6Gen.exists_data_of_mem_USet hΩG hUM
  exact ⟨u, hu, (T3.mem_of_isPGroup hu inf_le_left hU2 (by omega)).2⟩

theorem uniq_of_thinY [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K J : Subgroup G}
    {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (h : Q3T8.Asc77.BadStd8 Ω K J S R T W z t) (hint : IsIntrinsicU (.sl2 3 1) K z)
    (hthin : ThinY Ω K z) {W₀ : Subgroup G} (hW₀ : W₀ ∈ WSet Ω) (hzW : z ∈ W₀)
    {N N' : Subgroup G} (hN : N ∈ omegaNbr Ω K) (hN' : N' ∈ omegaNbr Ω K)
    (hUN : N ⊓ W₀ ∈ USet Ω) (hUN' : N' ⊓ W₀ ∈ USet Ω) : N = N' := by
  classical
  have hstd := h.std
  have hK : K ∈ Ω := hstd.stand.mem
  have hz : IsUniqueInvolution K z := hstd.hz
  have hΩG : HypOmegaGen Ω := hstd.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩG.conjInvariant hstd.stand.trans hstd.noTwins hM
  have htq : ∀ M ∈ omegaNbr Ω K, M ∈ tqMembers3 Ω z := fun M hM =>
    mem_tqMembers3_of_nbr h hint hK hz hM
  set Y : Subgroup G := nbrLayer Ω K z with hYdef
  have hGen := genSection_layerFam h hint hK hz
  have hΦ : HypOmegaGen (layerFam Ω K z) := hGen.hyp
  have hPΦ : Q3CL.PartIHypG (layerFam Ω K z) := ⟨hGen.hyp, hGen.cls, hGen.aEmpty⟩
  set N₀ : Subgroup ↥Y := classicalInvolutionOddCore ↥Y with hN₀def
  have hNodd : Odd (Nat.card N₀) := CFSG.ComponentClassification.OddCore.odd_card ↥Y
  set π := QuotientGroup.mk' N₀ with hπ
  have hW₀2 : IsPGroup 2 W₀ := isPGroup_of_mem_WSet hW₀
  have hcore : ∀ M ∈ omegaNbr Ω K, M ⊓ W₀ ≤ exactCore3 z M := fun M hM =>
    inf_le_exactCore3_of_mem_two_group hzW hW₀2 (htq M hM).2
  have hUY : N ⊓ W₀ ≤ Y := (hcore N hN).trans (exactCore3_le_nbrLayer hN)
  have hU'Y : N' ⊓ W₀ ≤ Y := (hcore N' hN').trans (exactCore3_le_nbrLayer hN')
  have hQW : (N ⊓ W₀) ⊔ (N' ⊓ W₀) ≤ W₀ := sup_le inf_le_right inf_le_right
  have hQ2 : IsPGroup 2 ↥(((N ⊓ W₀) ⊔ (N' ⊓ W₀)).subgroupOf Y) :=
    (hW₀2.to_le hQW).comap_subtype
  obtain ⟨S₁, hS₁⟩ := hQ2.exists_le_sylow
  set Sb : Sylow 2 (↥Y ⧸ N₀) := Sylow.mapSurjective (QuotientGroup.mk'_surjective N₀) S₁
    with hSbdef
  have hSb : (Sb : Subgroup (↥Y ⧸ N₀)) = (S₁ : Subgroup ↥Y).map π := Sylow.coe_mapSurjective _ _
  obtain ⟨η, hη, hinv⟩ := Sec6Gen.exists_invariant_mem_etaSet hΦ Sb
  have hηG : η ∈ etaG (layerFam Ω K z) := ⟨Sb, hη, hinv⟩
  set W₁ : Subgroup (↥Y ⧸ N₀) := ⨆ U ∈ η, U with hW₁def
  have hW₁ : W₁ ∈ WSet (layerFam Ω K z) := ⟨η, hηG, rfl⟩
  have hηS : ∀ V ∈ η, V ≤ (Sb : Subgroup (↥Y ⧸ N₀)) := fun V hV => (hη.1 hV).2
  have key : ∀ M : Subgroup G, M ∈ omegaNbr Ω K → M ⊓ W₀ ∈ USet Ω →
      (M ⊓ W₀).subgroupOf Y ≤ (S₁ : Subgroup ↥Y) →
      ∃ ρ : Rep (layerFam Ω K z) W₁, ρ.K = modOddIn Y (exactCore3 z M) := by
    intro M hM hUM hMS
    have hUY' : M ⊓ W₀ ≤ Y := (hcore M hM).trans (exactCore3_le_nbrLayer hM)
    have hU2 : IsPGroup 2 ↥(M ⊓ W₀) := Sec6Gen.isPGroup_of_mem_USet hΩG hUM
    obtain ⟨R'', -, J', -, hRJ, hUR, hcyc, hcard, h4⟩ := Sec6Gen.exists_data_of_mem_USet hΩG hUM
    have hU'2 : IsPGroup 2 ↥((M ⊓ W₀).subgroupOf Y) := hU2.comap_subtype
    have hcardU' : Nat.card ↥((M ⊓ W₀).subgroupOf Y) = Nat.card ↥(M ⊓ W₀) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUY').toEquiv
    have hNU : N₀ ⊓ (M ⊓ W₀).subgroupOf Y = ⊥ := by
      rw [inf_comm]
      exact AscQuot.inf_eq_bot_of_isPGroup_of_odd N₀ hU'2 le_rfl (odd_natCard_inf hNodd _)
    have hcardUb : Nat.card ↥(((M ⊓ W₀).subgroupOf Y).map π) = Nat.card ↥(M ⊓ W₀) := by
      have h' := natCard_map_mk_mul (N := N₀) ((M ⊓ W₀).subgroupOf Y)
      rw [hNU, Subgroup.card_bot, mul_one, hcardU'] at h'
      exact h'
    have hMb : modOddIn Y (exactCore3 z M) ∈ layerFam Ω K z := modOddIn_mem_layerFam hM
    have hUbM : ((M ⊓ W₀).subgroupOf Y).map π ≤ modOddIn Y (exactCore3 z M) :=
      Subgroup.map_mono (Subgroup.subgroupOf_mono Y (hcore M hM))
    have hUbS : ((M ⊓ W₀).subgroupOf Y).map π ≤ (Sb : Subgroup (↥Y ⧸ N₀)) := by
      rw [hSb]
      exact Subgroup.map_mono hMS
    have hcard2 : 2 < Nat.card ↥(modOddIn Y (exactCore3 z M) ⊓ (Sb : Subgroup (↥Y ⧸ N₀))) := by
      have h1 := Subgroup.card_le_of_le (le_inf hUbM hUbS)
      have h5 : 4 ≤ Nat.card ↥(((M ⊓ W₀).subgroupOf Y).map π) := by omega
      exact lt_of_lt_of_le (by norm_num) (h5.trans h1)
    have h611 := Q3T8.Asc77.l6_11_proved (↥Y ⧸ N₀) (layerFam Ω K z) hΦ Sb η hηG hηS _ hMb hcard2
    have hV := hη.1 h611
    obtain ⟨z', hz'⟩ := Sec6Gen.exists_uniqueInvolution hΦ hMb
    have hV2 : IsPGroup 2 ↥(modOddIn Y (exactCore3 z M) ⊓ W₁) :=
      Sec6Gen.isPGroup_of_mem_USet hΦ hV.1
    obtain ⟨-, -, -, -, -, -, -, -, hV4⟩ := Sec6Gen.exists_data_of_mem_USet hΦ hV.1
    have hV4' : 4 ≤ Nat.card ↥(modOddIn Y (exactCore3 z M) ⊓ W₁) := hV4
    have hzV : z' ∈ modOddIn Y (exactCore3 z M) ⊓ W₁ :=
      T3.mem_of_isPGroup hz' inf_le_left hV2 (le_trans (by norm_num) hV4')
    have c₁ := Q3T8.Asc77.MuTab.muTabCtx hPΦ hW₁
    exact c₁.exists_rep_of_involution_mem hPΦ.cls hMb hz' hzV.2
  have hNS : (N ⊓ W₀).subgroupOf Y ≤ (S₁ : Subgroup ↥Y) :=
    (Subgroup.subgroupOf_mono Y (le_sup_left : N ⊓ W₀ ≤ (N ⊓ W₀) ⊔ (N' ⊓ W₀))).trans hS₁
  have hN'S : (N' ⊓ W₀).subgroupOf Y ≤ (S₁ : Subgroup ↥Y) :=
    (Subgroup.subgroupOf_mono Y (le_sup_right : N' ⊓ W₀ ≤ (N ⊓ W₀) ⊔ (N' ⊓ W₀))).trans hS₁
  obtain ⟨ρ, hρ⟩ := key N hN hUN hNS
  obtain ⟨ρ', hρ'⟩ := key N' hN' hUN' hN'S
  obtain ⟨W', hW', hZ⟩ := hthin
  obtain ⟨e'⟩ := Q3T8.Asc77.l7_5_2_proved (↥Y ⧸ N₀) _ hGen.modU W₁ hW₁ W' hW'
  obtain ⟨e⟩ := hZ
  have e2 := e'.trans e
  have hTT := Q3T8.Asc77.Thompson.isTT_muDelta hΦ hW₁ (Q3CL.thompsonCube hPΦ W₁ hW₁)
  have hne1 : e2 (MuTab.muTabElt ρ) ≠ 1 := fun h' =>
    hTT.ne_one _ (MuTab.muTabElt_mem ρ) (e2.injective (by rw [h', map_one]))
  have hne2 : e2 (MuTab.muTabElt ρ') ≠ 1 := fun h' =>
    hTT.ne_one _ (MuTab.muTabElt_mem ρ') (e2.injective (by rw [h', map_one]))
  have heq : MuTab.muTabElt ρ = MuTab.muTabElt ρ' :=
    e2.injective (s26_z2_eq _ _ hne1 hne2)
  have hKeq : ρ.K = ρ'.K := (Q3T8.Asc77.MuTab.muTabElt_eq_iff hPΦ hW₁ ρ ρ').mp heq
  have hmap : modOddIn Y (exactCore3 z N) = modOddIn Y (exactCore3 z N') := by
    rw [← hρ, ← hρ']
    exact hKeq
  obtain ⟨u, hu, huW⟩ := exists_involution_mem_of_inf_mem_USet hΩG hN.1 hUN
  obtain ⟨u', hu', hu'W⟩ := exists_involution_mem_of_inf_mem_USet hΩG hN'.1 hUN'
  exact eq_of_modOddIn_exactCore3_eq hnt hN.1 hN'.1 (htq N hN).2.1 (htq N' hN').2.1
    (exactCore3_le_nbrLayer hN) (exactCore3_le_nbrLayer hN') hu hu' hW₀2 huW hu'W hmap

end Uniq

end CFSG.ClassicalInvolution.Q3.Q3AM
