module

public import CFSG.ClassicalInvolution.Q3.TL4E3Z2
public import CFSG.ClassicalInvolution.Q3.Q3AM710Img
public import CFSG.ClassicalInvolution.Q3.Q3T8C262A
public import CFSG.ClassicalInvolution.Q3.Q3AM710Cls
public import CFSG.ClassicalInvolution.Q3.TL4Conn278Main
public import CFSG.ClassicalInvolution.Q3.TL4E3Norm
public import CFSG.ClassicalInvolution.Q3.TL4OddBasic

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Q3.Q3AM710
open CFSG.ClassicalInvolution.Q3.TC.Graph

section Gen

variable {G : Type} [Group G] [Finite G] {r : ℕ} {Ω : Set (Subgroup G)}

theorem E3.eq_of_thinSec (hΩG : HypOmegaGen Ω) (hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M)
    {X : Subgroup G} {Φ : Set (Subgroup (↥X ⧸ classicalInvolutionOddCore ↥X))}
    (hPΦ : Q3CL.PartIHypG Φ) (hthin : ∀ W' ∈ WSet Φ, MuIsoZ2 Φ W') {P : Subgroup G}
    (hP : IsPGroup 2 ↥P) {L L' : Subgroup G} (hL : L ∈ Ω) (hL' : L' ∈ Ω) (hLX : L ≤ X)
    (hL'X : L' ≤ X)
    (hLΦ : (L.subgroupOf X).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥X)) ∈ Φ)
    (hL'Φ : (L'.subgroupOf X).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥X)) ∈ Φ)
    (h4 : 4 ≤ Nat.card ↥(L ⊓ P)) (h4' : 4 ≤ Nat.card ↥(L' ⊓ P)) : L = L' := by
  classical
  have hΦ : HypOmegaGen Φ := hPΦ.hyp
  set N : Subgroup ↥X := classicalInvolutionOddCore ↥X with hNdef
  have hNodd : Odd (Nat.card N) := CFSG.ComponentClassification.OddCore.odd_card ↥X
  set π := QuotientGroup.mk' N with hπ
  have hQW : (L ⊓ P) ⊔ (L' ⊓ P) ≤ P := sup_le inf_le_right inf_le_right
  have hQ2 : IsPGroup 2 ↥(((L ⊓ P) ⊔ (L' ⊓ P)).subgroupOf X) :=
    (hP.to_le hQW).comap_subtype
  obtain ⟨S₁, hS₁⟩ := hQ2.exists_le_sylow
  set Sb : Sylow 2 (↥X ⧸ N) := Sylow.mapSurjective (QuotientGroup.mk'_surjective N) S₁ with hSbdef
  have hSb : (Sb : Subgroup (↥X ⧸ N)) = (S₁ : Subgroup ↥X).map π := Sylow.coe_mapSurjective _ _
  obtain ⟨η, hη, hinv⟩ := Disconnected.AschTight.Sec6Gen.exists_invariant_mem_etaSet hΦ Sb
  have hηG : η ∈ etaG Φ := ⟨Sb, hη, hinv⟩
  set W₁ : Subgroup (↥X ⧸ N) := ⨆ U ∈ η, U with hW₁def
  have hW₁ : W₁ ∈ WSet Φ := ⟨η, hηG, rfl⟩
  have hηS : ∀ V ∈ η, V ≤ (Sb : Subgroup (↥X ⧸ N)) := fun V hV => (hη.1 hV).2
  have key : ∀ M : Subgroup G, M ≤ X → 4 ≤ Nat.card ↥(M ⊓ P) → (M.subgroupOf X).map π ∈ Φ →
      (M ⊓ P).subgroupOf X ≤ (S₁ : Subgroup ↥X) →
      ∃ ρ : Rep Φ W₁, ρ.K = (M.subgroupOf X).map π := by
    intro M hMX h4M hMb hMS
    have hUX' : M ⊓ P ≤ X := inf_le_left.trans hMX
    have hU2 : IsPGroup 2 ↥(M ⊓ P) := hP.to_le inf_le_right
    have hU'2 : IsPGroup 2 ↥((M ⊓ P).subgroupOf X) := hU2.comap_subtype
    have hcardU' : Nat.card ↥((M ⊓ P).subgroupOf X) = Nat.card ↥(M ⊓ P) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUX').toEquiv
    have hNU : N ⊓ (M ⊓ P).subgroupOf X = ⊥ := by
      rw [inf_comm]
      exact AscQuot.inf_eq_bot_of_isPGroup_of_odd N hU'2 le_rfl (odd_natCard_inf hNodd _)
    have hcardUb : Nat.card ↥(((M ⊓ P).subgroupOf X).map π) = Nat.card ↥(M ⊓ P) := by
      have h := natCard_map_mk_mul (N := N) ((M ⊓ P).subgroupOf X)
      rw [hNU, Subgroup.card_bot, mul_one, hcardU'] at h
      exact h
    have hUbM : ((M ⊓ P).subgroupOf X).map π ≤ (M.subgroupOf X).map π :=
      Subgroup.map_mono (Subgroup.subgroupOf_mono X inf_le_left)
    have hUbS : ((M ⊓ P).subgroupOf X).map π ≤ (Sb : Subgroup (↥X ⧸ N)) := by
      rw [hSb]
      exact Subgroup.map_mono hMS
    have hcard2 : 2 < Nat.card ↥((M.subgroupOf X).map π ⊓ (Sb : Subgroup (↥X ⧸ N))) := by
      have h1 := Subgroup.card_le_of_le (le_inf hUbM hUbS)
      omega
    have h611 := Q3T8.Asc77.l6_11_proved (↥X ⧸ N) Φ hΦ Sb η hηG hηS _ hMb hcard2
    have hV := hη.1 h611
    obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΦ hMb
    have hV2 : IsPGroup 2 ↥((M.subgroupOf X).map π ⊓ W₁) := Sec6Gen.isPGroup_of_mem_USet hΦ hV.1
    obtain ⟨-, -, -, -, -, -, -, -, hV4⟩ := Sec6Gen.exists_data_of_mem_USet hΦ hV.1
    have hV4' : 4 ≤ Nat.card ↥((M.subgroupOf X).map π ⊓ W₁) := hV4
    have hzV : z ∈ (M.subgroupOf X).map π ⊓ W₁ :=
      T3.mem_of_isPGroup hz inf_le_left hV2 (le_trans (by norm_num) hV4')
    have c₁ := Q3T8.Asc77.MuTab.muTabCtx hPΦ hW₁
    exact c₁.exists_rep_of_involution_mem hPΦ.cls hMb hz hzV.2
  have hLS : (L ⊓ P).subgroupOf X ≤ (S₁ : Subgroup ↥X) :=
    (Subgroup.subgroupOf_mono X (le_sup_left : L ⊓ P ≤ (L ⊓ P) ⊔ (L' ⊓ P))).trans hS₁
  have hL'S : (L' ⊓ P).subgroupOf X ≤ (S₁ : Subgroup ↥X) :=
    (Subgroup.subgroupOf_mono X (le_sup_right : L' ⊓ P ≤ (L ⊓ P) ⊔ (L' ⊓ P))).trans hS₁
  obtain ⟨ρ, hρ⟩ := key L hLX h4 hLΦ hLS
  obtain ⟨ρ', hρ'⟩ := key L' hL'X h4' hL'Φ hL'S
  obtain ⟨e2⟩ := hthin W₁ hW₁
  have hTT := Q3T8.Asc77.Thompson.isTT_muDelta hΦ hW₁ (Q3CL.thompsonCube hPΦ W₁ hW₁)
  have hne1 : e2 (MuTab.muTabElt ρ) ≠ 1 := fun h =>
    hTT.ne_one _ (MuTab.muTabElt_mem ρ) (e2.injective (by rw [h, map_one]))
  have hne2 : e2 (MuTab.muTabElt ρ') ≠ 1 := fun h =>
    hTT.ne_one _ (MuTab.muTabElt_mem ρ') (e2.injective (by rw [h, map_one]))
  have heq : MuTab.muTabElt ρ = MuTab.muTabElt ρ' := e2.injective (s26_z2_eq _ _ hne1 hne2)
  have hKeq : ρ.K = ρ'.K := (Q3T8.Asc77.MuTab.muTabElt_eq_iff hPΦ hW₁ ρ ρ').mp heq
  have hmap : (L.subgroupOf X).map π = (L'.subgroupOf X).map π := by
    rw [← hρ, ← hρ']
    exact hKeq
  have hinv' : ∀ M : Subgroup G, M ∈ Ω → 4 ≤ Nat.card ↥(M ⊓ P) →
      ∃ u, IsUniqueInvolution M u ∧ u ∈ P := by
    intro M hM h4M
    obtain ⟨u, hu⟩ := Sec6Gen.exists_uniqueInvolution hΩG hM
    have hU2 : IsPGroup 2 ↥(M ⊓ P) := hP.to_le inf_le_right
    exact ⟨u, hu, (T3.mem_of_isPGroup hu inf_le_left hU2 (by omega)).2⟩
  obtain ⟨u, hu, huW⟩ := hinv' L hL h4
  obtain ⟨u', hu', hu'W⟩ := hinv' L' hL' h4'
  exact member_eq_of_map_eq hnt hL hL' hLX hL'X hu hu' hP huW hu'W hmap

theorem E3.partnerUniq_of_nbr (hΩG : HypOmegaGen Ω) {K : Subgroup G}
    (htrans : ∀ J ∈ Ω, ∃ g : G, conjSub g K = J)
    (huniq : ∀ W₀ ∈ WSet Ω, ∀ L ∈ omegaNbr Ω K, ∀ L' ∈ omegaNbr Ω K, L ⊓ W₀ ∈ USet Ω →
      L' ⊓ W₀ ∈ USet Ω → L = L')
    {W : Subgroup G} (hW : W ∈ WSet Ω) : PartnerUniq Ω W := by
  intro ρ σ σ' hσ hσ'
  have hc : ConjInvariant Ω := hΩG.conjInvariant
  obtain ⟨g, hg⟩ := htrans ρ.K ρ.hK
  have hX : ∀ τ : Rep Ω W, τ.K ∈ omegaNbr Ω ρ.K → conjSub g⁻¹ τ.K ∈ omegaNbr Ω K := by
    intro τ hτ
    have h1 := omegaNbr_conj hc hτ g⁻¹
    rwa [← hg, conjSub_inv_conjSub] at h1
  have hW' : conjSub g⁻¹ W ∈ WSet Ω := WSet.conj hc hW g⁻¹
  have hU : ∀ τ : Rep Ω W, conjSub g⁻¹ τ.K ⊓ conjSub g⁻¹ W ∈ USet Ω := by
    intro τ
    have h := USet.conj hc (Q3CL.Thompson.inf_W_of_mem_D hΩG hW τ.hR τ.hK τ.hRK).2.1 g⁻¹
    have e : conjSub g⁻¹ (τ.K ⊓ W) = conjSub g⁻¹ τ.K ⊓ conjSub g⁻¹ W :=
      Subgroup.map_inf_eq _ _ _ (MulAut.conj g⁻¹).injective
    rwa [e] at h
  exact (conjSub_inj g⁻¹).mp (huniq _ hW' _ (hX σ hσ) _ (hX σ' hσ') (hU σ) (hU σ'))

theorem E3.tightCore_map {H H' : Type} [Group H] [Finite H] [Group H'] [Finite H']
    (f : H →* H') (R : Subgroup H) : tightCore (R.map f) = (tightCore R).map f := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨⟨r, hr, rfl⟩, h2⟩
    obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos r).ne'
    have hrm : orderOf (r ^ m) = 2 ^ a := by
      rw [orderOf_pow_of_dvd hm.pos.ne' (by rw [hn]; exact dvd_mul_left _ _), hn,
        Nat.mul_div_cancel _ hm.pos]
    have hrm2 : IsPGroup 2 ↥(Subgroup.zpowers (r ^ m)) :=
      IsPGroup.of_card (n := a) (by rw [Nat.card_zpowers, hrm])
    have hrmK : r ^ m ∈ tightCore R :=
      Subgroup.subset_closure ⟨R.pow_mem hr m, hrm2⟩
    obtain ⟨b, hb⟩ := (IsPGroup.iff_card.mp h2)
    rw [Nat.card_zpowers] at hb
    have hcop : m.Coprime (orderOf (f r)) := by
      rw [hb]
      exact Nat.Coprime.pow_right b
        (Nat.Coprime.symm ((Nat.prime_two.coprime_iff_not_dvd).mpr hm.not_two_dvd_nat))
    obtain ⟨k, hk⟩ := exists_pow_eq_self_of_coprime hcop
    refine ⟨(r ^ m) ^ k, (tightCore R).pow_mem hrmK k, ?_⟩
    rw [map_pow, map_pow, hk]
  · rw [tightCore, MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨x, ⟨hxR, hx2⟩, rfl⟩
    refine ⟨⟨x, hxR, rfl⟩, ?_⟩
    rw [← MonoidHom.map_zpowers]
    exact hx2.map _

end Gen

section Cit3

section Std

variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {Rd : Subgroup Y} {Sd : Sylow 2 Rd} {z : Y}
  {J : Subgroup Y} {S : Sylow 2 Y} {R T W : Subgroup Y} {t : Y}

theorem TightStd8R.muIso_E4_or_S4_of_uniq (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hU : PartnerUniq (CoreAssembly.conjClass (tightCore Rd)) W) :
    MuIsoE4 (CoreAssembly.conjClass (tightCore Rd)) W ∨
      MuIsoS4 (CoreAssembly.conjClass (tightCore Rd)) W := by
  have hP : Q3CL.PartIHypG (CoreAssembly.conjClass (tightCore Rd)) :=
    TightLargeHypR.partIHypG hs.large
  have hΩG := hP.hyp
  have hW : W ∈ WSet (CoreAssembly.conjClass (tightCore Rd)) := hs.hW.1
  have hK : tightCore Rd ∈ CoreAssembly.conjClass (tightCore Rd) := ⟨1, conjSub_one _⟩
  have hJΩ : J ∈ CoreAssembly.conjClass (tightCore Rd) := hs.hJ.1
  have hSN : ∀ x ∈ (S : Subgroup Y), x ∈ Subgroup.normalizer (W : Set Y) := fun x hx =>
    mem_normalizer_iff_conjSub_eq.mpr (hs.hW.2.2 x hx)
  have hRD : R ∈ DSet (CoreAssembly.conjClass (tightCore Rd)) W :=
    ⟨hs.hR.1, fun x hx => hSN x (hs.hR.2.2 hx)⟩
  have hTD : T ∈ DSet (CoreAssembly.conjClass (tightCore Rd)) W :=
    ⟨hs.hT.1, fun x hx => hSN x (hs.hT.2.2 hx)⟩
  have hRsyl : IsSylow2In R (tightCore Rd) :=
    Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩG hK hs.hR.1 hs.hR.2.1
  have hTsyl : IsSylow2In T J := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩG hJΩ hs.hT.1 hs.hT.2.1
  obtain ⟨r₀, hr₀R, hr₀W⟩ := Q3CL.Thompson.exists_not_mem_of_mem_D hΩG hW hRD
  obtain ⟨t₀, ht₀T, ht₀W⟩ := Q3CL.Thompson.exists_not_mem_of_mem_D hΩG hW hTD
  let ρ : Rep (CoreAssembly.conjClass (tightCore Rd)) W :=
    ⟨tightCore Rd, R, r₀, hK, hRD, hRsyl, hr₀R, hr₀W⟩
  let σ : Rep (CoreAssembly.conjClass (tightCore Rd)) W := ⟨J, T, t₀, hJΩ, hTD, hTsyl, ht₀T, ht₀W⟩
  exact muIso_E4_or_S4 hP hW hU ρ σ hs.hJ

end Std

section Frame

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J : Subgroup Y} {u : Y}

theorem E3Frame.nbr_le_centralizer (hF : E3Frame n R S t J u) {M : Subgroup Y}
    (hM : M ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J) :
    M ≤ Subgroup.centralizer ({u} : Set Y) := by
  obtain ⟨g, Sd, S', R', T, W, hgJ, hu, hs⟩ := hF.exists_std8
  have hcore : tightCore (conjSub g R) = J := by rw [← conjSub_tightCore, hgJ]
  have hfam : CoreAssembly.conjClass (tightCore (conjSub g R)) =
      CoreAssembly.conjClass (tightCore R) := by
    rw [← conjSub_tightCore, conjClass_conjSub]
  have hα : TightSepAlpha (conjSub g R) u := hu ▸ hF.alpha.conj g
  have hM' : M ∈ omegaNbr (CoreAssembly.conjClass (tightCore (conjSub g R)))
      (tightCore (conjSub g R)) := by
    rw [hfam, hcore]
    exact hM
  obtain ⟨v, hv⟩ := Sec6Gen.exists_uniqueInvolution hs.large.datum.hypOmegaGen hM'.1
  exact edge_le_centralizer_of_alpha hs.large.datum hM' hv (hα M hM' v hv)

theorem E3Frame.nbrGen_le_centralizer (hF : E3Frame n R S t J u) :
    nbrGen (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J ≤
      Subgroup.centralizer ({u} : Set Y) :=
  iSup₂_le fun _ hM => hF.nbr_le_centralizer hM.2

theorem E3Frame.core_le_centralizer (hF : E3Frame n R S t J u) :
    tightCore R ≤ Subgroup.centralizer ({u} : Set Y) := by
  have hd := hF.large.datum
  have hJn := hF.maxAdj.1.2
  exact hF.nbr_le_centralizer
    (Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hd.hypOmegaGen hF.maxAdj.1.1 hJn.1 hJn)

theorem E3Frame.nbrGen_le_secH (hF : E3Frame n R S t J u)
    (hO : omegaNbr (CoreAssembly.conjClass (tightCore R)) J ⊆
      orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J (tightCore R)) :
    (nbrGen (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J).subgroupOf
      (Subgroup.centralizer ({u} : Set Y)) ≤ secH R u := by
  set C := Subgroup.centralizer ({u} : Set Y) with hC
  set X := nbrGen (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J with hX
  have hXC : X ≤ C := hF.nbrGen_le_centralizer
  have hKC : tightCore R ≤ C := hF.core_le_centralizer
  have claim : ∀ H M : Subgroup C, IsSubnormal H M → M = ⊤ →
      (tightCore R).subgroupOf C ≤ H → X ≤ H.map C.subtype := by
    intro H M hsub
    induction hsub with
    | refl H =>
      intro hH _
      rw [hH, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
      exact hXC
    | @step H M K hHM hN hMK ih =>
      intro hK hKH
      have hXM : X ≤ M.map C.subtype := ih hK (hKH.trans hHM)
      refine iSup₂_le fun L hL => ?_
      obtain ⟨l, hl, rfl⟩ := hO hL.2
      obtain ⟨m, hmM, rfl⟩ := hXM hl
      rintro _ ⟨k, hk, rfl⟩
      have hkC : k ∈ C := hKC hk
      have hkH : (⟨k, hkC⟩ : C) ∈ H := hKH (Subgroup.mem_subgroupOf.mpr hk)
      have hkM : (⟨k, hkC⟩ : C) ∈ M := hHM hkH
      have h1 := hN.conj_mem ⟨⟨k, hkC⟩, hkM⟩ (Subgroup.mem_subgroupOf.mpr hkH) ⟨m, hmM⟩
      rw [Subgroup.mem_subgroupOf] at h1
      exact ⟨_, h1, rfl⟩
  intro x hx
  have hx' : (x : Y) ∈ X := Subgroup.mem_subgroupOf.mp hx
  show x ∈ subnormalClosure (tightCore (R.subgroupOf C))
  rw [tightCore_subgroupOf hKC]
  refine (le_sInf fun H hH => ?_ : (X.subgroupOf C) ≤ _) hx
  intro y hy
  obtain ⟨h, hh, hhy⟩ := claim H ⊤ hH.2 rfl hH.1 (Subgroup.mem_subgroupOf.mp hy)
  have : h = y := Subtype.ext hhy
  rwa [← this]

theorem E3Frame.tightCore_secR (hF : E3Frame n R S t J u) :
    tightCore (secR R u) =
      (((tightCore R).subgroupOf (Subgroup.centralizer ({u} : Set Y))).subgroupOf
        (secH R u)).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R u))) := by
  have hKC : tightCore R ≤ Subgroup.centralizer ({u} : Set Y) := hF.core_le_centralizer
  rw [E3.tightCore_map, tightCore_subgroupOf (le_subnormalClosure _)]
  exact congrArg (fun A => (A.subgroupOf (secH R u)).map
    (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R u)))) (tightCore_subgroupOf hKC)

theorem E3Frame.map_mem_secΩ (hF : E3Frame n R S t J u)
    (hO : omegaNbr (CoreAssembly.conjClass (tightCore R)) J ⊆
      orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J (tightCore R))
    {L : Subgroup Y} (hL : L ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J) :
    ((L.subgroupOf (Subgroup.centralizer ({u} : Set Y))).subgroupOf (secH R u)).map
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R u))) ∈ E3.secΩ R u := by
  obtain ⟨l, hl, rfl⟩ := hO hL
  have hlC : l ∈ Subgroup.centralizer ({u} : Set Y) := hF.nbrGen_le_centralizer hl
  have hlH : (⟨l, hlC⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u :=
    hF.nbrGen_le_secH hO (Subgroup.mem_subgroupOf.mpr hl)
  refine ⟨QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R u)) ⟨⟨l, hlC⟩, hlH⟩, ?_⟩
  show conjSub _ (tightCore (secR R u)) = _
  rw [hF.tightCore_secR, ← TwistQ.conjSub_map, conjSub_subgroupOf, conjSub_subgroupOf]

theorem E3Frame.partnerUniq_of_oneOrbit (hF : E3Frame n R S t J u)
    (hO : omegaNbr (CoreAssembly.conjClass (tightCore R)) J ⊆
      orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J (tightCore R))
    (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
    (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u)
    (hthin : ∀ W ∈ WSet (E3.secΩ R u), MuIsoZ2 (E3.secΩ R u) W) {W : Subgroup Y}
    (hW : W ∈ WSet (CoreAssembly.conjClass (tightCore R))) :
    PartnerUniq (CoreAssembly.conjClass (tightCore R)) W := by
  set C := Subgroup.centralizer ({u} : Set Y) with hC
  have hR : TypeRFam 3 (CoreAssembly.conjClass (tightCore R)) := TightLargeHypR.typeRFam hF.large
  have hRC := hR.restrict C
  obtain ⟨Sq, hdq, -⟩ := hF.exists_secCls htu ht
  have hPΦ : Q3CL.PartIHypG (E3.secΩ R u) := hdq.partIHypG
  have hJΩ : J ∈ CoreAssembly.conjClass (tightCore R) := hF.maxAdj.1.2.1
  obtain ⟨g₀, hg₀'⟩ := hJΩ
  have hg₀ : conjSub g₀ (tightCore R) = J := hg₀'
  have htrans : ∀ J' ∈ CoreAssembly.conjClass (tightCore R), ∃ g : Y, conjSub g J = J' := by
    rintro _ ⟨g, rfl⟩
    refine ⟨g * g₀⁻¹, ?_⟩
    show conjSub (g * g₀⁻¹) J = conjSub g (tightCore R)
    rw [← hg₀, conjSub_mul, conjSub_inv_conjSub]
  refine E3.partnerUniq_of_nbr hR.hyp htrans ?_ hW
  intro W₀ hW₀ L hL L' hL' hU hU'
  have hLC : L ≤ C := hF.nbr_le_centralizer hL
  have hL'C : L' ≤ C := hF.nbr_le_centralizer hL'
  have hLX : L.subgroupOf C ≤ secH R u :=
    (Subgroup.subgroupOf_mono C (le_iSup₂ (f := fun M (_ : M ∈ {M | TC.nbrAdj
      (CoreAssembly.conjClass (tightCore R)) J M}) => M) L ⟨⟨g₀, hg₀⟩, hL⟩)).trans
      (hF.nbrGen_le_secH hO)
  have hL'X : L'.subgroupOf C ≤ secH R u :=
    (Subgroup.subgroupOf_mono C (le_iSup₂ (f := fun M (_ : M ∈ {M | TC.nbrAdj
      (CoreAssembly.conjClass (tightCore R)) J M}) => M) L' ⟨⟨g₀, hg₀⟩, hL'⟩)).trans
      (hF.nbrGen_le_secH hO)
  have hcard : ∀ M : Subgroup Y, M ≤ C →
      Nat.card ↥(M.subgroupOf C ⊓ W₀.subgroupOf C) = Nat.card ↥(M ⊓ W₀) := by
    intro M hMC
    have e : M.subgroupOf C ⊓ W₀.subgroupOf C = (M ⊓ W₀).subgroupOf C := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    rw [e]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hMC)).toEquiv
  obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := Sec6Gen.exists_data_of_mem_USet hR.hyp hU
  obtain ⟨-, -, -, -, -, -, -, -, h4'⟩ := Sec6Gen.exists_data_of_mem_USet hR.hyp hU'
  have key := E3.eq_of_thinSec hRC.hyp hRC.noTwins hPΦ hthin (P := W₀.subgroupOf C)
    ((isPGroup_of_mem_WSet hW₀).comap_subtype) ⟨L, hL.1, hLC, rfl⟩ ⟨L', hL'.1, hL'C, rfl⟩ hLX
    hL'X (hF.map_mem_secΩ hO hL) (hF.map_mem_secΩ hO hL') (by rw [hcard L hLC]; exact h4)
    (by rw [hcard L' hL'C]; exact h4')
  rw [Subgroup.subgroupOf_inj, inf_of_le_left hLC, inf_of_le_left hL'C] at key
  exact key

theorem E3Frame.t_mem_centralizer (hF : E3Frame n R S t J u) :
    t ∈ Subgroup.centralizer ({u} : Set Y) :=
  hF.core_le_centralizer hF.large.datum.isUniqueInvolution_core.mem

theorem E3Frame.t_mem_secH (hF : E3Frame n R S t J u) :
    (⟨t, hF.t_mem_centralizer⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u := by
  refine le_subnormalClosure _ ?_
  rw [tightCore_subgroupOf hF.core_le_centralizer]
  exact Subgroup.mem_subgroupOf.mpr hF.large.datum.isUniqueInvolution_core.mem

end Frame

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
