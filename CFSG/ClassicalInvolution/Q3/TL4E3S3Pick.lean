module

public import CFSG.ClassicalInvolution.Q3.TL4E3S3
public import CFSG.ClassicalInvolution.Q3.TL4E3MuPass
public import CFSG.ClassicalInvolution.Q3.TL4E3Trans

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph
open scoped commutatorElement

theorem E3.nbrGen_eq_omegaNbrGen {G : Type} [Group G] {Ω : Set (Subgroup G)} {J : Subgroup G}
    (hJ : J ∈ Ω) : nbrGen (TC.nbrAdj Ω) J = omegaNbrGen Ω J :=
  le_antisymm (iSup₂_le fun M hM => le_iSup₂ (f := fun N (_ : N ∈ omegaNbr Ω J) => N) M hM.2)
    (iSup₂_le fun M hM =>
      le_iSup₂ (f := fun N (_ : N ∈ {N | TC.nbrAdj Ω J N}) => N) M ⟨hJ, hM⟩)

theorem E3.quotFamily_conjClass {H : Type} [Group H] (K N : Subgroup H) [N.Normal] :
    quotFamily (CoreAssembly.conjClass K) N =
      CoreAssembly.conjClass (K.map (QuotientGroup.mk' N)) := by
  ext A
  constructor
  · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
    exact ⟨QuotientGroup.mk' N g, (E3.map_conjSub _ g K).symm⟩
  · rintro ⟨b, rfl⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N b
    exact ⟨conjSub g K, ⟨g, rfl⟩, E3.map_conjSub _ g K⟩

section Cit3


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J : Subgroup Y} {u : Y}

theorem E3Frame.secH_le_nbrGen (hF : E3Frame n R S t J u) :
    secH R u ≤ (nbrGen (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J).subgroupOf
      (Subgroup.centralizer ({u} : Set Y)) := by
  set C := Subgroup.centralizer ({u} : Set Y) with hC
  set X := nbrGen (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J with hX
  have hd := hF.large.datum
  have hXC : X ≤ C := hF.nbrGen_le_centralizer
  have hKC : tightCore R ≤ C := hF.core_le_centralizer
  have hJn := hF.maxAdj.1.2
  have hJΩ : J ∈ CoreAssembly.conjClass (tightCore R) := hJn.1
  have hK₀J : tightCore R ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J :=
    Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hd.hypOmegaGen hF.maxAdj.1.1 hJn.1 hJn
  obtain ⟨g, Sd, S', R', T, W, hgJ, hu, hs⟩ := hF.exists_std8
  have hcore : tightCore (conjSub g R) = J := by rw [← conjSub_tightCore, hgJ]
  have hCN : C ≤ Subgroup.normalizer (X : Set Y) := by
    intro c hc
    have hcJ : conjSub c J = J := by
      have h1 := hs.large.datum.le_normalizer_core hc
      rw [hcore] at h1
      exact mem_normalizer_iff_conjSub_eq.mp h1
    rw [mem_normalizer_iff_conjSub_eq, hX, E3.nbrGen_eq_omegaNbrGen hJΩ]
    exact conjSub_omegaNbrGen_of_conjSub_eq hd.hypOmegaGen.conjInvariant hcJ
  have hXn : (X.subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXC).mpr hCN
  refine subnormalClosure_le ?_ ?_
  · rw [tightCore_subgroupOf hKC]
    exact Subgroup.subgroupOf_mono C (le_iSup₂ (f := fun N (_ : N ∈ {N | TC.nbrAdj
      (CoreAssembly.conjClass (tightCore R)) J N}) => N) (tightCore R) ⟨hJΩ, hK₀J⟩)
  · exact isSubnormal_of_normal_subgroupOf le_top inferInstance

end Cit3

section Cit3b


theorem tightE3S3Pick_proved {n : ℕ} : TightE3S3Pick n := by
  classical
  intro Y _ _ R S t J u hF hedge hμ
  set C := Subgroup.centralizer ({u} : Set Y) with hC
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hd := hF.large.datum
  have hKC : tightCore R ≤ C := hF.core_le_centralizer
  have htu := hF.t_mem_centralizer
  have ht := hF.t_mem_secH
  obtain ⟨Sq, hdq⟩ := E3.exists_secDatum hd hF.maxAdj.1.2 hF.inv htu ht
  have hP : Q3CL.PartIHypG (E3.secΩ R u) := hdq.partIHypG
  obtain ⟨Sb⟩ : Nonempty (Sylow 2 (SecQ R u)) := inferInstance
  obtain ⟨η, hη, hinv⟩ := Sec6Gen.exists_invariant_mem_etaSet hP.hyp Sb
  have hW₁ : (⨆ U ∈ η, U) ∈ WSet (E3.secΩ R u) := ⟨η, ⟨Sb, hη, hinv⟩, rfl⟩
  have hstar : ∃ A ∈ E3.secΩ R u, (omegaStarNbr (E3.secΩ R u) A).Nonempty := by
    by_contra hcon
    push Not at hcon
    obtain ⟨e₂⟩ := Q3T6.Mu.muIsoZ2_of_shape hP hW₁ ⟨_, CoreAssembly.mem_conjClass_self _⟩
      hcon
    obtain ⟨e₆⟩ := hμ _ hW₁
    have h26 := Nat.card_congr (e₂.symm.trans e₆).toEquiv
    simp [Nat.card_eq_fintype_card, Fintype.card_perm] at h26
    exact absurd h26 (by decide)
  obtain ⟨_, ⟨a, rfl⟩, B, hB⟩ := hstar
  have hcΦ : ConjInvariant (E3.secΩ R u) := hP.hyp.conjInvariant
  have hB' := omegaStarNbr_conj hcΦ hB a⁻¹
  rw [conjSub_inv_conjSub] at hB'
  obtain ⟨b, hb'⟩ := hB'.1
  have hb : conjSub b (tightCore (secR R u)) = conjSub a⁻¹ B := hb'
  set H := secH R u with hHdef
  set N := classicalInvolutionOddCore ↥H with hNdef
  set K' : Subgroup ↥H := ((tightCore R).subgroupOf C).subgroupOf H with hK'def
  have hK'map : K'.map (QuotientGroup.mk' N) = tightCore (secR R u) := hF.tightCore_secR.symm
  have hfamq : quotFamily (CoreAssembly.conjClass K') N = E3.secΩ R u := by
    rw [E3.quotFamily_conjClass, hK'map]
  obtain ⟨-, hu2, hut, -, huK, -⟩ := hd.edge_involution hF.maxAdj.1.2 hF.inv
  have hcomm : ∀ r ∈ R, ⁅u, r⁆ ∈ oddCoreImg R := (hd.act_eq_one_iff hut).mp huK
  have huN : u ∈ Subgroup.normalizer (R : Set Y) := hd.le_normalizer hut
  have huC : u ∈ centralizerModOdd ⊤ R :=
    ⟨Subgroup.mem_top u, huN, mem_normalizer_oddCore_of_mem_normalizer huN, hcomm⟩
  obtain ⟨S', hS'⟩ := hd.exists_sylow_le_centralizer
    (Balance.isPGroup_zpowers_of_mul_self_eq_one hu2) (Subgroup.zpowers_le.mpr huC)
  have hS'u : (S' : Subgroup R).map R.subtype ≤ C :=
    hS'.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers u)))
  obtain ⟨S₁, hd₁, -⟩ := (hd.ofSylow S').restrict hS'u
  have hSH : (S₁ : Subgroup ↥(R.subgroupOf C)).map (R.subgroupOf C).subtype ≤ H :=
    hd₁.sylow_core.1.trans (le_subnormalClosure _)
  obtain ⟨S₂, hd₂, -⟩ := hd₁.restrict hSH
  have hΩ'G : HypOmegaGen (CoreAssembly.conjClass K') := by
    have h : HypOmegaGen (CoreAssembly.conjClass (tightCore ((R.subgroupOf C).subgroupOf H))) :=
      hd₂.hypOmegaGen
    have e : tightCore ((R.subgroupOf C).subgroupOf H) = K' := by
      rw [tightCore_subgroupOf (le_subnormalClosure _)]
      exact congrArg (fun A => A.subgroupOf H) (tightCore_subgroupOf hKC)
    rwa [e] at h
  have hNodd : Odd (Nat.card N) := CFSG.ComponentClassification.OddCore.odd_card ↥H
  have hΩq : HypOmegaGen (quotFamily (CoreAssembly.conjClass K') N) := by
    rw [hfamq]
    exact hP.hyp
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective N b
  have hL'map : (conjSub h K').map (QuotientGroup.mk' N) = conjSub a⁻¹ B := by
    rw [E3.map_conjSub, hK'map]
    exact hb
  obtain ⟨m, hmN, hm⟩ := C25J.exists_conj_omegaStarNbr_gen hΩ'G hΩq hNodd (K := K')
    (J := conjSub h K') (CoreAssembly.mem_conjClass_self _) ⟨h, rfl⟩
    (by rw [hL'map, hK'map, hfamq]; exact hB')
  have hL'' := omegaStarNbr_conj hΩ'G.conjInvariant hm m⁻¹
  rw [conjSub_inv_conjSub, ← conjSub_mul] at hL''
  set φ : ↥H →* Y := C.subtype.comp H.subtype with hφdef
  have hφ : Function.Injective φ := Subtype.val_injective.comp Subtype.val_injective
  have hKH : (tightCore R).subgroupOf C ≤ H :=
    (tightCore_subgroupOf hKC).symm.le.trans (le_subnormalClosure _)
  have hK'φ : K'.map φ = tightCore R := by
    rw [hφdef, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hKH,
      Subgroup.map_subgroupOf_eq_of_le hKC]
  have hΩmap : ∀ X ∈ CoreAssembly.conjClass K', X.map φ ∈ Ω := by
    rintro _ ⟨g, rfl⟩
    refine ⟨φ g, ?_⟩
    show conjSub (φ g) (tightCore R) = (conjSub g K').map φ
    rw [E3.map_conjSub, hK'φ]
  have hstarY := E3.mem_omegaStarNbr_map φ hφ hΩmap hL''
  rw [hK'φ] at hstarY
  have hLeq : (conjSub (m⁻¹ * h) K').map φ = conjSub (φ (m⁻¹ * h)) (tightCore R) := by
    rw [E3.map_conjSub, hK'φ]
  have hmemX : φ (m⁻¹ * h) ∈ nbrGen (TC.nbrAdj Ω) J :=
    Subgroup.mem_subgroupOf.mp (hF.secH_le_nbrGen (m⁻¹ * h).2)
  refine ⟨_, ⟨φ (m⁻¹ * h), hmemX, hLeq.symm⟩, hstarY, ?_⟩
  intro hLn
  obtain ⟨hLΩ, -, P, hP, hPL, hPN⟩ := hLn
  have hPr : P ≤ φ.range := hPL.trans (Subgroup.map_le_range _ _)
  set P' := P.comap φ with hP'def
  have hP'map : P'.map φ = P := Subgroup.map_comap_eq_self hPr
  have hPsyl : IsSylow2In P ((conjSub (m⁻¹ * h) K').map φ) :=
    Sec6Gen.isSylow2In_of_mem_RSet_of_le hd.hypOmegaGen hLΩ hP hPL
  have hP'syl : IsSylow2In P' (conjSub (m⁻¹ * h) K') := by
    rw [← hP'map, hφdef, ← Subgroup.map_map, ← Subgroup.map_map] at hPsyl
    exact isSylow2In_map_subtype_iff.mp (isSylow2In_map_subtype_iff.mp hPsyl)
  have hP'N : P' ≤ Subgroup.normalizer (K' : Set ↥H) := by
    intro x hx
    have hxN : φ x ∈ Subgroup.normalizer (tightCore R : Set Y) := hPN (Subgroup.mem_comap.mp hx)
    rw [mem_normalizer_iff_conjSub_eq] at hxN ⊢
    apply Subgroup.map_injective hφ
    rw [E3.map_conjSub, hK'φ, hxN]
  have hLbar : (conjSub (m⁻¹ * h) K').map (QuotientGroup.mk' N) = conjSub a⁻¹ B := by
    have hm1 : QuotientGroup.mk' N m = 1 := (QuotientGroup.eq_one_iff m).mpr hmN
    rw [E3.map_conjSub, map_mul, map_inv, hm1, inv_one, one_mul, ← E3.map_conjSub]
    exact hL'map
  have hnbr : conjSub a⁻¹ B ∈ omegaNbr (E3.secΩ R u) (tightCore (secR R u)) := by
    refine ⟨hB'.1, hB'.2.1, P'.map (QuotientGroup.mk' N), ?_, ?_, ?_⟩
    · have hLb : (conjSub (m⁻¹ * h) K').map (QuotientGroup.mk' N) ∈ E3.secΩ R u :=
        hLbar ▸ hB'.1
      exact mem_RSet_of_isSylow2In hLb (Hall196.isSylow2In_map_hom _ hP'syl)
    · rw [← hLbar]
      exact Subgroup.map_mono hP'syl.1
    · rw [← hK'map]
      exact (Subgroup.map_mono hP'N).trans (Subgroup.le_normalizer_map _)
  exact hedge _ (CoreAssembly.mem_conjClass_self _) _ hB'.1 (Or.inl hnbr)

end Cit3b

end CFSG.ClassicalInvolution.Q3.TL4
