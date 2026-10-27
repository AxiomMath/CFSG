module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResE3S3F3
public import CFSG.ClassicalInvolution.Q3.TL4E3S3NB

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TC.Graph
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  (transitive_of_maxOrb piGen le_piGen piGen_le piGen_conj)
open scoped commutatorElement

section Cit3b


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J : Subgroup Y} {u : Y}

theorem E3FrameR.exists_pick (hF : E3FrameR r n R S t J u) (hedge : TightEdgeless (secR R u))
    (hμ : ∀ W ∈ WSet (E3.secΩ R u), MuIsoS3 (E3.secΩ R u) W) :
    ∃ L ∈ orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J (tightCore R),
      L ∈ omegaStarNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R) ∧
        L ∉ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R) := by
  classical
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

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J : Subgroup Y} {u : Y}

theorem E3FrameR.omegaNbr_ne_of_gen (hG : TightSecGenS3R r n) (hF : E3FrameR r n R S t J u)
    (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
    (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u)
    (Sb : Sylow 2 ↥(secR R u)) (hex : TightEx (SecQ R u) (secR R u) Sb (E3.secT htu ht))
    (hedge : TightEdgeless (secR R u)) (hnE2 : ¬ TightInO2 (E3.secT htu ht))
    (h163 : Concl163 (secR R u) (E3.secT htu ht)) {L : Subgroup Y}
    (hLπ : L ∈ orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J (tightCore R))
    (hLs : L ∈ omegaStarNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hLn : L ∉ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) :
    omegaNbr (CoreAssembly.conjClass (tightCore R)) L ≠
      omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R) := by
  intro heq
  classical
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  set Φ := omegaNbr Ω (tightCore R) with hΦdef
  have hd := hF.large.datum
  have hΩG := hd.hypOmegaGen
  have hc : ConjInvariant Ω := hΩG.conjInvariant
  have h := TightLargeHypR.typeRFam hF.large
  have hJn : J ∈ Φ := hF.maxAdj.1.2
  have hK₀Ω : tightCore R ∈ Ω := CoreAssembly.mem_conjClass_self _
  have hCt : Subgroup.centralizer ({t} : Set Y) ≤
      Subgroup.normalizer ((tightCore R : Subgroup Y) : Set Y) :=
    h.tight _ hK₀Ω t hd.isUniqueInvolution_core
  have hO := hF.omegaNbr_subset_orbOf htu ht h163
  obtain ⟨x, hxN, hxK⟩ := hLπ
  have hsL : IsUniqueInvolution L (x * t * x⁻¹) := hxK ▸ hd.isUniqueInvolution_core.conj x
  obtain ⟨-, -, U, hU, hUK, hUN⟩ := Q3T6.Mu.omegaStarNbr_symm hΩG hK₀Ω hLs.1 hLs
  obtain ⟨-, -, -, -, -, -, -, -, hU4⟩ := Sec6Gen.exists_data_of_mem_USet hΩG hU
  have htU : t ∈ U := T3.mem_of_isPGroup hd.isUniqueInvolution_core hUK
    (Sec6Gen.isPGroup_of_mem_USet hΩG hU) (le_trans (by norm_num) hU4)
  have htL : conjSub t L = L := mem_normalizer_iff_conjSub_eq.mp (hUN htU)
  have hts : t * (x * t * x⁻¹) * t⁻¹ = x * t * x⁻¹ := hsL.conj_eq htL
  have hcomm : x * t * x⁻¹ * t = t * (x * t * x⁻¹) := by
    calc x * t * x⁻¹ * t = t * (x * t * x⁻¹) * t⁻¹ * t := by rw [hts]
      _ = t * (x * t * x⁻¹) := by group
  have hxt : x * t * x⁻¹ ≠ t := by
    intro hst
    apply hLs.2.1
    rw [← hxK]
    refine mem_normalizer_iff_conjSub_eq.mp (hCt ?_)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * t = x * t * x⁻¹ * x := by group
      _ = t * x := by rw [hst]
  have hX := hF.le_sup_of_secGen hO htu ht (hG Y R S t J u hF htu ht Sb hex hedge hnE2) hxN hxt
    hcomm
  set P := piGen Φ with hPdef
  have hnormΦ : ∀ c : Y, conjSub c '' Φ = Φ → c ∈ Subgroup.normalizer (P : Set Y) := by
    intro c hcΦ
    refine Generic.mem_normalizer_of_conjSub_eq ?_
    rw [hPdef, ← piGen_conj, hcΦ]
  have hCtP : Subgroup.centralizer ({t} : Set Y) ≤ Subgroup.normalizer (P : Set Y) := by
    intro c hc'
    refine hnormΦ c ?_
    rw [hΦdef, E3.image_conjSub_omegaNbr hc, mem_normalizer_iff_conjSub_eq.mp (hCt hc')]
  have hxP : x ∈ Subgroup.normalizer (P : Set Y) := by
    refine hnormΦ x ?_
    rw [hΦdef, E3.image_conjSub_omegaNbr hc, hxK, heq]
  have hXeq := hF.nbrGen_eq_orbGen_J hO
  have hOX : oddCoreOf (nbrGen (TC.nbrAdj Ω) J) ≤ Subgroup.centralizer ({t} : Set Y) := by
    rw [hXeq]
    exact hF.oddCoreOf_orbGen_J_le_centralizer
  have hXP : nbrGen (TC.nbrAdj Ω) J ≤ Subgroup.normalizer (P : Set Y) :=
    hX.trans (sup_le (sup_le (inf_le_right.trans hCtP) (Subgroup.zpowers_le.mpr hxP))
      (hOX.trans hCtP))
  have hNt : nbrGen (TC.nbrAdj Ω) (tightCore R) ≤ Subgroup.centralizer ({t} : Set Y) :=
    iSup₂_le fun M hM => hF.le_centralizer_of_mem_omegaNbr hK₀Ω hM.2 hd.isUniqueInvolution_core
  have hXgP : E3.orbGen Ω (tightCore R) J ≤ P := by
    refine iSup₂_le fun M hM => ?_
    obtain ⟨l, hl, rfl⟩ := hM
    refine le_piGen ?_
    have h1 := omegaNbr_conj hc hJn l
    rwa [mem_normalizer_iff_conjSub_eq.mp (hCt (hNt hl))] at h1
  have htop := hF.eq_top_of_orbGen_le (H := Subgroup.normalizer (P : Set Y))
    (hXgP.trans Subgroup.le_normalizer) (hXeq.symm.le.trans hXP)
  have hPn : P.Normal := Subgroup.normalizer_eq_top_iff.mp htop
  obtain ⟨g, hg'⟩ := hJn.1
  have hgJ : conjSub g (tightCore R) = J := hg'
  have hJP : J ≤ P := le_piGen hJn
  have hPtop : (⊤ : Subgroup Y) ≤ P := by
    have hgen : (⨆ M ∈ Ω, M) = ⊤ := by
      rw [iSup_conjClass_eq]
      exact hF.large.cls.2.1
    rw [← hgen]
    refine iSup₂_le fun M hM => ?_
    obtain ⟨y, hy'⟩ := hM
    have hy : conjSub y (tightCore R) = M := hy'
    have hyJ : M = conjSub (y * g⁻¹) J := by rw [← hy, ← hgJ, conjSub_mul, conjSub_inv_conjSub]
    rw [hyJ]
    intro z hz
    rw [mem_conjSub_iff] at hz
    have h1 := hPn.conj_mem _ (hJP hz) (y * g⁻¹)
    rwa [show y * g⁻¹ * ((y * g⁻¹)⁻¹ * z * (y * g⁻¹)) * (y * g⁻¹)⁻¹ = z by group] at h1
  have hPt : P ≤ Subgroup.centralizer ({t} : Set Y) :=
    piGen_le fun M hM => hF.le_centralizer_of_mem_omegaNbr hK₀Ω hM hd.isUniqueInvolution_core
  have htZ : t ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subgroup.mem_centralizer_singleton_iff.mp (hPt (hPtop (Subgroup.mem_top y)))
  rw [hF.large.center, Subgroup.mem_bot] at htZ
  exact hd.isUniqueInvolution_core.ne_one htZ

theorem E3FrameR.cent_of_notBeta (hF : E3FrameR r n R S t J u)
    (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
    (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u)
    (h163 : Concl163 (secR R u) (E3.secT htu ht)) {L : Subgroup Y}
    (hLπ : L ∈ orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J (tightCore R))
    (hLs : L ∈ omegaStarNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hB : omegaNbr (CoreAssembly.conjClass (tightCore R)) L ≠
      omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hLn : L ∉ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) :
    ∀ y ∈ E3.orbGen (CoreAssembly.conjClass (tightCore R)) L J,
      ⁅u * t, y⁆ ∈ oddCoreOf (E3.orbGen (CoreAssembly.conjClass (tightCore R)) L J) := by
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hd := hF.large.datum
  have hΩG := hd.hypOmegaGen
  have hc : ConjInvariant Ω := hΩG.conjInvariant
  have hJn : J ∈ omegaNbr Ω (tightCore R) := hF.maxAdj.1.2
  have hJΩ : J ∈ Ω := hJn.1
  have hK₀Ω : tightCore R ∈ Ω := CoreAssembly.mem_conjClass_self _
  obtain ⟨g, hgJ, hgK, hgt⟩ := hF.exists_conj_edge' hLπ
  have hJt : J ≤ Subgroup.centralizer ({t} : Set Y) :=
    edge_le_centralizer_of_alpha hd hJn hF.inv (hF.alpha J hJn u hF.inv)
  have hLΩ : L ∈ Ω := hLs.1
  obtain ⟨-, -, U, hU, hUK, hUN⟩ := Q3T6.Mu.omegaStarNbr_symm hΩG hK₀Ω hLΩ hLs
  obtain ⟨-, -, -, -, -, -, -, -, hU4⟩ := Sec6Gen.exists_data_of_mem_USet hΩG hU
  have htU : t ∈ U := T3.mem_of_isPGroup hd.isUniqueInvolution_core hUK
    (Sec6Gen.isPGroup_of_mem_USet hΩG hU) (le_trans (by norm_num) hU4)
  have htL : conjSub t L = L := mem_normalizer_iff_conjSub_eq.mp (hUN htU)
  set t₀ := g⁻¹ * t * g with ht₀def
  have ht₀J : conjSub t₀ J = J := by
    rw [ht₀def, conjSub_mul, conjSub_mul, hgJ, htL, ← hgJ, conjSub_inv_conjSub]
  have ht₀C : t₀ ∈ Subgroup.centralizer ({u} : Set Y) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hF.inv.conj_eq ht₀J
    calc t₀ * u = t₀ * u * t₀⁻¹ * t₀ := by group
      _ = u * t₀ := by rw [h1]
  have ht₀K : ∀ k ∈ tightCore R, t₀ * k * t₀⁻¹ = k := by
    intro k hk
    have hkJ : g * k * g⁻¹ ∈ J := by
      rw [← hgK]
      exact conj_mem_conjSub hk
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hJt hkJ)
    calc t₀ * k * t₀⁻¹ = g⁻¹ * (t * (g * k * g⁻¹)) * t⁻¹ * g := by rw [ht₀def]; group
      _ = g⁻¹ * ((g * k * g⁻¹) * t) * t⁻¹ * g := by rw [← h1]
      _ = k := by group
  have ht2 : t * t = 1 := hd.isUniqueInvolution_core.sq
  have horb : conjSub g (E3.orbGen Ω J (tightCore R)) = E3.orbGen Ω L J := by
    rw [← E3.orbGen_conj hc hJΩ g, hgJ, hgK]
  rcases hF.cent_or_cent_conj htu ht h163 g ht2 ht₀C ht₀K with h | h
  · refine (hB (hF.omegaNbr_eq_of_cent htu ht h163 hLπ hLn ?_)).elim
    rw [← horb]
    exact h
  · rw [hgt, horb] at h
    exact h

end Cit3

end CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes
