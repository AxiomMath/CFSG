module

public import CFSG.ClassicalInvolution.Q3.TL4E3C269BDefs
public import CFSG.ClassicalInvolution.Q3.TL4E3C269B1
public import CFSG.ClassicalInvolution.Q3.TL4E3C269B2
public import CFSG.ClassicalInvolution.Q3.TL4E3OneOrbitC
public import CFSG.ClassicalInvolution.Q3.TL4E3C269Defs

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph
open scoped commutatorElement

section Cit3


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J : Subgroup Y} {u : Y}

theorem E3Frame.false_of_le_normalizer (hF : E3Frame n R S t J u)
    (hN : nbrGen (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J ≤
      Subgroup.normalizer
        (E3.orbGen (CoreAssembly.conjClass (tightCore R)) (tightCore R) J : Set Y)) :
    False := by
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  set π := orbOf (TC.nbrAdj Ω) (tightCore R) J with hπdef
  have hFam := hF.graphFam
  have hd := hF.large.datum
  have hΩ := hd.hypOmegaGen
  have hgen : (⨆ L ∈ Ω, L) = ⊤ := by
    rw [iSup_conjClass_eq]
    exact hF.large.cls.2.1
  obtain ⟨g, hg'⟩ := hF.maxAdj.1.2.1
  have hgJ : conjSub g (tightCore R) = J := hg'
  have hJπ : J ∈ π := mem_orbOf_self _ _
  have hY := hF.lemma1710.generate hgen g (by rw [hgJ]; exact hJπ)
  have hπK : ∀ N ∈ π, N ∈ omegaNbr Ω (tightCore R) := fun N hN =>
    (adj_of_mem_isMaxOrb hFam hF.maxAdj.2 hN).2
  have hπJ : ∀ M ∈ conjSub g '' π, M ∈ omegaNbr Ω J := by
    rintro _ ⟨N, hN, rfl⟩
    have h1 := hFam.graph.conj g (adj_of_mem_isMaxOrb hFam hF.maxAdj.2 hN)
    rw [hgJ] at h1
    exact h1.2
  set P : Subgroup Y := ⨆ N ∈ π, N with hP
  set Q : Subgroup Y := ⨆ M ∈ conjSub g '' π, M with hQ
  have hQX : Q ≤ nbrGen (TC.nbrAdj Ω) J := iSup₂_le fun M hM =>
    le_iSup₂ (f := fun N (_ : N ∈ {N | TC.nbrAdj Ω J N}) => N) M ⟨hF.maxAdj.1.2.1, hπJ M hM⟩
  have hPQ : P ⊔ Q = ⊤ := by
    rw [← hY, iSup_union]
  have hPn : P.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hPQ]
    exact sup_le Subgroup.le_normalizer (hQX.trans hN)
  have hJP : J ≤ P := le_iSup₂_of_le J hJπ le_rfl
  have hPtop : P = ⊤ := by
    rw [eq_top_iff, ← hgen]
    refine iSup₂_le fun L hL => ?_
    obtain ⟨a, rfl⟩ := hL
    have hK : conjSub a (tightCore R) = conjSub (a * g⁻¹) J := by
      rw [← hgJ, conjSub_mul, conjSub_inv_conjSub]
    show conjSub a (tightCore R) ≤ P
    rw [hK]
    intro x hx
    rw [mem_conjSub_iff] at hx
    have h1 := hPn.conj_mem _ (hJP hx) (a * g⁻¹)
    simpa [mul_assoc] using h1
  have hPC : P ≤ Subgroup.centralizer ({t} : Set Y) := by
    refine iSup₂_le fun L hL => ?_
    obtain ⟨v, hv⟩ := Sec6Gen.exists_uniqueInvolution hΩ (hπK L hL).1
    exact edge_le_centralizer_of_alpha hd (hπK L hL) hv (hF.alpha L (hπK L hL) v hv)
  have htZ : t ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff]
    intro y
    have hy : y ∈ P := by rw [hPtop]; exact Subgroup.mem_top y
    exact Subgroup.mem_centralizer_singleton_iff.mp (hPC hy)
  rw [hF.large.center, Subgroup.mem_bot] at htZ
  exact ne_one_of_datum hd htZ

theorem E3Frame.false_of_c264One (hF : E3Frame n R S t J u) (hΛ : TightLambdaCommR 3 n)
    (hOJ : omegaNbr (CoreAssembly.conjClass (tightCore R)) J ⊆
      orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J (tightCore R))
    (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
    (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u)
    (h163 : Concl163 (secR R u) (E3.secT htu ht)) {Rd : Subgroup Y} {Sd : Sylow 2 Rd}
    {S' : Sylow 2 Y} {R' T W : Subgroup Y} (hRd : tightCore Rd = J)
    (hs : TightStd8R 3 n Rd Sd u (tightCore R) S' R' T W t)
    (hE4 : MuIsoE4 (CoreAssembly.conjClass (tightCore Rd)) W)
    (hexc : ∀ x ∈ nbrGen (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J,
      ¬ ∀ y ∈ E3.orbGen (CoreAssembly.conjClass (tightCore R)) (tightCore R) J,
        ⁅x * (u * t) * x⁻¹, y⁆ ∈
          oddCoreOf (E3.orbGen (CoreAssembly.conjClass (tightCore R)) (tightCore R) J))
    (hgen : ∀ x ∈ nbrGen (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J,
      x * t * x⁻¹ ≠ t → x * t * x⁻¹ * t = t * (x * t * x⁻¹) →
        nbrGen (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J ≤
          nbrGen (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J ⊓
              Subgroup.centralizer ({t} : Set Y) ⊔ Subgroup.zpowers x ⊔
            oddCoreOf (nbrGen (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J)) :
    False := by
  classical
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  set X := nbrGen (TC.nbrAdj Ω) J with hXdef
  set P := E3.orbGen Ω (tightCore R) J with hPdef
  have hd := hF.large.datum
  have hJn : J ∈ omegaNbr Ω (tightCore R) := hF.maxAdj.1.2
  have hJΩ : J ∈ Ω := hJn.1
  obtain ⟨g, Sd₀, S₀, R₀, T₀, W₀, hgJ, hgu, -⟩ := hF.exists_std8
  have hfamJ : CoreAssembly.conjClass J = Ω := by rw [← hgJ, conjClass_conjSub]
  have hfam : CoreAssembly.conjClass (tightCore Rd) = Ω := by rw [hRd, hfamJ]
  have hcore₀ : tightCore (conjSub g R) = J := by rw [← conjSub_tightCore, hgJ]
  have hαJ : TightSepAlpha (conjSub g R) u := hgu ▸ hF.alpha.conj g
  have hαd : TightSepAlpha Rd u := by
    intro J' hJ' v hv
    have hcd : tightCore Rd = tightCore (conjSub g R) := by rw [hcore₀, hRd]
    exact hαJ J' (by rw [← hcd]; exact hJ') v hv
  have hΛp := hs.sup_omegaNbrGen_ne_top_of_alpha hαd
  obtain ⟨t₁, ht₁2, -, ht₁t, htt₁, hut₁, ht₁R, -, -, -, J₁, hJ₁Ω, hJ₁X, hJ₁inv⟩ :=
    hs.exists_good_involution_E4_of_ne_top hΛ hΛp hE4
  have hXeq : omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) = X := by
    rw [hfam, hRd, hXdef, E3.nbrGen_eq_omegaNbrGen hJΩ]
  rw [hfam] at hJ₁Ω
  rw [hXeq] at hJ₁X
  have hXC : X ≤ Subgroup.centralizer ({u} : Set Y) := hF.nbrGen_le_centralizer
  have hCJ : ∀ c ∈ Subgroup.centralizer ({u} : Set Y), conjSub c J = J := by
    intro c hc'
    have h1 := hs.large.datum.le_normalizer_core hc'
    rw [hRd] at h1
    exact mem_normalizer_iff_conjSub_eq.mp h1
  have hJX : ¬ J ≤ X := by
    have h1 := hs.not_le_omegaNbrGen_of_ne_top (tightSecNbrGenR_of_comm hΛ)
      (ne_top_of_le_ne_top hΛp le_sup_right)
    rwa [hXeq, hRd] at h1
  have hJ₁n : J₁ ∈ omegaNbr Ω J := by
    refine ⟨hJ₁Ω, fun h => hJX (h ▸ hJ₁X), ?_⟩
    obtain ⟨Q₁⟩ : Nonempty (Sylow 2 ↥J₁) := inferInstance
    refine ⟨(Q₁ : Subgroup ↥J₁).map J₁.subtype, ⟨J₁, hJ₁Ω, Q₁, rfl⟩,
      Subgroup.map_subtype_le _, fun y hy => ?_⟩
    exact mem_normalizer_iff_conjSub_eq.mpr (hCJ y (hXC (hJ₁X (Subgroup.map_subtype_le _ hy))))
  obtain ⟨x, hx, hxJ₁⟩ := hOJ hJ₁n
  have hxt : x * t * x⁻¹ = t₁ := by
    have h1 := hd.isUniqueInvolution_core.conj x
    rw [hxJ₁] at h1
    exact h1.eq hJ₁inv
  have hR := TightLargeHypR.typeRFam hs.large
  have hJ2 : IsPGroup 2 (↥J ⧸ classicalInvolutionOddCore ↥J) := by
    have h1 := hR.twoGroup (tightCore Rd) hs.mem
    rwa [hRd] at h1
  have hRsyl : IsSylow2In R' J := by
    have h1 := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hs.hyp hs.mem hs.hR.1 hs.hR.2.1
    rwa [hRd] at h1
  have ht₁C : t₁ ∈ Subgroup.centralizer ({u} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hut₁.symm
  have hcommJ : ∀ j ∈ J, ⁅t₁, j⁆ ∈ oddCoreOf J := fun j hj =>
    comm_mem_oddCoreOf_of_twoGroup hJ2 hRsyl (mem_normalizer_iff_conjSub_eq.mpr (hCJ t₁ ht₁C))
      (fun p hp => (ht₁R p hp).symm) hj
  have hJC : J ≤ Subgroup.centralizer ({u} : Set Y) := by
    rw [← hRd]
    exact (tightCore_le Rd).trans hs.large.datum.cent
  have hOJu : oddCoreOf J ≤ oddCoreOf (Subgroup.centralizer ({u} : Set Y)) :=
    Asc77.T8.oddCoreOf_le_oddCoreOf_of_normalized hJC hCJ
  have hαu₁ : alphaOf (Subgroup.closure ({u, t₁} : Set Y)) = ⊥ :=
    hαJ J₁ (by rw [hcore₀, hfamJ]; exact hJ₁n) t₁ hJ₁inv
  have hOCt₁ := E3.oddCore_le_centralizer_of_alpha hαu₁ hF.inv.ne_one
  have ht₁J : ∀ j ∈ J, t₁ * j = j * t₁ := by
    intro j hj
    have hcO : t₁ * j * t₁⁻¹ * j⁻¹ ∈ oddCoreOf J := by
      have h1 := hcommJ j hj
      rwa [commutatorElement_def] at h1
    have hct := Subgroup.mem_centralizer_singleton_iff.mp (hOCt₁ (hOJu hcO))
    have hc' : t₁ * j * t₁⁻¹ * j⁻¹ = j * t₁⁻¹ * j⁻¹ * t₁⁻¹ := by
      calc t₁ * j * t₁⁻¹ * j⁻¹ = t₁ * j * t₁⁻¹ * j⁻¹ * t₁ * t₁⁻¹ := by group
        _ = t₁ * (t₁ * j * t₁⁻¹ * j⁻¹) * t₁⁻¹ := by rw [hct]
        _ = (t₁ * t₁) * j * t₁⁻¹ * j⁻¹ * t₁⁻¹ := by group
        _ = j * t₁⁻¹ * j⁻¹ * t₁⁻¹ := by rw [ht₁2]; group
    have hcc : (t₁ * j * t₁⁻¹ * j⁻¹) * (t₁ * j * t₁⁻¹ * j⁻¹) = 1 := by
      calc (t₁ * j * t₁⁻¹ * j⁻¹) * (t₁ * j * t₁⁻¹ * j⁻¹) =
          (t₁ * j * t₁⁻¹ * j⁻¹) * (j * t₁⁻¹ * j⁻¹ * t₁⁻¹) := by rw [← hc']
        _ = t₁ * j * (t₁ * t₁)⁻¹ * j⁻¹ * t₁⁻¹ := by group
        _ = 1 := by rw [ht₁2]; group
    have hc1 : t₁ * j * t₁⁻¹ * j⁻¹ = 1 := by
      by_contra hne
      exact hne (eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard J) hcO
        (isPGroup_zpowers_of_mul_self_eq_one hcc hne))
    calc t₁ * j = t₁ * j * t₁⁻¹ * j⁻¹ * (j * t₁) := by group
      _ = j * t₁ := by rw [hc1, one_mul]
  have hex := hexc x hx
  have hxu : x * (u * t) * x⁻¹ = u * t₁ := by
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hXC hx)
    rw [← hxt]
    calc x * (u * t) * x⁻¹ = (x * u) * t * x⁻¹ := by group
      _ = (u * x) * t * x⁻¹ := by rw [h1]
      _ = u * (x * t * x⁻¹) := by group
  have hcent : ∀ y ∈ P, ⁅x * t * x⁻¹, y⁆ ∈ oddCoreOf P := by
    rcases hF.cent_or_cent_mul hOJ htu ht h163 ht₁2 htt₁.symm ht₁J with h1 | h1
    · rw [hxt]
      exact h1
    · exact absurd (fun y hy => hxu ▸ h1 y hy) hex
  have hst : x * t * x⁻¹ * t = t * (x * t * x⁻¹) := by rw [hxt]; exact htt₁.symm
  have hxP : conjSub x P = P := hF.conjSub_orbGen_of_cent hx hst hcent hex
  have hCtN : Subgroup.centralizer ({t} : Set Y) ≤ Subgroup.normalizer (P : Set Y) :=
    fun c hc' => mem_normalizer_iff_conjSub_eq.mpr (hF.conjSub_orbGen_core hc')
  have hxN : Subgroup.zpowers x ≤ Subgroup.normalizer (P : Set Y) :=
    Subgroup.zpowers_le.mpr (mem_normalizer_iff_conjSub_eq.mpr hxP)
  have hCX : ∀ c ∈ Subgroup.centralizer ({u} : Set Y), conjSub c X = X := by
    intro c hc'
    rw [hXdef, E3.nbrGen_eq_omegaNbrGen hJΩ]
    exact conjSub_omegaNbrGen_of_conjSub_eq hd.hypOmegaGen.conjInvariant (hCJ c hc')
  have hαut : alphaOf (Subgroup.closure ({u, t} : Set Y)) = ⊥ := by
    rw [Set.pair_comm]
    exact hF.alpha J hJn u hF.inv
  have hON : oddCoreOf X ≤ Subgroup.normalizer (P : Set Y) :=
    ((Asc77.T8.oddCoreOf_le_oddCoreOf_of_normalized hXC hCX).trans
      (E3.oddCore_le_centralizer_of_alpha hαut hF.inv.ne_one)).trans hCtN
  have hne : x * t * x⁻¹ ≠ t := by rw [hxt]; exact ht₁t
  have hXN : X ≤ Subgroup.normalizer (P : Set Y) :=
    (hgen x hx hne hst).trans (sup_le (sup_le (inf_le_right.trans hCtN) hxN) hON)
  exact hF.false_of_le_normalizer hXN

theorem tightE3C269S_of {n : ℕ} (hEx : TightE3C268Ex n) (hGen : TightE3C269Gen n) :
    TightE3C269S n := by
  intro hΛ Y _ _ R S t J u hF htu ht Sb hex hedge hμ hnE2 h163 Rd Sd S' R' T W hRd hs hE4 hC1
  have hOJ := hF.omegaNbr_subset_orbOf htu ht h163
  exact hF.false_of_c264One hΛ hOJ htu ht h163 hRd hs hE4
    (hEx Y R S t J u hF htu ht hedge hμ hnE2 h163 Rd Sd S' R' T W hRd hs hE4 hC1)
    (hGen Y R S t J u hF htu ht Sb hex hedge hμ hnE2 hOJ Rd Sd S' R' T W hRd hs hE4)

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
