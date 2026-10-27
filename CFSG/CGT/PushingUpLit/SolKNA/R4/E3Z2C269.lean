module

public import CFSG.ClassicalInvolution.Q3.TL4E3C269BEx
public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResE3S3F2

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Q3.Q3AM710
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TC.Graph
open scoped commutatorElement

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J : Subgroup Y} {u : Y}

theorem E3FrameR.conjSub_orbGen_of_cent (hF : E3FrameR r n R S t J u) {x : Y}
    (hx : x ∈ nbrGen (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J)
    (hst : x * t * x⁻¹ * t = t * (x * t * x⁻¹))
    (hcent : ∀ y ∈ E3.orbGen (CoreAssembly.conjClass (tightCore R)) (tightCore R) J,
      ⁅x * t * x⁻¹, y⁆ ∈
        oddCoreOf (E3.orbGen (CoreAssembly.conjClass (tightCore R)) (tightCore R) J))
    (hex : ¬ ∀ y ∈ E3.orbGen (CoreAssembly.conjClass (tightCore R)) (tightCore R) J,
      ⁅x * (u * t) * x⁻¹, y⁆ ∈
        oddCoreOf (E3.orbGen (CoreAssembly.conjClass (tightCore R)) (tightCore R) J)) :
    conjSub x (E3.orbGen (CoreAssembly.conjClass (tightCore R)) (tightCore R) J) =
      E3.orbGen (CoreAssembly.conjClass (tightCore R)) (tightCore R) J := by
  classical
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  set π := orbOf (TC.nbrAdj Ω) (tightCore R) J with hπdef
  set P := E3.orbGen Ω (tightCore R) J with hPdef
  set s := x * t * x⁻¹ with hsdef
  set J₁ := conjSub x (tightCore R) with hJ₁def
  have hFam := hF.graphFam
  have hd := hF.large.datum
  have hΩG := hd.hypOmegaGen
  have hR : TypeRFam r Ω := TightLargeHypR.typeRFam hF.large
  have hc : ConjInvariant Ω := hΩG.conjInvariant
  have hK₀Ω : tightCore R ∈ Ω := CoreAssembly.mem_conjClass_self _
  have hπ : π ∈ maxOrbs (TC.nbrAdj Ω) (tightCore R) := hF.maxAdj.2
  have hπK : ∀ N ∈ π, N ∈ omegaNbr Ω (tightCore R) := fun N hN =>
    (adj_of_mem_isMaxOrb hFam hπ hN).2
  have hJ₁Ω : J₁ ∈ Ω := hc x _ hK₀Ω
  have hsJ₁ : IsUniqueInvolution J₁ s := hd.isUniqueInvolution_core.conj x
  have hCt : ∀ c ∈ Subgroup.centralizer ({t} : Set Y), conjSub c P = P := fun c hc' =>
    hF.conjSub_orbGen_core hc'
  have hNO : ∀ {c : Y}, c ∈ Subgroup.centralizer ({t} : Set Y) → ∀ y ∈ oddCoreOf P,
      c * y * c⁻¹ ∈ oddCoreOf P := fun hc' _ hy =>
    mem_normalizer_oddCoreOf_of_mem_normalizer (mem_normalizer_iff_conjSub_eq.mpr (hCt _ hc')) hy
  have hsC : s ∈ Subgroup.centralizer ({t} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hst
  have huC : u ∈ Subgroup.centralizer ({t} : Set Y) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_singleton_iff.mp hF.t_mem_centralizer).symm
  have hPC : P ≤ Subgroup.centralizer ({t} : Set Y) := by
    refine iSup₂_le fun L hL => ?_
    obtain ⟨v, hv⟩ := Sec6Gen.exists_uniqueInvolution hΩG (hπK L hL).1
    exact edge_le_centralizer_of_alpha hd (hπK L hL) hv (hF.alpha L (hπK L hL) v hv)
  have hOC : oddCoreOf P ≤ oddCoreOf (Subgroup.centralizer ({t} : Set Y)) :=
    Asc77.T8.oddCoreOf_le_oddCoreOf_of_normalized hPC hCt
  have hON : ∀ L ∈ π, oddCoreOf P ≤ Subgroup.normalizer (L : Set Y) := by
    intro L hL
    obtain ⟨v, hv⟩ := Sec6Gen.exists_uniqueInvolution hΩG (hπK L hL).1
    have h1 := E3.oddCore_le_centralizer_of_alpha (hF.alpha L (hπK L hL) v hv) (ne_one_of_datum hd)
    exact (hOC.trans h1).trans (hR.tight L (hπK L hL).1 v hv)
  have hs2 : IsPGroup 2 (Subgroup.zpowers s) :=
    isPGroup_zpowers_of_mul_self_eq_one hsJ₁.sq hsJ₁.ne_one
  have hsyl : ∀ L ∈ π, ∃ Q : Subgroup Y, IsSylow2In Q L ∧
      Q ≤ Subgroup.centralizer ({s} : Set Y) := by
    intro L hL
    refine E3.exists_sylow_le_centralizer_of_modOdd (oddCoreOf_odd_natCard P) (hON L hL) hs2
      (hNO hsC) fun l hl => ?_
    have h1 := hcent l (le_iSup₂ (f := fun N (_ : N ∈ π) => N) L hL hl)
    rwa [commutatorElement_def] at h1
  have hCs : Subgroup.centralizer ({s} : Set Y) ≤ Subgroup.normalizer (J₁ : Set Y) :=
    hR.tight J₁ hJ₁Ω s hsJ₁
  have hJ₁π : J₁ ∉ π := by
    intro hJ₁
    obtain ⟨p, hp, hpJ⟩ := hF.lemma1710.trans J (mem_orbOf_self _ _) J₁ hJ₁
    have hps : p * u * p⁻¹ = s := by
      have h1 := hF.inv.conj p
      rw [hpJ] at h1
      exact h1.eq hsJ₁
    have hpP : p ∈ P := hp
    have hPO : ∀ {q : Y}, q ∈ P → ∀ y ∈ oddCoreOf P, q * y * q⁻¹ ∈ oddCoreOf P := fun hq _ hy =>
      mem_normalizer_oddCoreOf_of_mem_normalizer (Subgroup.le_normalizer hq) hy
    have hu : ∀ y ∈ P, ⁅u, y⁆ ∈ oddCoreOf P := by
      intro y hy
      have h1 := hcent (p * y * p⁻¹) (P.mul_mem (P.mul_mem hpP hy) (P.inv_mem hpP))
      have h2 := hPO (P.inv_mem hpP) _ h1
      convert h2 using 1
      rw [← hps]
      simp only [commutatorElement_def]
      group
    apply hex
    intro y hy
    have hxu : x * u * x⁻¹ = u := by
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hF.nbrGen_le_centralizer hx)
      calc x * u * x⁻¹ = u * x * x⁻¹ := by rw [← h1]
        _ = u := by group
    have h1 := (oddCoreOf P).mul_mem (hNO huC _ (hcent y hy)) (hu y hy)
    convert h1 using 1
    calc ⁅x * (u * t) * x⁻¹, y⁆ = ⁅(x * u * x⁻¹) * s, y⁆ := by rw [hsdef]; group
      _ = u * ⁅s, y⁆ * u⁻¹ * ⁅u, y⁆ := by
        rw [hxu]
        simp only [commutatorElement_def]
        group
  have hβ : J₁ ∈ PhilipHall.Frame.betaOf (TC.nbrAdj Ω) Ω π := by
    refine ⟨hJ₁Ω, fun L hL => ⟨hJ₁Ω, (hπK L hL).1, fun h => hJ₁π (h ▸ hL), ?_⟩⟩
    obtain ⟨Q, hQ, hQs⟩ := hsyl L hL
    exact ⟨Q, mem_RSet_of_isSylow2In (hπK L hL).1 hQ, hQ.1, hQs.trans hCs⟩
  have h1 : π ∈ maxOrbs (TC.nbrAdj Ω) J₁ :=
    (PhilipHall.Frame.mem_betaOf_iff hFam hK₀Ω hπ).mp hβ
  have h2 : conjSub x '' π ∈ maxOrbs (TC.nbrAdj Ω) J₁ := isMaxOrb_conj hFam hπ x
  have h3 : conjSub x '' π = π := maxOrb_unique hFam hJ₁Ω h2 h1
  have h4 := E3.orbGen_conj hc hK₀Ω (J := J) x
  have h5 := orbOf_conj hFam.graph (tightCore R) J x
  rw [← h4]
  show (⨆ M ∈ orbOf (TC.nbrAdj Ω) (conjSub x (tightCore R)) (conjSub x J), M) = ⨆ M ∈ π, M
  rw [h5, h3]

theorem E3FrameR.false_of_le_normalizer (hF : E3FrameR r n R S t J u)
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

theorem E3FrameR.false_of_c264One (hF : E3FrameR r n R S t J u) (hΛ : TightLambdaCommR r n)
    (hOJ : omegaNbr (CoreAssembly.conjClass (tightCore R)) J ⊆
      orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J (tightCore R))
    (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
    (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u)
    (h163 : Concl163 (secR R u) (E3.secT htu ht)) {Rd : Subgroup Y} {Sd : Sylow 2 Rd}
    {S' : Sylow 2 Y} {R' T W : Subgroup Y} (hRd : tightCore Rd = J)
    (hs : TightStd8R r n Rd Sd u (tightCore R) S' R' T W t)
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
    rcases hF.cent_or_cent_mul' htu ht h163 ht₁2 htt₁.symm ht₁J with h1 | h1
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

theorem E3FrameR.not_cent_of_c264One (hF : E3FrameR r n R S t J u) {Rd : Subgroup Y}
    (hRd : tightCore Rd = J) (hC1 : C264One (CoreAssembly.conjClass (tightCore Rd)) u t) {x : Y}
    (hx : x ∈ nbrGen (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J) :
    ¬ ∀ y ∈ E3.orbGen (CoreAssembly.conjClass (tightCore R)) (tightCore R) J,
      ⁅x * (u * t) * x⁻¹, y⁆ ∈
        oddCoreOf (E3.orbGen (CoreAssembly.conjClass (tightCore R)) (tightCore R) J) := by
  classical
  intro hb
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  set X := nbrGen (TC.nbrAdj Ω) J with hXdef
  set π := orbOf (TC.nbrAdj Ω) (tightCore R) J with hπdef
  set P := E3.orbGen Ω (tightCore R) J with hPdef
  have hd := hF.large.datum
  have hΩG := hd.hypOmegaGen
  have hR : TypeRFam r Ω := TightLargeHypR.typeRFam hF.large
  have hcl : ConjInvariant Ω := hΩG.conjInvariant
  have hJn : J ∈ omegaNbr Ω (tightCore R) := hF.maxAdj.1.2
  have hJΩ : J ∈ Ω := hJn.1
  have hK₀Ω : tightCore R ∈ Ω := CoreAssembly.mem_conjClass_self _
  have hK₀J : tightCore R ∈ omegaNbr Ω J :=
    Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩG hF.maxAdj.1.1 hJn.1 hJn
  have hJπ : J ∈ π := mem_orbOf_self _ _
  have hXC : X ≤ Subgroup.centralizer ({u} : Set Y) := hF.nbrGen_le_centralizer
  have hCuJ : Subgroup.centralizer ({u} : Set Y) ≤ Subgroup.normalizer (J : Set Y) :=
    hR.tight J hJΩ u hF.inv
  have hJC : J ≤ Subgroup.centralizer ({u} : Set Y) := hR.le_centralizer hJΩ hF.inv
  have hu2 : u * u = 1 := hF.inv.sq
  have ht2 : t * t = 1 := hd.isUniqueInvolution_core.sq
  have hut : u * t = t * u := (Subgroup.mem_centralizer_singleton_iff.mp hF.t_mem_centralizer).symm
  have hxu : x * u = u * x := Subgroup.mem_centralizer_singleton_iff.mp (hXC hx)
  have htu1 : t ≠ u := by
    intro h
    apply hJn.2.1
    have hJt : IsUniqueInvolution J t := by rw [h]; exact hF.inv
    exact hR.noTwins _ hK₀Ω J ⟨hJΩ, t, hd.isUniqueInvolution_core, hJt⟩
  have ha1 : u * t ≠ 1 := by
    intro h
    apply htu1
    calc t = u * (u * t) := by rw [← mul_assoc, hu2, one_mul]
      _ = u := by rw [h, mul_one]
  have hut2 : u * t * (u * t) = 1 := by
    calc u * t * (u * t) = u * (t * u) * t := by group
      _ = u * (u * t) * t := by rw [← hut]
      _ = u * u * (t * t) := by group
      _ = 1 := by rw [hu2, ht2, one_mul]
  obtain ⟨g, hg'⟩ := hJn.1
  have hgJ : conjSub g (tightCore R) = J := hg'
  have hfamJ : CoreAssembly.conjClass J = Ω := by rw [← hgJ, conjClass_conjSub]
  rw [hRd, hfamJ] at hC1
  have hN : Subgroup.centralizer ({u * t} : Set Y) ≤ Subgroup.normalizer
      ((Subgroup.closure ({u * t, u} : Set Y) ⊔ oddCoreOf (layerY Ω (u * t)) : Subgroup Y) :
        Set Y) := hC1
  have hαut : alphaOf (Subgroup.closure ({t, u} : Set Y)) = ⊥ := hF.alpha J hJn u hF.inv
  have hOY : oddCoreOf (layerY Ω (u * t)) ≤ Subgroup.centralizer ({u * t} : Set Y) :=
    (oddCoreOf_le_self _).trans (layerY_le_centralizer (Ω := Ω) (x := u * t))
  have hOYu : oddCoreOf (layerY Ω (u * t)) ≤ Subgroup.centralizer ({u} : Set Y) :=
    (Asc77.T8.oddCoreOf_le_oddCoreOf_of_normalized (layerY_le_centralizer (Ω := Ω) (x := u * t))
      fun c hc => layerY_conjSub_eq hcl hc).trans
      (E3.oddCore_le_centralizer_of_alpha_mem hαut
        (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp))) ha1 (Subgroup.subset_closure (by simp)))
  have hπK : ∀ M ∈ π, M ∈ omegaNbr Ω (tightCore R) := fun M hM =>
    (adj_of_mem_isMaxOrb hF.graphFam hF.maxAdj.2 hM).2
  have hPC : P ≤ Subgroup.centralizer ({t} : Set Y) := by
    refine iSup₂_le fun L hL => ?_
    obtain ⟨v, hv⟩ := Sec6Gen.exists_uniqueInvolution hΩG (hπK L hL).1
    exact edge_le_centralizer_of_alpha hd (hπK L hL) hv (hF.alpha L (hπK L hL) v hv)
  have hOPJ : oddCoreOf P ≤ Subgroup.normalizer (J : Set Y) :=
    ((Asc77.T8.oddCoreOf_le_oddCoreOf_of_normalized hPC fun c hc =>
      hF.conjSub_orbGen_core hc).trans
      (E3.oddCore_le_centralizer_of_alpha hαut (ne_one_of_datum hd))).trans hCuJ
  set b := x * (u * t) * x⁻¹ with hbdef
  have hb2 : b * b = 1 := by
    calc b * b = x * (u * t * (u * t)) * x⁻¹ := by rw [hbdef]; group
      _ = 1 := by rw [hut2]; group
  have hb1 : b ≠ 1 := by
    intro h
    apply ha1
    calc u * t = x⁻¹ * b * x := by rw [hbdef]; group
      _ = 1 := by rw [h]; group
  have hbP : ∀ y ∈ P, b * y * b⁻¹ ∈ P := fun y hy => by
    have e : b * y * b⁻¹ = ⁅b, y⁆ * y := by rw [commutatorElement_def]; group
    rw [e]
    exact P.mul_mem (oddCoreOf_le_self P (hb y hy)) hy
  have hbN : b ∈ Subgroup.normalizer (P : Set Y) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨hbP h, fun hh => ?_⟩
    have h1 := hbP _ hh
    have e : b * (b * h * b⁻¹) * b⁻¹ = h := by
      calc b * (b * h * b⁻¹) * b⁻¹ = b * b * h * (b * b)⁻¹ := by group
        _ = h := by rw [hb2]; group
    rwa [e] at h1
  have hzb : ∀ c ∈ Subgroup.zpowers b, c = 1 ∨ c = b := by
    intro c hc
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    have hbsq : b ^ (2 : ℤ) = 1 := by rw [zpow_two, hb2]
    obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
    · left
      rw [zpow_mul, hbsq, one_zpow]
    · right
      rw [zpow_add, zpow_mul, hbsq, one_zpow, one_mul, zpow_one]
  have hcov : ∀ M ∈ π, ∃ c ∈ Subgroup.centralizer ({b} : Set Y), conjSub c J = M := by
    intro M hM
    obtain ⟨y, hyP, hyM⟩ := hF.lemma1710.trans J hJπ M hM
    obtain ⟨o, ho, hfix⟩ := Balance.Bootstrap.exists_fixed_mem_coset_of_isPGroup
      (isPGroup_zpowers_of_mul_self_eq_one hb2 hb1) (oddCoreOf_odd_natCard P)
      (fun c hc o ho => mem_normalizer_oddCoreOf_of_mem_normalizer
        ((Subgroup.zpowers_le.mpr hbN) hc) ho) (x := y) (fun c hc => by
          rcases hzb c hc with rfl | rfl
          · simp
          · have h1 := mem_normalizer_oddCoreOf_of_mem_normalizer
              (Subgroup.le_normalizer (P.inv_mem hyP)) (hb y hyP)
            convert h1 using 1
            rw [commutatorElement_def]
            group)
    refine ⟨y * o, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := hfix b (Subgroup.mem_zpowers b)
      calc y * o * b = b * (y * o) * b⁻¹ * b := by rw [h1]
        _ = b * (y * o) := by group
    · rw [conjSub_mul, mem_normalizer_iff_conjSub_eq.mp (hOPJ ho), hyM]
  have hJ₁Ω : conjSub x (tightCore R) ∈ Ω := hcl x _ hK₀Ω
  have hJ₁inv : IsUniqueInvolution (conjSub x (tightCore R)) (x * t * x⁻¹) :=
    hd.isUniqueInvolution_core.conj x
  have hK₀X : tightCore R ≤ X :=
    le_iSup₂ (f := fun N (_ : N ∈ {N | TC.nbrAdj Ω J N}) => N) _ ⟨hJΩ, hK₀J⟩
  have hJ₁C : conjSub x (tightCore R) ≤ Subgroup.centralizer ({u} : Set Y) := by
    intro y hy
    rw [mem_conjSub_iff] at hy
    have h1 := X.mul_mem (X.mul_mem hx (hK₀X hy)) (X.inv_mem hx)
    exact hXC (by simpa [mul_assoc] using h1)
  have hxu' : x⁻¹ * u * x = u := by
    calc x⁻¹ * u * x = x⁻¹ * (u * x) := by group
      _ = x⁻¹ * (x * u) := by rw [hxu]
      _ = u := by group
  have hπC : ∀ M ∈ π, M ≤ Subgroup.centralizer ({u} : Set Y) := by
    intro M hM
    obtain ⟨c, hcb, hcM⟩ := hcov M hM
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp hcb
    have hc' : x⁻¹ * c * x ∈ Subgroup.centralizer ({u * t} : Set Y) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc x⁻¹ * c * x * (u * t) = x⁻¹ * (c * b) * x := by rw [hbdef]; group
        _ = x⁻¹ * (b * c) * x := by rw [h1]
        _ = u * t * (x⁻¹ * c * x) := by rw [hbdef]; group
    have h2 := Subgroup.mem_centralizer_singleton_iff.mp hc'
    set w := x⁻¹ * c * x * u * (x⁻¹ * c * x)⁻¹ with hwdef
    have hwE : w ∈ Subgroup.closure ({u * t, u} : Set Y) ⊔ oddCoreOf (layerY Ω (u * t)) :=
      (Subgroup.mem_normalizer_iff.mp (hN hc') u).mp
        (Subgroup.mem_sup_left (Subgroup.subset_closure (by simp)))
    have hw2 : w * w = 1 := by
      calc w * w = x⁻¹ * c * x * (u * u) * (x⁻¹ * c * x)⁻¹ := by rw [hwdef]; group
        _ = 1 := by rw [hu2]; group
    have hwu : u = (x⁻¹ * c * x)⁻¹ * w * (x⁻¹ * c * x) := by rw [hwdef]; group
    have hw1 : w ≠ 1 := by
      intro h
      apply hF.inv.ne_one
      rw [hwu, h]
      group
    have hwa : w ≠ u * t := by
      intro h
      apply ne_one_of_datum hd
      have h3 : u = u * t := by
        calc u = (x⁻¹ * c * x)⁻¹ * w * (x⁻¹ * c * x) := hwu
          _ = (x⁻¹ * c * x)⁻¹ * (u * t * (x⁻¹ * c * x)) := by rw [h]; group
          _ = (x⁻¹ * c * x)⁻¹ * (x⁻¹ * c * x * (u * t)) := by rw [← h2]
          _ = u * t := by group
      calc t = u⁻¹ * (u * t) := by group
        _ = 1 := by rw [← h3, inv_mul_cancel]
    have hzM : c * u * c⁻¹ = x * w * x⁻¹ := by
      calc c * u * c⁻¹ = x * (x⁻¹ * c * x) * (x⁻¹ * u * x) * (x⁻¹ * c * x)⁻¹ * x⁻¹ := by group
        _ = x * w * x⁻¹ := by rw [hxu', hwdef]; group
    have hab : u * t * u = u * (u * t) := by rw [mul_assoc, ← hut]
    have hMinv := hF.inv.conj c
    rw [hcM, hzM] at hMinv
    rcases E3.eq_of_mem_closure_pair_sup hut2 hu2 hab (oddCoreOf_odd_natCard _) hOY hOYu hwE hw2
      hw1 with h | h | h
    · exact absurd h hwa
    · have hxux : x * w * x⁻¹ = u := by
        rw [h]
        calc x * u * x⁻¹ = u * x * x⁻¹ := by rw [hxu]
          _ = u := by group
      rw [hxux] at hMinv
      rw [hR.noTwins J hJΩ M ⟨(hπK M hM).1, u, hF.inv, hMinv⟩]
      exact hJC
    · have hwt : x * w * x⁻¹ = x * t * x⁻¹ := by
        rw [h, hab, ← mul_assoc u u t, hu2, one_mul]
      rw [hwt] at hMinv
      rw [hR.noTwins _ hJ₁Ω M ⟨(hπK M hM).1, x * t * x⁻¹, hJ₁inv, hMinv⟩]
      exact hJ₁C
  have hPu : P ≤ Subgroup.centralizer ({u} : Set Y) := iSup₂_le fun M hM => hπC M hM
  have hπJ : ∀ M ∈ π, M = J := by
    intro M hM
    obtain ⟨y, hyP, hyM⟩ := hF.lemma1710.trans J hJπ M hM
    rw [← hyM]
    exact mem_normalizer_iff_conjSub_eq.mp (hCuJ (hPu hyP))
  have hPJ : P = J :=
    le_antisymm (iSup₂_le fun M hM => (hπJ M hM).le) (le_iSup₂_of_le J hJπ le_rfl)
  have hXN : X ≤ Subgroup.normalizer (P : Set Y) := by
    rw [hPJ]
    exact hXC.trans hCuJ
  exact hF.false_of_le_normalizer hXN

end Cit3

end CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes
