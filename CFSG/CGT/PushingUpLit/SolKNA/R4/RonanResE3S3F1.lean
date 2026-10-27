module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResE3S3Defs
public import CFSG.CGT.PushingUpLit.SolKNA.R4.EdgeFalseT
public import CFSG.ClassicalInvolution.Q3.TL4E3S3Cent
public import CFSG.ClassicalInvolution.Q3.TL4OddConv

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TC.Graph
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  (transitive_of_maxOrb piGen le_piGen piGen_le piGen_conj)
open scoped commutatorElement

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J : Subgroup Y} {u : Y}

theorem E3FrameR.exists_std8 {J : Subgroup Y} {u : Y} (hF : E3FrameR r n R S t J u) :
    ∃ (g : Y) (Sd : Sylow 2 ↥(conjSub g R)) (S' : Sylow 2 Y) (R' T W : Subgroup Y),
      conjSub g (tightCore R) = J ∧ g * t * g⁻¹ = u ∧
        TightStd8R r n (conjSub g R) Sd u (tightCore R) S' R' T W t := by
  have hd := hF.large.datum
  have hΩ := hd.hypOmegaGen
  have hJn := hF.maxAdj.1.2
  obtain ⟨g, hg⟩ := hJn.1
  have hgJ : conjSub g (tightCore R) = J := hg
  obtain ⟨Sd, hLd⟩ := tightLargeHypR_conj hF.large g
  have hu : g * t * g⁻¹ = u := by
    have h1 := hd.isUniqueInvolution_core.conj g
    rw [hgJ] at h1
    exact h1.eq hF.inv
  have hcore : tightCore (conjSub g R) = J := by rw [← conjSub_tightCore, hgJ]
  have hfam : CoreAssembly.conjClass (tightCore (conjSub g R)) =
      CoreAssembly.conjClass (tightCore R) := by
    rw [← conjSub_tightCore, conjClass_conjSub]
  have hK₀ : tightCore R ∈ omegaNbr (CoreAssembly.conjClass (tightCore (conjSub g R)))
      (tightCore (conjSub g R)) := by
    rw [hfam, hcore]
    exact Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hF.maxAdj.1.1 hJn.1 hJn
  rw [hu] at hLd
  obtain ⟨S', R', T, W, hs⟩ :=
    TightLargeHypR.exists_std8 hLd hK₀ hd.isUniqueInvolution_core
  exact ⟨g, Sd, S', R', T, W, hgJ, hu, hs⟩

theorem E3FrameR.nbr_le_centralizer (hF : E3FrameR r n R S t J u) {M : Subgroup Y}
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

theorem E3FrameR.nbrGen_le_centralizer (hF : E3FrameR r n R S t J u) :
    nbrGen (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J ≤
      Subgroup.centralizer ({u} : Set Y) :=
  iSup₂_le fun _ hM => hF.nbr_le_centralizer hM.2

theorem E3FrameR.core_le_centralizer (hF : E3FrameR r n R S t J u) :
    tightCore R ≤ Subgroup.centralizer ({u} : Set Y) := by
  have hd := hF.large.datum
  have hJn := hF.maxAdj.1.2
  exact hF.nbr_le_centralizer
    (Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hd.hypOmegaGen hF.maxAdj.1.1 hJn.1 hJn)

theorem E3FrameR.nbrGen_le_secH (hF : E3FrameR r n R S t J u)
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

theorem E3FrameR.tightCore_secR (hF : E3FrameR r n R S t J u) :
    tightCore (secR R u) =
      (((tightCore R).subgroupOf (Subgroup.centralizer ({u} : Set Y))).subgroupOf
        (secH R u)).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R u))) := by
  have hKC : tightCore R ≤ Subgroup.centralizer ({u} : Set Y) := hF.core_le_centralizer
  rw [E3.tightCore_map, tightCore_subgroupOf (le_subnormalClosure _)]
  exact congrArg (fun A => (A.subgroupOf (secH R u)).map
    (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R u)))) (tightCore_subgroupOf hKC)

theorem E3FrameR.t_mem_centralizer (hF : E3FrameR r n R S t J u) :
    t ∈ Subgroup.centralizer ({u} : Set Y) :=
  hF.core_le_centralizer hF.large.datum.isUniqueInvolution_core.mem

theorem E3FrameR.t_mem_secH (hF : E3FrameR r n R S t J u) :
    (⟨t, hF.t_mem_centralizer⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u := by
  refine le_subnormalClosure _ ?_
  rw [tightCore_subgroupOf hF.core_le_centralizer]
  exact Subgroup.mem_subgroupOf.mpr hF.large.datum.isUniqueInvolution_core.mem

theorem E3FrameR.le_centralizer_of_mem_omegaNbr (hF : E3FrameR r n R S t J u) {M P : Subgroup Y}
    (hM : M ∈ CoreAssembly.conjClass (tightCore R))
    (hP : P ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) M) {v : Y}
    (hv : IsUniqueInvolution M v) : P ≤ Subgroup.centralizer ({v} : Set Y) := by
  obtain ⟨m, hm'⟩ := hM
  have hm : conjSub m (tightCore R) = M := hm'
  have hd := hF.large.datum
  obtain ⟨S', hd', -⟩ := hd.conj m
  have hcore : tightCore (conjSub m R) = M := by rw [← conjSub_tightCore, hm]
  have hfam : CoreAssembly.conjClass (tightCore (conjSub m R)) =
      CoreAssembly.conjClass (tightCore R) := by
    rw [← conjSub_tightCore, conjClass_conjSub]
  have hα := hF.alpha.conj m
  have hP' : P ∈ omegaNbr (CoreAssembly.conjClass (tightCore (conjSub m R)))
      (tightCore (conjSub m R)) := by
    rw [hfam, hcore]
    exact hP
  obtain ⟨w, hw⟩ := Sec6Gen.exists_uniqueInvolution hd.hypOmegaGen hP.1
  have hvt : m * t * m⁻¹ = v := by
    have h1 := hd.isUniqueInvolution_core.conj m
    rw [hm] at h1
    exact h1.eq hv
  have h2 := edge_le_centralizer_of_alpha hd' hP' hw (hα P hP' w hw)
  rwa [hvt] at h2

theorem orbitGraph_of_sepAlphaR (hL : TightLargeHypR r n Y R S t) (hα : TightSepAlpha R t)
    (hsp : TC.SepHyp (CoreAssembly.conjClass (tightCore R))) :
    OrbitGraph (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) := by
  have hΩ := hL.datum.hypOmegaGen
  refine ⟨fun {K J} h => ⟨h.2.1, Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ h.1 h.2.1 h.2⟩,
    fun K h => h.2.2.1 rfl,
    fun {K J} g h => ⟨hΩ.conjInvariant g K h.1, Asc77.omegaNbr_conj hΩ.conjInvariant h.2 g⟩,
    fun {K J} h j hj => ?_, fun hKJ hKJ' h => hsp hKJ hKJ' h⟩
  obtain ⟨g, hgK'⟩ := h.1
  have hgK : conjSub g (tightCore R) = K := hgK'
  obtain ⟨a, haJ'⟩ := h.2.1
  have haJ : conjSub a (tightCore R) = J := haJ'
  obtain ⟨SJ, hLg⟩ := tightLargeHypR_conj hL g
  have hcore : tightCore (conjSub g R) = K := by rw [← conjSub_tightCore, hgK]
  have hfam : CoreAssembly.conjClass (tightCore (conjSub g R)) =
      CoreAssembly.conjClass (tightCore R) := by
    rw [← conjSub_tightCore, conjClass_conjSub]
  have hJ' : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore (conjSub g R)))
      (tightCore (conjSub g R)) := by
    rw [hfam, hcore]
    exact h.2
  have huJ : IsUniqueInvolution J (a * t * a⁻¹) := haJ ▸ hL.datum.isUniqueInvolution_core.conj a
  have hαJ := (hα.conj g) J hJ' (a * t * a⁻¹) huJ
  have hJN := edge_le_normalizer_of_alpha hLg.datum hJ' huJ hαJ
  rw [hcore] at hJN
  exact conjSub_eq_of_mem_normalizer (hJN hj)

theorem graphFam_of_sepAlphaR (hL : TightLargeHypR r n Y R S t) (hα : TightSepAlpha R t)
    (hc : Disconnected.DConnected (CoreAssembly.conjClass (tightCore R)))
    (hsp : TC.SepHyp (CoreAssembly.conjClass (tightCore R))) :
    GraphFam (CoreAssembly.conjClass (tightCore R))
      (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) := by
  have hΩ := hL.datum.hypOmegaGen
  have hgen : (⨆ J ∈ CoreAssembly.conjClass (tightCore R), J) = ⊤ := by
    rw [iSup_conjClass_eq]
    exact hL.cls.2.1
  refine ⟨orbitGraph_of_sepAlphaR hL hα hsp, fun h => h.1,
    fun K hK g => hΩ.conjInvariant g K hK, ?_, ?_⟩
  · intro L hL' M hM
    obtain ⟨a, rfl⟩ := hL'
    obtain ⟨b, rfl⟩ := hM
    refine ⟨b * a⁻¹, by rw [hgen]; exact Subgroup.mem_top _, ?_⟩
    rw [conjSub_mul, conjSub_inv_conjSub]
  · intro L hL' M hM
    have key : ∀ b, Relation.ReflTransGen (fun M N : Subgroup Y =>
        N ∈ CoreAssembly.conjClass (tightCore R) ∧
          Disconnected.dAdj (CoreAssembly.conjClass (tightCore R)) M N) L b →
        b ∈ CoreAssembly.conjClass (tightCore R) ∧
          Relation.ReflTransGen (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) L b := by
      intro b hb
      induction hb with
      | refl => exact ⟨hL', Relation.ReflTransGen.refl⟩
      | tail _ hbc ih =>
        rename_i b c
        obtain ⟨hbΩ, hpath⟩ := ih
        obtain ⟨hcΩ, hadj⟩ := hbc
        refine ⟨hcΩ, hpath.tail ⟨hbΩ, ?_⟩⟩
        rcases hadj with h | h
        · exact h
        · exact Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hcΩ hbΩ h
    exact (key M (hc L hL' M hM)).2

theorem E3FrameR.graphFam (hF : E3FrameR r n R S t J u) :
    GraphFam (CoreAssembly.conjClass (tightCore R))
      (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) :=
  graphFam_of_sepAlphaR hF.large hF.alpha hF.conn hF.sep

theorem E3FrameR.lemma1710 (hF : E3FrameR r n R S t J u) :
    PhilipHall.Frame.Lemma1710 (TC.nbrAdj (CoreAssembly.conjClass (tightCore R)))
      (CoreAssembly.conjClass (tightCore R)) (tightCore R)
      (orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) (tightCore R) J) :=
  PhilipHall.Frame.graph_17_10 hF.graphFam (CoreAssembly.mem_conjClass_self _) hF.maxAdj.2

theorem E3FrameR.conjSub_J_of_mem_centralizer (hF : E3FrameR r n R S t J u) {c : Y}
    (hc : c ∈ Subgroup.centralizer ({u} : Set Y)) : conjSub c J = J := by
  obtain ⟨gs, Sd, S', R', T, W, hgJ, -, hs⟩ := hF.exists_std8
  have hcore : tightCore (conjSub gs R) = J := by rw [← conjSub_tightCore, hgJ]
  have h1 := hs.large.datum.le_normalizer_core hc
  rw [hcore] at h1
  exact mem_normalizer_iff_conjSub_eq.mp h1

theorem E3FrameR.orbOf_J_mem_maxOrbs (hF : E3FrameR r n R S t J u) :
    orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J (tightCore R) ∈
      maxOrbs (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J :=
  orbOf_mem_maxOrbs hF.graphFam hF.maxAdj.1 hF.maxAdj.2

theorem E3FrameR.conjSub_image_orbOf_J (hF : E3FrameR r n R S t J u) {c : Y}
    (hc : c ∈ Subgroup.centralizer ({u} : Set Y)) :
    conjSub c '' orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J (tightCore R) =
      orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J (tightCore R) := by
  have hFam := hF.graphFam
  have h1 := isMaxOrb_conj hFam hF.orbOf_J_mem_maxOrbs c
  rw [hF.conjSub_J_of_mem_centralizer hc] at h1
  exact maxOrb_unique hFam hF.maxAdj.1.2.1 h1 hF.orbOf_J_mem_maxOrbs

theorem E3FrameR.conjSub_orbGen_J (hF : E3FrameR r n R S t J u) {c : Y}
    (hc : c ∈ Subgroup.centralizer ({u} : Set Y)) :
    conjSub c (E3.orbGen (CoreAssembly.conjClass (tightCore R)) J (tightCore R)) =
      E3.orbGen (CoreAssembly.conjClass (tightCore R)) J (tightCore R) := by
  have hcJ := hF.conjSub_J_of_mem_centralizer hc
  have hcl := hF.large.datum.hypOmegaGen.conjInvariant
  rw [← E3.orbGen_conj hcl hF.maxAdj.1.2.1 c, hcJ]
  have h1 := orbOf_conj hF.graphFam.graph J (tightCore R) c
  rw [hcJ, hF.conjSub_image_orbOf_J hc] at h1
  show (⨆ M ∈ orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J
    (conjSub c (tightCore R)), M) = ⨆ M ∈ orbOf (TC.nbrAdj (CoreAssembly.conjClass
      (tightCore R))) J (tightCore R), M
  rw [h1]

theorem E3FrameR.orbGen_J_le_centralizer (hF : E3FrameR r n R S t J u) :
    E3.orbGen (CoreAssembly.conjClass (tightCore R)) J (tightCore R) ≤
      Subgroup.centralizer ({u} : Set Y) := by
  refine iSup₂_le fun M hM => ?_
  obtain ⟨l, hl, rfl⟩ := hM
  calc conjSub l (tightCore R) ≤ conjSub l (Subgroup.centralizer ({u} : Set Y)) :=
        conjSub_mono hF.core_le_centralizer
    _ = Subgroup.centralizer ({u} : Set Y) := conjSub_eq_self_of_mem (hF.nbrGen_le_centralizer hl)

theorem E3FrameR.exists_conj_of_mem_orbOf_J (hF : E3FrameR r n R S t J u) {M : Subgroup Y}
    (hM : M ∈ orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J (tightCore R)) :
    ∃ a ∈ E3.orbGen (CoreAssembly.conjClass (tightCore R)) J (tightCore R),
      conjSub a (tightCore R) = M :=
  transitive_of_maxOrb hF.graphFam hF.orbOf_J_mem_maxOrbs _ (mem_orbOf_self _ _) M hM

theorem E3FrameR.secH_eq_orbGen (hF : E3FrameR r n R S t J u) :
    secH R u = (E3.orbGen (CoreAssembly.conjClass (tightCore R)) J (tightCore R)).subgroupOf
      (Subgroup.centralizer ({u} : Set Y)) := by
  set C := Subgroup.centralizer ({u} : Set Y) with hC
  set X := E3.orbGen (CoreAssembly.conjClass (tightCore R)) J (tightCore R) with hX
  have hXC : X ≤ C := hF.orbGen_J_le_centralizer
  have hKC : tightCore R ≤ C := hF.core_le_centralizer
  have hKX : tightCore R ≤ X :=
    le_iSup₂ (f := fun M (_ : M ∈ orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J
      (tightCore R)) => M) _ (mem_orbOf_self _ _)
  have hXn : (X.subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXC).mpr fun c hc =>
      mem_normalizer_of_conjSub_eq (hF.conjSub_orbGen_J hc)
  apply le_antisymm
  · refine subnormalClosure_le ?_ ?_
    · rw [tightCore_subgroupOf hKC]
      exact Subgroup.subgroupOf_mono C hKX
    · exact isSubnormal_of_normal_subgroupOf le_top inferInstance
  · have claim : ∀ H M : Subgroup C, IsSubnormal H M → M = ⊤ →
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
        obtain ⟨l, hl, rfl⟩ := hF.exists_conj_of_mem_orbOf_J hL
        obtain ⟨m, hmM, rfl⟩ := hXM hl
        rintro _ ⟨k, hk, rfl⟩
        have hkC : k ∈ C := hKC hk
        have hkH : (⟨k, hkC⟩ : C) ∈ H := hKH (Subgroup.mem_subgroupOf.mpr hk)
        have hkM : (⟨k, hkC⟩ : C) ∈ M := hHM hkH
        have h1 := hN.conj_mem ⟨⟨k, hkC⟩, hkM⟩ (Subgroup.mem_subgroupOf.mpr hkH) ⟨m, hmM⟩
        rw [Subgroup.mem_subgroupOf] at h1
        exact ⟨_, h1, rfl⟩
    intro x hx
    show x ∈ subnormalClosure (tightCore (R.subgroupOf C))
    rw [tightCore_subgroupOf hKC]
    refine (le_sInf fun H hH => ?_ : (X.subgroupOf C) ≤ _) hx
    intro y hy
    obtain ⟨h, hh, hhy⟩ := claim H ⊤ hH.2 rfl hH.1 (Subgroup.mem_subgroupOf.mp hy)
    have : h = y := Subtype.ext hhy
    rwa [← this]

theorem E3FrameR.exists_swap' (hF : E3FrameR r n R S t J u) :
    ∃ g' : Y, conjSub g' (tightCore R) = J ∧ conjSub g' J = tightCore R ∧
      g' * t * g'⁻¹ = u ∧ g' * u * g'⁻¹ = t := by
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hd := hF.large.datum
  have hFam := hF.graphFam
  have hJn : J ∈ omegaNbr Ω (tightCore R) := hF.maxAdj.1.2
  obtain ⟨g₀, hg₀'⟩ := hJn.1
  have hg₀ : conjSub g₀ (tightCore R) = J := hg₀'
  have hπ : conjSub g₀ '' orbOf (TC.nbrAdj Ω) (tightCore R) J =
      orbOf (TC.nbrAdj Ω) J (tightCore R) := by
    have h1 := isMaxOrb_conj hFam hF.maxAdj.2 g₀
    rw [hg₀] at h1
    exact maxOrb_unique hFam hJn.1 h1 hF.orbOf_J_mem_maxOrbs
  have hJ₁ : conjSub g₀ J ∈ orbOf (TC.nbrAdj Ω) J (tightCore R) := by
    rw [← hπ]
    exact ⟨J, mem_orbOf_self _ _, rfl⟩
  obtain ⟨l₁, hl₁, hl₁J⟩ := hJ₁
  have hl₁C := (Subgroup.centralizer ({u} : Set Y)).inv_mem (hF.nbrGen_le_centralizer hl₁)
  refine ⟨l₁⁻¹ * g₀, ?_, ?_, ?_, ?_⟩
  · rw [conjSub_mul, hg₀, hF.conjSub_J_of_mem_centralizer hl₁C]
  · rw [conjSub_mul, ← hl₁J, conjSub_inv_conjSub]
  · have h1 := hd.isUniqueInvolution_core.conj (l₁⁻¹ * g₀)
    rw [conjSub_mul, hg₀, hF.conjSub_J_of_mem_centralizer hl₁C] at h1
    exact h1.eq hF.inv
  · have h1 := hF.inv.conj (l₁⁻¹ * g₀)
    rw [conjSub_mul, ← hl₁J, conjSub_inv_conjSub] at h1
    exact h1.eq hd.isUniqueInvolution_core

theorem E3FrameR.conjSub_image_orbOf (hF : E3FrameR r n R S t J u) {c : Y}
    (hc : c ∈ Subgroup.centralizer ({t} : Set Y)) :
    conjSub c '' orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) (tightCore R) J =
      orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) (tightCore R) J := by
  have hFam := hF.graphFam
  have hcK : conjSub c (tightCore R) = tightCore R :=
    mem_normalizer_iff_conjSub_eq.mp (hF.large.datum.le_normalizer_core hc)
  have h1 := isMaxOrb_conj hFam hF.maxAdj.2 c
  rw [hcK] at h1
  exact maxOrb_unique hFam (CoreAssembly.mem_conjClass_self _) h1 hF.maxAdj.2

theorem E3FrameR.conjSub_orbGen_core (hF : E3FrameR r n R S t J u) {c : Y}
    (hc : c ∈ Subgroup.centralizer ({t} : Set Y)) :
    conjSub c (E3.orbGen (CoreAssembly.conjClass (tightCore R)) (tightCore R) J) =
      E3.orbGen (CoreAssembly.conjClass (tightCore R)) (tightCore R) J := by
  have hcK : conjSub c (tightCore R) = tightCore R :=
    mem_normalizer_iff_conjSub_eq.mp (hF.large.datum.le_normalizer_core hc)
  have hcl := hF.large.datum.hypOmegaGen.conjInvariant
  rw [← E3.orbGen_conj hcl (CoreAssembly.mem_conjClass_self _) c, hcK]
  have h1 := orbOf_conj hF.graphFam.graph (tightCore R) J c
  rw [hcK, hF.conjSub_image_orbOf hc] at h1
  show (⨆ M ∈ orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) (tightCore R)
    (conjSub c J), M) = ⨆ M ∈ orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R)))
      (tightCore R) J, M
  rw [h1]

theorem E3FrameR.secH_le_nbrGen (hF : E3FrameR r n R S t J u) :
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

theorem E3.exists_secClsR {r : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R}
    {t : Y} (hd : TightDatum R S t)
    (hq : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2)))) {J : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) {u : Y}
    (hu : IsUniqueInvolution J u) (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
    (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u) :
    ∃ Sq : Sylow 2 ↥(secR R u), TightDatum (secR R u) Sq (E3.secT htu ht) ∧
      TightClsR r (SecQ R u) (secR R u) Sq (E3.secT htu ht) := by
  obtain ⟨-, hu2, hut, -, huK, -⟩ := hd.edge_involution hJ hu
  have hcomm : ∀ r ∈ R, ⁅u, r⁆ ∈ oddCoreImg R := (hd.act_eq_one_iff hut).mp huK
  have huN : u ∈ Subgroup.normalizer (R : Set Y) := hd.le_normalizer hut
  have huC : u ∈ centralizerModOdd ⊤ R :=
    ⟨Subgroup.mem_top u, huN, mem_normalizer_oddCore_of_mem_normalizer huN, hcomm⟩
  obtain ⟨S', hS'⟩ := hd.exists_sylow_le_centralizer
    (Balance.isPGroup_zpowers_of_mul_self_eq_one hu2) (Subgroup.zpowers_le.mpr huC)
  have hS'u : (S' : Subgroup R).map R.subtype ≤ Subgroup.centralizer ({u} : Set Y) :=
    hS'.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers u)))
  obtain ⟨S₁, hd₁, ⟨e₁⟩⟩ := (hd.ofSylow S').restrict hS'u
  have hq' : Nonempty (↥(S₁ : Subgroup (R.subgroupOf (Subgroup.centralizer ({u} : Set Y)))) ≃*
      QuaternionGroup (2 ^ (r - 2))) := ⟨e₁.trans ((Sylow.equiv S' S).trans hq.some)⟩
  obtain ⟨_ht, S₂, hd₂, -, hcls⟩ := exists_clsR_subnormalClosure hd₁ hq'
  exact ⟨_, OddQ.datum hd₂ (CFSG.ComponentClassification.OddCore.odd_card _), hcls⟩

theorem E3FrameR.exists_secClsR (hF : E3FrameR r n R S t J u)
    (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
    (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u) :
    ∃ Sq : Sylow 2 ↥(secR R u), TightDatum (secR R u) Sq (E3.secT htu ht) ∧
      TightClsR r (SecQ R u) (secR R u) Sq (E3.secT htu ht) :=
  E3.exists_secClsR hF.large.datum hF.large.cls.1 hF.maxAdj.1.2 hF.inv htu ht

end Cit3

end CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes
