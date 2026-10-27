module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResE3S3F2
public import CFSG.ClassicalInvolution.Q3.TL4E3C269GA
public import CFSG.ClassicalInvolution.Q3.TL4E3S3NC

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

theorem E3FrameR.oddCoreOf_orbGen_le_centralizer (hF : E3FrameR r n R S t J u) {L : Subgroup Y}
    (hLπ : L ∈ orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J (tightCore R)) :
    oddCoreOf (E3.orbGen (CoreAssembly.conjClass (tightCore R)) L J) ≤
      Subgroup.centralizer ({u} : Set Y) := by
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hd := hF.large.datum
  have hc : ConjInvariant Ω := hd.hypOmegaGen.conjInvariant
  have hK₀Ω : tightCore R ∈ Ω := CoreAssembly.mem_conjClass_self _
  have hJn : J ∈ omegaNbr Ω (tightCore R) := hF.maxAdj.1.2
  obtain ⟨gs, Sd, S', R', T, W, hgJ, hu, hs⟩ := hF.exists_std8
  have hcore : tightCore (conjSub gs R) = J := by rw [← conjSub_tightCore, hgJ]
  obtain ⟨x, hx, hxL⟩ := hLπ
  have hxC : x ∈ Subgroup.centralizer ({u} : Set Y) := hF.nbrGen_le_centralizer hx
  have hxJ : conjSub x J = J := by
    have h1 := hs.large.datum.le_normalizer_core hxC
    rw [hcore] at h1
    exact mem_normalizer_iff_conjSub_eq.mp h1
  have hX : E3.orbGen Ω L J = conjSub x (E3.orbGen Ω (tightCore R) J) := by
    rw [← hxL, ← E3.orbGen_conj hc hK₀Ω x, hxJ]
  have h1 : oddCoreOf (E3.orbGen Ω (tightCore R) J) ≤ Subgroup.centralizer ({u} : Set Y) :=
    hF.oddCoreOf_orbGen_core_le.trans (E3.oddCore_le_centralizer_of_alpha
      (hF.alpha J hJn u hF.inv) hd.isUniqueInvolution_core.ne_one)
  rw [hX]
  calc oddCoreOf (conjSub x (E3.orbGen Ω (tightCore R) J))
      = conjSub x (oddCoreOf (E3.orbGen Ω (tightCore R) J)) :=
        Vtx.oddCoreOf_map_of_inj (MulAut.conj x).toMonoidHom (MulAut.conj x).injective _
    _ ≤ conjSub x (Subgroup.centralizer ({u} : Set Y)) := conjSub_mono h1
    _ = Subgroup.centralizer ({u} : Set Y) := conjSub_eq_self_of_mem hxC

theorem E3FrameR.exists_conj_edge' (hF : E3FrameR r n R S t J u) {L : Subgroup Y}
    (hLπ : L ∈ orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J (tightCore R)) :
    ∃ g : Y, conjSub g J = L ∧ conjSub g (tightCore R) = J ∧ g * t * g⁻¹ = u := by
  obtain ⟨g', hg'K, hg'J, hgt, -⟩ := hF.exists_swap'
  obtain ⟨x, hx, hxL⟩ := hLπ
  have hxC := hF.nbrGen_le_centralizer hx
  refine ⟨x * g', ?_, ?_, ?_⟩
  · rw [conjSub_mul, hg'J, hxL]
  · rw [conjSub_mul, hg'K, hF.conjSub_J_of_mem_centralizer hxC]
  · calc x * g' * t * (x * g')⁻¹ = x * (g' * t * g'⁻¹) * x⁻¹ := by group
      _ = x * u * x⁻¹ := by rw [hgt]
      _ = u := by rw [Subgroup.mem_centralizer_singleton_iff.mp hxC]; group

theorem E3FrameR.orbOf_mem_maxOrbs_of_mem (hF : E3FrameR r n R S t J u) {L : Subgroup Y}
    (hLπ : L ∈ orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J (tightCore R)) :
    orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) L J ∈
      maxOrbs (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) L := by
  obtain ⟨g, hgJ, hgK, -⟩ := hF.exists_conj_edge' hLπ
  have h1 := isMaxOrb_conj hF.graphFam hF.orbOf_J_mem_maxOrbs g
  rw [← orbOf_conj hF.graphFam.graph J (tightCore R) g, hgJ, hgK] at h1
  exact h1

theorem E3FrameR.exists_conj_of_mem_orbOf_L (hF : E3FrameR r n R S t J u) {L : Subgroup Y}
    (hLπ : L ∈ orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J (tightCore R))
    {M : Subgroup Y} (hM : M ∈ orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) L J) :
    ∃ l ∈ E3.orbGen (CoreAssembly.conjClass (tightCore R)) L J, conjSub l J = M :=
  transitive_of_maxOrb hF.graphFam (hF.orbOf_mem_maxOrbs_of_mem hLπ) J (mem_orbOf_self L J) M hM

theorem E3FrameR.omegaNbr_subset_orbOf_L (hF : E3FrameR r n R S t J u)
    (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
    (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u)
    (h163 : Concl163 (secR R u) (E3.secT htu ht)) {L : Subgroup Y}
    (hLπ : L ∈ orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J (tightCore R)) :
    omegaNbr (CoreAssembly.conjClass (tightCore R)) L ⊆
      orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) L J := by
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hc : ConjInvariant Ω := hF.large.datum.hypOmegaGen.conjInvariant
  have hJΩ : J ∈ Ω := hF.maxAdj.1.2.1
  obtain ⟨g, hgJ, hgK, -⟩ := hF.exists_conj_edge' hLπ
  have hO := hF.omegaNbr_subset_orbOf htu ht h163
  have e := E3.orbOf_conj hc hJΩ (tightCore R) g
  rw [hgJ, hgK] at e
  intro M hM
  have hM' : conjSub g⁻¹ M ∈ omegaNbr Ω J := by
    have h1 := omegaNbr_conj hc hM g⁻¹
    rwa [← hgJ, conjSub_inv_conjSub] at h1
  rw [e]
  exact ⟨_, hO hM', conjSub_conjSub_inv g M⟩

theorem E3FrameR.omegaNbr_eq_of_cent (hF : E3FrameR r n R S t J u)
    (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
    (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u)
    (h163 : Concl163 (secR R u) (E3.secT htu ht)) {L : Subgroup Y}
    (hLπ : L ∈ orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J (tightCore R))
    (hLn : L ∉ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hct : ∀ y ∈ E3.orbGen (CoreAssembly.conjClass (tightCore R)) L J,
      ⁅t, y⁆ ∈ oddCoreOf (E3.orbGen (CoreAssembly.conjClass (tightCore R)) L J)) :
    omegaNbr (CoreAssembly.conjClass (tightCore R)) L =
      omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R) := by
  classical
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hd := hF.large.datum
  have hΩG := hd.hypOmegaGen
  have hc : ConjInvariant Ω := hΩG.conjInvariant
  have h := TightLargeHypR.typeRFam hF.large
  have hJΩ : J ∈ Ω := hF.maxAdj.1.2.1
  have hK₀Ω : tightCore R ∈ Ω := CoreAssembly.mem_conjClass_self _
  have hLΩ : L ∈ Ω := by
    obtain ⟨x, -, hxL⟩ := hLπ
    rw [← hxL]
    exact hc x _ hK₀Ω
  have ht2 : t * t = 1 := hd.isUniqueInvolution_core.sq
  have hsub : omegaNbr Ω L ⊆ omegaNbr Ω (tightCore R) := by
    intro M hM
    have hMπ := hF.omegaNbr_subset_orbOf_L htu ht h163 hLπ hM
    obtain ⟨l, hl, hlM⟩ := hF.exists_conj_of_mem_orbOf_L hLπ hMπ
    have hMX : conjSub l J ≤ E3.orbGen Ω L J := by
      rw [hlM]
      exact le_iSup₂ (f := fun N (_ : N ∈ orbOf (TC.nbrAdj Ω) L J) => N) M hMπ
    obtain ⟨P, hP, hPt⟩ := E3.exists_sylow_le_centralizer_of_conj h ht2 hJΩ hF.inv hct
      (hF.oddCoreOf_orbGen_le_centralizer hLπ) hl hMX
    rw [hlM] at hP
    refine ⟨hM.1, ?_, P, mem_RSet_of_isSylow2In hM.1 hP, hP.1,
      hPt.trans (h.tight _ hK₀Ω t hd.isUniqueInvolution_core)⟩
    rintro rfl
    exact hLn (Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩG hLΩ hK₀Ω hM)
  obtain ⟨x, -, hxL⟩ := hLπ
  have himg : omegaNbr Ω L = conjSub x '' omegaNbr Ω (tightCore R) := by
    ext M
    constructor
    · intro hM
      refine ⟨conjSub x⁻¹ M, ?_, conjSub_conjSub_inv x M⟩
      have h1 := omegaNbr_conj hc hM x⁻¹
      rwa [← hxL, conjSub_inv_conjSub] at h1
    · rintro ⟨M, hM, rfl⟩
      have h1 := omegaNbr_conj hc hM x
      rwa [hxL] at h1
  have hcard : (omegaNbr Ω L).ncard = (omegaNbr Ω (tightCore R)).ncard := by
    rw [himg]
    exact Set.ncard_image_of_injective _ (conjSub_injective x)
  have : Finite (Subgroup Y) :=
    Finite.of_injective (fun H : Subgroup Y => (H : Set Y)) SetLike.coe_injective
  exact Set.eq_of_subset_of_ncard_le hsub hcard.symm.le (Set.toFinite _)

theorem E3FrameR.oddCoreOf_orbGen_J_le_centralizer (hF : E3FrameR r n R S t J u) :
    oddCoreOf (E3.orbGen (CoreAssembly.conjClass (tightCore R)) J (tightCore R)) ≤
      Subgroup.centralizer ({t} : Set Y) := by
  have hle := hF.orbGen_J_le_centralizer
  have hn : ((E3.orbGen (CoreAssembly.conjClass (tightCore R)) J (tightCore R)).subgroupOf
      (Subgroup.centralizer ({u} : Set Y))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr fun c hc =>
      Generic.mem_normalizer_of_conjSub_eq (hF.conjSub_orbGen_J hc)
  have h1 : oddCoreOf (E3.orbGen (CoreAssembly.conjClass (tightCore R)) J (tightCore R)) ≤
      oddCoreOf (Subgroup.centralizer ({u} : Set Y)) :=
    Balance.oddCoreIn_le_of_isSubnormal (isSubnormal_of_normal_subgroupOf hle hn)
  have hα := hF.alpha J hF.maxAdj.1.2 u hF.inv
  rw [Set.pair_comm] at hα
  exact h1.trans (E3.oddCore_le_centralizer_of_alpha hα hF.inv.ne_one)

theorem E3FrameR.nbrGen_eq_orbGen_J (hF : E3FrameR r n R S t J u)
    (hO : omegaNbr (CoreAssembly.conjClass (tightCore R)) J ⊆
      orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J (tightCore R)) :
    nbrGen (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J =
      E3.orbGen (CoreAssembly.conjClass (tightCore R)) J (tightCore R) := by
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hΩG := hF.large.datum.hypOmegaGen
  have hJn : J ∈ omegaNbr Ω (tightCore R) := hF.maxAdj.1.2
  have hK₀J : tightCore R ∈ omegaNbr Ω J :=
    Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩG hF.maxAdj.1.1 hJn.1 hJn
  apply le_antisymm
  · refine iSup₂_le fun M hM => ?_
    exact le_iSup₂ (f := fun N (_ : N ∈ orbOf (TC.nbrAdj Ω) J (tightCore R)) => N) M (hO hM.2)
  · refine iSup₂_le fun M hM => ?_
    obtain ⟨l, hl, rfl⟩ := hM
    have hK : tightCore R ≤ nbrGen (TC.nbrAdj Ω) J :=
      le_iSup₂ (f := fun N (_ : N ∈ {N : Subgroup Y | TC.nbrAdj Ω J N}) => N) (tightCore R)
        ⟨hJn.1, hK₀J⟩
    calc conjSub l (tightCore R) ≤ conjSub l (nbrGen (TC.nbrAdj Ω) J) := conjSub_mono hK
      _ = nbrGen (TC.nbrAdj Ω) J := conjSub_eq_self_of_mem hl

theorem E3FrameR.secH_equiv (hF : E3FrameR r n R S t J u)
    (hO : omegaNbr (CoreAssembly.conjClass (tightCore R)) J ⊆
      orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J (tightCore R)) :
    ∃ e : ↥(secH R u) ≃* ↥(nbrGen (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J),
      ∀ h, ((e h : ↥(nbrGen (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J)) : Y) =
        ((h : ↥(Subgroup.centralizer ({u} : Set Y))) : Y) :=
  ⟨(MulEquiv.subgroupCongr (le_antisymm hF.secH_le_nbrGen (hF.nbrGen_le_secH hO))).trans
    (Subgroup.subgroupOfEquivOfLe hF.nbrGen_le_centralizer), fun _ => rfl⟩

theorem E3FrameR.le_sup_of_secGen (hF : E3FrameR r n R S t J u)
    (hO : omegaNbr (CoreAssembly.conjClass (tightCore R)) J ⊆
      orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J (tightCore R))
    (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
    (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u)
    (hgen : ∀ s : SecQ R u, E3.secT htu ht * s = s * E3.secT htu ht → s ≠ E3.secT htu ht →
      (∃ g : SecQ R u, s = g * E3.secT htu ht * g⁻¹) →
        Subgroup.centralizer ({E3.secT htu ht} : Set (SecQ R u)) ⊔
          Subgroup.centralizer ({s} : Set (SecQ R u)) = ⊤)
    {x : Y} (hx : x ∈ nbrGen (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J)
    (hxt : x * t * x⁻¹ ≠ t) (hcomm : x * t * x⁻¹ * t = t * (x * t * x⁻¹)) :
    nbrGen (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J ≤
      nbrGen (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J ⊓
          Subgroup.centralizer ({t} : Set Y) ⊔ Subgroup.zpowers x ⊔
        oddCoreOf (nbrGen (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J) := by
  obtain ⟨e, he⟩ := hF.secH_equiv hO
  have hxC : x ∈ Subgroup.centralizer ({u} : Set Y) := hF.nbrGen_le_centralizer hx
  have hxH : (⟨x, hxC⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u :=
    hF.nbrGen_le_secH hO (Subgroup.mem_subgroupOf.mpr hx)
  have hinj : Function.Injective fun w : ↥(secH R u) =>
      ((w : ↥(Subgroup.centralizer ({u} : Set Y))) : Y) :=
    Subtype.val_injective.comp Subtype.val_injective
  have htt : t * t = 1 := by rw [← pow_two, ← hF.large.datum.order, pow_orderOf_eq_one]
  have key := E3C269G.le_sup_oddCoreOf_of_gen e (t := ⟨⟨t, htu⟩, ht⟩) (x := ⟨⟨x, hxC⟩, hxH⟩)
    (hinj htt) (hinj hcomm) (fun h => hxt (congrArg (fun w : ↥(secH R u) =>
      ((w : ↥(Subgroup.centralizer ({u} : Set Y))) : Y)) h)) hgen
  rwa [he, he] at key

end Cit3

end CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes
