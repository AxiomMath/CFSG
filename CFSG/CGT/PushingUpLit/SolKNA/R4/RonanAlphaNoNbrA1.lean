module

public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2L2S
public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanAlphaNoNbrFrames
public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanAlphaNoNbrHyp51
public import CFSG.ClassicalInvolution.Q3.TL4S289U1

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T8 CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.Blueprint
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open scoped commutatorElement

section Cit3

variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem hyp51At_wcoset_r (hr : 4 ≤ r) (hNo : NoQ16E4) (h4 : Thm4RBelow r n)
    (hL : TightLargeHypR r n Y R S t) {J : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) {u : Y}
    (hu : IsUniqueInvolution J u) {w : Y} (hwt : w * t = t * w) (hwu : w * u = u * w)
    (hBe : IsElemAbelian 2 (Subgroup.closure ({t, u, w} : Set Y)))
    (hcent : ∀ x : Y, x * t = t * x → x * u = u * x → x * w = w * x →
      ∀ c ∈ Subgroup.closure ({t, u, w} : Set Y), x * c = c * x)
    (hEB : Subgroup.closure ({t, u} : Set Y) ≤ Subgroup.closure ({t, u, w} : Set Y)) {e' : Y}
    (he' : e' ∈ Subgroup.closure ({t, u} : Set Y))
    (hwB : w ∈ Subgroup.closure ({t, u, w} : Set Y)) (hc1 : e' * w ≠ 1)
    (hwE : w ∉ Subgroup.closure ({t, u} : Set Y)) {R₀ : Subgroup Y}
    (hR₀ : IsSylow2In R₀ (tightCore R)) (hR₀u : R₀ ≤ Subgroup.centralizer ({u} : Set Y))
    (hR₀w : R₀ ≤ Subgroup.centralizer ({w} : Set Y)) {T₀ : Subgroup Y} (hT₀ : IsSylow2In T₀ J)
    (hT₀N : T₀ ≤ Subgroup.normalizer ((tightCore R : Subgroup Y) : Set Y))
    (hT₀w : T₀ ≤ Subgroup.centralizer ({w} : Set Y)) :
    Hyp51At (Subgroup.closure ({t, u, w} : Set Y)) (e' * w) := by
  have h := TightLargeHypR.typeRFam hL
  have hΩ := h.hyp
  have ht := hL.datum.isUniqueInvolution_core
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) :=
    CoreAssembly.mem_conjClass_self _
  have ctu : t * u = u * t := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ ht hJ hu
  have htu : t ≠ u := fun h' => hJ.2.1 (eq_core_of_isUniqueInvolution hL hJ.1 (h' ▸ hu))
  have htE : t ∈ Subgroup.closure ({t, u} : Set Y) := Subgroup.subset_closure (by simp)
  have huE : u ∈ Subgroup.closure ({t, u} : Set Y) := Subgroup.subset_closure (by simp)
  have hne : ∀ x ∈ Subgroup.closure ({t, u} : Set Y), x ≠ e' * w := by
    intro x hx hxc
    apply hwE
    have h1 : e'⁻¹ * x ∈ Subgroup.closure ({t, u} : Set Y) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ he') hx
    rwa [hxc, inv_mul_cancel_left] at h1
  have hcB' : e' * w ∈ Subgroup.closure ({t, u, w} : Set Y) := Subgroup.mul_mem _ (hEB he') hwB
  have hgen : Subgroup.closure ({t, u, w} : Set Y) =
      Subgroup.closure ({t, u, e' * w} : Set Y) := by
    have htC : t ∈ Subgroup.closure ({t, u, e' * w} : Set Y) := Subgroup.subset_closure (by simp)
    have huC : u ∈ Subgroup.closure ({t, u, e' * w} : Set Y) := Subgroup.subset_closure (by simp)
    have hcC : e' * w ∈ Subgroup.closure ({t, u, e' * w} : Set Y) :=
      Subgroup.subset_closure (by simp)
    have hE' : Subgroup.closure ({t, u} : Set Y) ≤ Subgroup.closure ({t, u, e' * w} : Set Y) := by
      rw [Subgroup.closure_le]
      intro v hv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with hv | hv <;> rw [hv]
      · exact htC
      · exact huC
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro v hv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with hv | hv | hv <;> rw [hv]
      · exact htC
      · exact huC
      · have h1 : e'⁻¹ * (e' * w) ∈ Subgroup.closure ({t, u, e' * w} : Set Y) :=
          Subgroup.mul_mem _ (Subgroup.inv_mem _ (hE' he')) hcC
        rwa [inv_mul_cancel_left] at h1
    · rw [Subgroup.closure_le]
      intro v hv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with hv | hv | hv <;> rw [hv]
      · exact hEB htE
      · exact hEB huE
      · exact hcB'
  have hct : e' * w * t = t * (e' * w) := (hcent t rfl ctu hwt.symm _ hcB').symm
  have hcu : e' * w * u = u * (e' * w) := (hcent u ctu.symm rfl hwu.symm _ hcB').symm
  have hMa : XMem (CoreAssembly.conjClass (tightCore R)) (e' * w) (tightCore R) := by
    refine ⟨hK, h.tight _ hK t ht (Subgroup.mem_centralizer_singleton_iff.mpr hct), R₀, hR₀,
      fun x hx => hcent x ?_ (Subgroup.mem_centralizer_singleton_iff.mp (hR₀u hx))
        (Subgroup.mem_centralizer_singleton_iff.mp (hR₀w hx)) _ hcB'⟩
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (S1916.normalizer_le_centralizer_of_isUniqueInvolution ht
        (Subgroup.le_normalizer (hR₀.1 hx)))
  have hTc : ∀ x ∈ T₀, x * (e' * w) = e' * w * x := fun x hx => hcent x
    (Subgroup.mem_centralizer_singleton_iff.mp
      (S1916.normalizer_le_centralizer_of_isUniqueInvolution ht (hT₀N hx)))
    (Subgroup.mem_centralizer_singleton_iff.mp
      (S1916.normalizer_le_centralizer_of_isUniqueInvolution hu
        (Subgroup.le_normalizer (hT₀.1 hx))))
    (Subgroup.mem_centralizer_singleton_iff.mp (hT₀w hx)) _ hcB'
  have hMb : XMem (CoreAssembly.conjClass (tightCore R)) (e' * w) J :=
    ⟨hJ.1, h.tight _ hJ.1 u hu (Subgroup.mem_centralizer_singleton_iff.mpr hcu), T₀, hT₀, hTc⟩
  exact hyp51At_of_vtxPair_four_le hr hNo h4 hL.tbelow hL.center hL.card.le h hBe hgen hc1
    ht.ne_one (hne t htE) hu.ne_one (hne u huE) htu (hne (t * u) (Subgroup.mul_mem _ htE huE))
    hMa hMb ht hu hT₀ (fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (hTc x hx)) hT₀N

theorem hyp51_z2Frame_r (hr : 4 ≤ r) (hNo : NoQ16E4) (h4 : Thm4RBelow r n)
    (hL : TightLargeHypR r n Y R S t) {J : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) {u : Y}
    (hu : IsUniqueInvolution J u) {w : Y} (hw2 : w * w = 1) (hwt : w * t = t * w)
    (hwu : w * u = u * w) (hwE : w ∉ Subgroup.closure ({t, u} : Set Y)) {R₀ : Subgroup Y}
    (hR₀ : IsSylow2In R₀ (tightCore R)) (hR₀u : R₀ ≤ Subgroup.centralizer ({u} : Set Y))
    (hR₀w : R₀ ≤ Subgroup.centralizer ({w} : Set Y)) {T₀ : Subgroup Y} (hT₀ : IsSylow2In T₀ J)
    (hT₀N : T₀ ≤ Subgroup.normalizer ((tightCore R : Subgroup Y) : Set Y))
    (hT₀w : T₀ ≤ Subgroup.centralizer ({w} : Set Y))
    (htrivt : ∀ y ∈ linkLayer R t, w * y * w⁻¹ * y⁻¹ ∈ oddCoreOf (linkLayer R t))
    (htrivu : ∀ y ∈ linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u,
      w * y * w⁻¹ * y⁻¹ ∈ oddCoreOf (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u)) :
    Hyp51 (Subgroup.closure ({t, u, w} : Set Y)) := by
  have h := TightLargeHypR.typeRFam hL
  have hΩ := h.hyp
  have ht := hL.datum.isUniqueInvolution_core
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) :=
    CoreAssembly.mem_conjClass_self _
  have ctu : t * u = u * t := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ ht hJ hu
  have htu : t ≠ u := fun h' => hJ.2.1 (eq_core_of_isUniqueInvolution hL hJ.1 (h' ▸ hu))
  have hw1 : w ≠ 1 := fun h' => hwE (h' ▸ Subgroup.one_mem _)
  have hBe : IsElemAbelian 2 (Subgroup.closure ({t, u, w} : Set Y)) :=
    T8T.isElemAbelian_closure_three ht.sq hu.sq hw2 ctu hwt.symm hwu.symm
  have hB8 : Nat.card ↥(Subgroup.closure ({t, u, w} : Set Y)) = 8 :=
    T8T.natCard_closure_three ht.sq hu.sq hw2 ctu hwt.symm hwu.symm ht.ne_one hu.ne_one htu hw1
      hwE
  have htB : t ∈ Subgroup.closure ({t, u, w} : Set Y) := Subgroup.subset_closure (by simp)
  have huB : u ∈ Subgroup.closure ({t, u, w} : Set Y) := Subgroup.subset_closure (by simp)
  have hwB : w ∈ Subgroup.closure ({t, u, w} : Set Y) := Subgroup.subset_closure (by simp)
  have htE : t ∈ Subgroup.closure ({t, u} : Set Y) := Subgroup.subset_closure (by simp)
  have huE : u ∈ Subgroup.closure ({t, u} : Set Y) := Subgroup.subset_closure (by simp)
  have hEB : Subgroup.closure ({t, u} : Set Y) ≤ Subgroup.closure ({t, u, w} : Set Y) := by
    rw [Subgroup.closure_le]
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with hv | hv <;> rw [hv]
    · exact htB
    · exact huB
  have hcent : ∀ x : Y, x * t = t * x → x * u = u * x → x * w = w * x →
      ∀ c ∈ Subgroup.closure ({t, u, w} : Set Y), x * c = c * x := by
    intro x hxt hxu hxw c hc
    have hle : Subgroup.closure ({t, u, w} : Set Y) ≤ Subgroup.centralizer ({x} : Set Y) := by
      rw [Subgroup.closure_le]
      intro v hv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with hv | hv | hv <;> rw [hv]
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hxt.symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hxu.symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hxw.symm
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hc)).symm
  have hK₀J : tightCore R ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J :=
    Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hK hJ.1 hJ
  have huΛ : u ∈ linkLayer R t :=
    coreAt_le_linkLayerAt hJ (mem_coreAt_of_sq_sq hu.mem (by rw [hu.sq, one_mul]) ctu.symm)
  have htΛ : t ∈ linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u :=
    coreAt_le_linkLayerAt hK₀J (mem_coreAt_of_sq_sq ht.mem (by rw [ht.sq, one_mul]) ctu)
  have hNu : ∀ c ∈ Subgroup.centralizer ({u} : Set Y),
      ∀ y ∈ linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u,
        c * y * c⁻¹ ∈ linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u :=
    fun c hc _ hy => conj_mem_linkLayerAt hΩ.conjInvariant hc
      (mem_normalizer_iff_conjSub_eq.mp (h.tight J hJ.1 u hu hc)) hy
  have hwt' : w ≠ t := fun h' => hwE (h' ▸ htE)
  have hwu' : w ≠ u := fun h' => hwE (h' ▸ huE)
  refine ⟨hBe, hB8, fun c hcB hc1 => ?_⟩
  rcases mem_closure_three_cases hw2 hwt.symm hwu.symm hcB with hcE | ⟨e', he', hce⟩
  ·
    rcases TypeCSetup.mem_closure_pair ht.sq hu.sq ctu hcE with h1 | h1 | h1 | h1
    · exact absurd h1 hc1
    · rw [h1]
      exact LinkZ2A.hyp51At_of_forall_not (LinkZ2A.not_movedByAll_of_layer linkLayerAt_le_centralizer
        (fun _ hc _ hy => conj_mem_linkLayer hL hc hy) hBe htB ht.ne_one huB hu.ne_one
        htu.symm huΛ hwB hw1 hwt' htrivt)
    · rw [h1]
      exact LinkZ2A.hyp51At_of_forall_not (LinkZ2A.not_movedByAll_of_layer linkLayerAt_le_centralizer hNu hBe
        huB hu.ne_one htB ht.ne_one htu htΛ hwB hw1 hwu' htrivu)
    · rw [h1]
      exact hyp51At_mul_of_edge_four_le hr hNo h4 hL hJ hu hBe htB huB
  subst hce
  exact hyp51At_wcoset_r hr hNo h4 hL hJ hu hwt hwu hBe hcent hEB he' hwB hc1 hwE hR₀
    hR₀u hR₀w hT₀ hT₀N hT₀w

theorem false_of_frameA1_r (hr : 4 ≤ r) (hNo : NoQ16E4) (h4 : Thm4RBelow r n)
    (hL : TightLargeHypR r n Y R S t)
    (hc : DConnected (CoreAssembly.conjClass (tightCore R))) (hα : LinkAlphaBad R t)
    (htr : LinkTrans R t) {J : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) {u : Y}
    (hu : IsUniqueInvolution J u) {w : Y} (hw2 : w * w = 1) (hwt : w * t = t * w)
    (hwu : w * u = u * w) (hwE : w ∉ Subgroup.closure ({t, u} : Set Y)) {R₀ : Subgroup Y}
    (hR₀ : IsSylow2In R₀ (tightCore R)) (hR₀u : R₀ ≤ Subgroup.centralizer ({u} : Set Y))
    (hR₀w : R₀ ≤ Subgroup.centralizer ({w} : Set Y)) {T₀ : Subgroup Y} (hT₀ : IsSylow2In T₀ J)
    (hT₀N : T₀ ≤ Subgroup.normalizer ((tightCore R : Subgroup Y) : Set Y))
    (hT₀w : T₀ ≤ Subgroup.centralizer ({w} : Set Y))
    (htrivt : ∀ y ∈ linkLayer R t, w * y * w⁻¹ * y⁻¹ ∈ oddCoreOf (linkLayer R t))
    (htrivu : ∀ y ∈ linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u,
      w * y * w⁻¹ * y⁻¹ ∈ oddCoreOf (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u)) :
    False := by
  have hΩ := hL.datum.hypOmegaGen
  have ht := hL.datum.isUniqueInvolution_core
  have ctu : t * u = u * t := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ ht hJ hu
  have htu : t ≠ u := fun h' => hJ.2.1 (eq_core_of_isUniqueInvolution hL hJ.1 (h' ▸ hu))
  have hw1 : w ≠ 1 := fun h' => hwE (h' ▸ Subgroup.one_mem _)
  have hwt' : w ≠ t := fun h' => hwE (h' ▸ Subgroup.subset_closure (by simp))
  have hH := hyp51_z2Frame_r hr hNo h4 hL hJ hu hw2 hwt hwu hwE hR₀ hR₀u hR₀w hT₀ hT₀N
    hT₀w htrivt htrivu
  have hDB : Subgroup.closure ({u, t} : Set Y) ≤ Subgroup.closure ({t, u, w} : Set Y) :=
    Subgroup.closure_mono (Set.insert_subset_iff.mpr ⟨by simp, Set.singleton_subset_iff.mpr
      (by simp)⟩)
  have h54 := lemma54_odd_and_eq hH hDB
    (T7A.isElemAbelian2_closure_pair hu.sq ht.sq hu.ne_one ht.ne_one htu.symm ctu.symm)
  have hWB : Subgroup.closure ({w, t} : Set Y) ≤ Subgroup.closure ({t, u, w} : Set Y) :=
    Subgroup.closure_mono (Set.insert_subset_iff.mpr ⟨by simp, Set.singleton_subset_iff.mpr
      (by simp)⟩)
  have hαwt : alphaOf (Subgroup.closure ({w, t} : Set Y)) =
      alphaOf (Subgroup.closure ({u, t} : Set Y)) :=
    h54.2 _ hWB (T7A.isElemAbelian2_closure_pair hw2 ht.sq hw1 ht.ne_one hwt' hwt)
  have hOC : oddCoreOf (Subgroup.centralizer ({t} : Set Y)) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u, t} : Set Y)) : Set Y) := by
    rw [Set.pair_comm]
    exact oddCoreOf_centralizer_le_normalizer_alphaOf hu.sq ht.ne_one ctu
  have hO : oddCoreOf (layerY (CoreAssembly.conjClass (tightCore R)) t) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u, t} : Set Y)) : Set Y) :=
    (oddCoreOf_layerY_le hΩ.conjInvariant).trans hOC
  have hΛN : linkLayer R t ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u, t} : Set Y)) : Set Y) := by
    intro x hx
    obtain ⟨c, hc, o, ho, rfl⟩ := AscE184Sect.exists_mul_of_mem
      (ExactLayer.isPGroup_zpowers_of_sq_eq_one hw2) (LinkZ2A.commutator_zpowers_le hw2 htrivt) hx
    obtain ⟨hcΛ, hcw⟩ := Subgroup.mem_inf.mp hc
    refine Subgroup.mul_mem _ ?_ ?_
    · have hcw' : c * w = w * c :=
        (Subgroup.mem_centralizer_iff.mp hcw w (Subgroup.mem_zpowers w)).symm
      have hct : c * t = t * c :=
        Subgroup.mem_centralizer_singleton_iff.mp (linkLayerAt_le_centralizer hcΛ)
      rw [← hαwt]
      exact mem_normalizer_alphaOf_of_centralizes hcw' hct
    · rw [S289.oddCoreOf_eq_inf linkLayerAt_le_centralizer
        (fun _ hc' _ hy => conj_mem_linkLayer hL hc' hy)] at ho
      exact hOC (Subgroup.mem_inf.mp ho).2
  have hconst : ∀ L ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R), ∀ l : Y,
      IsUniqueInvolution L l →
        alphaOf (Subgroup.closure ({l, t} : Set Y)) =
          alphaOf (Subgroup.closure ({u, t} : Set Y)) := by
    intro L hL' l hl
    obtain ⟨g, hg⟩ := LinkZ2A.exists_linkLayer_conj hL htr hJ hL'
    exact AlphaFr.alphaOf_eq_of_secImg_conj hL hJ hL' hu hl hO
      (g := ⟨g, linkLayer_le_layerY hL g.2⟩) (hΛN g.2) hg
  have hnorm := LinkDisc.normal_alphaOf_of_edges hΩ hc ht hJ hconst
  have hbot : alphaOf (Subgroup.closure ({u, t} : Set Y)) = ⊥ := by
    have hle : alphaOf (Subgroup.closure ({u, t} : Set Y)) ≤ classicalInvolutionOddCore Y :=
      le_sSup ⟨hnorm, h54.1⟩
    rwa [hL.cls.2.2, le_bot_iff] at hle
  obtain ⟨J', hJ', u', hu', hne⟩ := hα
  apply hne
  rw [Set.pair_comm, hconst J' hJ' u' hu', hbot]

theorem triv_or_triv_mul_gen {G : Type} [Group G] [Finite G] {Λ Q : Subgroup G} {w d : G}
    (hw2 : w * w = 1) (hwΛ : ∀ y ∈ Λ, w * y * w⁻¹ ∈ Λ) (hQΛ : Q ≤ Λ) (hdΛ : d ∈ Λ)
    (hd2 : d * d = 1) (hwQ : ∀ x ∈ Q, w * x = x * w)
    (hD : ∀ β : MulAut (↥Λ ⧸ classicalInvolutionOddCore ↥Λ), β * β = 1 →
      (∀ x ∈ (Q.subgroupOf Λ).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥Λ)), β x = x) →
      β = 1 ∨ β = MulAut.conj (QuotientGroup.mk (⟨d, hdΛ⟩ : ↥Λ))) :
    (∀ y ∈ Λ, w * y * w⁻¹ * y⁻¹ ∈ oddCoreOf Λ) ∨
      (∀ y ∈ Λ, w * d * y * (w * d)⁻¹ * y⁻¹ ∈ oddCoreOf Λ) := by
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_left hw2
  let γ : MulAut ↥Λ :=
    { toFun := fun y => ⟨w * y * w⁻¹, hwΛ y y.2⟩
      invFun := fun y => ⟨w * y * w⁻¹, hwΛ y y.2⟩
      left_inv := fun y => Subtype.ext (by
        show w * (w * (y : G) * w⁻¹) * w⁻¹ = y
        rw [hwinv]
        calc w * (w * (y : G) * w) * w = w * w * y * (w * w) := by group
          _ = y := by rw [hw2, one_mul, mul_one])
      right_inv := fun y => Subtype.ext (by
        show w * (w * (y : G) * w⁻¹) * w⁻¹ = y
        rw [hwinv]
        calc w * (w * (y : G) * w) * w = w * w * y * (w * w) := by group
          _ = y := by rw [hw2, one_mul, mul_one])
      map_mul' := fun x y => Subtype.ext (by
        show w * ((x : G) * y) * w⁻¹ = w * x * w⁻¹ * (w * y * w⁻¹)
        group) }
  have hγ : ∀ y : ↥Λ, ((γ y : ↥Λ) : G) = w * y * w⁻¹ := fun _ => rfl
  have hO : (classicalInvolutionOddCore ↥Λ).map γ.toMonoidHom = classicalInvolutionOddCore ↥Λ :=
    CFSG.ComponentClassification.OddCore.char_invariant γ
  set O := classicalInvolutionOddCore ↥Λ with hOdef
  let β : MulAut (↥Λ ⧸ O) := QuotientGroup.congr O O γ hO
  have hβ : ∀ y : ↥Λ, β (QuotientGroup.mk y) = QuotientGroup.mk (γ y) := fun _ => rfl
  have hβ2 : β * β = 1 := by
    refine MulEquiv.ext fun x => ?_
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    rw [MulAut.mul_apply, hβ, hβ, MulAut.one_apply]
    congr 1
    exact γ.left_inv y
  have hfix : ∀ x ∈ (Q.subgroupOf Λ).map (QuotientGroup.mk' O), β x = x := by
    rintro _ ⟨q, hq, rfl⟩
    change β (QuotientGroup.mk (q : ↥Λ)) = QuotientGroup.mk (q : ↥Λ)
    rw [hβ]
    congr 1
    apply Subtype.ext
    rw [hγ]
    have hq' : ((q : ↥Λ) : G) ∈ Q := Subgroup.mem_subgroupOf.mp hq
    rw [hwQ _ hq', mul_inv_cancel_right]
  rcases hD β hβ2 hfix with h | h
  · left
    intro y hy
    have h1 : β (QuotientGroup.mk ⟨y, hy⟩) = QuotientGroup.mk ⟨y, hy⟩ := by rw [h]; rfl
    rw [hβ] at h1
    have e1 : γ ⟨y, hy⟩ = ⟨w * y * w⁻¹, hwΛ y hy⟩ := rfl
    rw [e1] at h1
    exact LinkZ2S.mul_inv_mem_oddCoreOf (hwΛ y hy) hy h1
  · right
    intro y hy
    have hdy : d * y * d⁻¹ ∈ Λ := Λ.mul_mem (Λ.mul_mem hdΛ hy) (Λ.inv_mem hdΛ)
    have h1 : β (QuotientGroup.mk ⟨d * y * d⁻¹, hdy⟩) =
        QuotientGroup.mk (⟨d, hdΛ⟩ : ↥Λ) * QuotientGroup.mk ⟨d * y * d⁻¹, hdy⟩ *
          (QuotientGroup.mk (⟨d, hdΛ⟩ : ↥Λ))⁻¹ := by
      rw [h, MulAut.conj_apply]
    rw [hβ, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul] at h1
    have hwdΛ : w * d * y * (w * d)⁻¹ ∈ Λ := by
      have := hwΛ _ hdy
      rwa [show w * (d * y * d⁻¹) * w⁻¹ = w * d * y * (w * d)⁻¹ by group] at this
    have e1 : γ ⟨d * y * d⁻¹, hdy⟩ = ⟨w * d * y * (w * d)⁻¹, hwdΛ⟩ :=
      Subtype.ext (by rw [hγ]; group)
    have e2 : (⟨d, hdΛ⟩ : ↥Λ) * ⟨d * y * d⁻¹, hdy⟩ * (⟨d, hdΛ⟩ : ↥Λ)⁻¹ = ⟨y, hy⟩ :=
      Subtype.ext (by
        show d * (d * y * d⁻¹) * d⁻¹ = y
        calc d * (d * y * d⁻¹) * d⁻¹ = (d * d) * y * (d * d)⁻¹ := by group
          _ = y := by rw [hd2]; group)
    rw [e1, e2] at h1
    exact LinkZ2S.mul_inv_mem_oddCoreOf hwdΛ hy h1

theorem linkDichSyl_quot (hL : TightLargeHypR r n Y R S t) (hD : LinkDichSyl R t)
    {J' : Subgroup Y}
    (hJ' : J' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) {t' : Y}
    (ht' : IsUniqueInvolution J' t') (ht'Λ : t' ∈ linkLayer R t) {Q : Subgroup Y}
    (hQ : IsSylow2In Q J') (hQc : Q ≤ coreAt t J') :
    ∀ β : MulAut (↥(linkLayer R t) ⧸ classicalInvolutionOddCore ↥(linkLayer R t)),
      β * β = 1 →
      (∀ x ∈ (Q.subgroupOf (linkLayer R t)).map
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥(linkLayer R t))), β x = x) →
      β = 1 ∨ β = MulAut.conj (QuotientGroup.mk (⟨t', ht'Λ⟩ : ↥(linkLayer R t))) := by
  intro β hβ2 hβfix
  set ε := linkLayerEquiv hL with hε
  have hc : ∀ m, MulAut.congr ε (MulAut.conj m) = MulAut.conj (ε m) := fun m => by
    refine MulEquiv.ext fun x => ?_
    change ε (m * ε.symm x * m⁻¹) = ε m * x * (ε m)⁻¹
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  have hβ' : MulAut.congr ε β * MulAut.congr ε β = 1 := by rw [← map_mul, hβ2, map_one]
  have hfix : ∀ x ∈ (Q.subgroupOf (linkLayer R t)).map (linkLayerHom' hL),
      MulAut.congr ε β x = x := by
    rintro _ ⟨q, hq, rfl⟩
    have h1 := hβfix (QuotientGroup.mk q) ⟨q, hq, rfl⟩
    have e1 : linkLayerHom' hL q = ε (QuotientGroup.mk q) :=
      Subtype.ext (linkLayerEquiv_mk hL q).symm
    rw [e1]
    show ε (β (ε.symm (ε (QuotientGroup.mk q)))) = ε (QuotientGroup.mk q)
    rw [MulEquiv.symm_apply_apply, h1]
  have hinv := isUniqueInvolution_linkLayerHom'_r hL hJ' ht' ht'Λ
  have ea : linkLayerHom' hL ⟨t', ht'Λ⟩ = ε (QuotientGroup.mk (⟨t', ht'Λ⟩ : ↥(linkLayer R t))) :=
    Subtype.ext (linkLayerEquiv_mk hL _).symm
  rw [ea] at hinv
  rcases hD _ (subgroupOf_mem_linkRestrict (t := t) hJ') _ hinv _
    (S289.isSylow2In_map_member hL hJ' hQ hQc) _ hβ' hfix with h | h
  · left
    apply (MulAut.congr ε).injective
    rw [h, map_one]
  · right
    apply (MulAut.congr ε).injective
    rw [h, hc]

theorem triv_at_t_r (hL : TightLargeHypR r n Y R S t) (hD : LinkDichSyl R t) {J : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) {u : Y}
    (hu : IsUniqueInvolution J u) {T₀ : Subgroup Y} (hT₀ : IsSylow2In T₀ J)
    (hT₀N : T₀ ≤ Subgroup.normalizer ((tightCore R : Subgroup Y) : Set Y)) {w : Y}
    (hw2 : w * w = 1) (hwt : w * t = t * w) (hT₀w : T₀ ≤ Subgroup.centralizer ({w} : Set Y)) :
    (∀ y ∈ linkLayer R t, w * y * w⁻¹ * y⁻¹ ∈ oddCoreOf (linkLayer R t)) ∨
      (∀ y ∈ linkLayer R t, w * u * y * (w * u)⁻¹ * y⁻¹ ∈ oddCoreOf (linkLayer R t)) := by
  have ht := hL.datum.isUniqueInvolution_core
  have hT₀t : T₀ ≤ Subgroup.centralizer ({t} : Set Y) := fun x hx =>
    S1916.normalizer_le_centralizer_of_isUniqueInvolution ht (hT₀N hx)
  have hT₀c : T₀ ≤ coreAt t J := LinkZ2S.le_coreAt_of_isPGroup hT₀.1 hT₀t hT₀.2.1
  have hQΛ : T₀ ≤ linkLayer R t := hT₀c.trans (coreAt_le_linkLayerAt hJ)
  have ctu : t * u = u * t := Q3CL.T8.mul_comm_of_mem_omegaNbr hL.datum.hypOmegaGen ht hJ hu
  have huΛ : u ∈ linkLayer R t :=
    coreAt_le_linkLayerAt hJ (mem_coreAt_of_sq_sq hu.mem (by rw [hu.sq, one_mul]) ctu.symm)
  exact triv_or_triv_mul_gen hw2
    (fun y hy => conj_mem_linkLayer hL (Subgroup.mem_centralizer_singleton_iff.mpr hwt) hy)
    hQΛ huΛ hu.sq (fun x hx => (Subgroup.mem_centralizer_singleton_iff.mp (hT₀w hx)).symm)
    (linkDichSyl_quot hL hD hJ hu huΛ hT₀ hT₀c)

theorem triv_at_u_r (hL : TightLargeHypR r n Y R S t) (hD : LinkDichSyl R t)
    {J : Subgroup Y} (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    {u : Y} (hu : IsUniqueInvolution J u) {R₀ : Subgroup Y} (hR₀ : IsSylow2In R₀ (tightCore R))
    (hR₀u : R₀ ≤ Subgroup.centralizer ({u} : Set Y)) {w : Y} (hw2 : w * w = 1)
    (hwu : w * u = u * w) (hR₀w : R₀ ≤ Subgroup.centralizer ({w} : Set Y)) :
    (∀ y ∈ linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u, w * y * w⁻¹ * y⁻¹ ∈
      oddCoreOf (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u)) ∨
    (∀ y ∈ linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u, w * t * y * (w * t)⁻¹ * y⁻¹ ∈
      oddCoreOf (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u)) := by
  have hΩ := hL.datum.hypOmegaGen
  have hcl : ConjInvariant (CoreAssembly.conjClass (tightCore R)) := hΩ.conjInvariant
  have ht := hL.datum.isUniqueInvolution_core
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) := ⟨1, conjSub_one _⟩
  obtain ⟨g, hg⟩ := hJ.1
  have hg' : conjSub g (tightCore R) = J := hg
  have hug : u = g * t * g⁻¹ := by
    have h1 := ht.conj g
    rw [hg'] at h1
    exact hu.eq h1
  have hKJ := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hK hJ.1 hJ
  have hM : conjSub g⁻¹ (tightCore R) ∈
      omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R) := by
    have h1 := omegaNbr_conj hcl hKJ g⁻¹
    rwa [← hg', conjSub_inv_conjSub] at h1
  have hQt : conjSub g⁻¹ R₀ ≤ Subgroup.centralizer ({t} : Set Y) := by
    intro x hx
    rw [mem_conjSub_iff, inv_inv] at hx
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hR₀u hx)
    rw [hug] at h1
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h2 : g * (x * t) * g⁻¹ = g * (t * x) * g⁻¹ := by
      calc g * (x * t) * g⁻¹ = g * x * g⁻¹ * (g * t * g⁻¹) := by group
        _ = g * t * g⁻¹ * (g * x * g⁻¹) := h1
        _ = g * (t * x) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)
  have hQ2 : IsPGroup 2 ↥(conjSub g⁻¹ R₀) := hR₀.2.1.map _
  have hQΛ : conjSub g⁻¹ R₀ ≤ linkLayer R t :=
    (LinkZ2S.le_coreAt_of_isPGroup (conjSub_mono hR₀.1) hQt hQ2).trans (coreAt_le_linkLayerAt hM)
  have hQsyl : IsSylow2In (conjSub g⁻¹ R₀) (conjSub g⁻¹ (tightCore R)) :=
    S1916.IsSylow2In.conj hR₀ g⁻¹
  have hQc : conjSub g⁻¹ R₀ ≤ coreAt t (conjSub g⁻¹ (tightCore R)) :=
    LinkZ2S.le_coreAt_of_isPGroup (conjSub_mono hR₀.1) hQt hQ2
  have hM' : IsUniqueInvolution (conjSub g⁻¹ (tightCore R)) (g⁻¹ * t * g) := by
    have h1 := ht.conj g⁻¹
    rwa [inv_inv] at h1
  have hdΛ : g⁻¹ * t * g ∈ linkLayer R t := by
    have htg : t * (g⁻¹ * t * g) = (g⁻¹ * t * g) * t := by
      have h1 := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ ht hM hM'
      exact h1
    exact coreAt_le_linkLayerAt hM (mem_coreAt_of_sq_sq hM'.mem (by rw [hM'.sq, one_mul]) htg.symm)
  have hd2 : g⁻¹ * t * g * (g⁻¹ * t * g) = 1 := by
    calc g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
      _ = 1 := by rw [ht.sq]; group
  have hw₁2 : g⁻¹ * w * g * (g⁻¹ * w * g) = 1 := by
    calc g⁻¹ * w * g * (g⁻¹ * w * g) = g⁻¹ * (w * w) * g := by group
      _ = 1 := by rw [hw2]; group
  have hw₁t : g⁻¹ * w * g * t = t * (g⁻¹ * w * g) := by
    rw [hug] at hwu
    calc g⁻¹ * w * g * t = g⁻¹ * (w * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * w) * g := by rw [hwu]
      _ = t * (g⁻¹ * w * g) := by group
  have hw₁Q : ∀ x ∈ conjSub g⁻¹ R₀, g⁻¹ * w * g * x = x * (g⁻¹ * w * g) := by
    intro x hx
    rw [mem_conjSub_iff, inv_inv] at hx
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hR₀w hx)
    calc g⁻¹ * w * g * x = g⁻¹ * (w * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * w) * g := by rw [h1]
      _ = x * (g⁻¹ * w * g) := by group
  have hV := triv_or_triv_mul_gen hw₁2
    (fun y hy => conj_mem_linkLayer hL (Subgroup.mem_centralizer_singleton_iff.mpr hw₁t) hy)
    hQΛ hdΛ hd2 hw₁Q (linkDichSyl_quot hL hD hM hM' hdΛ hQsyl hQc)
  have hΛ : linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u = conjSub g (linkLayer R t) := by
    show _ = conjSub g (linkLayerAt (CoreAssembly.conjClass (tightCore R)) (tightCore R) t)
    rw [conjSub_linkLayerAt hcl g, hg', ← hug]
  have hO : oddCoreOf (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) =
      conjSub g (oddCoreOf (linkLayer R t)) := by
    rw [hΛ, Thompson.oddCoreOf_conjSub_eq]
  rcases hV with h | h
  · left
    intro y hy
    rw [hΛ, mem_conjSub_iff] at hy
    rw [hO, mem_conjSub_iff]
    have h1 := h _ hy
    have e : g⁻¹ * (w * y * w⁻¹ * y⁻¹) * g = g⁻¹ * w * g * (g⁻¹ * y * g) *
        (g⁻¹ * w * g)⁻¹ * (g⁻¹ * y * g)⁻¹ := by group
    rw [e]
    exact h1
  · right
    intro y hy
    rw [hΛ, mem_conjSub_iff] at hy
    rw [hO, mem_conjSub_iff]
    have h1 := h _ hy
    have e : g⁻¹ * (w * t * y * (w * t)⁻¹ * y⁻¹) * g = g⁻¹ * w * g * (g⁻¹ * t * g) *
        (g⁻¹ * y * g) * (g⁻¹ * w * g * (g⁻¹ * t * g))⁻¹ * (g⁻¹ * y * g)⁻¹ := by group
    rw [e]
    exact h1

theorem false_of_caseA1_r (hr : 4 ≤ r) (hNo : NoQ16E4) (h4 : Thm4RBelow r n)
    (hL : TightLargeHypR r n Y R S t)
    (hc : DConnected (CoreAssembly.conjClass (tightCore R))) (hα : LinkAlphaBad R t)
    (htr : LinkTrans R t) (hD : LinkDichSyl R t)
    {J : Subgroup Y} (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    {u : Y} (hu : IsUniqueInvolution J u) {R₀ : Subgroup Y} (hR₀ : IsSylow2In R₀ (tightCore R))
    (hR₀u : R₀ ≤ Subgroup.centralizer ({u} : Set Y)) {T₀ : Subgroup Y} (hT₀ : IsSylow2In T₀ J)
    (hT₀N : T₀ ≤ Subgroup.normalizer ((tightCore R : Subgroup Y) : Set Y)) {w : Y}
    (hw2 : w * w = 1) (hwt : w * t = t * w) (hwu : w * u = u * w)
    (hwE : w ∉ Subgroup.closure ({t, u} : Set Y))
    (hR₀w : R₀ ≤ Subgroup.centralizer ({w} : Set Y))
    (hT₀w : T₀ ≤ Subgroup.centralizer ({w} : Set Y)) : False := by
  have hΩ := hL.datum.hypOmegaGen
  have ht := hL.datum.isUniqueInvolution_core
  have ctu : t * u = u * t := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ ht hJ hu
  have hR₀t : R₀ ≤ Subgroup.centralizer ({t} : Set Y) :=
    hR₀.1.trans ((tightCore_le R).trans hL.datum.cent)
  have hT₀t : T₀ ≤ Subgroup.centralizer ({t} : Set Y) := fun x hx =>
    S1916.normalizer_le_centralizer_of_isUniqueInvolution ht (hT₀N hx)
  have hT₀u : T₀ ≤ Subgroup.centralizer ({u} : Set Y) := fun x hx =>
    S1916.normalizer_le_centralizer_of_isUniqueInvolution hu (Subgroup.le_normalizer (hT₀.1 hx))
  have hΛt : ∀ y ∈ linkLayer R t, t * y = y * t := fun y hy =>
    (Subgroup.mem_centralizer_singleton_iff.mp (linkLayerAt_le_centralizer hy)).symm
  have hΛu : ∀ y ∈ linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u, u * y = y * u :=
    fun y hy => (Subgroup.mem_centralizer_singleton_iff.mp (linkLayerAt_le_centralizer hy)).symm
  have htE : t ∈ Subgroup.closure ({t, u} : Set Y) := Subgroup.subset_closure (by simp)
  have huE : u ∈ Subgroup.closure ({t, u} : Set Y) := Subgroup.subset_closure (by simp)
  have hut2 : u * t * (u * t) = 1 := by
    calc u * t * (u * t) = u * (t * u) * t := by group
      _ = u * (u * t) * t := by rw [ctu]
      _ = u * u * (t * t) := by group
      _ = 1 := by rw [hu.sq, ht.sq, one_mul]
  have frame : ∀ w' : Y, w' * w' = 1 → w' * t = t * w' → w' * u = u * w' →
      w' ∉ Subgroup.closure ({t, u} : Set Y) → R₀ ≤ Subgroup.centralizer ({w'} : Set Y) →
      T₀ ≤ Subgroup.centralizer ({w'} : Set Y) →
      (∀ y ∈ linkLayer R t, w' * y * w'⁻¹ * y⁻¹ ∈ oddCoreOf (linkLayer R t)) →
      (∀ y ∈ linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u, w' * y * w'⁻¹ * y⁻¹ ∈
        oddCoreOf (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u)) → False :=
    fun w' h1 h2 h3 h4' h5' h6 h7 h8 =>
      false_of_frameA1_r hr hNo h4 hL hc hα htr hJ hu h1 h2 h3 h4' hR₀ hR₀u h5'
        hT₀ hT₀N h6 h7 h8
  have vt := triv_at_t_r hL hD hJ hu hT₀ hT₀N hw2 hwt hT₀w
  have vu := triv_at_u_r hL hD hJ hu hR₀ hR₀u hw2 hwu hR₀w
  rcases vt with ht' | ht' <;> rcases vu with hu' | hu'
  · exact frame w hw2 hwt hwu hwE hR₀w hT₀w ht' hu'
  · obtain ⟨a1, a2, a3, a4, a5, a6⟩ := LinkZ2S.caseA1_mul hw2 hwt hwu hwE hR₀w hT₀w ht.sq rfl ctu
      hwt.symm htE hR₀t hT₀t
    exact frame _ a1 a2 a3 a4 a5 a6 (LinkZ2S.triv_mul_of_comm hΛt ht') hu'
  · obtain ⟨a1, a2, a3, a4, a5, a6⟩ := LinkZ2S.caseA1_mul hw2 hwt hwu hwE hR₀w hT₀w hu.sq ctu.symm rfl
      hwu.symm huE hR₀u hT₀u
    exact frame _ a1 a2 a3 a4 a5 a6 ht' (LinkZ2S.triv_mul_of_comm hΛu hu')
  · have hutt : u * t * t = t * (u * t) := by rw [← mul_assoc, ctu]
    have hutu : u * t * u = u * (u * t) := by rw [mul_assoc, ctu]
    have hutw : u * t * w = w * (u * t) := by
      calc u * t * w = u * (t * w) := by group
        _ = u * (w * t) := by rw [hwt]
        _ = (u * w) * t := by group
        _ = (w * u) * t := by rw [hwu]
        _ = w * (u * t) := by group
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := LinkZ2S.caseA1_mul hw2 hwt hwu hwE hR₀w hT₀w hut2 hutt hutu hutw
      (Subgroup.mul_mem _ huE htE) (fun x hx => LinkZ2S.mem_centralizer_mul (hR₀u hx) (hR₀t hx))
      (fun x hx => LinkZ2S.mem_centralizer_mul (hT₀u hx) (hT₀t hx))
    have e1 : w * (u * t) = w * u * t := by group
    have e2 : w * (u * t) = w * t * u := by rw [← ctu]; group
    refine frame _ a1 a2 a3 a4 a5 a6 ?_ ?_
    · rw [e1]
      exact LinkZ2S.triv_mul_of_comm hΛt ht'
    · rw [e2]
      exact LinkZ2S.triv_mul_of_comm hΛu hu'

end Cit3

end CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes
