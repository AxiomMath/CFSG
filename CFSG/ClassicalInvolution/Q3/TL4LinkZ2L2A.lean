module

public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2L2A1
public import CFSG.ClassicalInvolution.Q3.TL4LinkDiscC1
public import CFSG.ClassicalInvolution.Q3.TL4LinkCases

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open scoped commutatorElement

namespace LinkZ2A

theorem commutator_zpowers_le {G : Type} [Group G] {Λ : Subgroup G} {w : G} (hw2 : w * w = 1)
    (htriv : ∀ y ∈ Λ, w * y * w⁻¹ * y⁻¹ ∈ oddCoreOf Λ) :
    ⁅Subgroup.zpowers w, Λ⁆ ≤ oddCoreOf Λ := by
  rw [Subgroup.commutator_le]
  intro h hh y hy
  rcases Bootstrap.mem_zpowers_involution hw2 hh with rfl | rfl
  · rw [commutatorElement_def, one_mul, inv_one, mul_one, mul_inv_cancel]
    exact Subgroup.one_mem _
  · rw [commutatorElement_def]
    exact htriv y hy

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem exists_linkLayer_conj (hL : TightLargeHypR r n Y R S t) (htr : LinkTrans R t)
    {J L : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hL' : L ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) :
    ∃ g : ↥(linkLayer R t), conjSub (linkLayerHom hL g)
      (secImg (CoreAssembly.conjClass (tightCore R)) t J) =
        secImg (CoreAssembly.conjClass (tightCore R)) t L := by
  obtain ⟨gb, hgb⟩ := htr _ (subgroupOf_mem_linkRestrict (t := t) hJ) _
    (subgroupOf_mem_linkRestrict (t := t) hL')
  rw [Generic.conjSub_subgroupOf] at hgb
  have hle : conjSub (gb : SecQuot (CoreAssembly.conjClass (tightCore R)) t)
      (secImg (CoreAssembly.conjClass (tightCore R)) t J) ≤ linkGrp R t := by
    have h1 := conjSub_mono (n := (gb : SecQuot (CoreAssembly.conjClass (tightCore R)) t))
      (le_linkGrp (t := t) hJ)
    rwa [conjSub_eq_self_of_mem gb.2] at h1
  have h1 := Subgroup.subgroupOf_inj.mp hgb
  rw [inf_of_le_left hle, inf_of_le_left (le_linkGrp (t := t) hL')] at h1
  obtain ⟨g₁, hg₁⟩ := linkLayerHom'_surjective hL gb
  refine ⟨g₁, ?_⟩
  have e : linkLayerHom hL g₁ = (gb : SecQuot (CoreAssembly.conjClass (tightCore R)) t) := by
    rw [← hg₁]
    rfl
  rw [e, h1]

end Cit3

section Frame


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem false_of_frameA1 (h4 : Thm4RBelow 3 n) (h5 : Thm5RBelowF 3 n)
    (htw : PhilipHall.Frame.Thm1RTwinLiftSetEBelow n) (hE4 : E4AutOddFreeR)
    (hOm : OmegaAutOddFreeR) (hL : TightLargeHypR 3 n Y R S t)
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
  have hH := hyp51_z2Frame h4 h5 htw hE4 hOm hL hJ hu hw2 hwt hwu hwE hR₀ hR₀u hR₀w hT₀ hT₀N
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
      (ExactLayer.isPGroup_zpowers_of_sq_eq_one hw2) (commutator_zpowers_le hw2 htrivt) hx
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
    obtain ⟨g, hg⟩ := exists_linkLayer_conj hL htr hJ hL'
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

end Frame

end LinkZ2A

end CFSG.ClassicalInvolution.Q3.TL4
