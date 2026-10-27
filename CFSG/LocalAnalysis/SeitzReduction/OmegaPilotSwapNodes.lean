module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSwapOverlap
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotGlobalGen

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup CFSG.Open
open CFSG.Quasithin (perfectCore perfectCore_le)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.SeitzQ2 (SwapParam SwapPairExclusion)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {n : ℕ}

theorem perfect_le_pairPerp_of_le (hq : 4 ≤ Nat.card K)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) (a : Fin n) {H : Subgroup G}
    (hH : ⁅H, H⁆ = H)
    (hle : H ≤ L ⊓ centralizer (modelToG e (pairTorus (K := K) a) : Set G)) :
    H ≤ modelToG e (pairPerp (K := K) a) := by
  rw [UnitaryPilot.inf_centralizer_modelToG, centralizer_pairTorus hq a,
    UnitaryPilot.modelToG_sup] at hle
  have hXX : modelToG e (pairTorus (K := K) a) ≤
      centralizer (modelToG e (pairTorus (K := K) a) : Set G) :=
    UnitaryPilot.modelToG_le_centralizer e
      (F4Pilot.le_centralizer_self_of_isCyclic (isCyclic_pairTorus a))
  have hXD : modelToG e (pairTorus (K := K) a) ≤
      centralizer (modelToG e (pairPerp (K := K) a) : Set G) :=
    UnitaryPilot.modelToG_le_centralizer e
      (isHypCoord_coordinateQuadPlus a).pairTorusOf_le_centralizer_pairPerpOf
  have hab : ∀ x ∈ modelToG e (pairTorus (K := K) a), ∀ y ∈ modelToG e (pairTorus (K := K) a),
      x * y = y * x := fun x hx y hy => mem_centralizer_iff.1 (hXX hy) x hx
  rw [← hH]
  exact (Subgroup.commutator_mono hle hle).trans
    (F4Pilot.commutator_sup_le_of_comm_of_le_normalizer hab
      (hXD.trans (centralizer_le_normalizer _)))

theorem compl_plusNodeSet_inter_nonempty (hn : 5 ≤ n) (j j' : Fin n) :
    ((plusNodeSet n j)ᶜ ∩ (plusNodeSet n j')ᶜ).Nonempty := by
  classical
  rw [← Finset.compl_union, Finset.nonempty_iff_ne_empty, Ne, Finset.compl_eq_empty_iff]
  intro h
  have h1 := Finset.card_union_le (plusNodeSet n j) (plusNodeSet n j')
  rw [h, Finset.card_univ, Fintype.card_fin] at h1
  have := card_plusNodeSet_le j
  have := card_plusNodeSet_le j'
  omega

theorem modelToG_rationalNode_le_perfectCore (hq : 4 ≤ Nat.card K) (hn : 2 ≤ n)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) (j : Fin n) :
    modelToG e (rationalNode (K := K) (by omega : 1 ≤ n) j) ≤
      perfectCore (L ⊓ centralizer ((⨆ s ∈ (plusNodeSet n j)ᶜ,
        modelToG e (pairTorus (K := K) s) : Subgroup G) : Set G)) := by
  refine CFSG.Quasithin.le_perfectCore_of_perfect (le_inf (UnitaryPilot.modelToG_le e _) ?_)
    (UnitaryPilot.modelToG_perfect e (commutator_rationalNode hn hq j))
  rw [Subgroup.le_centralizer_iff]
  refine iSup₂_le fun s hs => ?_
  rw [← Subgroup.le_centralizer_iff]
  refine UnitaryPilot.modelToG_le_centralizer e ((rationalNode_le_centralizer _ j).trans
    (centralizer_le ?_))
  exact pairTorus_le_plusSignedLevelTorus (Finset.mem_compl.1 hs) _

theorem le_iSup_perfectCore_pieces {f : ℕ} (hKf : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K)
    (hn : 5 ≤ n) (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) :
    L ≤ ⨆ j : Fin n, perfectCore (L ⊓ centralizer ((⨆ s ∈ (plusNodeSet n j)ᶜ,
        modelToG e (pairTorus (K := K) s) : Subgroup G) : Set G)) := by
  have h1 : L = ⨆ j : Fin n, modelToG e (rationalNode (K := K) (by omega : 1 ≤ n) j) := by
    rw [← UnitaryPilot.modelToG_iSup, iSup_rationalNode (by omega) hKf hq,
      UnitaryPilot.modelToG_top]
  calc L = ⨆ j : Fin n, modelToG e (rationalNode (K := K) (by omega : 1 ≤ n) j) := h1
    _ ≤ _ := iSup_mono fun j => modelToG_rationalNode_le_perfectCore hq (by omega) e j

section Main

theorem false_of_swapCase_omega_plus_of_swapPairExclusion (hset : SeitzSetting G L) {f : ℕ}
    (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) (hn : 5 ≤ n)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {m f' : ℕ}
    (hS : ∀ k : Fin n, ∀ htX : t ∈ centralizer (modelToG e (pairTorus (K := K) k) : Set G),
      ∃ Kc : Subgroup (centralizer (modelToG e (pairTorus (K := K) k) : Set G) ⧸
          oddCore (centralizer (modelToG e (pairTorus (K := K) k) : Set G))),
        IsComponent Kc ∧
        OmegaNeighbourAlternative (QuotientGroup.mk'
            (oddCore (centralizer (modelToG e (pairTorus (K := K) k) : Set G))) ⟨t, htX⟩)
          (((modelToG e (pairPerp (K := K) k)).subgroupOf
              (centralizer (modelToG e (pairTorus (K := K) k) : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (modelToG e (pairTorus (K := K) k) :
              Set G))))) Kc m f' ∧
        Kc.map (MulAut.conj (QuotientGroup.mk'
            (oddCore (centralizer (modelToG e (pairTorus (K := K) k) : Set G)))
              ⟨t, htX⟩)).toMonoidHom ≠ Kc)
    (hP : SwapPairExclusion (matrixProjectiveDerived (coordinateQuadPlus n K))) : False := by
  have htC := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  set X : Fin n → Subgroup G := fun k => modelToG e (pairTorus (K := K) k) with hXdef
  set D : Fin n → Subgroup G := fun k => modelToG e (pairPerp (K := K) k) with hDdef
  have hdata : ∀ k : Fin n, X k ≤ L ∧ t ∈ centralizer (X k : Set G) ∧
      D k ≤ centralizer (X k : Set G) ∧ center (D k) = ⊥ := by
    intro k
    obtain ⟨hXL, htX, -, -, -, -, hDXt, -, hZ, -, -⟩ :=
      neighbour_data_pairTorus hKc hq hn k e htC (X := X k) rfl (D := D k) rfl
    exact ⟨hXL, htX, hDXt.trans inf_le_left, hZ⟩
  have hpar : ∀ k : Fin n, ∃ P : SwapParam t (D k), Function.Injective P.Ψ ∧
      P.Ψ.range = centralizerPerfectCore (X k) := fun k =>
    exists_swapParam_pairTorus hset hKc hq hn k e htC ht rfl (hdata k).2.1 rfl
      (hS k (hdata k).2.1)
  choose Ψ hinj hrange using hpar
  have hOut : Group.IsSolvable (Outer L) :=
    isSolvable_outer_of_mulEquiv_plus (by omega) (LinearPilot.one_le_of_card_eq_two_pow hKc) hKc e
  have hO' : ∀ a b, perfectCore (D a ⊓ centralizer (X b : Set G)) =
      modelToG e (plusOverlap (K := K) a b) := fun a b =>
    perfectCore_modelToG_inf_centralizer e _ _
  exact false_of_swapParam_pieces hset hOut e hP ht hKt Ψ hinj hrange (fun k => (hdata k).1)
    (fun k => UnitaryPilot.modelToG_le e _) (fun k => (hdata k).2.2.1) (fun k => (hdata k).2.2.2)
    (fun a H hH hle => perfect_le_pairPerp_of_le hq e a hH hle)
    (fun a b hab => UnitaryPilot.modelToG_mono e (pairTorus_le_pairPerp hab))
    (fun a b hab => by
      rw [hO']
      exact isSimpleGroup_modelToG e (isSimpleGroup_plusOverlap hq hn hab))
    (fun a b hab => by
      rw [hO']
      exact center_modelToG_eq_bot e (center_plusOverlap_eq_bot hq hn hab))
    ⟨0, by omega⟩
    (fun k l hk hl hkl => by
      rw [hO', hO', hO']
      exact exists_ne_one_mem_modelToG e
        (exists_ne_one_mem_plusOverlap_triple hq hn (Ne.symm hk) (Ne.symm hl) hkl))
    (fun j => (plusNodeSet n j)ᶜ) (compl_plusNodeSet_inter_nonempty hn)
    (le_iSup_perfectCore_pieces hKc hq hn e)

theorem false_of_swapRow_omega_plus_of_swapPairExclusion (hset : SeitzSetting G L) {f : ℕ}
    (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) (hn : 5 ≤ n)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {m f' : ℕ}
    (hHR8 : ∀ k : Fin n, ∀ htX : t ∈ centralizer (modelToG e (pairTorus (K := K) k) : Set G),
      NeighbourOvergroupOmega (QuotientGroup.mk'
          (oddCore (centralizer (modelToG e (pairTorus (K := K) k) : Set G))) ⟨t, htX⟩)
        (((modelToG e (pairPerp (K := K) k)).subgroupOf
            (centralizer (modelToG e (pairTorus (K := K) k) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (modelToG e (pairTorus (K := K) k) :
            Set G))))) m f')
    (hrow : ∀ k : Fin n, OmegaRowAt t (modelToG e (pairTorus (K := K) k))
      (modelToG e (pairPerp (K := K) k)) .swap)
    (hP : SwapPairExclusion (matrixProjectiveDerived (coordinateQuadPlus n K))) : False := by
  have htC := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  refine false_of_swapCase_omega_plus_of_swapPairExclusion hset hKc hq hn e ht hKt (m := m)
    (f' := f') (fun k htX => ?_) hP
  obtain ⟨hcomp, -, -⟩ :=
    neighbour_standard_pairTorus_of_seitzSetting hset hKc hq hn k e htC ht rfl htX rfl
  obtain ⟨htX', hr⟩ := hrow k
  have hs : (QuotientGroup.mk' (oddCore (centralizer
      (modelToG e (pairTorus (K := K) k) : Set G))) ⟨t, htX⟩) ^ 2 = 1 := by
    rw [← map_pow, sq, LinearPilot.mk_mul_mk_eq_one ht htX, map_one]
  exact swapCase_of_neighbourOvergroupOmega hs (commutator_eq_self_of_isQuasisimple_open hcomp.2.2)
    (ne_bot_of_isQuasisimple hcomp.2.2) (hHR8 k htX) hr

theorem two_le_of_four_le_card {f : ℕ} (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) :
    2 ≤ f := by
  by_contra h
  have h1 : 2 ^ f ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

end Main

end CFSG.SeitzReduction.OmegaPilot
