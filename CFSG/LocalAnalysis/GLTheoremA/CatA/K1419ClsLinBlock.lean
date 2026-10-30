module

import CFSG.LieType.SemisimpleCentralizers.HeldCompTrivSL
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
import CFSG.LieType.SemisimpleCentralizers.HeldLinearComponents

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K1419

open CFSG.Open CFSG.Open.StatedAPI Matrix
open CFSG.LieType.SemisimpleCentralizers.Held CFSG.StandardType.LinNonsplit
open scoped commutatorElement

theorem k1419ClsLinBlock_exists {F : Type} [Field F] [Finite F] {n : ℕ} (A : GL (Fin n) F)
    (hord : (orderOf A : F) ≠ 0) (M : Subgroup (GL (Fin n) F))
    (hM : IsComponentOf M (Subgroup.centralizer ({A} : Set (GL (Fin n) F)) ⊓ StatedSL n F)) :
    ∃ (r : ℕ) (D : Fin r → Type) (d : Fin r → ℕ) (_ : ∀ i, Field (D i)) (_ : ∀ i, Finite (D i))
      (_ : ∀ i, Algebra F (D i))
      (Φ : (∀ i, Matrix (Fin (d i)) (Fin (d i)) (D i)) →ₐ[F] Matrix (Fin n) (Fin n) F)
      (θ : (∀ i, GL (Fin (d i)) (D i)) →* GL (Fin n) F),
      (∀ i, 1 ≤ d i) ∧ Function.Injective Φ ∧ Function.Injective θ ∧
      θ.range = Subgroup.centralizer ({A} : Set (GL (Fin n) F)) ∧
      (∀ w, ((θ w : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        Φ (fun i => ((w i : GL (Fin (d i)) (D i)) : Matrix (Fin (d i)) (Fin (d i)) (D i)))) ∧
      ∃ i : Fin r, 2 ≤ d i ∧
        M = ((StatedSL (d i) (D i)).map
          (MonoidHom.mulSingle (fun j => GL (Fin (d j)) (D j)) i)).map θ := by
  classical
  have hA : (Nat.card (Subgroup.zpowers A) : F) ≠ 0 := by
    rw [Nat.card_zpowers]
    exact hord
  obtain ⟨r, D, d, hFld, hFin, hAlg, Φ, θ, hNZ, hΦinj, _hΦrange, hθinj, hθrange, hθapply⟩ :=
    exists_piMat_commutant (Subgroup.zpowers A) hA
  letI : ∀ i, Field (D i) := hFld
  haveI : ∀ i, Finite (D i) := hFin
  have hcent : Subgroup.centralizer ((Subgroup.zpowers A : Subgroup (GL (Fin n) F)) :
      Set (GL (Fin n) F)) = Subgroup.centralizer ({A} : Set (GL (Fin n) F)) := by
    ext g
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro hg h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact hg _ (Subgroup.mem_zpowers _)
    · intro hg h hh
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      have hc : Commute A g := hg A (Set.mem_singleton A)
      exact (hc.zpow_left k).eq
  have hSL' : ∀ (d : ℕ) (K : Type) [Field K] [Finite K] (X : Subgroup (StatedSL d K)),
      IsComponentOf X ⊤ → X = ⊤ :=
    CFSG.LieType.SemisimpleCentralizers.Held.SLComponentsTrivial_holds
  have hCeq : Subgroup.centralizer ({A} : Set (GL (Fin n) F)) ⊓ StatedSL n F =
      ((StatedSL n F).comap θ).map θ := by
    ext x
    constructor
    · rintro ⟨hx1, hx2⟩
      have hxr : x ∈ θ.range := by
        rw [hθrange, hcent]
        exact hx1
      obtain ⟨w, rfl⟩ := MonoidHom.mem_range.mp hxr
      exact Subgroup.mem_map.mpr ⟨w, hx2, rfl⟩
    · intro hx
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hx
      refine ⟨?_, hw⟩
      rw [← hcent, ← hθrange]
      exact MonoidHom.mem_range.mpr ⟨w, rfl⟩
  have hMle : M ≤ θ.range := by
    intro x hx
    have hx1 := (hM.1 hx).1
    rw [hθrange, hcent]
    exact hx1
  have hMmap : (M.comap θ).map θ = M := by
    rw [Subgroup.map_comap_eq]
    exact inf_eq_right.mpr hMle
  have hM'comp : IsComponentOf (M.comap θ) ((StatedSL n F).comap θ) := by
    refine isComponentOf_of_map_injective θ hθinj ?_
    rw [hMmap, ← hCeq]
    exact hM
  have hM'top : IsComponentOf (M.comap θ) ⊤ :=
    isComponentOf_top_of_normal' hM'comp
  obtain ⟨i, hi⟩ := exists_factor_of_isComponentOf_top (H := fun k => GL (Fin (d k)) (D k)) hM'top
  have hcommS : ∀ a b : GL (Fin (d i)) (D i), ⁅a, b⁆ ∈ StatedSL (d i) (D i) :=
    fun a b => commutatorElement_mem_statedSL a b
  have hms : Function.Injective (MonoidHom.mulSingle (fun k => GL (Fin (d k)) (D k)) i) := by
    intro a b hab
    have := congrFun hab i
    simpa [MonoidHom.mulSingle_apply] using this
  have hM'T : M.comap θ ≤ (StatedSL (d i) (D i)).map
      (MonoidHom.mulSingle (fun k => GL (Fin (d k)) (D k)) i) := by
    have h1 := commutator_eq_self_of_isComponentOf_top hM'top
    have h2 := Subgroup.commutator_mono hi hi
    rw [h1] at h2
    exact h2.trans (commutator_factorSub_le (H := fun k => GL (Fin (d k)) (D k))
      (StatedSL (d i) (D i)) hcommS)
  have hTeq : M.comap θ = (StatedSL (d i) (D i)).map
      (MonoidHom.mulSingle (fun k => GL (Fin (d k)) (D k)) i) := by
    have hX : IsComponentOf ((M.comap θ).subgroupOf _) ⊤ :=
      CFSG.ComponentClassification.LocalComponents.of_overgroup hM'top hM'T
    let e : ↥((StatedSL (d i) (D i)).map
        (MonoidHom.mulSingle (fun k => GL (Fin (d k)) (D k)) i)) ≃*
        ↥(StatedSL (d i) (D i)) :=
      (Subgroup.equivMapOfInjective (StatedSL (d i) (D i))
        (MonoidHom.mulSingle (fun k => GL (Fin (d k)) (D k)) i) hms).symm
    have hXe := (CFSG.ComponentClassification.LocalComponents.equiv_iff e _).2 hX
    have htop := hSL' (d i) (D i) _ hXe
    have hXtop : (M.comap θ).subgroupOf _ = ⊤ := eq_top_of_map_equiv_eq_top e _ htop
    exact le_antisymm hM'T (Subgroup.subgroupOf_eq_top.mp hXtop)
  have hMeq : M = (((StatedSL (d i) (D i)).map
      (MonoidHom.mulSingle (fun k => GL (Fin (d k)) (D k)) i))).map θ := by
    rw [← hTeq, hMmap]
  have hd2 : 2 ≤ d i := by
    by_contra hlt
    push Not at hlt
    have hall : ∀ a ∈ M, a = 1 := by
      intro a ha
      rw [hMeq] at ha
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      have hy1 := eq_one_of_mem_statedSL_of_le_one (by omega) hy
      rw [hy1, map_one, map_one]
    exact not_isQuasisimple_of_comm
      (fun a b => Subtype.ext (by simp [hall a a.2, hall b b.2])) hM.2.2
  refine ⟨r, D, d, hFld, hFin, hAlg, Φ, θ, ?_, hΦinj, hθinj, hθrange.trans hcent, hθapply,
    ⟨i, hd2, hMeq⟩⟩
  exact fun k => Nat.succ_le_of_lt (Nat.pos_of_ne_zero (hNZ k).out)

end CFSG.LocalAnalysis.GLTheoremA.K1419
