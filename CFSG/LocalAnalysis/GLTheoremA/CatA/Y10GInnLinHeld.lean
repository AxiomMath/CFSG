module

public import CFSG.LieType.SemisimpleCentralizers.HeldLinearComponents

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin

open CFSG.Open CFSG.Open.StatedAPI CFSG.StandardType.LinNonsplit Matrix
open scoped commutatorElement
open CFSG.LieType.SemisimpleCentralizers.Held

theorem held_linear_components_gl (hSL : SLComponentsTrivial) {F : Type} [Field F] [Finite F]
    {n : ℕ} (s : GL (Fin n) F) (hord : (orderOf s : F) ≠ 0)
    (J : Subgroup (GL (Fin n) F))
    (hJ : IsComponentOf J (Subgroup.centralizer ({s} : Set (GL (Fin n) F)) ⊓ StatedSL n F)) :
    ∃ (a : ℕ) (E : Type) (_ : Field E) (_ : Algebra F E) (_ : Finite E), 2 ≤ a ∧
      Nonempty (J ⧸ Subgroup.center J ≃* StatedProj (StatedSL a E)) := by
  have hA : (Nat.card (Subgroup.zpowers s) : F) ≠ 0 := by
    rw [Nat.card_zpowers]
    exact hord
  obtain ⟨r, D, d, hFld, hFin, hAlg, Φ, θ, _hNZ, _hΦinj, _hΦrange, hθinj, hθrange, _hθapply⟩ :=
    exists_piMat_commutant (Subgroup.zpowers s) hA
  letI : ∀ i, Field (D i) := hFld
  haveI : ∀ i, Finite (D i) := hFin
  have hcent : Subgroup.centralizer ((Subgroup.zpowers s : Subgroup (GL (Fin n) F)) :
      Set (GL (Fin n) F)) = Subgroup.centralizer ({s} : Set (GL (Fin n) F)) := by
    ext g
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro hg h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact hg _ (Subgroup.mem_zpowers _)
    · intro hg h hh
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      have hc : Commute s g := hg s (Set.mem_singleton s)
      exact (hc.zpow_left k).eq
  have hSL' : ∀ (d : ℕ) (K : Type) [Field K] [Finite K] (X : Subgroup (StatedSL d K)),
      IsComponentOf X ⊤ → X = ⊤ := hSL
  have hCeq : Subgroup.centralizer ({s} : Set (GL (Fin n) F)) ⊓ StatedSL n F =
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
  have hJle : J ≤ θ.range := by
    intro x hx
    have hx1 := (hJ.1 hx).1
    rw [hθrange, hcent]
    exact hx1
  have hJmap : (J.comap θ).map θ = J := by
    rw [Subgroup.map_comap_eq]
    exact inf_eq_right.mpr hJle
  have hJ'comp : IsComponentOf (J.comap θ) ((StatedSL n F).comap θ) := by
    refine isComponentOf_of_map_injective θ hθinj ?_
    rw [hJmap, ← hCeq]
    exact hJ
  have hJ'top : IsComponentOf (J.comap θ) ⊤ :=
    isComponentOf_top_of_normal' hJ'comp
  obtain ⟨i, hi⟩ := exists_factor_of_isComponentOf_top (H := fun k => GL (Fin (d k)) (D k)) hJ'top
  have hcommS : ∀ a b : GL (Fin (d i)) (D i), ⁅a, b⁆ ∈ StatedSL (d i) (D i) :=
    fun a b => commutatorElement_mem_statedSL a b
  have hms : Function.Injective (MonoidHom.mulSingle (fun k => GL (Fin (d k)) (D k)) i) := by
    intro a b hab
    have := congrFun hab i
    simpa [MonoidHom.mulSingle_apply] using this
  have hJ'T : J.comap θ ≤ (StatedSL (d i) (D i)).map
      (MonoidHom.mulSingle (fun k => GL (Fin (d k)) (D k)) i) := by
    have h1 := commutator_eq_self_of_isComponentOf_top hJ'top
    have h2 := Subgroup.commutator_mono hi hi
    rw [h1] at h2
    exact h2.trans (commutator_factorSub_le (H := fun k => GL (Fin (d k)) (D k))
      (StatedSL (d i) (D i)) hcommS)
  have hTeq : J.comap θ = (StatedSL (d i) (D i)).map
      (MonoidHom.mulSingle (fun k => GL (Fin (d k)) (D k)) i) := by
    have hX : IsComponentOf ((J.comap θ).subgroupOf _) ⊤ :=
      CFSG.ComponentClassification.LocalComponents.of_overgroup hJ'top hJ'T
    let e : ↥((StatedSL (d i) (D i)).map (MonoidHom.mulSingle (fun k => GL (Fin (d k)) (D k)) i)) ≃*
        ↥(StatedSL (d i) (D i)) :=
      (Subgroup.equivMapOfInjective (StatedSL (d i) (D i))
        (MonoidHom.mulSingle (fun k => GL (Fin (d k)) (D k)) i) hms).symm
    have hXe := (CFSG.ComponentClassification.LocalComponents.equiv_iff e _).2 hX
    have htop := hSL' (d i) (D i) _ hXe
    have hXtop : (J.comap θ).subgroupOf _ = ⊤ := eq_top_of_map_equiv_eq_top e _ htop
    exact le_antisymm hJ'T (Subgroup.subgroupOf_eq_top.mp hXtop)
  have hJeq : J = (((StatedSL (d i) (D i)).map
      (MonoidHom.mulSingle (fun k => GL (Fin (d k)) (D k)) i))).map θ := by
    rw [← hTeq, hJmap]
  have hd2 : 2 ≤ d i := by
    by_contra hlt
    push_neg at hlt
    have hall : ∀ a ∈ J, a = 1 := by
      intro a ha
      rw [hJeq] at ha
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      have hy1 := eq_one_of_mem_statedSL_of_le_one (by omega) hy
      rw [hy1, map_one, map_one]
    exact not_isQuasisimple_of_comm
      (fun a b => Subtype.ext (by simp [hall a a.2, hall b b.2])) hJ.2.2
  have eJ : ↥J ≃* ↥(StatedSL (d i) (D i)) :=
    (MulEquiv.subgroupCongr hJeq).trans
      ((Subgroup.equivMapOfInjective _ θ hθinj).symm.trans
        (Subgroup.equivMapOfInjective (StatedSL (d i) (D i))
          (MonoidHom.mulSingle (fun k => GL (Fin (d k)) (D k)) i) hms).symm)
  exact ⟨d i, D i, hFld i, hAlg i, hFin i, hd2, nonempty_quotientCenter_equiv_statedProj eJ⟩

end CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin

end
