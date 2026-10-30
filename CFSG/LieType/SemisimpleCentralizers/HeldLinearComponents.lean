module

public import CFSG.LieType.SemisimpleCentralizers.HeldSLFacts
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGSLBasic

public section

namespace CFSG.LieType.SemisimpleCentralizers.Held

open CFSG.Open CFSG.Open.StatedAPI CFSG.StandardType.LinNonsplit Matrix
open scoped commutatorElement

section Product

variable {ι : Type} [Fintype ι] [DecidableEq ι] {H : ι → Type} [∀ i, Group (H i)]

def factorSub (i : ι) : Subgroup (∀ j, H j) where
  carrier := {w | ∀ j, j ≠ i → w j = 1}
  mul_mem' := fun {a b} ha hb j hj => by simp [ha j hj, hb j hj]
  one_mem' := fun j _ => rfl
  inv_mem' := fun {a} ha j hj => by simp [ha j hj]

theorem mem_factorSub {i : ι} {w : ∀ j, H j} : w ∈ factorSub i ↔ ∀ j, j ≠ i → w j = 1 :=
  Iff.rfl

instance factorSub_normal (i : ι) : (factorSub (H := H) i).Normal where
  conj_mem n hn g := fun j hj => by simp [mem_factorSub.mp hn j hj]

theorem eq_mulSingle_of_mem_factorSub {i : ι} {w : ∀ j, H j} (hw : w ∈ factorSub i) :
    w = MonoidHom.mulSingle H i (w i) := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp
  · simp [MonoidHom.mulSingle_apply, Pi.mulSingle_apply, hj, hw j hj]

theorem commutator_factorSub_le {i : ι} (S : Subgroup (H i)) (hS : ∀ a b : H i, ⁅a, b⁆ ∈ S) :
    ⁅factorSub (H := H) i, factorSub (H := H) i⁆ ≤ S.map (MonoidHom.mulSingle H i) := by
  refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
  rw [eq_mulSingle_of_mem_factorSub hx, eq_mulSingle_of_mem_factorSub hy,
    ← map_commutatorElement]
  exact Subgroup.mem_map.mpr ⟨_, hS _ _, rfl⟩

theorem not_isQuasisimple_of_comm {Γ : Type*} [Group Γ] (h : ∀ a b : Γ, a * b = b * a) :
    ¬ CFSG.Open.IsQuasisimple Γ := by
  intro hq
  have hsimple : IsSimpleGroup (Γ ⧸ Subgroup.center Γ) := hq.2
  obtain ⟨q, hq1⟩ := exists_ne (1 : Γ ⧸ Subgroup.center Γ)
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
  apply hq1
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
  exact fun g => h g a

theorem exists_factor_of_isComponentOf_top [Finite ι] [∀ i, Finite (H i)]
    {J : Subgroup (∀ j, H j)} (hJ : IsComponentOf J ⊤) : ∃ i, J ≤ factorSub (H := H) i := by
  by_contra hcon
  push Not at hcon
  have hcomm : ∀ i, ⁅J, factorSub (H := H) i⁆ = ⊥ := fun i =>
    (CFSG.ComponentClassification.LocalComponents.normal_contains_or_commutes J
      (factorSub (H := H) i) hJ).resolve_left (hcon i)
  have hcent : ∀ x ∈ J, ∀ w : ∀ j, H j, x * w = w * x := by
    intro x hx w
    funext j
    have hc : J ≤ Subgroup.centralizer ((factorSub (H := H) j : Subgroup (∀ k, H k)) :
        Set (∀ k, H k)) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hcomm j)
    have hmem : MonoidHom.mulSingle H j (w j) ∈ factorSub j := by
      intro k hk
      simp [MonoidHom.mulSingle_apply, Pi.mulSingle_apply, hk]
    have h1 := Subgroup.mem_centralizer_iff.mp (hc hx) _ hmem
    have h2 := congrFun h1 j
    simpa [MonoidHom.mulSingle_apply, Pi.mulSingle_apply, eq_comm] using h2
  exact not_isQuasisimple_of_comm
    (fun a b => Subtype.ext (hcent a a.2 (b : ∀ j, H j))) hJ.2.2

end Product

theorem eq_one_of_mem_statedSL_of_le_one {E : Type} [Field E] {d : ℕ} (hd : d ≤ 1)
    {x : GL (Fin d) E} (hx : x ∈ StatedSL d E) : x = 1 := by
  rw [mem_statedSL_iff] at hx
  interval_cases d
  · exact Subsingleton.elim _ _
  · refine Units.ext (Matrix.ext fun a b => ?_)
    rw [Fin.fin_one_eq_zero a, Fin.fin_one_eq_zero b]
    simpa [Matrix.det_fin_one, Matrix.one_apply] using hx

theorem commutator_eq_self_of_isComponentOf_top {Γ : Type*} [Group Γ] {K : Subgroup Γ}
    (hK : IsComponentOf K ⊤) : ⁅K, K⁆ = K := by
  have hperf : Group.IsPerfect K := Group.isPerfect_def.mpr hK.2.2.1
  exact Subgroup.isPerfect_iff.mp hperf

theorem held_linear_components (hSL : SLComponentsTrivial) {F : Type} [Field F] [Finite F]
    {n : ℕ} (s : GL (Fin n) F) (_hs : s ∈ StatedSL n F) (hord : (orderOf s : F) ≠ 0)
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
    push Not at hlt
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

end CFSG.LieType.SemisimpleCentralizers.Held

end


