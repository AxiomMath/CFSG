module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015Transport
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T2021

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.I2015

section Conv

variable {G : Type} [Group G]

theorem glaPLayer_eq_sSup {p : ℕ} (X : Subgroup G) :
    GLAPLayer p X = sSup {L | GLAPComponent p X L} := rfl

theorem glaPPrimeCoreOf_eq_map {p : ℕ} (H : Subgroup G) :
    GLAPPrimeCoreOf p H = (GLAPPrimeCore p ↥H).map H.subtype := rfl

theorem subgroupOf_map_subtype_self {J : Subgroup G} (Y : Subgroup ↥J) :
    (Y.map J.subtype).subgroupOf J = Y := by
  ext x
  rw [Subgroup.mem_subgroupOf]
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx
    have : y = x := Subtype.ext hyx
    rw [← this]
    exact hy
  · intro hx
    exact Subgroup.mem_map.2 ⟨x, hx, rfl⟩

theorem glaPComponent_of_subgroupOf {p : ℕ} {J A : Subgroup G} {Y : Subgroup ↥J} (hAJ : A ≤ J)
    (h : GLAPComponent p (A.subgroupOf J) Y) : GLAPComponent p A (Y.map J.subtype) := by
  unfold GLAPComponent at h ⊢
  obtain ⟨hYX, hsub, hcomp, hmin⟩ := h
  let e : ↥(A.subgroupOf J) ≃* ↥A := Subgroup.subgroupOfEquivOfLe hAJ
  let Q : ↥(A.subgroupOf J) ⧸ GLAPPrimeCore p ↥(A.subgroupOf J) ≃*
      ↥A ⧸ GLAPPrimeCore p ↥A :=
    QuotientGroup.congr _ _ e (map_primeCore_subgroupOf hAJ)
  have hfun : Q.toMonoidHom.comp (QuotientGroup.mk' (GLAPPrimeCore p ↥(A.subgroupOf J))) =
      (QuotientGroup.mk' (GLAPPrimeCore p ↥A)).comp e.toMonoidHom := by
    ext x
    exact QuotientGroup.congr_mk _ _ e (map_primeCore_subgroupOf hAJ) x
  have hcomp_map : ∀ Z : Subgroup ↥J,
      ((Z.subgroupOf (A.subgroupOf J)).map (QuotientGroup.mk' (GLAPPrimeCore p ↥(A.subgroupOf J)))).map
          Q.toMonoidHom =
        ((Z.map J.subtype).subgroupOf A).map (QuotientGroup.mk' (GLAPPrimeCore p ↥A)) := by
    intro Z
    rw [Subgroup.map_map, ← map_subgroupOf_equiv hAJ Z, Subgroup.map_map, hfun]
  have hYA : Y.map J.subtype ≤ A := by
    have h1 : Y.map J.subtype ≤ (A.subgroupOf J).map J.subtype := Subgroup.map_mono hYX
    rwa [Subgroup.map_subgroupOf_eq_of_le hAJ] at h1
  refine ⟨hYA, ?_, ?_, ?_⟩
  · rw [isSubnormal_subgroupOf_iff hYA hAJ, subgroupOf_map_subtype_self]
    exact hsub
  · have h1 := (isComponentOf_top_iff_map Q _).1 hcomp
    rw [hcomp_map Y] at h1
    exact h1
  · intro K hKlt hKsub heq
    have hKA : K ≤ A := hKlt.le.trans hYA
    have hKJ : (K.subgroupOf J).map J.subtype = K := Subgroup.map_subgroupOf_eq_of_le (hKA.trans hAJ)
    have hK'Y : K.subgroupOf J ≤ Y := by
      intro x hx
      have hx' : (x : G) ∈ K := by
        rw [Subgroup.mem_subgroupOf] at hx
        exact hx
      have hxY : (x : G) ∈ Y.map J.subtype := hKlt.le hx'
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hxY
      have : y = x := Subtype.ext hyx
      rw [← this]
      exact hy
    have hK'lt : K.subgroupOf J < Y := by
      refine lt_of_le_of_ne hK'Y (fun heq' => hKlt.ne ?_)
      rw [← hKJ, heq']
    have hK'sub : IsSubnormal (K.subgroupOf J) (A.subgroupOf J) :=
      (isSubnormal_subgroupOf_iff hKA hAJ).1 hKsub
    have hM : (((K.subgroupOf J).subgroupOf (A.subgroupOf J)).map
        (QuotientGroup.mk' (GLAPPrimeCore p ↥(A.subgroupOf J)))) =
        (((Y).subgroupOf (A.subgroupOf J)).map (QuotientGroup.mk' (GLAPPrimeCore p ↥(A.subgroupOf J)))) := by
      apply Subgroup.map_injective (f := Q.toMonoidHom) Q.injective
      rw [hcomp_map (K.subgroupOf J), hKJ, heq, ← hcomp_map Y]
    exact hmin (K.subgroupOf J) hK'lt hK'sub hM

theorem map_glaPLayer_subgroupOf_le {p : ℕ} {J A : Subgroup G} (hAJ : A ≤ J) :
    (GLAPLayer p (A.subgroupOf J)).map J.subtype ≤ GLAPLayer p A := by
  rw [glaPLayer_eq_sSup, glaPLayer_eq_sSup, Subgroup.map_le_iff_le_comap]
  refine sSup_le (fun Y hY => ?_)
  rw [← Subgroup.map_le_iff_le_comap]
  exact le_sSup (glaPComponent_of_subgroupOf hAJ hY)

theorem map_glaPPrimeCoreOf_subgroupOf {p : ℕ} {J A : Subgroup G} (hAJ : A ≤ J) :
    (GLAPPrimeCoreOf p (A.subgroupOf J)).map J.subtype = GLAPPrimeCoreOf p A := by
  rw [glaPPrimeCoreOf_eq_map, glaPPrimeCoreOf_eq_map, Subgroup.map_map]
  have hcomp : J.subtype.comp (A.subgroupOf J).subtype =
      A.subtype.comp (Subgroup.subgroupOfEquivOfLe hAJ).toMonoidHom := by
    ext x
    rfl
  rw [hcomp, ← Subgroup.map_map, map_primeCore_subgroupOf hAJ]

end Conv

end CFSG.LocalAnalysis.GLTheoremA.T2021

end
