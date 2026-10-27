module

public import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.GroupTheory.PCore.PrimeSetCore
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K136Layer
import CFSG.SignalizerFunctorTheorem.Inheritance.TransportA.Fitting

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Subgroup
open scoped commutatorElement

section Layer

variable {Y : Type*} [Group Y] [Finite Y]

theorem eq_bot_of_layer_le_normalizer {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hY : CFSG.pPrimeCore p Y = ⊥) {T : Subgroup Y} (hT : IsPGroup 2 T)
    (hE : CFSG.layer Y ≤ normalizer (T : Set Y))
    (hP : T ≤ centralizer (CFSG.pCore p Y : Set Y)) : T = ⊥ := by
  classical
  rw [CFSG.layer_eq_componentClassification] at hE
  obtain ⟨E, hEdef⟩ : ∃ E : Subgroup Y, E = CFSG.ComponentClassification.Layer.subgroup Y :=
    ⟨_, rfl⟩
  rw [← hEdef] at hE
  have hEnorm : E.Normal := hEdef ▸ CFSG.ComponentClassification.Layer.normal Y
  have hE' : ∀ e ∈ E, ∀ t ∈ T, e * t * e⁻¹ ∈ T := fun e he t ht =>
    ((mem_normalizer_iff.mp (hE he) t).mp ht)
  have hdisj : Disjoint T (CFSG.pCore p Y) :=
    IsPGroup.disjoint_of_ne 2 p (Ne.symm hp2) T _ hT CFSG.pCore_isPGroup
  have hFit : CFSG.fittingSubgroup Y = CFSG.pCore p Y := CFSG.Fitting_eq_pcore Y p hY
  obtain ⟨R, hRdef⟩ : ∃ R : Subgroup Y, R = T ⊓ E := ⟨_, rfl⟩
  have hRmem : ∀ x, x ∈ R ↔ x ∈ T ∧ x ∈ E := fun x => by rw [hRdef, mem_inf]
  have hR2 : IsPGroup 2 R := hT.to_le (hRdef ▸ inf_le_left)
  haveI : Group.IsNilpotent R := hR2.isNilpotent
  haveI : Group.IsSolvable R := inferInstance
  have hRsub : R.IsSubnormal := by
    refine Subgroup.IsSubnormal.step R E (hRdef ▸ inf_le_right) hEnorm.isSubnormal ?_
    refine ⟨fun n hn g => ?_⟩
    rw [mem_subgroupOf, hRmem] at hn ⊢
    exact ⟨hE' g g.2 n hn.1, hEnorm.conj_mem n hn.2 g⟩
  have hcomm : ⁅E, R⁆ = ⊥ := by
    rw [hEdef]
    exact CFSG.ComponentClassification.Layer.commutes_with_solvable_subnormal R
      (CFSG.ComponentClassification.Components.chain_of_mathlib_subnormal hRsub)
  have hRbot : R = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall R).mpr fun t ht => ?_
    obtain ⟨htT, htE⟩ := (hRmem t).mp ht
    have hcen : (⟨t, htE⟩ : ↥E) ∈ Subgroup.center ↥E := by
      rw [Subgroup.mem_center_iff]
      intro e
      have h2 : ⁅(e : Y), t⁆ = 1 := by
        have := Subgroup.commutator_mem_commutator e.2 ht
        rw [hcomm, Subgroup.mem_bot] at this
        exact this
      exact Subtype.ext (commutatorElement_eq_one_iff_mul_comm.1 h2)
    have hF := CFSG.ComponentClassification.GeneralizedFitting.layer_center_le_fitting Y
    rw [← hEdef] at hF
    have hmem : t ∈ CFSG.ComponentClassification.Fitting.subgroup Y := hF ⟨⟨t, htE⟩, hcen, rfl⟩
    have hmem' : t ∈ CFSG.fittingSubgroup Y := hmem
    rw [hFit] at hmem'
    simpa using hdisj.le_bot ⟨htT, hmem'⟩
  have hTE : E ≤ centralizer (T : Set Y) := by
    intro e he
    rw [mem_centralizer_iff]
    intro t ht
    have h1 : t * e * t⁻¹ * e⁻¹ ∈ R := by
      rw [hRmem]
      refine ⟨?_, E.mul_mem (hEnorm.conj_mem e he t) (E.inv_mem he)⟩
      have := T.mul_mem ht (hE' e he t⁻¹ (T.inv_mem ht))
      simpa [mul_assoc] using this
    rw [hRbot, Subgroup.mem_bot] at h1
    exact (commutatorElement_eq_one_iff_mul_comm.1 h1)
  have hTF : T ≤ centralizer
      ((CFSG.ComponentClassification.GeneralizedFitting.subgroup Y : Subgroup Y) : Set Y) := by
    rw [Subgroup.le_centralizer_iff,
      CFSG.ComponentClassification.GeneralizedFitting.subgroup.eq_sup]
    refine sup_le ?_ (hEdef ▸ hTE)
    change CFSG.fittingSubgroup Y ≤ _
    rw [hFit]
    exact Subgroup.le_centralizer_iff.mp hP
  have hTP : T ≤ CFSG.pCore p Y := by
    intro t ht
    have h1 : t ∈ CFSG.ComponentClassification.Fitting.subgroup Y :=
      CFSG.ComponentClassification.GeneralizedFitting.centralizer_le_fitting Y (hTF ht)
    have h2 : t ∈ CFSG.fittingSubgroup Y := h1
    rwa [hFit] at h2
  exact hdisj.eq_bot_of_le hTP

end Layer

section PComponent

variable {X : Type*} [Group X] [Finite X]

theorem le_pLayer {p : ℕ} {L : Subgroup X} (hL : CFSG.IsPComponent p L) :
    L ≤ CFSG.pLayer X p :=
  le_sSup hL

theorem isComponent_map {A B : Type*} [Group A] [Group B] (e : A ≃* B) {K : Subgroup A}
    (hK : CFSG.IsComponent K) : CFSG.IsComponent (K.map e.toMonoidHom) := by
  rw [CFSG.isComponent_iff_open] at hK ⊢
  have h := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e hK
  rwa [Subgroup.map_top_of_surjective _ e.surjective] at h

theorem isPComponent_map (p : ℕ) (φ : X ≃* X) {L : Subgroup X} (hL : CFSG.IsPComponent p L) :
    CFSG.IsPComponent p (L.map φ.toMonoidHom) := by
  classical
  set O : Subgroup X := CFSG.pPrimeCore p X with hOdef
  have hO : O.map φ.toMonoidHom = O := CFSG.pPrimeCore_map_iso p φ
  set φb : X ⧸ O ≃* X ⧸ O := QuotientGroup.congr O O φ hO with hφb
  have hnat : ∀ J : Subgroup X, (J.map φ.toMonoidHom).map (QuotientGroup.mk' O) =
      (J.map (QuotientGroup.mk' O)).map φb.toMonoidHom := by
    intro J
    rw [Subgroup.map_map, Subgroup.map_map]
    rfl
  have hnat' : ∀ J : Subgroup X, (J.map φ.symm.toMonoidHom).map (QuotientGroup.mk' O) =
      (J.map (QuotientGroup.mk' O)).map φb.symm.toMonoidHom := by
    intro J
    rw [Subgroup.map_map, Subgroup.map_map]
    rfl
  have hcancel : ∀ K : Subgroup (X ⧸ O),
      (K.map φb.toMonoidHom).map φb.symm.toMonoidHom = K := by
    intro K
    ext y
    simp [Subgroup.mem_map]
  have hcancelX : ∀ J : Subgroup X,
      (J.map φ.toMonoidHom).map φ.symm.toMonoidHom = J := by
    intro J
    ext y
    simp [Subgroup.mem_map]
  have hcancelX' : ∀ J : Subgroup X,
      (J.map φ.symm.toMonoidHom).map φ.toMonoidHom = J := by
    intro J
    ext y
    simp [Subgroup.mem_map]
  obtain ⟨K, hK, hLsub, hLK, hmin⟩ := hL
  refine ⟨K.map φb.toMonoidHom, isComponent_map φb hK, hLsub.map φ.surjective,
    by rw [hnat, hLK], ?_⟩
  intro J hJ hJs hJK
  have hJ0 : J.map φ.symm.toMonoidHom < L := by
    have h : (J.map φ.symm.toMonoidHom).map φ.toMonoidHom < L.map φ.toMonoidHom := by
      rwa [hcancelX']
    exact (Subgroup.map_lt_map_iff_of_injective (f := φ.toMonoidHom) φ.injective).mp h
  refine hmin (J.map φ.symm.toMonoidHom) hJ0 (hJs.map φ.symm.surjective) ?_
  rw [hnat', hJK, hcancel]

theorem map_eq_bot_of_pComponents_normalize {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {A : Subgroup X} (hA : IsPGroup 2 A)
    (hP : A.map (QuotientGroup.mk' (CFSG.pPrimeCore p X)) ≤
      centralizer (CFSG.pCore p (X ⧸ CFSG.pPrimeCore p X) : Set (X ⧸ CFSG.pPrimeCore p X)))
    (hL : ∀ L : Subgroup X, CFSG.IsPComponent p L →
      L.map (QuotientGroup.mk' (CFSG.pPrimeCore p X)) ≤
        normalizer (A.map (QuotientGroup.mk' (CFSG.pPrimeCore p X)) :
          Set (X ⧸ CFSG.pPrimeCore p X))) :
    A.map (QuotientGroup.mk' (CFSG.pPrimeCore p X)) = ⊥ := by
  refine eq_bot_of_layer_le_normalizer hp2 (CFSG.pPrimeCore_quotient_eq_bot Fact.out)
    (hA.map _) ?_ hP
  rw [CFSG.layer.eq_sSup]
  refine sSup_le fun C hC => ?_
  obtain ⟨L, hLp, rfl⟩ :=
    RankThreeTheoremC.SmallRankE3.Parrott.P614.P614K136.exists_isPComponent_map_eq p hC
  exact hL L hLp

end PComponent

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
