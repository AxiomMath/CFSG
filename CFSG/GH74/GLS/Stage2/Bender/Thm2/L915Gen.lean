module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915Comp
public import CFSG.GroupTheory.LocalCores.Layer

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.L915

open Subgroup CFSG
open scoped commutatorElement

variable {Y : Type} [Group Y]

theorem commutator_eq_bot_of_commutator_le_centralizer {P X : Subgroup Y} (hP : Group.IsPerfect ↥P)
    (h : ⁅P, X⁆ ≤ centralizer (P : Set Y)) : ⁅P, X⁆ = ⊥ :=
  CFSG.LocalCores.perfect_double_commutator hP (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr h)

theorem le_centralizer_of_commutator_le_centralizer {P X : Subgroup Y} (hP : Group.IsPerfect ↥P)
    (h : ⁅P, X⁆ ≤ centralizer (P : Set Y)) : X ≤ centralizer (P : Set Y) := by
  have h1 := commutator_eq_bot_of_commutator_le_centralizer hP h
  rw [Subgroup.commutator_comm] at h1
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1

section Finite

variable [Finite Y]

theorem pCore_le_centralizer_component {p : ℕ} (hp : p.Prime) {J : Subgroup Y} (hJ : IsComponent J) :
    pCore p Y ≤ centralizer (J : Set Y) := by
  have : Fact p.Prime := ⟨hp⟩
  have h1 : ⁅fittingSubgroup Y, layer Y⁆ = ⊥ := CFSG.LocalCores.fitting_layer_commute
  have h2 : pCore p Y ≤ fittingSubgroup Y := CFSG.pCore_le_fitting Y p
  exact (h2.trans (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1)).trans
    (Subgroup.centralizer_le (CFSG.LocalCores.component_le_layer hJ))

theorem mem_normalizer_of_image {p : ℕ} (hp : p.Prime) {J : Subgroup Y} (hJ : IsComponent J) {a : Y}
    (ha : QuotientGroup.mk' (pCore p Y) a ∈
      normalizer ((J.map (QuotientGroup.mk' (pCore p Y)) : Subgroup (Y ⧸ pCore p Y)) :
        Set (Y ⧸ pCore p Y))) :
    a ∈ normalizer (J : Set Y) := by
  have : Fact p.Prime := ⟨hp⟩
  have hπJ : IsComponent (J.map (QuotientGroup.mk' (pCore p Y))) :=
    isComponent_map_mk hp CFSG.pCore_normal hJ CFSG.pCore_isPGroup
  have hJc : IsComponent (J.map (MulAut.conj a).toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj a) hJ
  rcases CFSG.LocalCores.distinct_components_commute hJ hJc with h | h
  · rw [mem_normalizer_iff_map_conj_eq]
    exact h.symm
  · exfalso
    have hmapJ : (J.map (MulAut.conj a).toMonoidHom).map (QuotientGroup.mk' (pCore p Y)) =
        J.map (QuotientGroup.mk' (pCore p Y)) := by
      rw [Subgroup.map_map]
      have hcomp : (QuotientGroup.mk' (pCore p Y)).comp (MulAut.conj a).toMonoidHom =
          (MulAut.conj (QuotientGroup.mk' (pCore p Y) a)).toMonoidHom.comp
            (QuotientGroup.mk' (pCore p Y)) := by
        ext x
        simp
      rw [hcomp, ← Subgroup.map_map]
      exact mem_normalizer_iff_map_conj_eq.mp ha
    have hcomm : ⁅J.map (QuotientGroup.mk' (pCore p Y)), J.map (QuotientGroup.mk' (pCore p Y))⁆ = ⊥ := by
      have := Subgroup.map_commutator J (J.map (MulAut.conj a).toMonoidHom) (QuotientGroup.mk' (pCore p Y))
      rw [h, Subgroup.map_bot, hmapJ] at this
      exact this.symm
    have hperf : ⁅J.map (QuotientGroup.mk' (pCore p Y)), J.map (QuotientGroup.mk' (pCore p Y))⁆ =
        J.map (QuotientGroup.mk' (pCore p Y)) := Subgroup.isPerfect_iff.mp hπJ.1.1
    rw [hcomm] at hperf
    have hnt := CFSG.LocalCores.isQuasisimple_nontrivial hπJ.1
    exact (Subgroup.nontrivial_iff_ne_bot _).mp hnt hperf.symm

theorem commute_of_normal_pgroup_of_normal_quasisimple {p : ℕ} (hp : p.Prime) {H U I : Subgroup Y}
    (hI : IsQuasisimple ↥I) (hIH : I ≤ H) (hIn : ∀ h ∈ H, h ∈ normalizer (I : Set Y))
    (hUH : U ≤ H) (hUn : ∀ h ∈ H, h ∈ normalizer (U : Set Y)) (hU : IsPGroup p ↥U) :
    U ≤ centralizer (I : Set Y) := by
  have hnorm : ((I ⊓ U).subgroupOf I).Normal := by
    refine ⟨fun x hx i => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    refine ⟨?_, ?_⟩
    · exact mul_mem (mul_mem i.2 hx.1) (I.inv_mem i.2)
    · have h1 := (mem_normalizer_iff.mp (hUn i (hIH i.2)) (x : Y)).mp hx.2
      simpa using h1
  have hperf : Group.IsPerfect ↥I := hI.1
  have hcen : ∀ i ∈ I, ∀ u ∈ U, ⁅i, u⁆ ∈ centralizer (I : Set Y) := by
    intro i hi u hu
    have hiI : ⁅i, u⁆ ∈ I := by
      rw [commutatorElement_def]
      have h1 := (mem_normalizer_iff.mp (hIn u (hUH hu)) i).mp hi
      have h2 : u * i⁻¹ * u⁻¹ ∈ I := by
        have := (mem_normalizer_iff.mp (hIn u (hUH hu)) i⁻¹).mp (inv_mem hi)
        exact this
      have he : i * u * i⁻¹ * u⁻¹ = i * (u * i⁻¹ * u⁻¹) := by group
      rw [he]
      exact mul_mem hi h2
    have hiU : ⁅i, u⁆ ∈ U := by
      rw [commutatorElement_def]
      have h1 : i * u * i⁻¹ ∈ U := (mem_normalizer_iff.mp (hUn i (hIH hi)) u).mp hu
      exact mul_mem h1 (inv_mem hu)
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hI hnorm with htop | hle
    · exfalso
      refine not_quasisimple_of_pgroup hp hI (hU.to_le ?_)
      intro x hx
      have : (⟨x, hx⟩ : ↥I) ∈ (I ⊓ U).subgroupOf I := htop ▸ Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.mp this).2
    · have hmem : (⟨⁅i, u⁆, hiI⟩ : ↥I) ∈ Subgroup.center ↥I :=
        hle (Subgroup.mem_subgroupOf.mpr ⟨hiI, hiU⟩)
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      have := Subgroup.mem_center_iff.mp hmem ⟨j, hj⟩
      simpa [Subgroup.coe_mul] using congrArg Subtype.val this
  refine le_centralizer_of_commutator_le_centralizer hperf ?_
  refine Subgroup.commutator_le.mpr fun i hi u hu => hcen i hi u hu

end Finite

@[expose] def centerLayerTwo (Y : Type) [Group Y] : Subgroup Y where
  carrier := {x | x ∈ layer Y ∧ (∀ l ∈ layer Y, x * l = l * x) ∧ x * x = 1}
  one_mem' := ⟨one_mem _, fun l _ => by simp, by simp⟩
  mul_mem' := by
    rintro a b ⟨haL, hac, ha2⟩ ⟨hbL, hbc, hb2⟩
    refine ⟨mul_mem haL hbL, fun l hl => ?_, ?_⟩
    · rw [mul_assoc, hbc l hl, ← mul_assoc, hac l hl, mul_assoc]
    · have hab : a * b = b * a := hac b hbL
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [hab]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [ha2, hb2, one_mul]
  inv_mem' := by
    rintro a ⟨haL, hac, ha2⟩
    refine ⟨(layer Y).inv_mem haL, fun l hl => ?_, ?_⟩
    · have h1 := hac l hl
      calc a⁻¹ * l = a⁻¹ * (l * a) * a⁻¹ := by group
        _ = a⁻¹ * (a * l) * a⁻¹ := by rw [h1]
        _ = l * a⁻¹ := by group
    · have : a⁻¹ = a := by
        calc a⁻¹ = a⁻¹ * (a * a) := by rw [ha2, mul_one]
          _ = a := by group
      rw [this, ha2]

section Finite2

variable [Finite Y]

omit [Finite Y] in
theorem centerLayerTwo_normal : (centerLayerTwo Y).Normal := by
  refine ⟨fun x hx y => ?_⟩
  obtain ⟨hxL, hxc, hx2⟩ := hx
  have hLn : (layer Y).Normal :=
    haveI := CFSG.LocalCores.layer_characteristic (G := Y)
    inferInstance
  refine ⟨hLn.conj_mem x hxL y, fun l hl => ?_, ?_⟩
  · have hl' : y⁻¹ * l * y ∈ layer Y := by
      have := hLn.conj_mem l hl y⁻¹
      simpa using this
    have h1 := hxc _ hl'
    calc y * x * y⁻¹ * l = y * (x * (y⁻¹ * l * y)) * y⁻¹ := by group
      _ = y * ((y⁻¹ * l * y) * x) * y⁻¹ := by rw [h1]
      _ = l * (y * x * y⁻¹) := by group
  · calc y * x * y⁻¹ * (y * x * y⁻¹) = y * (x * x) * y⁻¹ := by group
      _ = 1 := by rw [hx2]; group

omit [Finite Y] in
theorem centerLayerTwo_isPGroup : IsPGroup 2 ↥(centerLayerTwo Y) := by
  intro x
  refine ⟨1, ?_⟩
  apply Subtype.ext
  have := x.2.2.2
  simpa [pow_two] using this

theorem false_of_central_involution {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {J : Subgroup Y}
    (hJ : IsComponent J) (h2 : pCore 2 Y = ⊥) {t : Y ⧸ pCore p Y}
    (ht : t ∈ J.map (QuotientGroup.mk' (pCore p Y)))
    (htc : ∀ x ∈ J.map (QuotientGroup.mk' (pCore p Y)), t * x = x * t) (ht2 : t * t = 1)
    (ht1 : t ≠ 1) : False := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨j, hjJ, hjt⟩ := ht
  have hOJ := pCore_le_centralizer_component hp hJ
  have hJperf : Group.IsPerfect ↥J := hJ.1.1
  have hjc : j ∈ centralizer (J : Set Y) := by
    have hcomm : ⁅J, zpowers j⁆ ≤ centralizer (J : Set Y) := by
      refine Subgroup.commutator_le.mpr fun x hx g hg => ?_
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      have hπg : QuotientGroup.mk' (pCore p Y) (j ^ k) = t ^ k := by rw [map_zpow, hjt]
      have hx' : QuotientGroup.mk' (pCore p Y) x ∈ J.map (QuotientGroup.mk' (pCore p Y)) :=
        ⟨x, hx, rfl⟩
      have hc : Commute t (QuotientGroup.mk' (pCore p Y) x) := htc _ hx'
      have hπc : QuotientGroup.mk' (pCore p Y) ⁅x, j ^ k⁆ = 1 := by
        rw [map_commutatorElement, hπg, commutatorElement_eq_one_iff_mul_comm]
        exact (hc.zpow_left k).eq.symm
      have hmem : ⁅x, j ^ k⁆ ∈ pCore p Y := (QuotientGroup.eq_one_iff _).mp hπc
      exact hOJ hmem
    exact le_centralizer_of_commutator_le_centralizer hJperf hcomm (Subgroup.mem_zpowers j)
  have hjj : j * j ∈ pCore p Y := by
    have h1 : QuotientGroup.mk' (pCore p Y) (j * j) = 1 := by rw [map_mul, hjt, ht2]
    exact (QuotientGroup.eq_one_iff _).mp h1
  obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (G := Y) (p := p)) ⟨j * j, hjj⟩
  have hn' : (j * j) ^ (p ^ n) = 1 := congrArg Subtype.val hn
  set j' : Y := j ^ (p ^ n) with hj'
  have hj'2 : j' * j' = 1 := by
    rw [hj', ← (Commute.refl j).mul_pow]
    exact hn'
  have hpodd : Odd (p ^ n) := (hp.odd_of_ne_two hp2).pow
  have hπj' : QuotientGroup.mk' (pCore p Y) j' = t := by
    obtain ⟨m, hm⟩ := hpodd
    rw [hj', map_pow, hjt, hm, pow_succ, pow_mul, pow_two, ht2, one_pow, one_mul]
  have hj'J : j' ∈ J := Subgroup.pow_mem J hjJ _
  have hj'c : j' ∈ centralizer (J : Set Y) := Subgroup.pow_mem _ hjc _
  have hlayer : layer Y ≤ centralizer ({j'} : Set Y) := by
    refine sSup_le fun L hL => ?_
    rcases CFSG.LocalCores.distinct_components_commute hL hJ with rfl | hLJ
    · intro l hl
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hj'c l hl
    · intro l hl
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hl' : l ∈ centralizer (J : Set Y) := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hLJ hl
      exact (Subgroup.mem_centralizer_iff.mp hl' j' hj'J).symm
  have hj'T : j' ∈ centerLayerTwo Y := by
    refine ⟨CFSG.LocalCores.component_le_layer hJ hj'J, fun l hl => ?_, hj'2⟩
    have := Subgroup.mem_centralizer_singleton_iff.mp (hlayer hl)
    exact this.symm
  have hle : centerLayerTwo Y ≤ pCore 2 Y :=
    le_sSup ⟨centerLayerTwo_normal, centerLayerTwo_isPGroup⟩
  have hbot : j' = 1 := by
    have := hle hj'T
    rw [h2, Subgroup.mem_bot] at this
    exact this
  apply ht1
  rw [← hπj', hbot, map_one]

end Finite2

end CFSG.GH74.GLS.Stage2.Bender.Thm2.L915
