module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.DerivedOf
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.A5Transfer
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.FiberCount
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.FiberLe
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.CBridgeB
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.LeCommutator

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3
open scoped commutatorElement

variable {G : Type} [Group G] {a z : G}

private lemma sq_eq_one_of_isConj {G : Type*} [Group G] {a c : G} (ha : orderOf a = 2)
    (hc : IsConj a c) : c ^ 2 = 1 := by
  have ha2 : a ^ 2 = 1 := by
    have h := pow_orderOf_eq_one a
    rwa [ha] at h
  have h1 : IsConj (a ^ 2) (c ^ 2) := hc.pow 2
  rw [ha2] at h1
  exact isConj_one_right.mp h1

private lemma barOf_sq_eq_one {G : Type} [Group G] {z c : G} (hc : c ∈ Gx z)
    (hc2 : c ^ 2 = 1) : (barOf z (⟨c, hc⟩ : ↥(Gx z))) ^ 2 = 1 := by
  have hc' : (⟨c, hc⟩ : ↥(Gx z)) ^ 2 = 1 := by
    apply Subtype.ext
    simpa using hc2
  change (QuotientGroup.mk (⟨c, hc⟩ : ↥(Gx z))) ^ 2 = 1
  rw [← QuotientGroup.mk_pow, hc', QuotientGroup.mk_one]

private theorem map_commutator_mk' (z : G) :
    (_root_.commutator ↥(Gx z)).map (QuotientGroup.mk' (CFSG.pCore 2 ↥(Gx z))) =
      _root_.commutator (Gbar z) := by
  rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]

private theorem barOf_not_mem_commutator' (h : F5Std a z) {c : G} (hcz : c ∈ Gx z)
    (hcQ : c ∉ Qz z) (hcA : IsConj a c) :
    barOf z (⟨c, hcz⟩ : ↥(Gx z)) ∉ _root_.commutator (Gbar z) := by
  classical
  haveI : Finite G := h.finite
  let Q : Subgroup ↥(Gx z) := CFSG.pCore 2 ↥(Gx z)
  have hQ : IsExtraspecialPlusByA5WrTwoWith ↥(Gx z) Q :=
    isExtraspecialPlusByA5WrTwoWith_pCore h.typ.cent_z
  have hOrb : GzOrbitFacts a z := h.loc.gzOrbit.self
  obtain ⟨e⟩ := nonempty_mulEquiv_Gbar h.typ
  have hc2 : c ^ 2 = 1 := sq_eq_one_of_isConj h.typ.orderOf_a hcA
  have hc'2 : (⟨c, hcz⟩ : ↥(Gx z)) ^ 2 = 1 := by
    apply Subtype.ext
    simpa using hc2
  have hcbar2 : (barOf z (⟨c, hcz⟩ : ↥(Gx z))) ^ 2 = 1 := barOf_sq_eq_one hcz hc2
  have hcbar1 : barOf z (⟨c, hcz⟩ : ↥(Gx z)) ≠ 1 := by
    intro h1
    exact hcQ (by simpa using (barOf_eq_one_iff (⟨c, hcz⟩ : ↥(Gx z))).mp h1)
  have hQcard : Nat.card ↥Q = 512 := by
    rw [hQ.plus.2.1]
    norm_num
  have hcentK : Nat.card ↥(Subgroup.centralizer ({(⟨c, hcz⟩ : ↥(Gx z))} : Set ↥(Gx z))) =
      3840 := by
    have h1 : Nat.card ↥(Subgroup.centralizer ({(⟨c, hcz⟩ : ↥(Gx z))} : Set ↥(Gx z))) =
        2 ^ 8 * 15 := by
      rw [← card_Gx_inf_eq hcz]
      exact hOrb.orbit_outA.2 c ⟨hcz, hcQ, hcA⟩
    rw [h1]
    norm_num
  have hcentBar : Nat.card ↥(Subgroup.centralizer
      ({((⟨c, hcz⟩ : ↥(Gx z)) : ↥(Gx z) ⧸ Q)} : Set (↥(Gx z) ⧸ Q))) =
      Nat.card ↥(CbarCent z (⟨c, hcz⟩ : ↥(Gx z))) := rfl
  have hfiber := card_fiber_mul_card_centralizer Q (⟨c, hcz⟩ : ↥(Gx z))
  have hFiberEq :
      Nat.card {s : ↥(Gx z) // (∃ k : ↥(Gx z), k * (⟨c, hcz⟩ : ↥(Gx z)) * k⁻¹ = s) ∧
        (s : ↥(Gx z) ⧸ Q) = ((⟨c, hcz⟩ : ↥(Gx z)) : ↥(Gx z) ⧸ Q)} * 3840 =
        512 * Nat.card ↥(CbarCent z (⟨c, hcz⟩ : ↥(Gx z))) := by
    rw [hQcard, hcentK, hcentBar] at hfiber
    exact hfiber
  have hζ : GxSelf z ∈ centerOf Q := by
    rw [centerOf_eq_zpowers h.typ.orderOf_z hQ]
    exact Subgroup.mem_zpowers (GxSelf z)
  have hne : ∀ k : ↥(Gx z), k * (⟨c, hcz⟩ : ↥(Gx z)) * k⁻¹ ≠
      (⟨c, hcz⟩ : ↥(Gx z)) * GxSelf z := by
    intro k hk
    have hkG : (k : G) * c * (k : G)⁻¹ = c * z := by
      have h := congrArg (fun t : ↥(Gx z) => (t : G)) hk
      simpa [GxSelf] using h
    have hconj : IsConj c (c * z) := isConj_iff.mpr ⟨(k : G), hkG⟩
    have hf3 : Fusion3Facts c z := h.loc.fusion3 c z hcA (IsConj.refl z)
    exact hcQ (hf3.shape_2AB z ⟨IsConj.refl z, hconj⟩).2
  have hlt := card_fiber_lt Q hQ.plus hc'2 hζ hne
  rcases involution_cases_of_mulEquiv e hcbar2 hcbar1 with
    ⟨hout, _⟩ | ⟨hin, hcard⟩ | ⟨_, hcard⟩
  · exact hout
  · exfalso
    have hF32 :
        Nat.card {s : ↥(Gx z) // (∃ k : ↥(Gx z), k * (⟨c, hcz⟩ : ↥(Gx z)) * k⁻¹ = s) ∧
          (s : ↥(Gx z) ⧸ Q) = ((⟨c, hcz⟩ : ↥(Gx z)) : ↥(Gx z) ⧸ Q)} = 32 := by
      rw [hcard] at hFiberEq
      omega
    have hcentQ :
        Nat.card {q : ↥(Gx z) // q ∈ Q ∧ ⁅q, (⟨c, hcz⟩ : ↥(Gx z))⁆ ∈ centerOf Q} = 32 := by
      have h1 : Nat.card (centQtilde z ((⟨c, hcz⟩ : ↥(Gx z)) : G)) = 2 ^ 5 :=
        h.loc.structGz.self.centQ_inv ⟨c, hcz⟩ hcbar2 hcbar1
      have h2 := card_centQtilde_eq h.typ (⟨c, hcz⟩ : ↥(Gx z))
      rw [h1] at h2
      norm_num at h2
      exact h2.symm
    rw [hF32] at hlt
    rw [hcentQ] at hlt
    omega
  · exfalso
    have h := hFiberEq
    rw [hcard] at h
    omega

theorem not_mem_derived_of_outer_2A (h : F5Std a z) {c : G} (hcz : c ∈ Gx z) (hcQ : c ∉ Qz z)
    (hcA : IsConj a c) : c ∉ derivedOf (Gx z) := by
  intro hcD
  obtain ⟨hcz', hcComm⟩ := mem_derivedOf_iff.mp hcD
  have hEq : (⟨c, hcz'⟩ : ↥(Gx z)) = ⟨c, hcz⟩ := Subtype.ext rfl
  rw [hEq] at hcComm
  have hmk : barOf z (⟨c, hcz⟩ : ↥(Gx z)) ∈
      (_root_.commutator ↥(Gx z)).map (QuotientGroup.mk' (CFSG.pCore 2 ↥(Gx z))) :=
    Subgroup.mem_map.mpr ⟨⟨c, hcz⟩, hcComm, rfl⟩
  rw [map_commutator_mk' z] at hmk
  exact barOf_not_mem_commutator' h hcz hcQ hcA hmk

theorem exists_conj_mem_coset (h : F5Std a z) {c y : G} (hcz : c ∈ Gx z) (hcQ : c ∉ Qz z)
    (hcA : IsConj a c) (hy : y ∈ Gx z) (hy2 : y ^ 2 = 1) (hyd : y ∉ derivedOf (Gx z)) :
    ∃ k ∈ Gx z, ∃ q ∈ Qz z, k * y * k⁻¹ = c * q := by
  classical
  haveI : Finite G := h.finite
  have hc2 : c ^ 2 = 1 := sq_eq_one_of_isConj h.typ.orderOf_a hcA
  have hcbar2 : (barOf z (⟨c, hcz⟩ : ↥(Gx z))) ^ 2 = 1 := barOf_sq_eq_one hcz hc2
  have hcbar_out : barOf z (⟨c, hcz⟩ : ↥(Gx z)) ∉ _root_.commutator (Gbar z) :=
    barOf_not_mem_commutator' h hcz hcQ hcA
  have hybar2 : (barOf z (⟨y, hy⟩ : ↥(Gx z))) ^ 2 = 1 := barOf_sq_eq_one hy hy2
  have hmap := map_commutator_mk' z
  have hQle : CFSG.pCore 2 ↥(Gx z) ≤ _root_.commutator ↥(Gx z) := by
    obtain ⟨Q', hQ'n, hAH⟩ := h.loc.gz9.self.aschbacher
    haveI : Q'.Normal := hQ'n
    have hp : CFSG.pCore 2 ↥(Gx z) = Q' :=
      IsExtraspecialPlusByA5WrTwoWith.pCore_eq hAH.toIsExtraspecialPlusByA5WrTwoWith
    rw [hp]
    exact hAH.le_commutator
  have hybar_out : barOf z (⟨y, hy⟩ : ↥(Gx z)) ∉ _root_.commutator (Gbar z) := by
    intro hyin
    rw [← hmap] at hyin
    obtain ⟨g, hgComm, hgEq⟩ := Subgroup.mem_map.mp hyin
    have hgEq' : (g : ↥(Gx z) ⧸ CFSG.pCore 2 ↥(Gx z)) =
        ((⟨y, hy⟩ : ↥(Gx z)) : ↥(Gx z) ⧸ CFSG.pCore 2 ↥(Gx z)) := hgEq
    have hqQ : g⁻¹ * (⟨y, hy⟩ : ↥(Gx z)) ∈ CFSG.pCore 2 ↥(Gx z) := by
      rw [← QuotientGroup.eq_one_iff]
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hgEq']
      group
    have hyComm : (⟨y, hy⟩ : ↥(Gx z)) ∈ _root_.commutator ↥(Gx z) := by
      have h1 : (⟨y, hy⟩ : ↥(Gx z)) = g * (g⁻¹ * ⟨y, hy⟩) := by group
      rw [h1]
      exact (_root_.commutator ↥(Gx z)).mul_mem hgComm (hQle hqQ)
    exact hyd (mem_derivedOf_iff.mpr ⟨hy, hyComm⟩)
  obtain ⟨e⟩ := nonempty_mulEquiv_Gbar h.typ
  obtain ⟨b, _hbComm, hb⟩ :=
    exists_conj_of_outer_of_mulEquiv e hybar_out hcbar_out hybar2 hcbar2
  obtain ⟨k₀, hk₀⟩ := QuotientGroup.mk_surjective b
  have hk₀' : barOf z k₀ = b := hk₀
  refine ⟨(k₀ : G), k₀.2, ?_⟩
  refine ⟨c⁻¹ * ((k₀ : G) * y * (k₀ : G)⁻¹), ?_, ?_⟩
  · have hmemC : (⟨c, hcz⟩ : ↥(Gx z))⁻¹ *
        (k₀ * (⟨y, hy⟩ : ↥(Gx z)) * k₀⁻¹) ∈ CFSG.pCore 2 ↥(Gx z) := by
      refine (QuotientGroup.eq_one_iff _).mp ?_
      calc (((⟨c, hcz⟩ : ↥(Gx z))⁻¹ *
            (k₀ * (⟨y, hy⟩ : ↥(Gx z)) * k₀⁻¹) : ↥(Gx z)) :
              ↥(Gx z) ⧸ CFSG.pCore 2 ↥(Gx z))
          = (barOf z (⟨c, hcz⟩ : ↥(Gx z)))⁻¹ *
              (barOf z k₀ * barOf z (⟨y, hy⟩ : ↥(Gx z)) * (barOf z k₀)⁻¹) := by
            simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
        _ = (barOf z (⟨c, hcz⟩ : ↥(Gx z)))⁻¹ *
              (b * barOf z (⟨y, hy⟩ : ↥(Gx z)) * b⁻¹) := by rw [hk₀']
        _ = (barOf z (⟨c, hcz⟩ : ↥(Gx z)))⁻¹ * barOf z (⟨c, hcz⟩ : ↥(Gx z)) := by
              rw [hb]
        _ = 1 := by group
    have hq : (((⟨c, hcz⟩ : ↥(Gx z))⁻¹ *
          (k₀ * (⟨y, hy⟩ : ↥(Gx z)) * k₀⁻¹) : ↥(Gx z)) : G) ∈ Qz z :=
      Subgroup.mem_map.mpr ⟨_, hmemC, rfl⟩
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hq
  · group

end CFSG.EvenSporadicStandard.HNRecog.Section4
