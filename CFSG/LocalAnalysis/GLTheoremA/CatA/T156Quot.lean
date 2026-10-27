module

public import CFSG.LocalAnalysis.GLTheoremA.S10.Defs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Quot
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T156

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.S267
open scoped commutatorElement

theorem mem_core_iff_coe {p : ℕ} {A : Type} [Group A] [Finite A] {Y : Subgroup A} (x : ↥Y) :
    x ∈ GLAPPrimeCore p ↥Y ↔ (x : A) ∈ GLAPPrimeCoreOf p Y := by
  rw [mem_glaPPrimeCoreOf_iff]
  constructor
  · intro h
    exact ⟨x, h, rfl⟩
  · rintro ⟨h, hh, he⟩
    have : h = x := Subtype.ext he
    exact this ▸ hh

section Generic

variable {A Ω : Type} [Group A] [Group Ω] [Finite A] [Finite Ω]

theorem conj_mem' {L : Subgroup A} {g x : A} (hg : g ∈ Subgroup.normalizer (L : Set A)) (hx : x ∈ L) :
    g⁻¹ * x * g ∈ L := by
  refine (Subgroup.mem_normalizer_iff.1 hg (g⁻¹ * x * g)).2 ?_
  have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
  rw [e]
  exact hx

theorem map_normalizer_mem {Y : Subgroup A} {g : A} (π : A →* Ω)
    (hg : g ∈ Subgroup.normalizer (Y : Set A)) :
    π g ∈ Subgroup.normalizer ((Y.map π : Subgroup Ω) : Set Ω) := by
  rw [Subgroup.mem_normalizer_iff]
  intro t
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine Subgroup.mem_map.2 ⟨g * y * g⁻¹, ?_, by simp only [map_mul, map_inv]⟩
    exact (Subgroup.mem_normalizer_iff.1 hg y).1 hy
  · intro ht
    obtain ⟨y, hy, hyt⟩ := Subgroup.mem_map.1 ht
    refine Subgroup.mem_map.2 ⟨g⁻¹ * y * g, conj_mem' hg hy, ?_⟩
    calc π (g⁻¹ * y * g) = (π g)⁻¹ * π y * π g := by simp only [map_mul, map_inv]
      _ = t := by rw [hyt]; group

theorem indRel_iff_exists {p : ℕ} {L : Subgroup A} {g : A} (hg : g ∈ Subgroup.normalizer (L : Set A))
    (q q' : PQuot p L) :
    indRel p L g q q' ↔ ∃ u : ↥L, (QuotientGroup.mk u : PQuot p L) = q ∧
      (QuotientGroup.mk ⟨g⁻¹ * (u : A) * g, conj_mem' hg u.2⟩ : PQuot p L) = q' := by
  constructor
  · rintro ⟨l, l', hl, hl', hll⟩
    refine ⟨l, hl, ?_⟩
    have h : (⟨g⁻¹ * (l : A) * g, conj_mem' hg l.2⟩ : ↥L) = l' := Subtype.ext hll.symm
    rw [h, hl']
  · rintro ⟨u, hu, hu'⟩
    exact ⟨u, ⟨g⁻¹ * (u : A) * g, conj_mem' hg u.2⟩, hu, hu', rfl⟩

noncomputable def pquotMap {p : ℕ} (hp : p.Prime) (π : A →* Ω) (hN : ¬ p ∣ Nat.card π.ker) (Y : Subgroup A) :
    PQuot p Y ≃* PQuot p (Y.map π) := by
  classical
  let f : ↥Y →* PQuot p (Y.map π) :=
    (QuotientGroup.mk' (GLAPPrimeCore p ↥(Y.map π))).comp (π.subgroupMap Y)
  have hsurj : Function.Surjective f :=
    (QuotientGroup.mk'_surjective _).comp (π.subgroupMap_surjective Y)
  have hker : f.ker = GLAPPrimeCore p ↥Y := by
    ext x
    rw [MonoidHom.mem_ker]
    simp only [f, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    rw [mem_core_iff_coe, mem_core_iff_coe]
    exact (mem_glaPPrimeCoreOf_iff_map hp π hN x.2).symm
  exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hsurj)

theorem pquotMap_mk {p : ℕ} (hp : p.Prime) (π : A →* Ω) (hN : ¬ p ∣ Nat.card π.ker) (Y : Subgroup A)
    (y : ↥Y) :
    pquotMap hp π hN Y (QuotientGroup.mk y) = QuotientGroup.mk (π.subgroupMap Y y) := by
  unfold pquotMap
  rfl

theorem indRel_pquotMap {p : ℕ} (hp : p.Prime) (π : A →* Ω) (hN : ¬ p ∣ Nat.card π.ker) {Y : Subgroup A}
    {g : A} (hg : g ∈ Subgroup.normalizer (Y : Set A)) (q q' : PQuot p Y) :
    indRel p (Y.map π) (π g) (pquotMap hp π hN Y q) (pquotMap hp π hN Y q') ↔ indRel p Y g q q' := by
  have hgπ : π g ∈ Subgroup.normalizer ((Y.map π : Subgroup Ω) : Set Ω) := map_normalizer_mem π hg
  have hgc : g ∈ Subgroup.normalizer ((GLAPPrimeCoreOf p Y : Subgroup A) : Set A) :=
    normalizer_le_normalizer_glaPPrimeCoreOf p Y hg
  rw [indRel_iff_exists hgπ, indRel_iff_exists hg]
  obtain ⟨u₀, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨u', rfl⟩ := QuotientGroup.mk_surjective q'
  rw [pquotMap_mk, pquotMap_mk]
  constructor
  · rintro ⟨s, hs, hs'⟩
    refine ⟨u₀, rfl, ?_⟩
    have hc : (π.subgroupMap Y u₀ : ↥(Y.map π))⁻¹ * s ∈ GLAPPrimeCore p ↥(Y.map π) :=
      QuotientGroup.eq.1 hs.symm
    have hc' : (π u₀)⁻¹ * (s : Ω) ∈ GLAPPrimeCoreOf p (Y.map π) := (mem_core_iff_coe _).1 hc
    rw [← map_glaPPrimeCoreOf hp π hN Y] at hc'
    obtain ⟨w, hw, hwπ⟩ := Subgroup.mem_map.1 hc'
    have hsπ : (s : Ω) = π u₀ * π w := by
      rw [hwπ]
      group
    have hw' : g⁻¹ * w * g ∈ GLAPPrimeCoreOf p Y := conj_mem' hgc hw
    have hπw : π (g⁻¹ * w * g) ∈ GLAPPrimeCoreOf p (Y.map π) := by
      rw [← map_glaPPrimeCoreOf hp π hN Y]
      exact Subgroup.mem_map_of_mem π hw'
    have hcls : (QuotientGroup.mk (π.subgroupMap Y ⟨g⁻¹ * (u₀ : A) * g, conj_mem' hg u₀.2⟩) :
        PQuot p (Y.map π)) = QuotientGroup.mk ⟨(π g)⁻¹ * (s : Ω) * π g, conj_mem' hgπ s.2⟩ := by
      rw [QuotientGroup.eq]
      refine (mem_core_iff_coe _).2 ?_
      have e : ((π.subgroupMap Y ⟨g⁻¹ * (u₀ : A) * g, conj_mem' hg u₀.2⟩)⁻¹ *
          ⟨(π g)⁻¹ * (s : Ω) * π g, conj_mem' hgπ s.2⟩ : ↥(Y.map π)).1 = π (g⁻¹ * w * g) := by
        show (π (g⁻¹ * (u₀ : A) * g))⁻¹ * ((π g)⁻¹ * (s : Ω) * π g) = π (g⁻¹ * w * g)
        rw [hsπ]
        simp only [map_mul, map_inv]
        group
      rw [e]
      exact hπw
    have hfin : (QuotientGroup.mk (π.subgroupMap Y ⟨g⁻¹ * (u₀ : A) * g, conj_mem' hg u₀.2⟩) :
        PQuot p (Y.map π)) = QuotientGroup.mk (π.subgroupMap Y u') := hcls.trans hs'
    apply (pquotMap hp π hN Y).injective
    rw [pquotMap_mk, pquotMap_mk]
    exact hfin
  · rintro ⟨u, hu, hu'⟩
    refine ⟨π.subgroupMap Y u, ?_, ?_⟩
    · have h1 := congrArg (pquotMap hp π hN Y) hu
      rw [pquotMap_mk, pquotMap_mk] at h1
      exact h1
    · have h2 := congrArg (pquotMap hp π hN Y) hu'
      rw [pquotMap_mk, pquotMap_mk] at h2
      have e2 : (⟨(π g)⁻¹ * (π.subgroupMap Y u : Ω) * π g, conj_mem' hgπ (π.subgroupMap Y u).2⟩ :
          ↥(Y.map π)) = π.subgroupMap Y ⟨g⁻¹ * (u : A) * g, conj_mem' hg u.2⟩ := by
        apply Subtype.ext
        show (π g)⁻¹ * π (u : A) * π g = π (g⁻¹ * (u : A) * g)
        simp only [map_mul, map_inv]
      rw [e2]
      exact h2

theorem inducesInnerMod_of_map {p : ℕ} (hp : p.Prime) (π : A →* Ω) (hN : ¬ p ∣ Nat.card π.ker)
    {Y : Subgroup A} {g : A} (hg : g ∈ Subgroup.normalizer (Y : Set A))
    (h : InducesInnerMod p (Y.map π) (π g)) : InducesInnerMod p Y g := by
  obtain ⟨s, hs, hsall⟩ := h
  obtain ⟨l₀, hl₀, rfl⟩ := Subgroup.mem_map.1 hs
  refine ⟨l₀, hl₀, fun y hy => ?_⟩
  have hz : (l₀⁻¹ * y * l₀)⁻¹ * (g⁻¹ * y * g) ∈ Y :=
    Y.mul_mem (Y.inv_mem (Y.mul_mem (Y.mul_mem (Y.inv_mem hl₀) hy) hl₀)) (conj_mem' hg hy)
  have h1 := hsall (π y) (Subgroup.mem_map_of_mem π hy)
  have e : π ((l₀⁻¹ * y * l₀)⁻¹ * (g⁻¹ * y * g)) =
      ((π l₀)⁻¹ * π y * π l₀)⁻¹ * ((π g)⁻¹ * π y * π g) := by
    simp only [map_mul, map_inv]
  exact (mem_glaPPrimeCoreOf_iff_map hp π hN hz).2 (by rw [e]; exact h1)

end Generic

end CFSG.LocalAnalysis.GLTheoremA.T156

end
