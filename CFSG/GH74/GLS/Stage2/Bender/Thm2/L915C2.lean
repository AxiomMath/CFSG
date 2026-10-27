module

public import CFSG.GH74.GLS.Stage2.Signalizer.L46EAutC
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915Gen
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.L915

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.GH74.GLS.Stage2.Signalizer
open scoped commutatorElement

@[expose] def K1Statement : Prop :=
  ∀ (X : Type) [Group X] (p n : ℕ), p.Prime → p ≠ 2 → 1 ≤ n → LieModel X .PSL 3 p n →
    ∀ ζ : X, ζ * ζ = 1 → ζ ≠ 1 → ∀ R : Subgroup (MulAut X), IsPGroup p ↥R → (∀ r ∈ R, r ζ = ζ) →
      (∀ d : X, d * ζ = ζ * d → ∀ r ∈ R, MulAut.conj d * r * (MulAut.conj d)⁻¹ ∈ R) → R = ⊥

section Act

variable {Y : Type} [Group Y]

noncomputable def actQuot (J : Subgroup Y) (hJn : ∀ y : Y, y ∈ normalizer (J : Set Y)) :
    Y →* MulAut (↥J ⧸ center ↥J) :=
  have : J.Normal := Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.mpr fun y _ => hJn y)
  { toFun := fun y => QuotientGroup.congr (center ↥J) (center ↥J) (MulAut.conjNormal y : MulAut ↥J)
      (L46E.AutC.map_center_eq_of_mulAut _)
    map_one' := by
      ext q
      induction q using QuotientGroup.induction_on with
      | H x => simp [QuotientGroup.congr_mk]
    map_mul' := by
      intro a b
      ext q
      induction q using QuotientGroup.induction_on with
      | H x =>
        erw [QuotientGroup.congr_mk, MulAut.mul_apply, QuotientGroup.congr_mk]
        simp [map_mul] }

theorem actQuot_mk (J : Subgroup Y) (hJn : ∀ y : Y, y ∈ normalizer (J : Set Y)) (y : Y) (x : ↥J) :
    actQuot J hJn y (QuotientGroup.mk x) =
      QuotientGroup.mk ⟨y * x * y⁻¹, (mem_normalizer_iff.mp (hJn y) x).mp x.2⟩ := by
  have : J.Normal := Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.mpr fun y _ => hJn y)
  have h : actQuot J hJn y (QuotientGroup.mk x) = QuotientGroup.mk (MulAut.conjNormal y x : ↥J) := by
    simp only [actQuot, MonoidHom.coe_mk, OneHom.coe_mk]
    exact QuotientGroup.congr_mk _ _ _ _ x
  rw [h]
  congr 1

end Act

section Finite

variable {Y : Type} [Group Y] [Finite Y]

theorem eq_one_of_central_involution (h2 : pCore 2 Y = ⊥) {J : Subgroup Y} (hJ : IsComponent J) {c : Y}
    (hcJ : c ∈ J) (hcc : c ∈ centralizer (J : Set Y)) (hc2 : c * c = 1) : c = 1 := by
  have hlayer : layer Y ≤ centralizer ({c} : Set Y) := by
    refine sSup_le fun L hL => ?_
    rcases CFSG.LocalCores.distinct_components_commute hL hJ with rfl | hLJ
    · intro l hl
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hcc l hl
    · intro l hl
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hl' : l ∈ centralizer (J : Set Y) := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hLJ hl
      exact (Subgroup.mem_centralizer_iff.mp hl' c hcJ).symm
  have hcT : c ∈ centerLayerTwo Y :=
    ⟨CFSG.LocalCores.component_le_layer hJ hcJ,
      fun l hl => (Subgroup.mem_centralizer_singleton_iff.mp (hlayer hl)).symm, hc2⟩
  have hle : centerLayerTwo Y ≤ pCore 2 Y :=
    le_sSup ⟨centerLayerTwo_normal, centerLayerTwo_isPGroup⟩
  have h1 := hle hcT
  rw [h2, Subgroup.mem_bot] at h1
  exact h1

theorem centralizes_of_K1 (hK1 : K1Statement) {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 1 ≤ n)
    (h2 : pCore 2 Y = ⊥) {J : Subgroup Y} (hJ : IsComponent J)
    (hJn : ∀ y : Y, y ∈ normalizer (J : Set Y)) (hLie : LieModel (↥J ⧸ center ↥J) .PSL 3 p n)
    {z : Y} (hzJ : z ∈ J) (hz2 : z * z = 1) (hz1 : z ≠ 1) {A₀ : Subgroup Y} (hA₀p : IsPGroup p ↥A₀)
    (hA₀z : ∀ a ∈ A₀, a * z = z * a) (hA₀n : ∀ c : Y, c * z = z * c → c ∈ normalizer (A₀ : Set Y)) :
    A₀ ≤ centralizer (J : Set Y) := by
  have : Fact p.Prime := ⟨hp⟩
  set ρ := actQuot J hJn with hρ
  set z' : ↥J := ⟨z, hzJ⟩ with hz'
  have hz2' : z' * z' = 1 := Subtype.ext hz2
  set ζ : ↥J ⧸ center ↥J := QuotientGroup.mk z' with hζ
  have hζ2 : ζ * ζ = 1 := by
    rw [hζ, ← QuotientGroup.mk_mul, hz2']
    exact QuotientGroup.mk_one _
  have hcenter : ∀ c : ↥J, c ∈ center ↥J → (c : Y) ∈ centralizer (J : Set Y) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have := Subgroup.mem_center_iff.mp hc ⟨g, hg⟩
    exact congrArg Subtype.val this
  have hζ1 : ζ ≠ 1 := by
    intro h1
    have hc : z' ∈ center ↥J := (QuotientGroup.eq_one_iff _).mp h1
    exact hz1 (eq_one_of_central_involution h2 hJ hzJ (hcenter z' hc) hz2)
  set R : Subgroup (MulAut (↥J ⧸ center ↥J)) := A₀.map ρ with hRdef
  have hR : IsPGroup p ↥R := hA₀p.map ρ
  have hRζ : ∀ r ∈ R, r ζ = ζ := by
    rintro _ ⟨a, ha, rfl⟩
    rw [hζ, actQuot_mk]
    congr 1
    apply Subtype.ext
    show a * z * a⁻¹ = z
    rw [hA₀z a ha]
    group
  have hconj : ∀ j : ↥J, MulAut.conj (QuotientGroup.mk j : ↥J ⧸ center ↥J) = ρ (j : Y) := by
    intro j
    ext q
    induction q using QuotientGroup.induction_on with
    | H x =>
      rw [actQuot_mk, MulAut.conj_apply]
      rfl
  have hRn : ∀ d : ↥J ⧸ center ↥J, d * ζ = ζ * d →
      ∀ r ∈ R, MulAut.conj d * r * (MulAut.conj d)⁻¹ ∈ R := by
    intro d hd r hr
    obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective d
    obtain ⟨a, ha, rfl⟩ := hr
    have hmk : (QuotientGroup.mk (j * z') : ↥J ⧸ center ↥J) = QuotientGroup.mk (z' * j) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
      exact hd
    have hc : (j * z')⁻¹ * (z' * j) ∈ center ↥J := QuotientGroup.eq.mp hmk
    set c : ↥J := (j * z')⁻¹ * (z' * j) with hcdef
    have hcz : c * z' = z' * c := (Subgroup.mem_center_iff.mp hc z').symm
    have hzc : z' * c = j⁻¹ * z' * j := by
      rw [hcdef]
      have : z'⁻¹ = z' := inv_eq_of_mul_eq_one_right hz2'
      calc z' * ((j * z')⁻¹ * (z' * j)) = z' * (z'⁻¹ * j⁻¹) * (z' * j) := by group
        _ = j⁻¹ * z' * j := by group
    have hc2 : c * c = 1 := by
      have h1 : (z' * c) * (z' * c) = 1 := by
        rw [hzc]
        calc j⁻¹ * z' * j * (j⁻¹ * z' * j) = j⁻¹ * (z' * z') * j := by group
          _ = 1 := by rw [hz2']; group
      calc c * c = (z' * z') * (c * c) := by rw [hz2', one_mul]
        _ = z' * (z' * c) * c := by group
        _ = z' * (c * z') * c := by rw [hcz]
        _ = (z' * c) * (z' * c) := by group
        _ = 1 := h1
    have hc1 : c = 1 := by
      have := eq_one_of_central_involution h2 hJ c.2 (hcenter c hc) (congrArg Subtype.val hc2)
      exact Subtype.ext this
    have hjz' : j * z' = z' * j := by
      have : (j * z')⁻¹ * (z' * j) = 1 := hc1
      rw [inv_mul_eq_one] at this
      exact this
    have hjz : (j : Y) * z = z * (j : Y) := congrArg Subtype.val hjz'
    rw [hconj j]
    have hja : (j : Y) * a * (j : Y)⁻¹ ∈ A₀ := (mem_normalizer_iff.mp (hA₀n j hjz) a).mp ha
    refine ⟨(j : Y) * a * (j : Y)⁻¹, hja, ?_⟩
    show ρ ((j : Y) * a * (j : Y)⁻¹) = ρ (j : Y) * ρ a * (ρ (j : Y))⁻¹
    rw [map_mul, map_mul, map_inv]
  have hRbot : R = ⊥ := hK1 (↥J ⧸ center ↥J) p n hp hp2 hn hLie ζ hζ2 hζ1 R hR hRζ hRn
  have hcomm : ⁅J, A₀⁆ ≤ centralizer (J : Set Y) := by
    refine Subgroup.commutator_le.mpr fun x hx a ha => ?_
    have hρa : ρ a = 1 := by
      have : ρ a ∈ R := ⟨a, ha, rfl⟩
      rw [hRbot, Subgroup.mem_bot] at this
      exact this
    have hax : a * x * a⁻¹ ∈ J := (mem_normalizer_iff.mp (hJn a) x).mp hx
    have hmk : (QuotientGroup.mk ⟨a * x * a⁻¹, hax⟩ : ↥J ⧸ center ↥J) = QuotientGroup.mk ⟨x, hx⟩ := by
      have := actQuot_mk J hJn a ⟨x, hx⟩
      rw [hρa, MulAut.one_apply] at this
      exact this.symm
    have hw : (⟨x, hx⟩ : ↥J)⁻¹ * ⟨a * x * a⁻¹, hax⟩ ∈ center ↥J := by
      have := QuotientGroup.eq.mp hmk.symm
      exact this
    have hwc : x⁻¹ * (a * x * a⁻¹) ∈ centralizer (J : Set Y) := hcenter _ hw
    have hxw : x * (x⁻¹ * (a * x * a⁻¹)) = (x⁻¹ * (a * x * a⁻¹)) * x :=
      Subgroup.mem_centralizer_iff.mp hwc x hx
    have h3 : x * (x⁻¹ * (a * x * a⁻¹))⁻¹ = (x⁻¹ * (a * x * a⁻¹))⁻¹ * x :=
      (Commute.inv_right (show Commute x (x⁻¹ * (a * x * a⁻¹)) from hxw)).eq
    have hxa : x * a * x⁻¹ * a⁻¹ = (x⁻¹ * (a * x * a⁻¹))⁻¹ := by
      calc x * a * x⁻¹ * a⁻¹ = (x * (x⁻¹ * (a * x * a⁻¹))⁻¹) * x⁻¹ := by group
        _ = ((x⁻¹ * (a * x * a⁻¹))⁻¹ * x) * x⁻¹ := by rw [h3]
        _ = (x⁻¹ * (a * x * a⁻¹))⁻¹ := by group
    rw [commutatorElement_def, hxa]
    exact Subgroup.inv_mem _ hwc
  exact le_centralizer_of_commutator_le_centralizer hJ.1.1 hcomm

end Finite

end CFSG.GH74.GLS.Stage2.Bender.Thm2.L915
