module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuAct
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuPlane

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open CFSG.GMS78Ru CFSG.GMS78RuSim CFSG.GMS78RuQ

namespace RuQCode

@[expose] def wordImgs (a b : List Nat) (m : Nat) : List Nat :=
  [0, m, maskApply a m, maskApply b m, maskApply a (maskApply a m),
    maskApply b (maskApply a m), maskApply a (maskApply b m), maskApply b (maskApply b m)]

@[expose] def planeGens (t : Fin 8) : Lin8 × Lin8 :=
  match t.val with
  | 1 => ((1, 3, 6), (1, 4, 3))
  | 2 => ((3, 2, 5), (4, 2, 3))
  | 3 => ((2, 1, 5), (4, 7, 2))
  | 4 => ((2, 3, 4), (2, 7, 4))
  | 5 => ((2, 3, 7), (2, 6, 7))
  | 6 => ((2, 3, 5), (2, 5, 3))
  | 7 => ((2, 3, 6), (2, 4, 1))
  | _ => (linId, linId)

@[expose] def planeCheck (t : Fin 8) : Bool :=
  let r₁ := (planeGens t).1
  let r₂ := (planeGens t).2
  let a := adMat r₁
  let b := adMat r₂
  glList.contains r₁ && glList.contains r₂ && linApply r₁ t == t && linApply r₂ t == t &&
    all256.all fun m => m == 0 || (ppOf t).contains m ||
      decide (5 ≤ (wordImgs a b m).dedup.length)

theorem planeCheck_eq : ∀ t : Fin 8, t ≠ 0 → planeCheck t = true := by
  intro t ht
  fin_cases t
  · exact absurd rfl ht
  all_goals decide +kernel

theorem planeGens_spec {t : Fin 8} (ht : t ≠ 0) :
    (planeGens t).1 ∈ glList ∧ (planeGens t).2 ∈ glList ∧
      linApply (planeGens t).1 t = t ∧ linApply (planeGens t).2 t = t ∧
      ∀ m < 256, m ≠ 0 → m ∉ ppOf t →
        5 ≤ (wordImgs (adMat (planeGens t).1) (adMat (planeGens t).2) m).dedup.length := by
  have h := planeCheck_eq t ht
  simp only [planeCheck, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, beq_iff_eq,
    List.contains_iff_mem, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, h2, h3, h4, fun m hm hm0 hmp => ?_⟩
  rcases h5 m (List.mem_range.mpr hm) with (h | h) | h
  · exact absurd h hm0
  · exact absurd h hmp
  · exact h

end RuQCode

namespace Sec3.SzR.MaskCoords

variable {G : Type} [Group G] [Finite G] {L T R : Subgroup G} {μ : G → ℕ} {ν : G → Fin 8}
  (hM : MaskCoords L T R μ ν)
include hM

theorem eq_plane_of_le (hNC : normalizer (R : Set G) ⊓ centralizer (gmsA L T : Set G) = R)
    (hidx : R.relIndex (normalizer (R : Set G)) = 168) {f : G} (hfA : f ∈ gmsA L T)
    (hf1 : f ≠ 1) {X : Subgroup G} (hX : ∀ x, x ∈ X ↔ x ∈ R ∧ μ x ∈ 0 :: RuQCode.ppOf (ν f))
    {Y : Subgroup G} (hAY : gmsA L T ≤ Y) (hYR : Y ≤ R) (hY : Nat.card Y = 32)
    (hYn : centralizer ({f} : Set G) ⊓ normalizer (R : Set G) ≤ normalizer (Y : Set G)) :
    Y = X := by
  classical
  have ht : ν f ≠ 0 := fun h => hf1 (hM.ν_inj f hfA h)
  obtain ⟨hr₁, hr₂, hr₁t, hr₂t, hcheck⟩ := RuQCode.planeGens_spec ht
  set a := adMat (RuQCode.planeGens (ν f)).1 with ha
  set b := adMat (RuQCode.planeGens (ν f)).2 with hb
  have hreal : ∀ {r : Lin8}, r ∈ glList → linApply r (ν f) = ν f →
      ∀ y ∈ Y, ∃ y' ∈ Y, μ y' = maskApply (adMat r) (μ y) := by
    intro r hr hrt y hy
    obtain ⟨g, hgN, hgA, hgR⟩ := hM.exists_code_eq hNC hidx hr
    have hgf : g * f * g⁻¹ = f :=
      hM.eq_of_ν_eq (hM.normA g hgN f hfA) hfA (by rw [hgA f hfA, hrt])
    have hgC : g ∈ centralizer ({f} : Set G) := mem_centralizer_singleton_iff.mpr (by
      calc g * f = g * f * g⁻¹ * g := by group
        _ = f * g := by rw [hgf])
    have hgY := hYn (mem_inf.mpr ⟨hgC, hgN⟩)
    exact ⟨g * y * g⁻¹, (mem_normalizer_iff.mp hgY y).mp hy, hgR y (hYR hy)⟩
  have hA : ∀ y ∈ Y, ∃ y' ∈ Y, μ y' = maskApply a (μ y) := hreal hr₁ hr₁t
  have hB : ∀ y ∈ Y, ∃ y' ∈ Y, μ y' = maskApply b (μ y) := hreal hr₂ hr₂t
  set l : List Nat := (List.range 256).filter fun m => decide (∃ y ∈ Y, μ y = m) with hl
  have hmem : ∀ m, m ∈ l ↔ ∃ y ∈ Y, μ y = m := by
    intro m
    rw [hl, List.mem_filter, List.mem_range, decide_eq_true_eq]
    constructor
    · exact fun h => h.2
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hM.lt y (hYR hy), y, hy, rfl⟩
  have hcard := card_eq_length_mul_card hAY μ l (List.Nodup.filter _ List.nodup_range)
    (fun y hy => (hmem _).mpr ⟨y, hy, rfl⟩) (fun c hc => (hmem c).mp hc)
    (fun y hy y' hy' => by
      have hyR := hYR hy
      have hy'R := hYR hy'
      rw [← hM.ker _ (mul_mem (inv_mem hyR) hy'R), hM.mul _ (inv_mem hyR) _ hy'R, hM.μ_inv hyR]
      exact ⟨fun h => by rw [h]; exact Nat.xor_self _, RuQCode.nat_eq_of_xor_eq_zero⟩)
  rw [hY, hM.card_gmsA] at hcard
  have hl4 : l.length = 4 := by omega
  have hYX : Y ≤ X := by
    intro y hy
    refine (hX y).mpr ⟨hYR hy, ?_⟩
    by_contra hm
    have hm0 : μ y ≠ 0 := fun h => hm (by rw [h]; exact List.mem_cons_self)
    have hmp : μ y ∉ RuQCode.ppOf (ν f) := fun h => hm (List.mem_cons_of_mem _ h)
    have h5 := hcheck (μ y) (hM.lt y (hYR hy)) hm0 hmp
    have hsub : RuQCode.wordImgs a b (μ y) ⊆ l := by
      intro w hw
      rw [hmem]
      simp only [RuQCode.wordImgs, List.mem_cons, List.mem_nil_iff, or_false] at hw
      obtain ⟨ya, hya, hyam⟩ := hA y hy
      obtain ⟨yb, hyb, hybm⟩ := hB y hy
      obtain ⟨yaa, hyaa, hyaam⟩ := hA ya hya
      obtain ⟨yab, hyab, hyabm⟩ := hB ya hya
      obtain ⟨yba, hyba, hybam⟩ := hA yb hyb
      obtain ⟨ybb, hybb, hybbm⟩ := hB yb hyb
      rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨1, one_mem _, (hM.ker _ (one_mem _)).mpr (one_mem _)⟩
      · exact ⟨y, hy, rfl⟩
      · exact ⟨ya, hya, hyam⟩
      · exact ⟨yb, hyb, hybm⟩
      · exact ⟨yaa, hyaa, by rw [hyaam, hyam]⟩
      · exact ⟨yab, hyab, by rw [hyabm, hyam]⟩
      · exact ⟨yba, hyba, by rw [hybam, hybm]⟩
      · exact ⟨ybb, hybb, by rw [hybbm, hybm]⟩
    have hle : (RuQCode.wordImgs a b (μ y)).dedup.length ≤ l.length :=
      ((List.nodup_dedup _).subperm fun w hw => hsub (List.mem_dedup.mp hw)).length_le
    omega
  exact eq_of_le_of_card_ge hYX (by rw [hY, hM.card_plane hX hfA hf1])

end Sec3.SzR.MaskCoords

end CFSG.ComponentClassification.GMS78
