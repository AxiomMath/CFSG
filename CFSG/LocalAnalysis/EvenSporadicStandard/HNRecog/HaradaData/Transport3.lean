module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.HData3
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaData.Facts3
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaData.TransportCore

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup CFSG.EvenSporadicStandard.TwoHS

private lemma map_centralizer_singleton {G : Type} [Group G] {t : G} {x : G}
    (hx : x ∈ centralizer ({t} : Set G)) :
    (centralizer ({(⟨x, hx⟩ : ↥(centralizer ({t} : Set G)))} :
        Set ↥(centralizer ({t} : Set G)))).map (centralizer ({t} : Set G)).subtype
      = centralizer ({t} : Set G) ⊓ centralizer ({x} : Set G) := by
  ext y
  constructor
  · intro hy
    obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
    refine Subgroup.mem_inf.mpr ⟨y'.2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hy' ⊢
    exact congrArg (fun w : ↥(centralizer ({t} : Set G)) => (w : G)) hy'
  · intro hy
    rw [Subgroup.mem_inf] at hy
    refine Subgroup.mem_map.mpr ⟨⟨y, hy.1⟩, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp hy.2

private lemma tT_image {G : Type} [Group G] {t : G}
    {a z z₁ : ↥(centralizer ({t} : Set G))} {x : G}
    (hx : x ∈ centralizer ({t} : Set G)) (ha : (a : G) = t) :
    {y : G | y ∈ centralizer ({t} : Set G) ∧ y ∈ centralizer ({x} : Set G) ∧
        y ^ 2 = 1 ∧ y ≠ 1 ∧ Harada.tTG t (z : G) (z₁ : G) y}
      = (centralizer ({t} : Set G)).subtype ''
        {y' : ↥(centralizer ({t} : Set G)) |
          y' ∈ centralizer ({(⟨x, hx⟩ : ↥(centralizer ({t} : Set G)))} :
            Set ↥(centralizer ({t} : Set G))) ∧
          y' ^ 2 = 1 ∧ y' ≠ 1 ∧ tTH a z z₁ y'} := by
  ext y
  constructor
  · rintro ⟨hyH, hyx, hy2, hy1, hyt⟩
    refine ⟨⟨y, hyH⟩, ⟨?_, ?_, ?_, ?_⟩, rfl⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.mp hyx
    · apply Subtype.ext
      exact hy2
    · intro h
      exact hy1 (Subtype.ext_iff.mp h)
    · rcases hyt with ⟨h, hh, he⟩ | ⟨h, hh, he⟩ | ⟨h, hh, he⟩
      · left
        rw [isConj_iff]
        refine ⟨⟨h, hh⟩, ?_⟩
        apply Subtype.ext
        show h * y * h⁻¹ = (a : G)
        exact he.trans ha.symm
      · right; left
        rw [isConj_iff]
        refine ⟨⟨h, hh⟩, ?_⟩
        apply Subtype.ext
        show h * y * h⁻¹ = (a : G) * (z : G)
        rw [ha]
        exact he
      · right; right
        rw [isConj_iff]
        refine ⟨⟨h, hh⟩, ?_⟩
        apply Subtype.ext
        show h * y * h⁻¹ = (z₁ : G)
        exact he
  · rintro ⟨y', ⟨hy'x, hy'2, hy'1, hy't⟩, rfl⟩
    refine ⟨y'.2, ?_, ?_, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg (fun w : ↥(centralizer ({t} : Set G)) => (w : G))
        (Subgroup.mem_centralizer_singleton_iff.mp hy'x)
    · simpa using congrArg (fun w : ↥(centralizer ({t} : Set G)) => (w : G)) hy'2
    · intro h
      exact hy'1 (Subtype.ext h)
    · rcases hy't with h | h | h
      · left
        obtain ⟨c, hc⟩ := isConj_iff.mp h
        exact ⟨(c : G), c.2, by
          simpa [ha] using congrArg (centralizer ({t} : Set G)).subtype hc⟩
      · right; left
        obtain ⟨c, hc⟩ := isConj_iff.mp h
        exact ⟨(c : G), c.2, by
          simpa [ha] using congrArg (centralizer ({t} : Set G)).subtype hc⟩
      · right; right
        obtain ⟨c, hc⟩ := isConj_iff.mp h
        exact ⟨(c : G), c.2, by
          simpa using congrArg (centralizer ({t} : Set G)).subtype hc⟩

theorem HaradaFacts3.toHData3 {G : Type} [Group G] {t : G} (ht : orderOf t = 2)
    {E : Subgroup ↥(centralizer ({t} : Set G))} {a z b z₁ : ↥(centralizer ({t} : Set G))}
    {S T T' W0 : Subgroup ↥(centralizer ({t} : Set G))}
    {ι : Elem2 6 →* ↥(centralizer ({t} : Set G))}
    (hF : HaradaFacts3 ↥(centralizer ({t} : Set G)) E a z b z₁ S T T' W0 ι) :
    Harada.HData3 G t (z : G) (z₁ : G) := by
  let f : ↥(centralizer ({t} : Set G)) →* G := (centralizer ({t} : Set G)).subtype
  have hf : Function.Injective f := fun x y h => Subtype.ext h
  have ha : (a : G) = t := hF.toHaradaFacts.toTwoHSFacts.coe_eq ht
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro x hx y hy hx3 hy3
    let x' : ↥(centralizer ({t} : Set G)) := ⟨x, hx⟩
    let y' : ↥(centralizer ({t} : Set G)) := ⟨y, hy⟩
    have hx'3 : orderOf x' = 3 :=
      (Subgroup.orderOf_mk (H := centralizer ({t} : Set G)) x hx).trans hx3
    have hy'3 : orderOf y' = 3 :=
      (Subgroup.orderOf_mk (H := centralizer ({t} : Set G)) y hy).trans hy3
    obtain ⟨c, hc⟩ := isConj_iff.mp (hF.three_conj x' y' hx'3 hy'3)
    refine ⟨(c : G), c.2, ?_⟩
    simpa [f, map_mul, map_inv, x', y'] using congrArg f hc
  ·
    intro x hx hx3
    let x' : ↥(centralizer ({t} : Set G)) := ⟨x, hx⟩
    have hx'3 : orderOf x' = 3 :=
      (Subgroup.orderOf_mk (H := centralizer ({t} : Set G)) x hx).trans hx3
    rw [← map_centralizer_singleton hx,
      Subgroup.card_map_of_injective (f := (centralizer ({t} : Set G)).subtype)
        (fun x y h => Subtype.ext h)]
    exact hF.card_C3 x' hx'3
  ·
    intro x hx hx3 N hNle hNnorm hNodd
    let x' : ↥(centralizer ({t} : Set G)) := ⟨x, hx⟩
    have hx'3 : orderOf x' = 3 :=
      (Subgroup.orderOf_mk (H := centralizer ({t} : Set G)) x hx).trans hx3
    let N₀ : Subgroup ↥(centralizer ({t} : Set G)) := N.comap f
    have hfrange : f.range = centralizer ({t} : Set G) := by
      simpa [f] using Subgroup.range_subtype (centralizer ({t} : Set G))
    have hNle' : N ≤ f.range := by
      rw [hfrange]
      intro y hy
      exact (Subgroup.mem_inf.mp (hNle hy)).1
    have hmap : N₀.map f = N := Subgroup.map_comap_eq_self hNle'
    have hN₀le : N₀ ≤ centralizer ({x'} : Set ↥(centralizer ({t} : Set G))) := by
      intro n hn
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      have hnN : f n ∈ N := Subgroup.mem_comap.mp hn
      exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (hNle hnN)).2
    have hN₀norm : ∀ c ∈ centralizer ({x'} : Set ↥(centralizer ({t} : Set G))),
        ∀ n ∈ N₀, c * n * c⁻¹ ∈ N₀ := by
      intro c hc n hn
      rw [Subgroup.mem_comap]
      have hcx : f c ∈ centralizer ({x} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact congrArg (fun w : ↥(centralizer ({t} : Set G)) => (w : G))
          (Subgroup.mem_centralizer_singleton_iff.mp hc)
      have hcN : f c ∈ centralizer ({t} : Set G) ⊓ centralizer ({x} : Set G) :=
        ⟨c.2, hcx⟩
      have hnN : f n ∈ N := Subgroup.mem_comap.mp hn
      simpa [map_mul, map_inv] using hNnorm (f c) hcN (f n) hnN
    have hN₀odd : Odd (Nat.card N₀) := by
      rw [← Subgroup.card_map_of_injective (f := f) hf, hmap]
      exact hNodd
    have hle := hF.odd_normal x' hx'3 N₀ hN₀le hN₀norm hN₀odd
    calc N = N₀.map f := hmap.symm
      _ ≤ (zpowers x').map f := Subgroup.map_mono hle
      _ = zpowers x := by rw [MonoidHom.map_zpowers]; rfl
  ·
    intro x hx hx3
    let x' : ↥(centralizer ({t} : Set G)) := ⟨x, hx⟩
    have hx'3 : orderOf x' = 3 :=
      (Subgroup.orderOf_mk (H := centralizer ({t} : Set G)) x hx).trans hx3
    rw [tT_image hx ha,
      Set.ncard_image_of_injective (f := (centralizer ({t} : Set G)).subtype) _
        (fun a b h => Subtype.ext h)]
    exact hF.card_tT x' hx'3
  ·
    intro x hx hx3
    let x' : ↥(centralizer ({t} : Set G)) := ⟨x, hx⟩
    have hx'3 : orderOf x' = 3 :=
      (Subgroup.orderOf_mk (H := centralizer ({t} : Set G)) x hx).trans hx3
    obtain ⟨M', hM'le, hM'comm, hM'card, hM'inf⟩ := hF.perfect60 x' hx'3
    refine ⟨M'.map f, ?_, ?_, ?_, ?_⟩
    · rw [← map_centralizer_singleton hx]
      exact Subgroup.map_mono (f := f) hM'le
    · rw [← Subgroup.map_commutator, hM'comm]
    · rw [Subgroup.card_map_of_injective (f := f) hf]
      exact hM'card
    · have hz : zpowers x = (zpowers x').map f := by
        rw [MonoidHom.map_zpowers]
        rfl
      rw [hz, ← Subgroup.map_inf M' (zpowers x') f hf, hM'inf, Subgroup.map_bot]
  ·
    intro x hx hx3
    let x' : ↥(centralizer ({t} : Set G)) := ⟨x, hx⟩
    have hx'3 : orderOf x' = 3 :=
      (Subgroup.orderOf_mk (H := centralizer ({t} : Set G)) x hx).trans hx3
    obtain ⟨s', hs'x, hs'2, hs'1, hs't, hs'comm⟩ := hF.W_comm x' hx'3
    have hW : Harada.WsubG t (z : G) (z₁ : G) x =
        (WsubH a z z₁ x').map (centralizer ({t} : Set G)).subtype := by
      unfold Harada.WsubG WsubH
      rw [MonoidHom.map_closure, ← tT_image hx ha]
    refine ⟨f s', s'.2, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      simpa [f] using congrArg (fun w : ↥(centralizer ({t} : Set G)) => (w : G))
        (Subgroup.mem_centralizer_singleton_iff.mp hs'x)
    · simpa [f] using congrArg (fun w : ↥(centralizer ({t} : Set G)) => (w : G)) hs'2
    · intro h
      exact hs'1 (Subtype.ext h)
    · rcases hs't with h | h | h
      · left
        obtain ⟨c, hc⟩ := isConj_iff.mp h
        exact ⟨(c : G), c.2, by
          simpa [f, ha] using congrArg f hc⟩
      · right; left
        obtain ⟨c, hc⟩ := isConj_iff.mp h
        exact ⟨(c : G), c.2, by
          simpa [f, ha] using congrArg f hc⟩
      · right; right
        obtain ⟨c, hc⟩ := isConj_iff.mp h
        exact ⟨(c : G), c.2, by
          simpa [f] using congrArg f hc⟩
    · rw [hW, ← Subgroup.map_commutator]
      exact Subgroup.mem_map.mpr ⟨s', hs'comm, by simp [f]⟩

end CFSG.EvenSporadicStandard.HNRecog
