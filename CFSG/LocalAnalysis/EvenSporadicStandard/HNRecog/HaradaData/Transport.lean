module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaData.TransportInv
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaData.Facts

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup CFSG.EvenSporadicStandard.TwoHS CFSG.EvenSporadicStandard.HNRecog.HaradaLA

variable {H G : Type} [Group H] [Group G]

private lemma conj_comp (f : H →* G) (n : H) :
    (MulAut.conj (f n)).toMonoidHom.comp f = f.comp (MulAut.conj n).toMonoidHom := by
  ext y
  simp [MulAut.conj_apply, map_mul]

private lemma map_mem_normalizer (f : H →* G) {A : Subgroup H} {n : H}
    (hn : n ∈ normalizer (A : Set H)) : f n ∈ normalizer (A.map f : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hn ⊢
  calc (A.map f).map (MulAut.conj (f n)).toMonoidHom
      = A.map ((MulAut.conj (f n)).toMonoidHom.comp f) :=
        Subgroup.map_map A (MulAut.conj (f n)).toMonoidHom f
    _ = A.map (f.comp (MulAut.conj n).toMonoidHom) := by rw [conj_comp]
    _ = (A.map (MulAut.conj n).toMonoidHom).map f :=
        (Subgroup.map_map A f (MulAut.conj n).toMonoidHom).symm
    _ = A.map f := congrArg (fun X : Subgroup H => X.map f) hn

private lemma mem_normalizer_of_map_mem_normalizer (f : H →* G) (hf : Function.Injective f)
    {A : Subgroup H} {n : H} (hn : f n ∈ normalizer (A.map f : Set G)) :
    n ∈ normalizer (A : Set H) := by
  rw [Subgroup.mem_normalizer_iff] at hn ⊢
  intro y
  rw [← Subgroup.mem_map_iff_mem hf (K := A) (x := y),
    ← Subgroup.mem_map_iff_mem hf (K := A) (x := n * y * n⁻¹),
    show f (n * y * n⁻¹) = f n * f y * (f n)⁻¹ by rw [map_mul, map_mul, map_inv]]
  exact hn (f y)

theorem HaradaFacts.toHData {G : Type} [Group G] {t : G} (ht : orderOf t = 2)
    {E : Subgroup ↥(centralizer ({t} : Set G))} {a z b z₁ : ↥(centralizer ({t} : Set G))}
    {S T T' W0 : Subgroup ↥(centralizer ({t} : Set G))}
    {ι : Elem2 6 →* ↥(centralizer ({t} : Set G))}
    (hE : TwoHS.IsF5Centralizer ↥(centralizer ({t} : Set G)) E)
    (hF : HaradaFacts ↥(centralizer ({t} : Set G)) E a z b z₁ S T T' W0 ι) :
    Harada.HData G t (z : G) (b : G) (z₁ : G) (S.map (centralizer ({t} : Set G)).subtype)
      (E.map (centralizer ({t} : Set G)).subtype) (T.map (centralizer ({t} : Set G)).subtype)
      (T'.map (centralizer ({t} : Set G)).subtype) (W0.map (centralizer ({t} : Set G)).subtype)
      ((centralizer ({t} : Set G)).subtype.comp ι) := by
  let f : ↥(centralizer ({t} : Set G)) →* G := (centralizer ({t} : Set G)).subtype
  have hf : Function.Injective f := fun x y h => Subtype.ext h
  have hf_coe : ∀ x : ↥(centralizer ({t} : Set G)), f x = (x : G) := fun x => rfl
  have ha : (a : G) = t := hF.toTwoHSFacts.coe_eq ht
  change Harada.HData G t (z : G) (b : G) (z₁ : G) (S.map f) (E.map f) (T.map f)
      (T'.map f) (W0.map f) (f.comp ι)
  have hι'range : (f.comp ι).range = ι.range.map f := MonoidHom.range_comp f ι
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact harCoreData_map_subtype ha hF.harCore
  · have hz : z ^ 2 = 1 := by
      simpa [hF.orderOf_z] using pow_orderOf_eq_one z
    simpa [map_pow, hf_coe] using congrArg f hz
  · exact hF.isPGroup_S.map f
  · rw [Subgroup.card_map_of_injective hf]
    exact hF.card_S
  · exact hF.card_eq
  · intro u hu hu2 hu1 hut
    obtain ⟨u', hu'E, rfl⟩ := hu
    have hu'2 : u' ^ 2 = 1 := by
      apply Subtype.ext
      change (f u') ^ 2 = 1
      exact hu2
    have hu'1 : u' ≠ 1 := fun hc => hu1 (by rw [hc, map_one])
    have hu'a : u' ≠ a := fun hc => hut (by rw [hc]; simpa [hf_coe] using ha)
    obtain ⟨h, hh⟩ := TwoHSFacts.inv_E hE hF.toTwoHSFacts u' hu'E hu'2 hu'1 hu'a
    refine ⟨(h : G), h.2, ?_⟩
    rcases hh with hh | hh
    · left
      simpa [map_mul, map_inv, hf_coe] using congrArg f hh
    · right
      simpa [map_mul, map_inv, hf_coe, ha] using congrArg f hh
  · intro p hp hp2 hpE
    let p' : ↥(centralizer ({t} : Set G)) := ⟨p, hp⟩
    have hp'2 : p' ^ 2 = 1 := by
      apply Subtype.ext
      change p ^ 2 = 1
      exact hp2
    have hp'E : p' ∉ E := fun hc => hpE (Subgroup.mem_map.mpr ⟨p', hc, rfl⟩)
    obtain ⟨h, hh⟩ := TwoHSFacts.inv_outer hE hF.toTwoHSFacts p' hp'2 hp'E
    refine ⟨(h : G), h.2, ?_⟩
    rcases hh with hh | hh
    · left
      simpa [p', f, hf_coe, map_mul, map_inv] using congrArg f hh
    · right
      simpa [p', f, hf_coe, map_mul, map_inv] using congrArg f hh
  · exact hf.comp hF.injective_ι
  · show f (ι (Multiplicative.ofAdd tv)) = t
    rw [hF.ι_tv]
    simpa [hf_coe] using ha
  · obtain ⟨v, hv, hl, hq⟩ := hF.coords_z
    refine ⟨v, ?_, hl, hq⟩
    show f (ι (Multiplicative.ofAdd v)) = (z : G)
    rw [hv]
    exact hf_coe z
  · obtain ⟨v, hv, hl, hq⟩ := hF.coords_b
    refine ⟨v, ?_, hl, hq⟩
    show f (ι (Multiplicative.ofAdd v)) = (b : G)
    rw [hv]
    exact hf_coe b
  · obtain ⟨v, hv, hl, hq⟩ := hF.coords_z₁
    refine ⟨v, ?_, hl, hq⟩
    show f (ι (Multiplicative.ofAdd v)) = (z₁ : G)
    rw [hv]
    exact hf_coe z₁
  · intro v
    show f (ι (Multiplicative.ofAdd v)) ∈ E.map f ↔ lam v = 0
    rw [Subgroup.mem_map_iff_mem hf]
    exact hF.mem_E_iff v
  · intro B hBle hBcard hBea
    let B₀ : Subgroup ↥(centralizer ({t} : Set G)) := B.comap f
    have hBle' : B ≤ f.range := by
      rw [Subgroup.range_subtype]
      exact hBle
    have hmap : B₀.map f = B := Subgroup.map_comap_eq_self hBle'
    have hcard₀ : Nat.card B₀ = 64 := by
      rw [← hBcard, ← hmap]
      exact (Subgroup.card_map_of_injective hf).symm
    have hea₀ : CFSG.Open.IsElemAbelian 2 B₀ := by
      constructor
      · haveI : IsMulCommutative B := hBea.1
        exact Subgroup.comap_injective_isMulCommutative B hf
      · intro x hx
        exact hf (by rw [map_pow, hBea.2 (f x) hx, map_one])
    obtain ⟨h, hBh⟩ := hF.conj_E64 B₀ hcard₀ hea₀
    refine ⟨(h : G), h.2, ?_⟩
    have hcomp : f.comp (MulAut.conj h).toMonoidHom =
        (MulAut.conj (f h)).toMonoidHom.comp f := (conj_comp f h).symm
    calc B = B₀.map f := hmap.symm
      _ = (ι.range.map (MulAut.conj h).toMonoidHom).map f := by rw [hBh]
      _ = ι.range.map (f.comp (MulAut.conj h).toMonoidHom) :=
          Subgroup.map_map ι.range f (MulAut.conj h).toMonoidHom
      _ = ι.range.map ((MulAut.conj (f h)).toMonoidHom.comp f) := by rw [hcomp]
      _ = (ι.range.map f).map (MulAut.conj (f h)).toMonoidHom :=
          (Subgroup.map_map ι.range (MulAut.conj (f h)).toMonoidHom f).symm
      _ = (f.comp ι).range.map (MulAut.conj (f h)).toMonoidHom := by rw [hι'range]
  · intro x hx
    have ht_mem : t ∈ (f.comp ι).range := by
      refine ⟨Multiplicative.ofAdd tv, ?_⟩
      show f (ι (Multiplicative.ofAdd tv)) = t
      rw [hF.ι_tv]
      simpa [hf_coe] using ha
    have hxt : x * t = t * x := (Subgroup.mem_centralizer_iff.mp hx t ht_mem).symm
    have hxcent : x ∈ centralizer ({t} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hxt
    let x' : ↥(centralizer ({t} : Set G)) := ⟨x, hxcent⟩
    have hx'N : x' ∈ centralizer (ι.range : Set ↥(centralizer ({t} : Set G))) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hy
      apply hf
      show f (ι a * x') = f (x' * ι a)
      rw [map_mul, map_mul]
      exact Subgroup.mem_centralizer_iff.mp hx (f (ι a)) ⟨a, rfl⟩
    obtain ⟨a, ha'⟩ := MonoidHom.mem_range.mp (hF.centralizer_le hx'N)
    exact ⟨a, by show f (ι a) = x; rw [ha']; rfl⟩
  · have hNH : normalizer ((f.comp ι).range : Set G) ⊓ centralizer ({t} : Set G) =
        (normalizer (ι.range : Set ↥(centralizer ({t} : Set G)))).map f := by
      ext n
      constructor
      · intro hn
        rw [Subgroup.mem_inf] at hn
        let n' : ↥(centralizer ({t} : Set G)) := ⟨n, hn.2⟩
        have hn'N : n' ∈ normalizer (ι.range : Set ↥(centralizer ({t} : Set G))) := by
          apply mem_normalizer_of_map_mem_normalizer f hf
          show n ∈ normalizer (ι.range.map f : Set G)
          rw [← hι'range]
          exact hn.1
        exact Subgroup.mem_map.mpr ⟨n', hn'N, rfl⟩
      · intro hn
        obtain ⟨n', hn'N, rfl⟩ := Subgroup.mem_map.mp hn
        rw [Subgroup.mem_inf]
        exact ⟨by rw [hι'range]; exact map_mem_normalizer f hn'N, n'.2⟩
    rw [hNH, Subgroup.card_map_of_injective hf, hF.card_normalizer]
  · intro v w hv0 hvtv hw0 hwtv hl hq
    obtain ⟨n, hn, heq⟩ := hF.fuse v w hv0 hvtv hw0 hwtv hl hq
    refine ⟨(n : G), ?_, ?_⟩
    · rw [Subgroup.mem_inf]
      exact ⟨by rw [hι'range]; exact map_mem_normalizer f hn, n.2⟩
    · simpa [map_mul, map_inv, hf_coe, Harada.coordElt] using congrArg f heq

end CFSG.EvenSporadicStandard.HNRecog
