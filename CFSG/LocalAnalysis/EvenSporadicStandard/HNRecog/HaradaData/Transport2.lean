module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.HData2
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaData.Facts2

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

theorem HaradaFacts2.toHData2 {G : Type} [Group G] {t : G}
    {E : Subgroup ↥(centralizer ({t} : Set G))} {a z b z₁ : ↥(centralizer ({t} : Set G))}
    {S T T' W0 R0 F : Subgroup ↥(centralizer ({t} : Set G))}
    {ι : Elem2 6 →* ↥(centralizer ({t} : Set G))} {zv : V6}
    (hF : HaradaFacts2 ↥(centralizer ({t} : Set G)) E a z b z₁ S T T' W0 ι zv R0 F) :
    Harada.HData2 G t (z : G) (z₁ : G) ((centralizer ({t} : Set G)).subtype.comp ι) zv
      (R0.map (centralizer ({t} : Set G)).subtype) (F.map (centralizer ({t} : Set G)).subtype) := by
  let f : ↥(centralizer ({t} : Set G)) →* G := (centralizer ({t} : Set G)).subtype
  have hf : Function.Injective f := fun x y h => Subtype.ext h
  change Harada.HData2 G t (z : G) (z₁ : G) (f.comp ι) zv (R0.map f) (F.map f)
  have hι'range : (f.comp ι).range = ι.range.map f := MonoidHom.range_comp f ι
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show f (ι (Multiplicative.ofAdd zv)) = (z : G)
    rw [hF.ι_zv]
    rfl
  · exact hF.lam_zv
  · exact hF.qm_zv
  · rw [Subgroup.card_map_of_injective hf]
    exact hF.card_R0
  · rintro x ⟨r, hr, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨r.2, ?_⟩
    have hcomm : r * z = z * r :=
      Subgroup.mem_centralizer_singleton_iff.mp (hF.R0_le_centralizer hr)
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (by simpa [f, map_mul] using congrArg f hcomm)
  · rintro x ⟨r, hr, rfl⟩
    rw [hι'range]
    exact map_mem_normalizer f (hF.R0_le_normalizer hr)
  · rintro c hc x ⟨r, hr, rfl⟩
    let c' : ↥(centralizer ({t} : Set G)) := ⟨c, (Subgroup.mem_inf.mp hc).1⟩
    have hc'z : c' ∈ centralizer ({z} : Set ↥(centralizer ({t} : Set G))) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      have hcz : c * (z : G) = (z : G) * c :=
        Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hc).2
      simpa using hcz
    refine Subgroup.mem_map.mpr ⟨c' * r * c'⁻¹, hF.R0_normal c' hc'z r hr, ?_⟩
    simp [f, c', map_mul, map_inv]
  · intro P hP hP2 hPnorm
    let P₀ : Subgroup ↥(centralizer ({t} : Set G)) := P.comap f
    have hPle : P ≤ f.range := by
      intro x hx
      rw [Subgroup.range_subtype]
      exact (Subgroup.mem_inf.mp (hP hx)).1
    have hmap : P₀.map f = P := Subgroup.map_comap_eq_self hPle
    have hP₀z : P₀ ≤ centralizer ({z} : Set ↥(centralizer ({t} : Set G))) := by
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply hf
      rw [map_mul, map_mul]
      exact Subgroup.mem_centralizer_singleton_iff.mp
        (Subgroup.mem_inf.mp (hP (Subgroup.mem_comap.mp hx))).2
    have hP₀p : IsPGroup 2 P₀ := hP2.comap_of_injective f hf
    have hP₀norm : ∀ c ∈ centralizer ({z} : Set ↥(centralizer ({t} : Set G))),
        ∀ x ∈ P₀, c * x * c⁻¹ ∈ P₀ := by
      intro c hc x hx
      rw [Subgroup.mem_comap]
      have hcz : f c ∈ centralizer ({↑z} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hcomm : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp hc
        simpa [f, map_mul] using congrArg f hcomm
      have hcP : f c ∈ centralizer ({t} : Set G) ⊓ centralizer ({↑z} : Set G) :=
        ⟨c.2, hcz⟩
      have hxP : f x ∈ P := Subgroup.mem_comap.mp hx
      simpa [map_mul, map_inv] using hPnorm (f c) hcP (f x) hxP
    rw [← hmap]
    exact Subgroup.map_mono (hF.R0_max P₀ hP₀z hP₀p hP₀norm)
  · rintro x ⟨r, hr, rfl⟩
    have h : f (r ^ 2) ∈ (zpowers z).map f :=
      Subgroup.mem_map.mpr ⟨r ^ 2, hF.R0_sq r hr, rfl⟩
    rw [MonoidHom.map_zpowers] at h
    simpa [f, map_pow] using h
  · rintro x ⟨r, hr, rfl⟩ y ⟨s, hs, rfl⟩
    have h : f (r * s * r⁻¹ * s⁻¹) ∈ (zpowers z).map f :=
      Subgroup.mem_map.mpr ⟨r * s * r⁻¹ * s⁻¹, hF.R0_comm r hr s hs, rfl⟩
    rw [MonoidHom.map_zpowers] at h
    simpa [f, map_mul, map_inv] using h
  · intro v
    show f (ι (Multiplicative.ofAdd v)) ∈ R0.map f ↔ bil v zv = 0
    rw [Subgroup.mem_map_iff_mem hf]
    exact hF.R0_inter v
  · rintro x ⟨r, hr, rfl⟩
    obtain ⟨u, hu, hl, he⟩ := hF.R0_eichler r hr
    refine ⟨u, hu, hl, ?_⟩
    intro x
    simpa [Harada.coordElt, map_mul, map_inv] using congrArg f (he x)
  · intro u hu hl
    obtain ⟨r, hr, he⟩ := hF.R0_surj u hu hl
    refine ⟨f r, Subgroup.mem_map.mpr ⟨r, hr, rfl⟩, ?_⟩
    intro x
    simpa [Harada.coordElt, map_mul, map_inv] using congrArg f (he x)
  · rintro c hc htriv
    let c' : ↥(centralizer ({t} : Set G)) := ⟨c, (Subgroup.mem_inf.mp hc).1⟩
    have hc'z : c' ∈ centralizer ({z} : Set ↥(centralizer ({t} : Set G))) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      have hcz : c * (z : G) = (z : G) * c :=
        Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hc).2
      simpa using hcz
    have hcond : ∀ x ∈ R0, c' * x * c'⁻¹ * x⁻¹ ∈ zpowers z := by
      intro x hx
      rw [← Subgroup.mem_map_iff_mem hf (K := zpowers z), MonoidHom.map_zpowers]
      simpa [f, c', map_mul, map_inv] using htriv (f x) (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
    exact Subgroup.mem_map.mpr ⟨c', hF.R0_faith c' hc'z hcond, rfl⟩
  · rintro x ⟨y, hy, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨y.2, ?_⟩
    have hcomm : y * z₁ = z₁ * y :=
      Subgroup.mem_centralizer_singleton_iff.mp (hF.F_le_centralizer hy)
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (by simpa [f, map_mul] using congrArg f hcomm)
  · rintro x ⟨y, hy, rfl⟩
    rw [hι'range]
    exact map_mem_normalizer f (hF.F_le_normalizer hy)
  · obtain ⟨e⟩ := hF.F_iso
    exact ⟨(Subgroup.equivMapOfInjective F f hf).symm.trans e⟩

end CFSG.EvenSporadicStandard.HNRecog
