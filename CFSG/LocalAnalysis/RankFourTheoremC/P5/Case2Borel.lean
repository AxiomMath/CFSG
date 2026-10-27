module

import CFSG.LocalAnalysis.RankFourTheoremC.PPointCase2Borel
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerRank
import CFSG.LocalAnalysis.RankThreeTheoremC.D1ConstrainedPhase3Unique
public import CFSG.LocalAnalysis.RankFourTheoremC.P5.BorelDataP

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.P5

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools CFSG.AGLEmbedding
  CFSG.LocalAnalysis.RankThreeTheoremC CFSG.LocalAnalysis.RankFourTheoremC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem mem_glbPrimeCore_of_mk_eq_one_gen {p : ℕ} [Fact p.Prime] {H : Subgroup G} {r : G}
    (hr : r ∈ H) (h : QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨r, hr⟩ = 1) :
    r ∈ GLBPrimeCore p H := by
  have h1 : (⟨r, hr⟩ : H) ∈ primeComplementCore (G := H) p := (QuotientGroup.eq_one_iff _).mp h
  rw [← glbPrimeCore_subgroupOf] at h1
  exact Subgroup.mem_subgroupOf.mp h1

namespace BorelDataP

variable {p : ℕ} [hp : Fact p.Prime] {P : Sylow p G} {M : Subgroup G} {x : G} {n : ℕ}
  {f : GaloisField p n → G} {W : Subgroup G}

theorem inf_centralizer_le_normalizer_QK_sup (hB : BorelDataP p P M x f W) :
    M ⊓ centralizer ({x} : Set G) ≤
      normalizer ((hB.QK ⊔ GLBPrimeCore p (centralizer ({x} : Set G)) : Subgroup G) : Set G) := by
  have hp5 := hB.five_le
  obtain ⟨R, K, d, hfacts, hd, ⟨eK⟩, hρ, hsurj, -, -, hReq⟩ := hB.reduced
  have hKn : K.Normal := hfacts.red.normal
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set Ox : Subgroup G := GLBPrimeCore p C with hOx
  set X₀ : Subgroup (RedCent p x) := redCentM p M x with hX₀
  have hn1 : 1 ≤ n := by
    have := hB.three_le
    omega
  obtain ⟨hE, hcard⟩ := isElemAbelian_sylow_inf_of_psl2GF (p := p) hn1 eK R
  have hrk : 2 ≤ Open.pRank p ((R : Subgroup (RedCent p x)) ⊓ K) := by
    have h1 := le_pRank_of_elemAbelian_card (p := p) le_rfl hE hcard
    have := hB.three_le
    omega
  have hNX : normalizer (((R : Subgroup (RedCent p x)) ⊓ K : Subgroup (RedCent p x)) :
      Set (RedCent p x)) ≤ X₀ :=
    (CFSG.PreuniquenessRankFour.Helpers.fullCore_le_iff p 2 _ _).mp hfacts.red.fullCore _
      inf_le_left hrk
  have hX₀K : X₀ ⊓ K ≤ normalizer (((R : Subgroup (RedCent p x)) ⊓ K : Subgroup (RedCent p x)) :
      Set (RedCent p x)) :=
    inf_le_normalizer_of_psl2GF (by omega) hn1 eK R hNX hfacts.red.not_le
  obtain ⟨T, hT⟩ := exists_sylow_map_subtype_eq_inf K R
  have hSyl : IsSylowOf p ((R : Subgroup (RedCent p x)) ⊓ K) K := ⟨T, hT⟩
  have hX₀N : X₀ ≤ normalizer (((R : Subgroup (RedCent p x)) ⊓ K : Subgroup (RedCent p x)) :
      Set (RedCent p x)) := by
    have h1 := inf_normalizer_le_normalizer_of_sylow hSyl (le_normalizer.trans hNX) hX₀K
    rwa [Subgroup.normalizer_eq_top, inf_top_eq] at h1
  intro h hh
  have hhC : h ∈ C := hh.2
  have hhX : QuotientGroup.mk' (primeComplementCore (G := C) p) ⟨h, hhC⟩ ∈ X₀ :=
    ⟨⟨h, hhC⟩, mem_subgroupOf.mpr ⟨hhC, hh.1⟩, rfl⟩
  have hnormOx : ∀ r ∈ Ox, h * r * h⁻¹ ∈ Ox := fun r hr =>
    (mem_normalizer_iff.mp (le_normalizer_glbPrimeCore p C hhC) r).mp hr
  have hQ : ∀ q ∈ hB.QK, h * q * h⁻¹ ∈ hB.QK ⊔ Ox := by
    intro q hq
    obtain ⟨t, rfl⟩ := hB.mem_QK.mp hq
    obtain ⟨hct, hRt, -⟩ := hρ t
    have h1 := (mem_normalizer_iff.mp (hX₀N hhX)
      (QuotientGroup.mk' (primeComplementCore (G := C) p) ⟨f t, hct⟩)).mp hRt
    obtain ⟨s, hcs, hs⟩ := hsurj _ h1
    have hu : h * f t * h⁻¹ ∈ C := C.mul_mem (C.mul_mem hhC hct) (C.inv_mem hhC)
    have hr : (f s)⁻¹ * (h * f t * h⁻¹) ∈ C := C.mul_mem (C.inv_mem hcs) hu
    have hmk : QuotientGroup.mk' (primeComplementCore (G := C) p)
        ⟨(f s)⁻¹ * (h * f t * h⁻¹), hr⟩ = 1 := by
      have e : (⟨(f s)⁻¹ * (h * f t * h⁻¹), hr⟩ : C) =
          (⟨f s, hcs⟩ : C)⁻¹ * ((⟨h, hhC⟩ : C) * ⟨f t, hct⟩ * (⟨h, hhC⟩ : C)⁻¹) := rfl
      rw [e, map_mul, map_inv, hs, map_mul, map_mul, map_inv, inv_mul_cancel]
    have hrO := mem_glbPrimeCore_of_mk_eq_one_gen hr hmk
    have : h * f t * h⁻¹ = f s * ((f s)⁻¹ * (h * f t * h⁻¹)) := by group
    rw [this]
    exact Subgroup.mul_mem _ (mem_sup_left (hB.f_mem_QK s)) (mem_sup_right hrO)
  refine mem_normalizer_of_map_conj_le ?_
  rw [Subgroup.map_sup]
  refine sup_le ?_ ?_
  · rintro _ ⟨q, hq, rfl⟩
    exact hQ q hq
  · rintro _ ⟨r, hr, rfl⟩
    exact mem_sup_right (hnormOx r hr)


end BorelDataP

end CFSG.LocalAnalysis.RankFourTheoremC.P5
