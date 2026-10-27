module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointQK
import CFSG.LocalAnalysis.RankFourTheoremC.PPointEndgame
import CFSG.LocalAnalysis.RankFourTheoremC.PPointFusion
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerRank

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools CFSG.AGLEmbedding
  CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

section Sylow

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {L U : Subgroup G}

theorem inf_normalizer_le_normalizer_of_sylow (hU : IsSylowOf p U L) {M : Subgroup G}
    (hUM : U ≤ M) (hML : M ⊓ L ≤ normalizer (U : Set G)) :
    M ⊓ normalizer (L : Set G) ≤ normalizer (U : Set G) := by
  have hconj : ∀ h ∈ M ⊓ normalizer (L : Set G), ∀ u ∈ U, h * u * h⁻¹ ∈ U := by
    intro h hh u hu
    have hVL : U.map (MulAut.conj h).toMonoidHom ≤ L := by
      rintro _ ⟨v, hv, rfl⟩
      exact (mem_normalizer_iff.mp hh.2 v).mp (hU.le hv)
    have hVN : U.map (MulAut.conj h).toMonoidHom ≤ normalizer (U : Set G) := by
      rintro _ ⟨v, hv, rfl⟩
      exact hML ⟨M.mul_mem (M.mul_mem hh.1 (hUM hv)) (M.inv_mem hh.1), hVL ⟨v, hv, rfl⟩⟩
    have heq := hU.eq_of_le le_sup_right (sup_le hVL hU.le)
      ((hU.isPGroup.map _).to_sup_of_normal_right' hU.isPGroup hVN)
    exact (le_sup_left.trans heq.le) ⟨u, hu, rfl⟩
  intro h hh
  rw [mem_normalizer_iff]
  refine fun u => ⟨hconj h hh u, fun hu => ?_⟩
  have h' := hconj h⁻¹ (inv_mem hh) _ hu
  rwa [show h⁻¹ * (h * u * h⁻¹) * h⁻¹⁻¹ = u by group] at h'

end Sylow

variable {G : Type} [Group G] [Finite G]

theorem BorelData3.inf_centralizer_le_normalizer_QK_sup {P : Sylow 3 G} {M : Subgroup G}
    {x : G} {n : ℕ} {f : GaloisField 3 n → G} {W : Subgroup G} (hB : BorelData3 P M x f W) :
    M ⊓ centralizer ({x} : Set G) ≤
      normalizer ((hB.QK ⊔ GLBPrimeCore 3 (centralizer ({x} : Set G)) : Subgroup G) : Set G) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨R, K, d, hfacts, hd, ⟨eK⟩, hρ, hsurj, -, -, hReq⟩ := hB.reduced
  have hKn : K.Normal := hfacts.red.normal
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set Ox : Subgroup G := GLBPrimeCore 3 C with hOx
  set X₀ : Subgroup (RedCent 3 x) := redCentM 3 M x with hX₀
  have hn1 : 1 ≤ n := by
    have := hB.three_le
    omega
  obtain ⟨hE, hcard⟩ := isElemAbelian_sylow_inf_of_psl2GF (p := 3) hn1 eK R
  have hrk : 2 ≤ Open.pRank 3 ((R : Subgroup (RedCent 3 x)) ⊓ K) := by
    have h1 := le_pRank_of_elemAbelian_card (p := 3) le_rfl hE hcard
    have := hB.three_le
    omega
  have hNX : normalizer (((R : Subgroup (RedCent 3 x)) ⊓ K : Subgroup (RedCent 3 x)) :
      Set (RedCent 3 x)) ≤ X₀ :=
    (CFSG.PreuniquenessRankFour.Helpers.fullCore_le_iff 3 2 _ _).mp hfacts.red.fullCore _
      inf_le_left hrk
  have hX₀K : X₀ ⊓ K ≤ normalizer (((R : Subgroup (RedCent 3 x)) ⊓ K : Subgroup (RedCent 3 x)) :
      Set (RedCent 3 x)) :=
    inf_le_normalizer_of_psl2GF (by norm_num) hn1 eK R hNX hfacts.red.not_le
  obtain ⟨T, hT⟩ := exists_sylow_map_subtype_eq_inf K R
  have hSyl : IsSylowOf 3 ((R : Subgroup (RedCent 3 x)) ⊓ K) K := ⟨T, hT⟩
  have hX₀N : X₀ ≤ normalizer (((R : Subgroup (RedCent 3 x)) ⊓ K : Subgroup (RedCent 3 x)) :
      Set (RedCent 3 x)) := by
    have h1 := inf_normalizer_le_normalizer_of_sylow hSyl (le_normalizer.trans hNX) hX₀K
    rwa [Subgroup.normalizer_eq_top, inf_top_eq] at h1
  intro h hh
  have hhC : h ∈ C := hh.2
  have hhX : QuotientGroup.mk' (primeComplementCore (G := C) 3) ⟨h, hhC⟩ ∈ X₀ :=
    ⟨⟨h, hhC⟩, mem_subgroupOf.mpr ⟨hhC, hh.1⟩, rfl⟩
  have hnormOx : ∀ r ∈ Ox, h * r * h⁻¹ ∈ Ox := fun r hr =>
    (mem_normalizer_iff.mp (le_normalizer_glbPrimeCore 3 C hhC) r).mp hr
  have hQ : ∀ q ∈ hB.QK, h * q * h⁻¹ ∈ hB.QK ⊔ Ox := by
    intro q hq
    obtain ⟨t, rfl⟩ := hB.mem_QK.mp hq
    obtain ⟨hct, hRt, -⟩ := hρ t
    have h1 := (mem_normalizer_iff.mp (hX₀N hhX)
      (QuotientGroup.mk' (primeComplementCore (G := C) 3) ⟨f t, hct⟩)).mp hRt
    obtain ⟨s, hcs, hs⟩ := hsurj _ h1
    have hu : h * f t * h⁻¹ ∈ C := C.mul_mem (C.mul_mem hhC hct) (C.inv_mem hhC)
    have hr : (f s)⁻¹ * (h * f t * h⁻¹) ∈ C := C.mul_mem (C.inv_mem hcs) hu
    have hmk : QuotientGroup.mk' (primeComplementCore (G := C) 3)
        ⟨(f s)⁻¹ * (h * f t * h⁻¹), hr⟩ = 1 := by
      have e : (⟨(f s)⁻¹ * (h * f t * h⁻¹), hr⟩ : C) =
          (⟨f s, hcs⟩ : C)⁻¹ * ((⟨h, hhC⟩ : C) * ⟨f t, hct⟩ * (⟨h, hhC⟩ : C)⁻¹) := rfl
      rw [e, map_mul, map_inv, hs, map_mul, map_mul, map_inv, inv_mul_cancel]
    have hrO := mem_glbPrimeCore_of_mk_eq_one hr hmk
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

end CFSG.LocalAnalysis.RankFourTheoremC
