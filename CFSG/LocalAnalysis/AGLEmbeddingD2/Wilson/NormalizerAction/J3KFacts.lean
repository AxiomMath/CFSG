module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3CoverFrame
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3CoverFacts
public import CFSG.RankThree.PartTwo.Sec21.Item2113Res3ProofJ3KSylow

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open CFSG.SectionRank.Native CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest
  CFSG.RankThree.Asc83Table CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec21 CFSG.Blueprint
  Subgroup
open scoped Matrix

theorem isElemAbelian_iff_isElementaryAbelian {p : ℕ} {G : Type*} [Group G] {E : Subgroup G} :
    CFSG.Assembly.IsElemAbelian p E ↔ IsElementaryAbelian p E :=
  (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p E).symm

variable
  (hchk : GammaWordFacts)
include hchk

theorem ks217J3CoverPreimage_of : KS217J3CoverPreimage := by
  intro X _ _ hX hT K hZK h81 hcomm hcube
  obtain ⟨hZ3, ⟨e⟩⟩ := hT
  set π := QuotientGroup.mk' (center X)
  have hker : π.ker = center X := QuotientGroup.ker_mk' _
  have hKbar : IsElementaryAbelian 3 (K.map π) := by
    rw [isElementaryAbelian_iff]
    constructor
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      have h1 : π (x * y * x⁻¹ * y⁻¹) = 1 := by
        rw [← MonoidHom.mem_ker, hker]
        exact hcomm x hx y hy
      rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
      calc π x * π y = (π x * π y * (π x)⁻¹ * (π y)⁻¹) * (π y * π x) := by group
        _ = π y * π x := by rw [h1, one_mul]
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, ← MonoidHom.mem_ker, hker]
      exact hcube x hx
  obtain ⟨k, hk, hKk, -⟩ := j3_frame hchk hX hZ3 e hKbar hZK (by rw [h81]; norm_num)
  rw [hKk]
  exact isElemAbelian_iff_isElementaryAbelian.2 hk.isElementaryAbelian_F0

theorem ks217J3CoverNoTransvection_of : KS217J3CoverNoTransvection := by
  intro X _ _ hX hT F hF hZF h81 y hy
  obtain ⟨hZ3, ⟨e⟩⟩ := hT
  have hFE : IsElementaryAbelian 3 F := isElemAbelian_iff_isElementaryAbelian.1 hF
  obtain ⟨k, hk, hFk, hnorm⟩ := j3_frame hchk hX hZ3 e
    (IsElementaryAbelian.map_hom (QuotientGroup.mk' (center X)) hFE) hZF h81
  subst hFk
  exact hk.not_transvection y (hnorm y hy) hy

theorem ks217J3CoverSylowFix_of : KS217J3CoverSylowFix := by
  intro X _ _ hX hT F hF hZF h81 f hf hfix
  obtain ⟨hZ3, ⟨e⟩⟩ := hT
  have hFE : IsElementaryAbelian 3 F := isElemAbelian_iff_isElementaryAbelian.1 hF
  obtain ⟨k, hk, hFk, hnorm⟩ := j3_frame hchk hX hZ3 e
    (IsElementaryAbelian.map_hom (QuotientGroup.mk' (center X)) hFE) hZF h81
  subst hFk
  obtain ⟨m, hm⟩ := hk.bEq.surjective ⟨f, hf⟩
  set a : Fin 4 → ZMod 3 := Multiplicative.toAdd m with ha
  have hfa : f = basisProd (xB k) a := by
    have h1 := congrArg Subtype.val hm
    have h2 : ((hk.bEq (Multiplicative.ofAdd a) : Subgroup.closure (Set.range (xB k))) : X) =
        basisProd (xB k) a := coe_basisEquiv _ _ _ a
    have h3 : Multiplicative.ofAdd a = m := rfl
    rw [h3] at h2
    exact h1.symm.trans h2
  have hpow : ∀ i : Fin 6, (i = 1 ∨ i = 2) → k i ^ 9 = 1 := by
    intro i hi
    have hm : powW i 9 ∈ eqWords := by
      rcases hi with rfl | rfl <;> simp [eqWords]
    have := hk.eqs _ hm
    rwa [evalW_powW] at this
  have hfixed : ∀ i : Fin 6, (i = 1 ∨ i = 2) → actMat i *ᵥ a = a := by
    intro i hi
    have hn : k i ∈ normalizer (F0 k : Set X) := hk.k_mem_normalizer i
    have h1 := hfix (k i) hn ⟨2, by
      rw [← map_pow]
      have : (⟨k i, hn⟩ : normalizer (F0 k : Set X)) ^ 3 ^ 2 = 1 :=
        Subtype.ext (by simpa using hpow i hi)
      rw [this, map_one]⟩
    rw [hfa, hk.conj_basisProd i a] at h1
    exact hk.basisProd_injective h1
  obtain ⟨h0, h1, h2⟩ := fix_triv a (hfixed 1 (Or.inl rfl)) (hfixed 2 (Or.inr rfl))
  rw [hfa, basisProd_xB, h0, h1, h2]
  simp only [ZMod.val_zero, pow_zero, one_mul]
  exact Subgroup.pow_mem _ hk.zc _

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
