module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutRadical
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutBasic
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSL
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSp
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSU
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSpinMinus
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeG2
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocal

public section

namespace CFSG.AGLEmbedding.LieOut

open CFSG.AGLEmbedding.ParabHub CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Unitary
open CFSG.SignalizerFunctorTheorem.CatalogBridge (NonLocalized)

@[expose] def OvergroupLocal (Y : Type) [Group Y] : Prop :=
  ∀ (S : Sylow 2 Y) (J : Subgroup Y), Subgroup.normalizer ((S : Subgroup Y) : Set Y) ≤ J →
    J ≠ ⊤ → ∃ R : Subgroup Y, R ≠ ⊥ ∧ IsPGroup 2 R ∧ J ≤ Subgroup.normalizer (R : Set Y)

theorem overgroupLocal_of_borelQuotient {K Y : Type} [Group K] [Finite K] [Group Y] [Finite Y]
    {D : CFSG.LieType.Universal.UniversalRootDatum K} {n : Fin D.rank → K}
    {H : Fin D.rank → Subgroup K} {π : K →* Y} {M : ℕ} (h : BorelQuotient D n H π M) :
    OvergroupLocal Y := by
  intro S J hNJ hJ
  obtain ⟨π', hπ', hker, hT⟩ := h.exists_conj_eq S
  have hQ : BorelQuotient D n H π' M :=
    { ct := h.ct, extras := h.extras, pGroup := h.pGroup, surj := hπ', odd := h.odd
      torus_pow := h.torus_pow
      ker_central := fun z hz => h.ker_central z (hker ▸ hz)
      ker_pow := fun z hz => h.ker_pow z (hker ▸ hz) }
  have hNπ := hQ.normalizer_map_posUnipotent
  rw [← hT] at hNπ
  exact exists_normal_twoGroup_of_borel_le hQ (hNπ ▸ hNJ) hJ

theorem overgroupLocal_of_model_psl {Y : Type} [Group Y] [Finite Y] {n f : ℕ}
    (h : StatedClassicalModel Y .PSL n 2 f) : OvergroupLocal Y := by
  obtain ⟨⟨-, -, hn, -⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact overgroupLocal_of_borelQuotient
    (borelQuotient_sl ((projectiveSpecialLinearGroupEquivStatedProj (m + 1) F).trans e.symm))

theorem overgroupLocal_of_model_psp {Y : Type} [Group Y] [Finite Y] {n f : ℕ}
    (h : StatedClassicalModel Y .PSp n 2 f) : OvergroupLocal Y := by
  obtain ⟨-, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  exact overgroupLocal_of_borelQuotient (borelQuotient_sp e)

theorem overgroupLocal_of_model_psu {Y : Type} [Group Y] [Finite Y] {n f : ℕ}
    (h : StatedClassicalModel Y .PSU n 2 f) : OvergroupLocal Y := by
  obtain ⟨⟨-, -, hn, -⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hcard, pow_mul])
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hcard
  exact overgroupLocal_of_borelQuotient (borelQuotient_su hcard (by omega) ζ hζ e)

theorem overgroupLocal_of_model_pomegaPlus {Y : Type} [Group Y] [Finite Y] {n f : ℕ}
    (h : StatedClassicalModel Y .POmegaPlus n 2 f) : OvergroupLocal Y := by
  obtain ⟨⟨-, -, hn⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have : NeZero n := ⟨by omega⟩
  have : Finite (spinGroup (quadPlus n F)) :=
    CFSG.LieType.Steinberg.finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadPlus (n := n) (K := F))
  exact overgroupLocal_of_borelQuotient (borelQuotient_spinPlus (by omega) e)

theorem overgroupLocal_of_model_pomegaMinus {Y : Type} [Group Y] [Finite Y] {n f : ℕ}
    (h : StatedClassicalModel Y .POmegaMinus n 2 f) : OvergroupLocal Y := by
  obtain ⟨⟨-, -, hn⟩, F, hF, hFfin, hcard, b, c, hirr, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have : Finite (spinGroup (quadMinus n F b c)) :=
    CFSG.LieType.Steinberg.finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus hirr)
  exact overgroupLocal_of_borelQuotient (borelQuotient_spinMinus hirr (by omega) e)

section G2


theorem overgroupLocal_of_g2 {K : Type} [Field K] [Finite K] [CharP K 2] {Y : Type} [Group Y]
    [Finite Y] (e : Y ≃* CFSG.Blueprint.AdjointQuotient CFSG.Blueprint.Chevalley.Tag.G2 K) :
    OvergroupLocal Y :=
  overgroupLocal_of_borelQuotient (borelQuotient_g2 e)

end G2

theorem not_le_quotImage_of_nonLocalized {Y : Type} [Group Y] [Finite Y] {L T J : Subgroup Y}
    (hOL : OvergroupLocal (↥L ⧸ Subgroup.center ↥L)) (hT : IsSylowTwoOf T L)
    (hJ : L ⊓ Subgroup.normalizer (T : Set Y) ≤ J) (hJL : J ≤ L) (hne : J ≠ L)
    {N₀ : Subgroup (↥L ⧸ Subgroup.center ↥L)} (hN₀ : NonLocalized N₀) :
    ¬ N₀ ≤ quotImage L J := by
  intro hle
  obtain ⟨R, hR1, hR2, hR3⟩ := hOL (barSylow hT) (quotImage L J)
    (normalizer_barSylow_le_quotImage hT hJ) (quotImage_ne_top hT hJ hJL hne)
  have : Group.IsNilpotent R := hR2.isNilpotent
  exact hN₀ R hR1 inferInstance (hle.trans hR3)

end CFSG.AGLEmbedding.LieOut
