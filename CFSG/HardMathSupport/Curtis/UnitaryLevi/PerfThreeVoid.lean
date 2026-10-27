module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeCensus
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutDiagLevi
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusBase

public section

namespace CFSG.AGLEmbedding.UnitaryLevi

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.AGLEmbedding.LieOut
open CFSG.AGLEmbedding.ParabPrime (exists_perfect_map_eq)
open scoped commutatorElement

section Reduction

theorem card_eq_two_of_perfect_coprime_comp {Y : Type} [Group Y] [Finite Y] {L J : Subgroup Y}
    (h : CompParab L J)
    (hperf : ∀ U : Subgroup Y, U ≤ J → ⁅U, U⁆ = U → Nat.Coprime 3 (Nat.card U))
    (d : TauCeti.ValidLieTypeIndex) (hd : IsClassicalOrG2Index d.1)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* (TauCeti.CFSGIndex.lie d).Group) :
    IsClassicalOrG2IndexTwo d.1 := by
  obtain ⟨hJL, T, hT, hNT⟩ := h.parab
  refine isClassicalOrG2IndexTwo_of_perfect_coprime d hd e (barSylow hT) (quotImage L J)
    (normalizer_barSylow_le_quotImage hT hNT)
    (quotImage_ne_normalizer hT hJL (h.ne_borel T hT) hNT) ?_
  intro U hUJ hUperf
  have hker : (QuotientGroup.mk' (Subgroup.center ↥L)).ker ≤ Subgroup.center ↥L := by
    rw [QuotientGroup.ker_mk']
  have hUrange : U ≤ (QuotientGroup.mk' (Subgroup.center ↥L)).range := by
    rw [MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]
    exact le_top
  obtain ⟨W, hWperf, hWle, hWmap⟩ := exists_perfect_map_eq _ hker hUperf hUrange
  have hWJ : W.map L.subtype ≤ J := by
    rintro _ ⟨w, hw, rfl⟩
    show (w : Y) ∈ J
    have hwU : (QuotientGroup.mk w : ↥L ⧸ Subgroup.center ↥L) ∈ U := by
      rw [← hWmap]
      exact Subgroup.mem_map_of_mem _ hw
    obtain ⟨l, hlJ, hl⟩ := mem_quotImage.1 (hUJ hwU)
    have hz : l⁻¹ * w ∈ Subgroup.center ↥L := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hl,
        inv_mul_cancel]
    have hzJ := center_le_of_normalizer_le hT hNT hz
    have : (w : Y) = (l : Y) * ((l⁻¹ * w : L) : Y) := by simp
    rw [this]
    exact J.mul_mem hlJ hzJ
  have hWperf' : ⁅W.map L.subtype, W.map L.subtype⁆ = W.map L.subtype := by
    rw [← Subgroup.map_commutator, hWperf]
  have hcop := hperf _ hWJ hWperf'
  have hcard : Nat.card W = Nat.card (W.map L.subtype) :=
    Nat.card_congr (W.equivMapOfInjective L.subtype L.subtype_injective).toEquiv
  rw [← hcard] at hcop
  have hdvd : Nat.card U ∣ Nat.card W := by
    rw [← hWmap]
    exact Subgroup.card_map_dvd _ _
  exact Nat.Coprime.coprime_dvd_right hdvd hcop

end Reduction

end CFSG.AGLEmbedding.UnitaryLevi
