module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.HGenFinal
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFourOneProof
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem commutator_mem_relPPrimeCore_of_mem_kSub_of_mem_xSub {M H : Subgroup G} {p : ℕ}
    (hp : p.Prime) {k w : G} (hk : k ∈ kSub p M H) (hw : w ∈ xSub p M H) :
    ⁅k, w⁆ ∈ relPPrimeCore p H := by
  have hkH : k ∈ H := kSub_le p M H hk
  have hwX : w ∈ CFSG.AGLEmbedding.d1PlusCore p H (kStar p M H) := hw
  obtain ⟨wH, hwCent, rfl⟩ := Subgroup.mem_map.mp hwX
  let π : ↥H →* (↥H ⧸ primeComplementCore (G := ↥H) p) :=
    QuotientGroup.mk' (primeComplementCore (G := ↥H) p)
  let kH : ↥H := ⟨k, hkH⟩
  have hkKstar : π kH ∈ kStar p M H := by
    refine Subgroup.mem_map.mpr ⟨kH, ?_, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr hk
  have hcomm : π kH * π wH = π wH * π kH :=
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_comap.mp hwCent)) (π kH) hkKstar
  have hker : π (kH * wH * kH⁻¹ * wH⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    calc π kH * π wH * (π kH)⁻¹ * (π wH)⁻¹
        = (π wH * π kH) * (π kH)⁻¹ * (π wH)⁻¹ := by rw [hcomm]
      _ = 1 := by group
  rw [relPPrimeCore_eq_map hp H]
  refine Subgroup.mem_map.mpr ⟨kH * wH * kH⁻¹ * wH⁻¹, ?_, ?_⟩
  · exact (QuotientGroup.eq_one_iff (N := primeComplementCore (G := ↥H) p) _).mp hker
  · rfl

private theorem commutator_mem_relPPrimeCore_of_mem_relPPrimeCore {H : Subgroup G} {p : ℕ}
    (hH : H ≤ Subgroup.normalizer (relPPrimeCore p H : Set G))
    {o w : G} (ho : o ∈ relPPrimeCore p H) (hw : w ∈ H) :
    ⁅o, w⁆ ∈ relPPrimeCore p H := by
  have hconj : w * o⁻¹ * w⁻¹ ∈ relPPrimeCore p H :=
    (Subgroup.mem_normalizer_iff.mp (hH hw) (o⁻¹)).1 ((relPPrimeCore p H).inv_mem ho)
  rw [commutatorElement_def,
    show o * w * o⁻¹ * w⁻¹ = o * (w * o⁻¹ * w⁻¹) from by group]
  exact (relPPrimeCore p H).mul_mem ho hconj

theorem not_le_xSub_of_isPGroup {M : Subgroup G} {p : ℕ} {Q H : Subgroup G}
    (h : TwelveCtx G M p Q H) (hI : NineNineOneInput) {W : Subgroup G}
    (hW : IsPGroup p W) (hCW : Subgroup.centralizer (W : Set G) ≤ M) :
    ¬ W ≤ xSub p M H := by
  intro hWX
  haveI : Fact p.Prime := ⟨h.p_prime⟩
  have hKH : kSub p M H ≤ H := kSub_le p M H
  have hOH : relPPrimeCore p H ≤ H := relPPrimeCore_le (p := p) H
  have hHnorm : H ≤ Subgroup.normalizer (relPPrimeCore p H : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOH).mp (relPPrimeCore_normal h.p_prime H)
  have hWH : W ≤ H := hWX.trans (xSub_le_H p M H)
  have hOcop : ¬ p ∣ Nat.card (relPPrimeCore p H) :=
    (Nat.Prime.coprime_iff_not_dvd h.p_prime).mp (coprime_card_relPPrimeCore h.p_prime H)
  have hc : ∀ n ∈ kSub p M H ⊔ relPPrimeCore p H, ∀ w ∈ W,
      ⁅n, w⁆ ∈ relPPrimeCore p H := by
    intro n hn w hw
    have hwX : w ∈ xSub p M H := hWX hw
    have hKW : ∀ k ∈ kSub p M H, ⁅k, w⁆ ∈ relPPrimeCore p H := fun k hk =>
      commutator_mem_relPPrimeCore_of_mem_kSub_of_mem_xSub h.p_prime hk hwX
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right (kSub p M H)
      (relPPrimeCore p H) (hKH.trans hHnorm), Set.mem_mul] at hn
    rcases hn with ⟨k, hk, o, ho, rfl⟩
    have hoW : ⁅o, w⁆ ∈ relPPrimeCore p H :=
      commutator_mem_relPPrimeCore_of_mem_relPPrimeCore hHnorm ho (hWH hw)
    have hconj : k * ⁅o, w⁆ * k⁻¹ ∈ relPPrimeCore p H :=
      (Subgroup.mem_normalizer_iff.mp (hHnorm (hKH hk)) ⁅o, w⁆).1 hoW
    have hprod : (k * ⁅o, w⁆ * k⁻¹) * ⁅k, w⁆ ∈ relPPrimeCore p H :=
      (relPPrimeCore p H).mul_mem hconj (hKW k hk)
    rw [show ⁅k * o, w⁆ = (k * ⁅o, w⁆ * k⁻¹) * ⁅k, w⁆ from by
      simp only [commutatorElement_def]; group]
    exact hprod
  have hNO : kSub p M H ⊔ relPPrimeCore p H ≤
      Subgroup.normalizer (relPPrimeCore p H : Set G) :=
    sup_le (hKH.trans hHnorm) Subgroup.le_normalizer
  have hWO : W ≤ Subgroup.normalizer (relPPrimeCore p H : Set G) := hWH.trans hHnorm
  have hcop := CFSG.LocalAnalysis.GLTheoremA.inf_centralizer_sup_eq_of_commutator_le
    (p := p) h.p_prime (W := kSub p M H ⊔ relPPrimeCore p H)
    (O := relPPrimeCore p H) (P := W) hW hOcop le_sup_right hNO hWO hc
  have hNM : kSub p M H ⊔ relPPrimeCore p H ≤ M := by
    rw [← hcop]
    exact sup_le (inf_le_right.trans hCW) (relPPrimeCore_le_M_of_twelveCtx h)
  exact not_kSub_le_M_of_nineNineOne h hI (le_sup_left.trans hNM)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
