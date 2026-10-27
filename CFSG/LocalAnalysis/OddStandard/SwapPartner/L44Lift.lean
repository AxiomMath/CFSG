module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.L44Excl
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.L44Quotient
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.AutProdCentral

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open CFSG.Blueprint Subgroup

theorem card_centralizer_ge_and_seven_dvd_card_of_perfect {H : Type} [Group H] [Finite H]
    (N D₀ : Subgroup H) [N.Normal] [D₀.Normal] (hN : ⁅N, N⁆ = N)
    (hD : ∀ h : H, h ∈ D₀ ↔ ∀ n ∈ N, h * n = n * h)
    (hS : LieModel (↥N ⧸ Subgroup.center ↥N) .PSL 4 2 2)
    (A : Subgroup (H ⧸ D₀)) (hAS : A ≤ N.map (QuotientGroup.mk' D₀))
    (eA : A ≃* alternatingGroup (Fin 8)) (t : H ⧸ D₀) (d : H)
    (ht1 : t ≠ 1) (ht2 : t * t = 1) (htA : ∀ a ∈ A, t * a = a * t)
    (hd2 : d * d = 1) (hdt : (d : H ⧸ D₀) * t = t * (d : H ⧸ D₀))
    (hdA : ∀ a ∈ A, (d : H ⧸ D₀) * a * (d : H ⧸ D₀)⁻¹ ∈ A)
    (hdout : ¬ ∃ a ∈ A, ∀ x ∈ A, (d : H ⧸ D₀) * x * (d : H ⧸ D₀)⁻¹ = a * x * a⁻¹) :
    15360 ≤ Nat.card (centralizer ({d} : Set H)) ∧
      (7 ∣ Nat.card (centralizer ({d} : Set H)) → 7 ∣ Nat.card D₀) := by
  classical
  let S : Subgroup (H ⧸ D₀) := N.map (QuotientGroup.mk' D₀)
  haveI : S.Normal :=
    Subgroup.Normal.map (H := N) inferInstance (QuotientGroup.mk' D₀)
      (QuotientGroup.mk'_surjective D₀)
  obtain ⟨e⟩ : Nonempty (↥S ≃* (↥N ⧸ Subgroup.center ↥N)) :=
    nonempty_mulEquiv_map_quotient_center N D₀ hD
  have hS' : LieModel S .PSL 4 2 2 := LieModel.of_mulEquiv e.symm hS
  have hC : ∀ y : H ⧸ D₀, (∀ s ∈ S, y * s = s * y) → y = 1 :=
    fun y hy => eq_one_of_commute_image_of_perfect N D₀ hN hD y hy
  have hd2' : (d : H ⧸ D₀) * (d : H ⧸ D₀) = 1 := by
    rw [← QuotientGroup.mk_mul, hd2, QuotientGroup.mk_one]
  obtain ⟨h1, h2⟩ :=
    card_centralizer_ge_and_not_seven_dvd_of_lieModel (Y := H ⧸ D₀) S A hS' hC hAS eA
      t (d : H ⧸ D₀) ht1 ht2 htA hd2' hdt hdA hdout
  exact ⟨le_trans h1 (card_centralizer_quotient_le D₀ d),
    fun h7 => dvd_card_of_dvd_centralizer_of_not_dvd_quotient D₀ d Nat.prime_seven h7 h2⟩

end CFSG.OddStandard.AltStdSec.SwapPartner
