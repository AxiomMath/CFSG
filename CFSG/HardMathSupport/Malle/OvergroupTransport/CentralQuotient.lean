module

public import CFSG.HardMathSupport.Malle.OvergroupTransport.Transport
import CFSG.LieType.BorelTits.CentralQuotient

public section

namespace CFSG.HardMathSupport.Malle.OvergroupTransport

theorem NormalizerMaximal.of_quotient_center {X : Type*} [Group X] (Z : Subgroup X) [Z.Normal]
    {r : ℕ} (hZ : Z ≤ Subgroup.center X) (hZr : Nat.Coprime (Nat.card Z) r) {U : Subgroup X}
    (hU : IsPGroup r U) (h : NormalizerMaximal (U.map (QuotientGroup.mk' Z))) :
    NormalizerMaximal U := by
  intro H hH
  have hN : Subgroup.normalizer (U : Set X) =
      (Subgroup.normalizer (U.map (QuotientGroup.mk' Z) : Set (X ⧸ Z))).comap
        (QuotientGroup.mk' Z) :=
    CFSG.LieType.BorelTits.normalizer_eq_comap_normalizer_map Z hZ hZr hU
  have hker : (QuotientGroup.mk' Z).ker ≤ H := by
    rw [QuotientGroup.ker_mk']
    exact hZ.trans ((Subgroup.center_le_normalizer (U : Set X)).trans hH)
  have hle : Subgroup.normalizer (U.map (QuotientGroup.mk' Z) : Set (X ⧸ Z)) ≤
      H.map (QuotientGroup.mk' Z) := by
    rw [← Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Z)
      (Subgroup.normalizer (U.map (QuotientGroup.mk' Z) : Set (X ⧸ Z)))]
    exact Subgroup.map_mono (hN ▸ hH)
  rcases h (H.map (QuotientGroup.mk' Z)) hle with h1 | h1
  · left
    calc H = (H.map (QuotientGroup.mk' Z)).comap (QuotientGroup.mk' Z) :=
          (Subgroup.comap_map_eq_self hker).symm
      _ = (Subgroup.normalizer (U.map (QuotientGroup.mk' Z) : Set (X ⧸ Z))).comap
            (QuotientGroup.mk' Z) := by rw [h1]
      _ = Subgroup.normalizer (U : Set X) := hN.symm
  · right
    calc H = (H.map (QuotientGroup.mk' Z)).comap (QuotientGroup.mk' Z) :=
          (Subgroup.comap_map_eq_self hker).symm
      _ = (⊤ : Subgroup (X ⧸ Z)).comap (QuotientGroup.mk' Z) := by rw [h1]
      _ = ⊤ := Subgroup.comap_top _

end CFSG.HardMathSupport.Malle.OvergroupTransport
