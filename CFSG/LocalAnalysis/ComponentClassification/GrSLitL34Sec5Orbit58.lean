module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Steps

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem oddIn_conjugate_eq (K : Subgroup G) (c : G) :
    oddIn (conjugate K c) = conjugate (oddIn K) c := by
  have h := pPrimeCore_map_iso 2 (K.equivMapOfInjective (MulAut.conj c⁻¹).toMonoidHom
    (MulAut.conj c⁻¹).injective)
  unfold conjugate oddIn
  rw [← h, map_map, map_map]
  rfl

omit [Finite G] in
theorem commutator_le_oddIn_conjugate_iff {K D : Subgroup G} {c : G}
    (hD : conjugate D c = D) :
    ⁅conjugate K c, D⁆ ≤ oddIn (conjugate K c) ↔ ⁅K, D⁆ ≤ oddIn K := by
  have h1 : ⁅conjugate K c, D⁆ = conjugate ⁅K, D⁆ c := by
    calc ⁅conjugate K c, D⁆ = ⁅conjugate K c, conjugate D c⁆ := by rw [hD]
      _ = conjugate ⁅K, D⁆ c := by rw [conjugate, conjugate, conjugate, map_commutator]
  rw [h1, oddIn_conjugate_eq]
  exact map_le_map_iff_of_injective (MulAut.conj c⁻¹).injective

omit [Finite G] in
theorem commutator_mul_commuting_eq {a b c d : G} (hca : Commute c a) (hcb : Commute c b)
    (hda : Commute d a) (hdb : Commute d b) (hcd : Commute c d) :
    (a * c)⁻¹ * (b * d)⁻¹ * (a * c) * (b * d) = a⁻¹ * b⁻¹ * a * b := by
  have hc : Commute c (a⁻¹ * d⁻¹ * b⁻¹ * a) :=
    ((hca.inv_right.mul_right hcd.inv_right).mul_right hcb.inv_right).mul_right hca
  have hd : Commute d (b⁻¹ * a * b) := (hdb.inv_right.mul_right hda).mul_right hdb
  calc (a * c)⁻¹ * (b * d)⁻¹ * (a * c) * (b * d)
      = c⁻¹ * ((a⁻¹ * d⁻¹ * b⁻¹ * a) * c) * b * d := by group
    _ = c⁻¹ * (c * (a⁻¹ * d⁻¹ * b⁻¹ * a)) * b * d := by rw [← hc.eq]
    _ = a⁻¹ * (d⁻¹ * ((b⁻¹ * a * b) * d)) := by group
    _ = a⁻¹ * (d⁻¹ * (d * (b⁻¹ * a * b))) := by rw [← hd.eq]
    _ = a⁻¹ * b⁻¹ * a * b := by group

omit [Finite G] in
theorem mem_normalizer_sup_of_normalizes {X Y : Subgroup G} {g : G}
    (hX : g ∈ normalizer (X : Set G)) (hY : g ∈ normalizer (Y : Set G)) :
    g ∈ normalizer ((X ⊔ Y : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq] at hX hY ⊢
  rw [Subgroup.map_sup, hX, hY]

end CFSG.ComponentClassification.GrSLit.GrS5
