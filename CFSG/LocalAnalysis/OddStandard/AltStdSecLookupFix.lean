module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic

public section

namespace CFSG.OddStandard.AltStdSec

open CFSG CFSG.ComponentClassification.CatLeaf Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem lookup_orderOf_eq_two_of_conj {S : Type} [Group S] [IsSimpleGroup S]
    (hna : ∃ x y : S, x * y ≠ y * x) {σ : MulAut S} (hσ2 : σ * σ = 1) (hσ1 : σ ≠ 1) {t : S}
    (ht : σ = MulAut.conj t) : orderOf t = 2 := by
  have hinj := mulAut_conj_injective_of_simple hna
  have ht2 : t ^ 2 = 1 := by
    apply hinj
    rw [map_pow, map_one, ← ht, sq]
    exact hσ2
  have ht1 : t ≠ 1 := by
    rintro rfl
    apply hσ1
    rw [ht, map_one]
  exact orderOf_eq_prime ht2 ht1

theorem lookup_fixedSubgroup_conj {S : Type} [Group S] (t : S) :
    fixedSubgroup (MulAut.conj t : MulAut S) = centralizer ({t} : Set S) := by
  ext x
  rw [mem_centralizer_singleton_iff]
  change t * x * t⁻¹ = x ↔ x * t = t * x
  rw [mul_inv_eq_iff_eq_mul]
  exact eq_comm

theorem isComponent_map_fixedSubgroup_conj {S : Type} [Group S] {t : S} {σ : MulAut S}
    (ht : σ = MulAut.conj t) {B : Subgroup (fixedSubgroup σ)} (hB : IsComponent B) :
    ∃ B' : Subgroup (centralizer ({t} : Set S)), IsComponent B' ∧ Nonempty (B' ≃* B) := by
  have hfix : fixedSubgroup σ = centralizer ({t} : Set S) := by
    rw [ht]
    exact lookup_fixedSubgroup_conj t
  let φ := MulEquiv.subgroupCongr hfix
  exact ⟨B.map φ.toMonoidHom, CFSG.LocalCores.isComponent_map_mulEquiv φ hB,
    ⟨(B.equivMapOfInjective φ.toMonoidHom φ.injective).symm⟩⟩

theorem lookup_card_dvd_of_fixed {S : Type} [Group S] [Finite S] {σ : MulAut S}
    (B : Subgroup (fixedSubgroup σ)) : Nat.card B ∣ Nat.card S :=
  (Subgroup.card_subgroup_dvd_card B).trans (Subgroup.card_subgroup_dvd_card _)

end CFSG.OddStandard.AltStdSec
