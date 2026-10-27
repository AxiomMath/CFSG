module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Interface
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableVIIProof.PermFive
import CFSG.Mathlib.GroupTheory.PermCommute

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog Equiv

structure TableVIICover (Y : Type*) [Group Y] (w : Y) (π : Y →* Perm (Fin 5)) : Prop where
  surj : Function.Surjective π
  ker_eq : π.ker = Subgroup.zpowers w
  le_comm : Subgroup.zpowers w ≤ commutator Y
  ne_one : w ≠ 1
  sq : w ^ 2 = 1

variable {Y : Type*} [Group Y]

theorem tableVII_card_of_shape (hY : IsNonsplitDoubleCoverOfS5 Y) : Nat.card Y = 240 := by
  obtain ⟨Z, _, hZcard, ⟨e⟩, -⟩ := hY
  have hq : Nat.card (Y ⧸ Z) = 120 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
    norm_num
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Z, hZcard, hq]

theorem tableVII_cover_of_shape (hY : IsNonsplitDoubleCoverOfS5 Y) {w : Y}
    (hw : w ∈ Subgroup.center Y) (hw1 : w ≠ 1) : ∃ π : Y →* Perm (Fin 5), TableVIICover Y w π := by
  obtain ⟨Z, hZn, hZcard, ⟨e⟩, hZc⟩ := hY
  haveI : Z.Normal := hZn
  let π : Y →* Perm (Fin 5) := e.toMonoidHom.comp (QuotientGroup.mk' Z)
  have hπsurj : Function.Surjective π :=
    e.surjective.comp (QuotientGroup.mk'_surjective Z)
  have hπker : π.ker = Z := by
    show (e.toMonoidHom.comp (QuotientGroup.mk' Z)).ker = Z
    rw [MonoidHom.ker_comp_of_injective (QuotientGroup.mk' Z) e.toMonoidHom e.injective,
      QuotientGroup.ker_mk']
  have hcomm : ∀ y : Y, w * y = y * w :=
    fun y => (Subgroup.mem_center_iff.mp hw y).symm
  have hπw : π w = 1 :=
    CFSG.perm_eq_one_of_forall_commute (by simp) fun σ => by
      obtain ⟨y, rfl⟩ := hπsurj σ
      calc π w * π y = π (w * y) := (map_mul π w y).symm
        _ = π (y * w) := by rw [hcomm y]
        _ = π y * π w := map_mul π y w
  have hwZ : w ∈ Z := by
    rw [← hπker, MonoidHom.mem_ker]
    exact hπw
  have hw2 : orderOf w = 2 := by
    have hdvd : orderOf w ∣ 2 := by
      have h := Subgroup.orderOf_dvd_natCard Z hwZ
      rwa [hZcard] at h
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hw1
    · exact h
  have hwsq : w ^ 2 = 1 := by
    have h := pow_orderOf_eq_one w
    rwa [hw2] at h
  have hZp : Subgroup.zpowers w = Z := by
    haveI : Finite Z := Nat.finite_of_card_ne_zero (by rw [hZcard]; norm_num)
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hwZ) ?_
    simp [hZcard, Nat.card_zpowers, hw2]
  have hZeq : Z = Subgroup.zpowers w := hZp.symm
  refine ⟨π, hπsurj, hπker.trans hZeq, ?_, hw1, hwsq⟩
  rw [← hZeq]
  exact hZc

variable {w : Y} {π : Y →* Perm (Fin 5)}

theorem tableVII_cover_card (hC : TableVIICover Y w π) : Nat.card Y = 240 := by
  have hq : Nat.card (Y ⧸ π.ker) = 120 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hC.surj).toEquiv,
      Nat.card_perm, Nat.card_fin]
    norm_num
  have hker : Nat.card π.ker = 2 := by
    rw [hC.ker_eq, Nat.card_zpowers, orderOf_eq_prime hC.sq hC.ne_one]
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker, hq, hker]

theorem tableVII_cover_mem_zpowers (hC : TableVIICover Y w π) {y : Y} :
    y ∈ Subgroup.zpowers w ↔ y = 1 ∨ y = w := by
  constructor
  · intro hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hz2 : w ^ (2 : ℤ) = 1 := by simpa using hC.sq
    rw [zpow_eq_zpow_emod k hz2]
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left; rw [h]; exact zpow_zero w
    · right; rw [h]; exact zpow_one w
  · rintro (h1 | h2)
    · rw [h1]; exact Subgroup.one_mem _
    · rw [h2]; exact Subgroup.mem_zpowers w

theorem tableVII_cover_pi_eq_one (hC : TableVIICover Y w π) {y : Y} :
    π y = 1 ↔ y = 1 ∨ y = w := by
  rw [← MonoidHom.mem_ker, hC.ker_eq]
  exact tableVII_cover_mem_zpowers hC

theorem tableVII_cover_central (hC : TableVIICover Y w π) (y : Y) : w * y = y * w := by
  have hw1 : π w = 1 := (tableVII_cover_pi_eq_one hC).mpr (Or.inr rfl)
  have hker : y * w * y⁻¹ ∈ Subgroup.zpowers w := by
    rw [← hC.ker_eq, MonoidHom.mem_ker]
    rw [map_mul, map_mul, map_inv, hw1]
    group
  rcases (tableVII_cover_mem_zpowers hC).mp hker with h | h
  · exfalso
    apply hC.ne_one
    have h' : y * w = y * 1 := by
      rw [mul_one]
      exact mul_inv_eq_one.mp h
    exact mul_left_cancel h'
  · exact (mul_inv_eq_iff_eq_mul.mp h).symm

theorem tableVII_cover_comm_eq (hC : TableVIICover Y w π) :
    commutator Y = (alternatingGroup (Fin 5)).comap π := by
  refine le_antisymm ?_ ?_
  · rw [commutator_def, Subgroup.commutator_le]
    intro y1 _ y2 _
    rw [Subgroup.mem_comap, map_commutatorElement π, Equiv.Perm.mem_alternatingGroup,
      map_commutatorElement Perm.sign]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
  · intro y hy
    rw [Subgroup.mem_comap] at hy
    have hmap : (commutator Y).map π = alternatingGroup (Fin 5) := by
      rw [commutator_def]
      rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective π hC.surj, ← commutator_def,
        tableVII_perm_commutator]
    have hmem : π y ∈ (commutator Y).map π := by rw [hmap]; exact hy
    obtain ⟨y', hy', hyy'⟩ := Subgroup.mem_map.mp hmem
    have hker : y * y'⁻¹ ∈ Subgroup.zpowers w := by
      rw [← hC.ker_eq, MonoidHom.mem_ker, map_mul, map_inv, hyy']
      simp
    have hyeq : y = (y * y'⁻¹) * y' := by group
    rw [hyeq]
    exact mul_mem (hC.le_comm hker) hy'

theorem tableVII_cover_mem_comm (hC : TableVIICover Y w π) {y : Y} :
    y ∈ commutator Y ↔ Perm.sign (π y) = 1 := by
  rw [tableVII_cover_comm_eq hC, Subgroup.mem_comap, Equiv.Perm.mem_alternatingGroup]

theorem tableVII_cover_card_comm (hC : TableVIICover Y w π) : Nat.card (commutator Y) = 120 := by
  have hidx : (commutator Y).index = 2 := by
    rw [tableVII_cover_comm_eq hC,
      Subgroup.index_comap_of_surjective (alternatingGroup (Fin 5)) hC.surj,
      alternatingGroup.index_eq_two]
  have hcard := Subgroup.card_mul_index (commutator Y)
  rw [hidx, tableVII_cover_card hC] at hcard
  omega

end CFSG.EvenSporadicStandard.HNRecog.Section3
