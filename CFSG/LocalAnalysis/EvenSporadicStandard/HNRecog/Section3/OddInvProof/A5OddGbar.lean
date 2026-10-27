module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.OddInvProof.A5OddCent
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.OddInvProof.A5OddFive

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private theorem a5Gbar_card_centralizer {Γ : Type*} [Group Γ] (e : Γ ≃* A5WrTwo)
    (u : Γ) : Nat.card (Subgroup.centralizer ({e u} : Set A5WrTwo)) =
      Nat.card (Subgroup.centralizer ({u} : Set Γ)) := by
  have hmap : (Subgroup.centralizer ({u} : Set Γ)).map e.toMonoidHom =
      Subgroup.centralizer ({e u} : Set A5WrTwo) := by
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff,
      MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [← map_mul, ← map_mul, hz]
    · intro hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      apply e.injective
      rw [map_mul, map_mul, e.apply_symm_apply, hy]
  rw [← hmap, Subgroup.card_map_of_injective e.injective]

private theorem a5Gbar_mem_commutator {Γ : Type*} [Group Γ] (e : Γ ≃* A5WrTwo)
    (u : Γ) : u ∈ commutator Γ ↔ e u ∈ commutator A5WrTwo := by
  have hmap : (commutator Γ).map e.toMonoidHom = commutator A5WrTwo := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e.surjective]
  rw [← hmap, Subgroup.mem_map_equiv]
  simp

theorem oddInv_gbar_orderOf {Γ : Type*} [Group Γ] (e : Γ ≃* A5WrTwo) {u v : Γ}
    (hu : u ∉ _root_.commutator Γ) (hv : v ∉ _root_.commutator Γ) (hu2 : u ^ 2 = 1)
    (hv2 : v ^ 2 = 1) (hodd : Odd (orderOf (u * v))) :
    orderOf (u * v) = 1 ∨ orderOf (u * v) = 3 ∨ orderOf (u * v) = 5 := by
  have heu : e u ∉ _root_.commutator A5WrTwo :=
    fun h => hu ((a5Gbar_mem_commutator e u).mpr h)
  have hev : e v ∉ _root_.commutator A5WrTwo :=
    fun h => hv ((a5Gbar_mem_commutator e v).mpr h)
  have heu2 : (e u) ^ 2 = 1 := by rw [← map_pow, hu2, map_one]
  have hev2 : (e v) ^ 2 = 1 := by rw [← map_pow, hv2, map_one]
  have heodd : Odd (orderOf (e u * e v)) := by
    rw [← map_mul, MulEquiv.orderOf_eq]
    exact hodd
  have horder : orderOf (u * v) = orderOf (e u * e v) := by
    rw [← map_mul, MulEquiv.orderOf_eq]
  rcases oddInv_wr_orderOf_mul heu hev heu2 hev2 heodd with h | h | h
  · exact Or.inl (by rw [horder]; exact h)
  · exact Or.inr (Or.inl (by rw [horder]; exact h))
  · exact Or.inr (Or.inr (by rw [horder]; exact h))

theorem oddInv_gbar_card_three {Γ : Type*} [Group Γ] (e : Γ ≃* A5WrTwo) {u v : Γ}
    (hu : u ∉ _root_.commutator Γ) (hv : v ∉ _root_.commutator Γ) (hu2 : u ^ 2 = 1)
    (hv2 : v ^ 2 = 1) (h3 : orderOf (u * v) = 3) :
    Nat.card ↥(Subgroup.centralizer ({u * v} : Set Γ)) = 18 := by
  have heu : e u ∉ _root_.commutator A5WrTwo :=
    fun h => hu ((a5Gbar_mem_commutator e u).mpr h)
  have hev : e v ∉ _root_.commutator A5WrTwo :=
    fun h => hv ((a5Gbar_mem_commutator e v).mpr h)
  have heu2 : (e u) ^ 2 = 1 := by rw [← map_pow, hu2, map_one]
  have hev2 : (e v) ^ 2 = 1 := by rw [← map_pow, hv2, map_one]
  have h3' : orderOf (e u * e v) = 3 := by
    rw [← map_mul, MulEquiv.orderOf_eq]
    exact h3
  have hcard := oddInv_wr_card_three heu hev heu2 hev2 h3'
  rw [← a5Gbar_card_centralizer e (u * v), map_mul]
  exact hcard

theorem oddInv_gbar_card_five {Γ : Type*} [Group Γ] (e : Γ ≃* A5WrTwo) {u v : Γ}
    (hu : u ∉ _root_.commutator Γ) (hv : v ∉ _root_.commutator Γ) (hu2 : u ^ 2 = 1)
    (hv2 : v ^ 2 = 1) (h5 : orderOf (u * v) = 5) :
    Nat.card ↥(Subgroup.centralizer ({u * v} : Set Γ)) = 50 := by
  have heu : e u ∉ _root_.commutator A5WrTwo :=
    fun h => hu ((a5Gbar_mem_commutator e u).mpr h)
  have hev : e v ∉ _root_.commutator A5WrTwo :=
    fun h => hv ((a5Gbar_mem_commutator e v).mpr h)
  have heu2 : (e u) ^ 2 = 1 := by rw [← map_pow, hu2, map_one]
  have hev2 : (e v) ^ 2 = 1 := by rw [← map_pow, hv2, map_one]
  have h5' : orderOf (e u * e v) = 5 := by
    rw [← map_mul, MulEquiv.orderOf_eq]
    exact h5
  have hcard := oddInv_wr_card_five heu hev heu2 hev2 h5'
  rw [← a5Gbar_card_centralizer e (u * v), map_mul]
  exact hcard

theorem oddInv_gbar_exists_outer {Γ : Type*} [Group Γ] (e : Γ ≃* A5WrTwo) {u v : Γ}
    (hu : u ∉ _root_.commutator Γ) (hv : v ∉ _root_.commutator Γ) (hu2 : u ^ 2 = 1)
    (hv2 : v ^ 2 = 1) :
    ∃ w : Γ, w ^ 2 = 1 ∧ w ∉ _root_.commutator Γ ∧ w * (u * v) = u * v * w := by
  have heu : e u ∉ _root_.commutator A5WrTwo :=
    fun h => hu ((a5Gbar_mem_commutator e u).mpr h)
  have hev : e v ∉ _root_.commutator A5WrTwo :=
    fun h => hv ((a5Gbar_mem_commutator e v).mpr h)
  have heu2 : (e u) ^ 2 = 1 := by rw [← map_pow, hu2, map_one]
  have hev2 : (e v) ^ 2 = 1 := by rw [← map_pow, hv2, map_one]
  obtain ⟨w', hw'2, hw'out, hw'c⟩ := oddInv_wr_exists_outer heu hev heu2 hev2
  refine ⟨e.symm w', ?_, ?_, ?_⟩
  · apply e.injective
    rw [map_pow, e.apply_symm_apply, map_one, hw'2]
  · intro hc
    apply hw'out
    have h' := (a5Gbar_mem_commutator e (e.symm w')).mp hc
    simpa using h'
  · apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using hw'c

theorem oddInv_gbar_sq_mul {Γ : Type*} [Group Γ] (e : Γ ≃* A5WrTwo) {u v w : Γ}
    (hu : u ∉ _root_.commutator Γ) (hv : v ∉ _root_.commutator Γ)
    (hw : w ∉ _root_.commutator Γ) (hu2 : u ^ 2 = 1) (hv2 : v ^ 2 = 1) (hw2 : w ^ 2 = 1)
    (h5 : orderOf (u * v) = 5) (hwc : w * (u * v) = u * v * w) : (u * w) ^ 2 = 1 := by
  have heu : e u ∉ _root_.commutator A5WrTwo :=
    fun h => hu ((a5Gbar_mem_commutator e u).mpr h)
  have hev : e v ∉ _root_.commutator A5WrTwo :=
    fun h => hv ((a5Gbar_mem_commutator e v).mpr h)
  have hew : e w ∉ _root_.commutator A5WrTwo :=
    fun h => hw ((a5Gbar_mem_commutator e w).mpr h)
  have heu2 : (e u) ^ 2 = 1 := by rw [← map_pow, hu2, map_one]
  have hev2 : (e v) ^ 2 = 1 := by rw [← map_pow, hv2, map_one]
  have hew2 : (e w) ^ 2 = 1 := by rw [← map_pow, hw2, map_one]
  have h5' : orderOf (e u * e v) = 5 := by
    rw [← map_mul, MulEquiv.orderOf_eq]
    exact h5
  have hwc' : e w * (e u * e v) = e u * e v * e w := by
    simpa only [map_mul] using congrArg e hwc
  have hsq := oddInv_wr_sq_mul heu hev hew heu2 hev2 hew2 h5' hwc'
  apply e.injective
  rw [map_pow, map_mul, map_one]
  exact hsq

end CFSG.EvenSporadicStandard.HNRecog.Section3
