module

public import CFSG.FeitThompson.Representations.DadeAveragingSupportBound
public import CFSG.FeitThompson.Representations.DadeSupportPacketCount

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open ComplexOrder

variable {G : Type*} [Group G] {I : Type*}

def dadeCoverComplement (A : I → Set G) (H : I → G → Subgroup G) : Set G :=
  (⋃ i, totalDadeSupport (A i) (H i))ᶜ

theorem dadeCoverComplement_eq_compl_iUnion (A : I → Set G) (H : I → G → Subgroup G) :
    dadeCoverComplement A H = (⋃ i, totalDadeSupport (A i) (H i))ᶜ := (rfl)

theorem mem_dadeCoverComplement_iff {A : I → Set G} {H : I → G → Subgroup G} {x : G} :
    x ∈ dadeCoverComplement A H ↔ ∀ i, x ∉ totalDadeSupport (A i) (H i) := by
  simp [dadeCoverComplement]

theorem disjoint_dadeCoverComplement_totalDadeSupport (A : I → Set G) (H : I → G → Subgroup G)
    (i : I) : Disjoint (dadeCoverComplement A H) (totalDadeSupport (A i) (H i)) :=
  Set.disjoint_left.2 fun _ hx => mem_dadeCoverComplement_iff.1 hx i

theorem dadeCoverComplement_finite [Finite G] (A : I → Set G) (H : I → G → Subgroup G) :
    (dadeCoverComplement A H).Finite := Set.toFinite _

theorem sum_dadeCoverComplement_add_sum_totalDadeSupport [Fintype G] [Fintype I] {M : Type*}
    [AddCommMonoid M] {A : I → Set G} {H : I → G → Subgroup G}
    (hdisj : Pairwise fun i j =>
      Disjoint (totalDadeSupport (A i) (H i)) (totalDadeSupport (A j) (H j)))
    (f : G → M) :
    (∑ g ∈ (dadeCoverComplement_finite A H).toFinset, f g)
      + ∑ i, ∑ g ∈ (totalDadeSupport_finite (A i) (H i)).toFinset, f g = ∑ g : G, f g := by
  classical
  set B : Finset G :=
    Finset.univ.biUnion fun i => (totalDadeSupport_finite (A i) (H i)).toFinset with hB
  have hBsum : ∑ g ∈ B, f g
      = ∑ i, ∑ g ∈ (totalDadeSupport_finite (A i) (H i)).toFinset, f g := by
    rw [hB]
    refine Finset.sum_biUnion ?_
    intro i _ j _ hij
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact Set.disjoint_left.1 (hdisj hij) (by simpa using hx) (by simpa using hx')
  have hF0 : (dadeCoverComplement_finite A H).toFinset = Finset.univ \ B := by
    ext x
    simp [hB, mem_dadeCoverComplement_iff]
  rw [hF0, hBsum.symm, Finset.sum_sdiff (Finset.subset_univ B)]

theorem ncard_dadeCoverComplement_add_sum_ncard_totalDadeSupport [Finite G] [Fintype I]
    {A : I → Set G} {H : I → G → Subgroup G}
    (hdisj : Pairwise fun i j =>
      Disjoint (totalDadeSupport (A i) (H i)) (totalDadeSupport (A j) (H j))) :
    (dadeCoverComplement A H).ncard + ∑ i, (totalDadeSupport (A i) (H i)).ncard = Nat.card G := by
  have _ := Fintype.ofFinite G
  have h := sum_dadeCoverComplement_add_sum_totalDadeSupport hdisj (fun _ : G => (1 : ℕ))
  rw [Set.ncard_eq_toFinset_card _ (dadeCoverComplement_finite A H),
    Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
      Set.ncard_eq_toFinset_card _ (totalDadeSupport_finite (A i) (H i))]
  simpa [Nat.card_eq_fintype_card] using h

theorem IsDadeData.natCard_inv_mul_ncard_totalDadeSupport [Finite G] {L : Subgroup G} {A : Set G}
    {H : G → Subgroup G} (hD : IsDadeData L A H) :
    (Nat.card G : ℂ)⁻¹ * ((totalDadeSupport A H).ncard : ℂ)
      = (A.ncard : ℂ) / (Nat.card ↥L : ℂ) := by
  have hG : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hL : (Nat.card ↥L : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have h : ((totalDadeSupport A H).ncard : ℂ) * (Nat.card ↥L : ℂ)
      = (A.ncard : ℂ) * (Nat.card G : ℂ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℂ) hD.ncard_totalDadeSupport_mul_natCard
  rw [inv_mul_eq_div, div_eq_div_iff hG hL]
  linear_combination h

theorem measure_dadeCoverComplement_add_sum_eq_one [Finite G] [Fintype I] {L : I → Subgroup G}
    {A : I → Set G} {H : I → G → Subgroup G} (hD : ∀ i, IsDadeData (L i) (A i) (H i))
    (hdisj : Pairwise fun i j =>
      Disjoint (totalDadeSupport (A i) (H i)) (totalDadeSupport (A j) (H j))) :
    (Nat.card G : ℂ)⁻¹ * ((dadeCoverComplement A H).ncard : ℂ)
      + ∑ i, ((A i).ncard : ℂ) / (Nat.card ↥(L i) : ℂ) = 1 := by
  have hG : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
      ((hD i).natCard_inv_mul_ncard_totalDadeSupport).symm,
    ← Finset.mul_sum, ← mul_add,
    show ((dadeCoverComplement A H).ncard : ℂ)
        + ∑ i, ((totalDadeSupport (A i) (H i)).ncard : ℂ) = (Nat.card G : ℂ) by
      rw [← Nat.cast_sum, ← Nat.cast_add,
        ncard_dadeCoverComplement_add_sum_ncard_totalDadeSupport hdisj]]
  exact inv_mul_cancel₀ hG

theorem dadeCover_inequality [Fintype G] [Fintype I] {L : I → Subgroup G}
    [∀ i, Fintype ↥(L i)] {A : I → Set G} {H : I → G → Subgroup G}
    (hD : ∀ i, IsDadeData (L i) (A i) (H i))
    (hdisj : Pairwise fun i j =>
      Disjoint (totalDadeSupport (A i) (H i)) (totalDadeSupport (A j) (H j)))
    (χ : classFun G) (hχ : cfInner (χ : G → ℂ) (χ : G → ℂ) = 1) :
    ((∑ g ∈ (dadeCoverComplement_finite A H).toFinset, (‖(χ : G → ℂ) g‖ : ℂ) ^ 2)
          - ((dadeCoverComplement A H).ncard : ℂ)) / (Nat.card G : ℂ)
        + ∑ i, (cfInner (fun y : ↥(L i) => dadeAverage (A i) (H i) (χ : G → ℂ) (y : G))
              (fun y : ↥(L i) => dadeAverage (A i) (H i) (χ : G → ℂ) (y : G))
            - ((A i).ncard : ℂ) / (Nat.card ↥(L i) : ℂ)) ≤ 0 := by
  set f : G → ℂ := fun g => (‖(χ : G → ℂ) g‖ : ℂ) ^ 2
  have hmass : (Nat.card G : ℂ)⁻¹ * ∑ g ∈ (dadeCoverComplement_finite A H).toFinset, f g
      + ∑ i, (Nat.card G : ℂ)⁻¹ * ∑ g ∈ (totalDadeSupport_finite (A i) (H i)).toFinset, f g
      = 1 := by
    rw [← Finset.mul_sum, ← mul_add, sum_dadeCoverComplement_add_sum_totalDadeSupport hdisj f,
      ← cfInner_self_eq_sum_norm_sq, hχ]
  have hbound : ∑ i, cfInner (fun y : ↥(L i) => dadeAverage (A i) (H i) (χ : G → ℂ) (y : G))
        (fun y : ↥(L i) => dadeAverage (A i) (H i) (χ : G → ℂ) (y : G))
      ≤ ∑ i, (Nat.card G : ℂ)⁻¹ * ∑ g ∈ (totalDadeSupport_finite (A i) (H i)).toFinset, f g :=
    Finset.sum_le_sum fun i _ => cfInner_self_dadeAverage_le_sum_totalDadeSupport (hD i) χ
  have hle : (Nat.card G : ℂ)⁻¹ * ∑ g ∈ (dadeCoverComplement_finite A H).toFinset, f g
      + ∑ i, cfInner (fun y : ↥(L i) => dadeAverage (A i) (H i) (χ : G → ℂ) (y : G))
          (fun y : ↥(L i) => dadeAverage (A i) (H i) (χ : G → ℂ) (y : G)) ≤ 1 := by
    rw [← hmass]
    exact add_le_add le_rfl hbound
  rw [sub_div, div_eq_inv_mul, div_eq_inv_mul, Finset.sum_sub_distrib,
    show (Nat.card G : ℂ)⁻¹ * ∑ g ∈ (dadeCoverComplement_finite A H).toFinset, f g
        - (Nat.card G : ℂ)⁻¹ * ((dadeCoverComplement A H).ncard : ℂ)
        + (∑ i, cfInner (fun y : ↥(L i) => dadeAverage (A i) (H i) (χ : G → ℂ) (y : G))
              (fun y : ↥(L i) => dadeAverage (A i) (H i) (χ : G → ℂ) (y : G))
            - ∑ i, ((A i).ncard : ℂ) / (Nat.card ↥(L i) : ℂ))
        = ((Nat.card G : ℂ)⁻¹ * ∑ g ∈ (dadeCoverComplement_finite A H).toFinset, f g
              + ∑ i, cfInner (fun y : ↥(L i) => dadeAverage (A i) (H i) (χ : G → ℂ) (y : G))
                  (fun y : ↥(L i) => dadeAverage (A i) (H i) (χ : G → ℂ) (y : G)))
            - ((Nat.card G : ℂ)⁻¹ * ((dadeCoverComplement A H).ncard : ℂ)
              + ∑ i, ((A i).ncard : ℂ) / (Nat.card ↥(L i) : ℂ)) from by ring,
    measure_dadeCoverComplement_add_sum_eq_one hD hdisj, sub_nonpos]
  exact hle

end CFSG.FeitThompson

end
