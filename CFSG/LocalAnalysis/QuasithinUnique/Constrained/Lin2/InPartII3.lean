module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InPartII2

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}

section Stage3

variable (h : Lin2Cfg G T M H S L n D) (dat : Lin2Data T M H S L n)
include h dat

omit dat in
theorem Lin2Cfg.R_isPGroup : IsPGroup 2 (thompsonJ S) :=
  h.S_isPGroup.to_le (thompsonJ_le_self S)

theorem Lin2Data.card_Bo : Nat.card (L ⊓ M : Subgroup G) = Nat.card (thompsonJ S) * Nat.card D := by
  have hDN : D ≤ Subgroup.normalizer (thompsonJ S : Set G) := dat.D_le_normalizer_R h
  have hc := card_sup_mul_card_inf hDN
  have hbot : D ⊓ thompsonJ S = ⊥ := by
    rw [dat.R_eq_P h]
    exact h.decomp.1
  rw [hbot, Subgroup.card_bot, mul_one, sup_comm, dat.R_sup_D h] at hc
  rw [hc, mul_comm]

theorem Lin2Data.card_K {x₀ : G} (hx₀ : x₀ ∈ T) (hx₀S : x₀ ∉ S) :
    ∃ c : ℕ, Nat.card (((L ⊓ M) ⊔ conjR D x₀ : Subgroup G)) =
        Nat.card (thompsonJ S) * Nat.card D * c ∧ Nat.card D = Nat.card (conjR D x₀ ⊓ (L ⊓ M) : Subgroup G) * c := by
  have hEn : conjR D x₀ ≤ Subgroup.normalizer ((L ⊓ M : Subgroup G) : Set G) :=
    dat.conjR_D_le_normalizer_Bo h hx₀ hx₀S
  have hc := card_sup_mul_card_inf hEn
  rw [sup_comm, card_conjR] at hc
  obtain ⟨c, hcc⟩ := Subgroup.card_dvd_of_le (inf_le_left : conjR D x₀ ⊓ (L ⊓ M) ≤ conjR D x₀)
  rw [card_conjR] at hcc
  have hpos : 0 < Nat.card (conjR D x₀ ⊓ (L ⊓ M) : Subgroup G) := Nat.card_pos
  refine ⟨c, ?_, hcc⟩
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [hc, dat.card_Bo h]
  calc Nat.card D * (Nat.card (thompsonJ S) * Nat.card D)
      = Nat.card (thompsonJ S) * Nat.card D * Nat.card D := by ring
    _ = Nat.card (thompsonJ S) * Nat.card D * (Nat.card (conjR D x₀ ⊓ (L ⊓ M) : Subgroup G) * c) := by
        rw [← hcc]
    _ = _ := by ring

theorem Lin2Data.relIndex_R_K_odd {x₀ : G} (hx₀ : x₀ ∈ T) (hx₀S : x₀ ∉ S) :
    ¬ 2 ∣ (thompsonJ S).relIndex ((L ⊓ M) ⊔ conjR D x₀) := by
  obtain ⟨c, hK, hD⟩ := dat.card_K h hx₀ hx₀S
  have hRK : thompsonJ S ≤ (L ⊓ M) ⊔ conjR D x₀ := (dat.R_le_Bo h).trans le_sup_left
  have hrel := Subgroup.relIndex_mul_card (H := thompsonJ S) (K := (L ⊓ M) ⊔ conjR D x₀)
  rw [inf_eq_left.mpr hRK, hK] at hrel
  have hRpos : 0 < Nat.card (thompsonJ S) := Nat.card_pos
  have h1 : (thompsonJ S).relIndex ((L ⊓ M) ⊔ conjR D x₀) = Nat.card D * c := by
    apply Nat.eq_of_mul_eq_mul_right hRpos
    rw [hrel]
    ring
  have hodd : Odd (Nat.card D) := h.hall.2.1
  have hc : Odd c := by
    have : c ∣ Nat.card D := ⟨_, by rw [hD, mul_comm]⟩
    exact Odd.of_dvd_nat hodd this
  rw [h1]
  exact (hodd.mul hc).not_two_dvd_nat

theorem Lin2Data.isSylowTwoOf_R_K {x₀ : G} (hx₀ : x₀ ∈ T) (hx₀S : x₀ ∉ S) :
    IsSylowTwoOf (thompsonJ S) ((L ⊓ M) ⊔ conjR D x₀) :=
  ⟨(dat.R_le_Bo h).trans le_sup_left, h.R_isPGroup, dat.relIndex_R_K_odd h hx₀ hx₀S⟩

theorem Lin2Data.K_le_normalizer_R {x₀ : G} (hx₀ : x₀ ∈ T) :
    (L ⊓ M) ⊔ conjR D x₀ ≤ Subgroup.normalizer (thompsonJ S : Set G) :=
  sup_le (dat.Bo_le_normalizer_R h) (dat.conjR_D_le_normalizer_R h hx₀)

theorem Lin2Data.T_inf_K {x₀ : G} (hx₀ : x₀ ∈ T) (hx₀S : x₀ ∉ S) :
    T ⊓ ((L ⊓ M) ⊔ conjR D x₀) = thompsonJ S := by
  apply le_antisymm
  · have hsyl := dat.isSylowTwoOf_R_K h hx₀ hx₀S
    have hTK2 : IsPGroup 2 ↥(T ⊓ ((L ⊓ M) ⊔ conjR D x₀)) :=
      h.sylowT.isPGroup.to_le inf_le_left
    have hX : IsPGroup 2 ↥(thompsonJ S ⊔ (T ⊓ ((L ⊓ M) ⊔ conjR D x₀))) :=
      (h.R_isPGroup).to_sup_of_normal_left' hTK2
        (fun t ht => dat.K_le_normalizer_R h hx₀ ht.2)
    have heq := hsyl.eq_of_le (le_sup_left : thompsonJ S ≤ _)
      (sup_le hsyl.le inf_le_right) hX
    rw [← heq]
    exact le_sup_right
  · exact le_inf (thompsonJ_le_self S |>.trans h.S_le_T) ((dat.R_le_Bo h).trans le_sup_left)

end Stage3

end CFSG.QuasithinUnique.Lin2
