module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AC16G
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.GroupTheory.Index

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] {K Y Q : Subgroup G} {t rho z u fz fu : G}

theorem c16_beta_surj [Finite G] (H : C16Ab K Y Q t rho z u fz fu) {R : Subgroup G}
    (hR : ∀ r, r ∈ R ↔ r ∈ Q ∧ ∀ f ∈ Y, r * f = f * r) (hQ : Nat.card Q = 2 ^ 9)
    (hRc : Nat.card R = 2 ^ 6) (hQm : ∀ q ∈ Q, c16Qm (c16Beta z u fz fu q)) :
    ∀ w, c16Qm w → ∃ q ∈ Q, c16Beta z u fz fu q = w := by
  classical
  let φ : ↥Q →* Multiplicative C16H0 :=
    { toFun := fun q => Multiplicative.ofAdd (c16Beta z u fz fu q.1)
      map_one' := by simp [c16_beta_one]
      map_mul' := fun x y => by simp [c16_beta_add H x.2 y.2] }
  have hker_card : Nat.card φ.ker = Nat.card R := by
    refine Nat.card_congr ?_
    refine
      { toFun := fun x =>
          ⟨x.1.1, (hR x.1.1).mpr ⟨x.1.2, (c16_beta_eq_zero_iff H x.1.2).mp ?_⟩⟩
        invFun := fun r => ⟨⟨r.1, ((hR r.1).mp r.2).1⟩, ?_⟩
        left_inv := fun x => Subtype.ext (Subtype.ext rfl)
        right_inv := fun r => Subtype.ext rfl }
    · exact ofAdd_eq_one.mp (by simpa [φ] using MonoidHom.mem_ker.mp x.2)
    · rw [MonoidHom.mem_ker]
      show Multiplicative.ofAdd (c16Beta z u fz fu r.1) = 1
      rw [(c16_beta_eq_zero_iff H ((hR r.1).mp r.2).1).mpr ((hR r.1).mp r.2).2]
      rfl
  have hcard := Subgroup.card_ker_mul_card_range φ
  rw [hker_card, hRc, hQ] at hcard
  have hrange_card : Nat.card φ.range = 8 := by
    have h : 2 ^ 6 * Nat.card φ.range = 2 ^ 6 * 2 ^ 3 := by
      rw [hcard]; norm_num
    exact Nat.mul_left_cancel (by norm_num) h
  let S : Finset C16H0 := Finset.univ.filter c16Qm
  have hS_card : S.card = 8 := by simpa [S] using c16_card_Qm
  have hsub : (φ.range : Set (Multiplicative C16H0)) ⊆
      ((S.image Multiplicative.ofAdd : Finset (Multiplicative C16H0)) :
        Set (Multiplicative C16H0)) := by
    intro x hx
    rcases MonoidHom.mem_range.mp hx with ⟨q, rfl⟩
    rw [Finset.mem_coe, Finset.mem_image]
    exact ⟨c16Beta z u fz fu q.1,
      by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hQm q.1 q.2⟩, rfl⟩
  have hA : (φ.range : Set (Multiplicative C16H0)).ncard = 8 := by
    rw [← Nat.card_coe_set_eq]; exact hrange_card
  have hB : ((S.image Multiplicative.ofAdd : Finset (Multiplicative C16H0)) :
      Set (Multiplicative C16H0)).ncard = 8 := by
    rw [Set.ncard_coe_finset,
      Finset.card_image_of_injective S Multiplicative.ofAdd.injective, hS_card]
  have hA' : (Set.range ⇑φ).ncard = 8 := by simpa using hA
  have hB' : (⇑Multiplicative.ofAdd '' (↑S : Set C16H0)).ncard = 8 := by simpa using hB
  have hseq : (φ.range : Set (Multiplicative C16H0)) =
      ((S.image Multiplicative.ofAdd : Finset (Multiplicative C16H0)) :
        Set (Multiplicative C16H0)) :=
    Set.eq_of_subset_of_ncard_le hsub (by simp [hA', hB'])
  intro w hw
  have hwB : Multiplicative.ofAdd w ∈
      ((S.image Multiplicative.ofAdd : Finset (Multiplicative C16H0)) :
        Set (Multiplicative C16H0)) := by
    rw [Finset.mem_coe, Finset.mem_image]
    exact ⟨w, by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hw⟩, rfl⟩
  have hwA : Multiplicative.ofAdd w ∈ φ.range := by
    have : Multiplicative.ofAdd w ∈ (φ.range : Set (Multiplicative C16H0)) := by
      rw [hseq]; exact hwB
    exact this
  rcases MonoidHom.mem_range.mp hwA with ⟨q, hq⟩
  exact ⟨q.1, q.2, Multiplicative.ofAdd.injective (by simpa [φ] using hq)⟩

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
