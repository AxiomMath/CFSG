module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzJtDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzFusB

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33 CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTheorem5.DeltaLocal

variable {G : Type} [Group G]

section GZ
variable [Finite G] {t : G} {L S T₂ : Subgroup G} {x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂ : G}

theorem fzJt_mem_closure_pair {a b e : G} (hab : Commute a b) (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (h : e ∈ closure ({a, b} : Set G)) : e = 1 ∨ e = a ∨ e = b ∨ e = a * b := by
  have haa : a * a = 1 := by rw [← pow_two, ha]
  have hbb : b * b = 1 := by rw [← pow_two, hb]
  have hba : b * a = a * b := hab.eq.symm
  let K : Subgroup G :=
    { carrier := {1, a, b, a * b},
      mul_mem' := by
        have h1 : a * (a * b) = b := by rw [← mul_assoc, haa, one_mul]
        have h2 : b * (a * b) = a := by rw [hab.eq, ← mul_assoc, hbb, one_mul]
        have h3 : a * b * a = b := by rw [mul_assoc, ← hab.eq, ← mul_assoc, haa, one_mul]
        have h4 : a * b * b = a := by rw [mul_assoc, hbb, mul_one]
        have h5 : a * b * (a * b) = 1 := by rw [← mul_assoc, h3, hbb]
        rintro x y (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl) <;>
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff, one_mul, mul_one, haa, hbb,
            h1, h2, h3, h4, h5, hba, true_or, or_true]
      one_mem' := Or.inl rfl
      inv_mem' := by
        have h5 : a * b * (a * b) = 1 := by
          rw [← mul_assoc, mul_assoc a b a, ← hab.eq, ← mul_assoc, haa, one_mul, hbb]
        rintro x (rfl | rfl | rfl | rfl)
        · simp
        · rw [inv_eq_of_mul_eq_one_right haa]; exact Or.inr (Or.inl rfl)
        · rw [inv_eq_of_mul_eq_one_right hbb]; exact Or.inr (Or.inr (Or.inl rfl))
        · rw [inv_eq_of_mul_eq_one_right h5]; exact Or.inr (Or.inr (Or.inr rfl)) }
  have hle : closure ({a, b} : Set G) ≤ K := by
    rw [Subgroup.closure_le]
    intro x hx
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hxa | hxb
    · rw [hxa]; exact Or.inr (Or.inl rfl)
    · rw [hxb]; exact Or.inr (Or.inr (Or.inl rfl))
  have heK : e ∈ K := hle h
  change e ∈ ({1, a, b, a * b} : Set G) at heK
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, or_false]
    using heK

theorem fzJt_not_isConj_t_z₃ (hset : FzSetting7 t L S T₂ x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂) :
    ¬ IsConj t ((x₁ * x₂) ^ 2) := by
  intro hc
  obtain ⟨c, hc⟩ := isConj_iff.mp hc
  have hctx0 := hset.ctx.toCtx0
  have ht : t ^ 2 = 1 := (orderOf_eq_prime_iff.mp hctx0.hyp.ord_t).1
  obtain ⟨h1, h2⟩ := fz_commute_t hctx0
  have htu : t * (x₁ * x₂) = (x₁ * x₂) * t := by
    rw [← mul_assoc, h1.eq, mul_assoc, h2.eq, mul_assoc]
  have hz := le_centralizer_z₃ hset.shape ht htu
  let f : G →* G := (MulAut.conj c⁻¹).toMonoidHom
  have hle : T₂.map f ≤ invCent t := by
    rintro _ ⟨d, hd, rfl⟩
    have hdz : d * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * d := mem_centralizer_singleton_iff.mp (hz hd)
    show c⁻¹ * d * c⁻¹⁻¹ ∈ centralizer ({t} : Set G)
    rw [mem_centralizer_singleton_iff, ← hc] at *
    rw [← hc] at hdz
    calc c⁻¹ * d * c⁻¹⁻¹ * t = c⁻¹ * (d * (c * t * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * t * c⁻¹) * d) * c := by rw [hdz]
      _ = t * (c⁻¹ * d * c⁻¹⁻¹) := by group
  have hcard : Nat.card (T₂.map f) = 2 ^ 9 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective, hset.shape.card]
  have hdvd := Subgroup.card_dvd_of_le hle
  have hmul : S.relIndex (invCent t) * Nat.card S = Nat.card (invCent t) := by
    have h := Subgroup.relIndex_mul_card (H := S) (K := invCent t)
    rwa [inf_eq_left.mpr hset.ctx.le_invCent] at h
  have hS : Nat.card S = 2 ^ 7 := by rw [hset.ctx.card_S, hset.card_twoCore]; norm_num
  rw [hcard, ← hmul, hS] at hdvd
  have hodd := hset.ctx.relIndex_odd
  have : 2 ^ 2 ∣ S.relIndex (invCent t) := by
    have h' : 2 ^ 2 * 2 ^ 7 ∣ S.relIndex (invCent t) * 2 ^ 7 := by
      rw [show (2 : ℕ) ^ 2 * 2 ^ 7 = 2 ^ 9 by norm_num]; exact hdvd
    exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) h'
  exact hodd (dvd_trans (by norm_num) this)

theorem fzInvolZ_holds : FzInvolZ := by
  intro G _ _ _ t L S T₂ x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂ hset v hv htv
  have hctx0 := hset.ctx.toCtx0
  have hWL : wreathGrp x₁ x₂ lam ≤ L := by rw [← hctx0.inf_eq]; exact inf_le_right
  have hx₁L : x₁ ∈ L := hWL (subset_closure (by simp))
  have hx₂L : x₂ ∈ L := hWL (subset_closure (by simp))
  have hlamL : lam ∈ L := hWL (subset_closure (by simp))
  have hz₃L : (x₁ * x₂) ^ 2 ∈ L := pow_mem (mul_mem hx₁L hx₂L) 2
  have hL : ∀ e ∈ L, e * e = 1 → e ≠ 1 → IsConj ((x₁ * x₂) ^ 2) e := fun e he h2 h1 => by
    obtain ⟨c, -, hc⟩ := hctx0.invol_L e he h2 h1
    exact isConj_iff.mpr ⟨c, hc⟩
  suffices hz : IsConj ((x₁ * x₂) ^ 2) v from fzJt_not_isConj_t_z₃ hset (htv.trans hz.symm)
  have hz1sq : (x₁ ^ 2) ^ 2 = 1 := by
    rw [← pow_mul, show 2 * 2 = 4 from rfl, ← hctx0.wreath.ord_x₁]; exact pow_orderOf_eq_one x₁
  have hz3sq : ((x₁ * x₂) ^ 2) ^ 2 = 1 := (orderOf_eq_prime_iff.mp (fz_orderOf_z hctx0)).1
  have hz13 : Commute (x₁ ^ 2) ((x₁ * x₂) ^ 2) :=
    (((Commute.refl x₁).mul_right hctx0.wreath.comm).pow_left 2).pow_right 2
  rcases hv with ⟨hv1, hvZ⟩ | ⟨h, -, rfl⟩
  · have hvL : v ∈ L := by
      have : fourGrp x₁ x₂ ≤ L := by
        rw [fourGrp, closure_le]
        intro e he
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
        rcases he with rfl | rfl
        · exact pow_mem hx₁L 2
        · exact hz₃L
      exact this hvZ
    refine hL v hvL ?_ hv1
    rcases fzJt_mem_closure_pair hz13 hz1sq hz3sq hvZ with rfl | rfl | rfl | rfl
    · exact mul_one 1
    · rw [← pow_two]; exact hz1sq
    · rw [← pow_two]; exact hz3sq
    · rw [← pow_two, hz13.mul_pow, hz1sq, hz3sq, one_mul]
  · have hlam2 : lam * lam = 1 := by rw [← pow_two]; exact hset.shape.lam_sq
    have hlam1 : lam ≠ 1 := by
      intro h1; have := hctx0.wreath.ord_lam; rw [h1, orderOf_one] at this
      exact absurd this (by norm_num)
    exact (hL lam hlamL hlam2 hlam1).trans (isConj_iff.mpr ⟨h, rfl⟩)

end GZ

end CFSG.OddStandard.SmallF3.FritzII
