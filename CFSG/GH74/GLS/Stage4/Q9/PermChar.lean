module

public import CFSG.GH74.GLS.Stage4.Q9.ModelBase
public import CFSG.CharacterTheory.Blocks.BrauerInduction
public import CFSG.CharacterTheory.Blocks.InnerProduct
public meta import CFSG.GH74.GLS.Stage4.Q9.ModelBase
public meta import Mathlib
public import CFSG.GH74.GLS.Stage4.Q9.PermCharInputs
public meta import CFSG.GH74.GLS.Stage4.Q9.PermCharInputs
public import Certificates.Certificate5100
public import Certificates.Certificate5101

public section

namespace CFSG.GH74.GLS.Stage4.Q9

open CFSG.TwoRankLowerBound.Helpers

theorem mk_one_mem_BL_iff (M : SL2) :
    (⟨M, 1⟩ : Lg) ∈ BL ↔ (M : Matrix (Fin 2) (Fin 2) F9) 1 0 = 0 := by
  simp [mem_BL_iff, inBL]

theorem card_BL : Nat.card BL = 144 :=
  Certificates.certificate5101.1

@[expose] noncomputable def indB : Lg → ℂ := inducedFunction BL (fun _ => 1)

@[expose] noncomputable def aFn : Lg → ℂ := indB - 1

theorem aFn_mem_blocksVChar : aFn ∈ CFSG.BlocksVChar Lg :=
  (CFSG.BlocksVChar Lg).sub_mem
    (CFSG.inducedFunction_mem_blocksVChar BL (φ := fun _ => 1) (CFSG.blocksVChar_one BL))
    (CFSG.blocksVChar_one Lg)

theorem card_filter_eq_card_mul_card_filter {G ι : Type*} [Group G] [Fintype G] [Fintype ι]
    (H : Subgroup G) [DecidablePred (· ∈ H)] (rep : ι → G)
    (hrep : ∀ x : G, (Finset.univ.filter fun i : ι => (rep i)⁻¹ * x ∈ H).card = 1)
    (P : G → Prop) [DecidablePred P] (hP : ∀ x, ∀ h ∈ H, P (x * h) ↔ P x) :
    (Finset.univ.filter P).card =
      Nat.card H * (Finset.univ.filter fun i : ι => P (rep i)).card := by
  have hH : ∀ c : ℕ, ∑ b : G, (if b ∈ H then c else 0) = Nat.card H * c := by
    intro c
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
    congr 1
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h1 : (Finset.univ.filter P).card = ∑ x : G, if P x then 1 else 0 := by
    rw [Finset.card_filter]
  have h2 : ∀ x : G, (if P x then 1 else 0 : ℕ) =
      ∑ i : ι, if (rep i)⁻¹ * x ∈ H then (if P x then 1 else 0) else 0 := by
    intro x
    rw [← Finset.sum_filter, Finset.sum_const, hrep x, one_smul]
  calc (Finset.univ.filter P).card
      = ∑ x : G, ∑ i : ι, if (rep i)⁻¹ * x ∈ H then (if P x then 1 else 0) else 0 := by
        rw [h1]; exact Finset.sum_congr rfl fun x _ => h2 x
    _ = ∑ i : ι, ∑ x : G, if (rep i)⁻¹ * x ∈ H then (if P x then 1 else 0) else 0 :=
        Finset.sum_comm
    _ = ∑ i : ι, ∑ b : G, if b ∈ H then (if P (rep i) then 1 else 0) else 0 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Equiv.sum_comp (Equiv.mulLeft (rep i))
          (fun x => if (rep i)⁻¹ * x ∈ H then (if P x then 1 else 0) else 0)]
        refine Finset.sum_congr rfl fun b _ => ?_
        simp only [Equiv.coe_mulLeft, inv_mul_cancel_left]
        by_cases hb : b ∈ H
        · simp [hb, hP (rep i) b hb]
        · simp [hb]
    _ = ∑ i : ι, Nat.card H * (if P (rep i) then 1 else 0) :=
        Finset.sum_congr rfl fun i _ => hH _
    _ = Nat.card H * (Finset.univ.filter fun i : ι => P (rep i)).card := by
        rw [← Finset.mul_sum, Finset.card_filter]

theorem repPt_spec : ∀ x : Lg,
    (Finset.univ.filter fun p : Option F9 => (repPt p)⁻¹ * x ∈ BL).card = 1 :=
  Certificates.certificate5101.2.1

@[expose] def aTab (l : Lg) : ℤ :=
  (((Finset.univ.filter fun x : Lg => x⁻¹ * l * x ∈ BL).card / 144 : ℕ) : ℤ) - 1

theorem card_conj_mem_BL (l : Lg) :
    (Finset.univ.filter fun x : Lg => x⁻¹ * l * x ∈ BL).card =
      144 * (Finset.univ.filter fun p : Option F9 => (repPt p)⁻¹ * l * repPt p ∈ BL).card := by
  rw [← card_BL]
  exact card_filter_eq_card_mul_card_filter BL repPt repPt_spec (fun x => x⁻¹ * l * x ∈ BL) (by
    intro x h hh
    have e : (x * h)⁻¹ * l * (x * h) = h⁻¹ * (x⁻¹ * l * x) * h := by group
    rw [e, Subgroup.mul_mem_cancel_right BL hh, Subgroup.mul_mem_cancel_left BL (BL.inv_mem hh)])

theorem aTab_eq_aTabFast (l : Lg) : aTab l = aTabFast l := by
  unfold aTab aTabFast
  rw [card_conj_mem_BL, Nat.mul_div_cancel_left _ (by norm_num)]

theorem indB_apply (l : Lg) :
    indB l = ((Finset.univ.filter fun x : Lg => x⁻¹ * l * x ∈ BL).card : ℂ) / 144 := by
  unfold indB inducedFunction
  rw [card_BL]
  simp only [dite_eq_ite]
  rw [Finset.sum_boole]
  push_cast
  rw [div_eq_inv_mul]

theorem aFn_eq_aTab (l : Lg) : aFn l = (aTab l : ℂ) := by
  show indB l - 1 = _
  rw [indB_apply]
  unfold aTab
  rw [card_conj_mem_BL, Nat.mul_div_cancel_left _ (by norm_num)]
  push_cast
  ring

theorem aTabFast_eq_nine_iff :
    ∀ l : Lg, aTabFast l = 9 ↔ l = 1 ∨ l = innerL minusOne :=
  Certificates.certificate5101.2.2.2.1

theorem aTab_eq_nine_iff :
    ∀ l : Lg, aTab l = 9 ↔ l = 1 ∨ l = innerL minusOne := fun l => by
  rw [aTab_eq_aTabFast]; exact aTabFast_eq_nine_iff l

theorem aTabFast_eq_aByOrder :
    ∀ l : Lg, aTabFast l = aByOrder (decide (parityL l = 1)) (ordL l) :=
  Certificates.certificate5101.2.2.2.2.2.2.2.2

theorem aTab_eq_aByOrder
    (l : Lg) : aTab l = aByOrder (decide (parityL l = 1)) (orderOf l) := by
  rw [aTab_eq_aTabFast, aTabFast_eq_aByOrder, orderOf_Lg]

end CFSG.GH74.GLS.Stage4.Q9
