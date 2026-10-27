module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisSModel
public import Certificates.Certificate22604

public section

namespace CFSG.ComponentClassification.GHarris.SCert.SE

open Subgroup

theorem dmul_lt_four : ∀ d e : Fin 8, d.val < 4 → e.val < 4 → (dmul d e).val < 4 := by
  decide

theorem evE_row1 : ∀ (d : Fin 8) (u w0 w1 w2 : ZMod 4), d.val < 4 → u.val % 2 = 0 →
    w1.val % 2 = 0 → w2.val % 2 = 0 →
    (u + (me d 1 0 * w0 + me d 1 1 * w1 + me d 1 2 * w2)).val % 2 = 0 := by
  decide +kernel

theorem evE_row2 : ∀ (d : Fin 8) (u w0 w1 w2 : ZMod 4), d.val < 4 → u.val % 2 = 0 →
    w1.val % 2 = 0 → w2.val % 2 = 0 →
    (u + (me d 2 0 * w0 + me d 2 1 * w1 + me d 2 2 * w2)).val % 2 = 0 := by
  decide +kernel

theorem me_row1_zero : ∀ d : Fin 8, me d 1 0 = 0 := by decide

theorem me_row2_zero : ∀ d : Fin 8, me d 2 0 = 0 := by decide

@[expose] def rowF1 (d e : Fin 8) (u w1 w2 : ZMod 4) : Prop :=
  d.val < 4 → e.val < 4 → u.val % 2 = parF1 d → w1.val % 2 = parF1 e → w2.val % 2 = parF2 e →
    (u + (me d 1 1 * w1 + me d 1 2 * w2)).val % 2 = parF1 (dmul d e)

@[expose] def rowF2 (d e : Fin 8) (u w1 w2 : ZMod 4) : Prop :=
  d.val < 4 → e.val < 4 → u.val % 2 = parF2 d → w1.val % 2 = parF1 e → w2.val % 2 = parF2 e →
    (u + (me d 2 1 * w1 + me d 2 2 * w2)).val % 2 = parF2 (dmul d e)

instance (d e : Fin 8) (u w1 w2 : ZMod 4) : Decidable (rowF1 d e u w1 w2) := by
  unfold rowF1; infer_instance

instance (d e : Fin 8) (u w1 w2 : ZMod 4) : Decidable (rowF2 d e u w1 w2) := by
  unfold rowF2; infer_instance

theorem rowF1_all : ∀ d e : Fin 8, ∀ u w1 w2 : ZMod 4, rowF1 d e u w1 w2 := by decide +kernel

theorem rowF2_all : ∀ d e : Fin 8, ∀ u w1 w2 : ZMod 4, rowF2 d e u w1 w2 := by decide +kernel

theorem evF_row1 (d e : Fin 8) (u w0 w1 w2 : ZMod 4) (hd : d.val < 4) (he : e.val < 4)
    (hu : u.val % 2 = parF1 d) (h1 : w1.val % 2 = parF1 e) (h2 : w2.val % 2 = parF2 e) :
    (u + (me d 1 0 * w0 + me d 1 1 * w1 + me d 1 2 * w2)).val % 2 = parF1 (dmul d e) := by
  rw [me_row1_zero, zero_mul, zero_add]
  exact rowF1_all d e u w1 w2 hd he hu h1 h2

theorem evF_row2 (d e : Fin 8) (u w0 w1 w2 : ZMod 4) (hd : d.val < 4) (he : e.val < 4)
    (hu : u.val % 2 = parF2 d) (h1 : w1.val % 2 = parF1 e) (h2 : w2.val % 2 = parF2 e) :
    (u + (me d 2 0 * w0 + me d 2 1 * w1 + me d 2 2 * w2)).val % 2 = parF2 (dmul d e) := by
  rw [me_row2_zero, zero_mul, zero_add]
  exact rowF2_all d e u w1 w2 hd he hu h1 h2

theorem predE_inv_aux : ∀ (d : Fin 8) (w0 w1 w2 : ZMod 4), d.val < 4 → w1.val % 2 = 0 →
    w2.val % 2 = 0 → (dinv d).val < 4 ∧
      (-(me (dinv d) 1 0 * w0 + me (dinv d) 1 1 * w1 + me (dinv d) 1 2 * w2)).val % 2 = 0 ∧
      (-(me (dinv d) 2 0 * w0 + me (dinv d) 2 1 * w1 + me (dinv d) 2 2 * w2)).val % 2 = 0 := by
  decide +kernel

theorem predF_inv_aux : ∀ (d : Fin 8) (w0 w1 w2 : ZMod 4), d.val < 4 → w1.val % 2 = parF1 d →
    w2.val % 2 = parF2 d → (dinv d).val < 4 ∧
      (-(me (dinv d) 1 0 * w0 + me (dinv d) 1 1 * w1 + me (dinv d) 1 2 * w2)).val % 2 =
        parF1 (dinv d) ∧
      (-(me (dinv d) 2 0 * w0 + me (dinv d) 2 1 * w1 + me (dinv d) 2 2 * w2)).val % 2 =
        parF2 (dinv d) := by
  decide +kernel

@[expose] def Esub : Subgroup SE where
  carrier := {s | predE s}
  mul_mem' {a b} ha hb := ⟨dmul_lt_four _ _ ha.1 hb.1,
    evE_row1 a.d a.v1 b.v0 b.v1 b.v2 ha.1 ha.2.1 hb.2.1 hb.2.2,
    evE_row2 a.d a.v2 b.v0 b.v1 b.v2 ha.1 ha.2.2 hb.2.1 hb.2.2⟩
  one_mem' := by decide
  inv_mem' {a} ha := predE_inv_aux a.d a.v0 a.v1 a.v2 ha.1 ha.2.1 ha.2.2

@[expose] def Fsub : Subgroup SE where
  carrier := {s | predF s}
  mul_mem' {a b} ha hb := ⟨dmul_lt_four _ _ ha.1 hb.1,
    evF_row1 a.d b.d a.v1 b.v0 b.v1 b.v2 ha.1 hb.1 ha.2.1 hb.2.1 hb.2.2,
    evF_row2 a.d b.d a.v2 b.v0 b.v1 b.v2 ha.1 hb.1 ha.2.2 hb.2.1 hb.2.2⟩
  one_mem' := by decide
  inv_mem' {a} ha := predF_inv_aux a.d a.v0 a.v1 a.v2 ha.1 ha.2.1 ha.2.2

theorem card_filter_predE : (Finset.univ.filter predE).card = 64 := by decide +kernel

theorem card_filter_predF : (Finset.univ.filter predF).card = 64 := by decide +kernel

theorem card_Esub : Nat.card Esub = 64 := by
  rw [← card_filter_predE, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)

theorem card_Fsub : Nat.card Fsub = 64 := by
  rw [← card_filter_predF, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)

theorem normal_of_conj_gen (H : Subgroup SE)
    (h : ∀ i : Fin 9, ∀ e ∈ H, gen i * e * (gen i)⁻¹ ∈ H ∧ (gen i)⁻¹ * e * gen i ∈ H) :
    H.Normal := by
  have hN : ∀ i, gen i ∈ normalizer (H : Set SE) := fun i => by
    rw [mem_normalizer_iff]
    intro e
    refine ⟨fun he => (h i e he).1, fun he => ?_⟩
    have := (h i _ he).2
    rwa [show (gen i)⁻¹ * (gen i * e * (gen i)⁻¹) * gen i = e by group] at this
  have htop : normalizer (H : Set SE) = ⊤ := by
    rw [eq_top_iff, ← closure_range_gen, closure_le]
    rintro _ ⟨i, rfl⟩
    exact hN i
  exact normalizer_eq_top_iff.mp htop

theorem predE_conj_gen : ∀ i : Fin 9, ∀ e : SE, predE e →
    predE (gen i * e * (gen i)⁻¹) ∧ predE ((gen i)⁻¹ * e * gen i) := by
  decide +kernel

theorem predF_conj_gen : ∀ i : Fin 9, ∀ e : SE, predF e →
    predF (gen i * e * (gen i)⁻¹) ∧ predF ((gen i)⁻¹ * e * gen i) := by
  decide +kernel

instance Esub_normal : Esub.Normal := normal_of_conj_gen _ predE_conj_gen

instance Fsub_normal : Fsub.Normal := normal_of_conj_gen _ predF_conj_gen

theorem sq_eq_z_cases : ∀ w : SE, w * w = gen 0 → predE w ∨ predF w := by decide +kernel

theorem gen_predE : predE (gen 1) ∧ predE (gen 2) ∧ predE (gen 3) ∧ predE (gen 4) ∧
    predE (gen 5) := by decide

theorem gen_predF : predF (gen 1) ∧ predF (gen 2) ∧ predF (gen 3) ∧ predF (gen 6) ∧
    predF (gen 7) := by decide

theorem gen0_predE : predE (gen 0) := by decide

theorem gen0_predF : predF (gen 0) := by decide

theorem l_comm_E : ∀ e : SE, predE e → e * gen 1 = gen 1 * e := by decide +kernel

theorem l_comm_F : ∀ e : SE, predF e → e * gen 1 = gen 1 * e := by decide +kernel

theorem center_E : ∀ s : SE, predE s → s * gen 1 = gen 1 * s → s * gen 2 = gen 2 * s →
    s * gen 3 = gen 3 * s → s * gen 4 = gen 4 * s → s * gen 5 = gen 5 * s →
    s = 1 ∨ s = gen 1 ∨ s = gen 0 ∨ s = gen 1 * gen 0 := by
  decide +kernel

theorem center_F : ∀ s : SE, predF s → s * gen 1 = gen 1 * s → s * gen 2 = gen 2 * s →
    s * gen 3 = gen 3 * s → s * gen 6 = gen 6 * s → s * gen 7 = gen 7 * s →
    s = 1 ∨ s = gen 1 ∨ s = gen 0 ∨ s = gen 1 * gen 0 := by
  decide +kernel

theorem exists_gen_conj_mul_z_E : ∀ w : SE, predE w → w ≠ 1 → w ≠ gen 0 →
    ∃ i : Fin 9, (gen i)⁻¹ * (w * gen 0) * gen i = w := by
  decide +kernel

theorem exists_gen_conj_mul_z_F : ∀ w : SE, predF w → w ≠ 1 → w ≠ gen 0 →
    ∃ i : Fin 9, (gen i)⁻¹ * (w * gen 0) * gen i = w := by
  decide +kernel

theorem not_commZ_mixed (e f : SE) (he : O4E e)
    (heF : ¬ predF e) (hf : O4F f) (hfE : ¬ predE f) : ¬ commZ e f :=
  Certificates.certificate22604.1 e f he heF hf hfE

theorem commZ_E (e f : SE) (he : predE e) (hf : predE f) :
    commZ e f :=
  Certificates.certificate22604.2.1 e f he hf

theorem commZ_F (e f : SE) (he : predF e) (hf : predF f) :
    commZ e f :=
  Certificates.certificate22604.2.2.1 e f he hf

theorem gen_E (e : SE) (he : predE e) :
    O4E e ∨ ∃ u v : SE, O4E u ∧ O4E v ∧ e = u * v :=
  Certificates.certificate22604.2.2.2.1 e he

theorem gen_F (e : SE) (he : predF e) :
    O4F e ∨ ∃ u v : SE, O4F u ∧ O4F v ∧ e = u * v :=
  Certificates.certificate22604.2.2.2.2 e he

end CFSG.ComponentClassification.GHarris.SCert.SE
