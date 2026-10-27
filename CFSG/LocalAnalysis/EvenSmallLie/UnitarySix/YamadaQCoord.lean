module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaQBasis
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaDInter

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaD

open Subgroup
open scoped commutatorElement

@[expose] def mU₁ : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  Matrix.of fun i j => if (i : ℕ) = (j : ℕ) ^^^ 1 then 1 else 0

@[expose] def mU₂ : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  Matrix.of fun i j => if (i : ℕ) = (j : ℕ) ^^^ 2 then 1 else 0

@[expose] def mT : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  Matrix.of fun i j => if i = j then 1 else if (j : ℕ) = (i : ℕ) + 4 then 1 else 0

theorem col_mU₁ (j : Fin 8) :
    (fun i => mU₁ i j) = Pi.single ⟨(j : ℕ) ^^^ 1, by fin_cases j <;> decide⟩ 1 := by
  revert j; decide

theorem col_mU₂ (j : Fin 8) :
    (fun i => mU₂ i j) = Pi.single ⟨(j : ℕ) ^^^ 2, by fin_cases j <;> decide⟩ 1 := by
  revert j; decide

theorem col_mT (j : Fin 8) : (fun i => mT i j) =
    if (j : ℕ) < 4 then Pi.single j 1 else Pi.single j 1 + Pi.single ⟨j - 4, by omega⟩ 1 := by
  revert j; decide

@[expose] def lo (w : Fin 4 → ZMod 2) : Fin 8 → ZMod 2 :=
  fun i => if hi : (i : ℕ) < 4 then w ⟨i, hi⟩ else 0

@[expose] def hiPart (v : Fin 8 → ZMod 2) : Fin 4 → ZMod 2 := fun k => v ⟨k + 4, by omega⟩

@[expose] def loPart (v : Fin 8 → ZMod 2) : Fin 4 → ZMod 2 := fun k => v ⟨k, by omega⟩

theorem lo_add (w w' : Fin 4 → ZMod 2) : lo (w + w') = lo w + lo w' := by
  ext i; simp only [lo, Pi.add_apply]; split_ifs <;> simp

set_option maxRecDepth 10000 in
theorem add_mT (v : Fin 8 → ZMod 2) : v + mT.mulVec v = lo (hiPart v) := by
  revert v; decide

set_option maxRecDepth 10000 in
theorem eq_lo_of_hiPart (v : Fin 8 → ZMod 2) (hv : hiPart v = 0) : v = lo (loPart v) := by
  revert v; decide

theorem lo_single (k : Fin 4) : lo (Pi.single k 1) = Pi.single ⟨k, by omega⟩ 1 := by
  revert k; decide

@[expose] def augZ (v : Fin 8 → ZMod 2) : Prop :=
  v 0 + v 1 + v 2 + v 3 = 0 ∧ v 4 + v 5 + v 6 + v 7 = 0

instance (v : Fin 8 → ZMod 2) : Decidable (augZ v) := by unfold augZ; infer_instance

set_option maxRecDepth 10000 in
theorem augZ_of_comm (v : Fin 8 → ZMod 2)
    (h1 : mU₁.mulVec (mU₁.mulVec v + v) = mU₁.mulVec v + v)
    (h2 : mU₂.mulVec (mU₁.mulVec v + v) = mU₁.mulVec v + v)
    (h3 : mU₁.mulVec (mU₂.mulVec v + v) = mU₂.mulVec v + v)
    (h4 : mU₂.mulVec (mU₂.mulVec v + v) = mU₂.mulVec v + v) : augZ v := by
  revert v; decide

theorem augZ_zero : augZ 0 := by decide

theorem augZ_add (v w : Fin 8 → ZMod 2) (hv : augZ v) (hw : augZ w) : augZ (v + w) := by
  obtain ⟨hv1, hv2⟩ := hv
  obtain ⟨hw1, hw2⟩ := hw
  refine ⟨?_, ?_⟩
  · simp only [Pi.add_apply]
    rw [show v 0 + w 0 + (v 1 + w 1) + (v 2 + w 2) + (v 3 + w 3) =
      (v 0 + v 1 + v 2 + v 3) + (w 0 + w 1 + w 2 + w 3) by ring, hv1, hw1, add_zero]
  · simp only [Pi.add_apply]
    rw [show v 4 + w 4 + (v 5 + w 5) + (v 6 + w 6) + (v 7 + w 7) =
      (v 4 + v 5 + v 6 + v 7) + (w 4 + w 5 + w 6 + w 7) by ring, hv2, hw2, add_zero]

theorem card_augZ : Fintype.card {v : Fin 8 → ZMod 2 // augZ v} = 2 ^ 6 := by
  rfl

@[expose] def mX : Fin 4 → Matrix (Fin 8) (Fin 8) (ZMod 2) := ![1, mU₁, mU₂, mU₁ * mU₂]

variable {G : Type*} [Group G]

namespace Data

variable (d : Data G)

@[expose] def xs : Fin 4 → G := ![1, d.u₁, d.u₂, d.u₁ * d.u₂]

@[expose] def basG (d₀ : G) (j : Fin 8) : G :=
  d.xs ⟨j % 4, Nat.mod_lt _ (by norm_num)⟩ * (if (j : ℕ) < 4 then d.a₀ else d₀) *
    (d.xs ⟨j % 4, Nat.mod_lt _ (by norm_num)⟩)⁻¹

end Data

theorem conj_mul_conj (x y c : G) : x * (y * c * y⁻¹) * x⁻¹ = (x * y) * c * (x * y)⁻¹ := by
  group

namespace Hyp

variable {d : Data G} (h : Hyp d)
include h

theorem xs_mem (k : Fin 4) : d.xs k ∈ d.X₁ := by
  fin_cases k
  · exact one_mem _
  · exact h.u₁_mem
  · exact h.u₂_mem
  · exact mul_mem h.u₁_mem h.u₂_mem

theorem u₁_mul_xs (k : Fin 4) :
    d.u₁ * d.xs k = d.xs ⟨(k : ℕ) ^^^ 1, by fin_cases k <;> decide⟩ := by
  fin_cases k
  · simp [Data.xs]
  · simp [Data.xs, h.u₁_sq]
  · simp [Data.xs]
  · simp [Data.xs, ← mul_assoc, h.u₁_sq]

theorem u₂_mul_xs (k : Fin 4) :
    d.u₂ * d.xs k = d.xs ⟨(k : ℕ) ^^^ 2, by fin_cases k <;> decide⟩ := by
  fin_cases k
  · simp [Data.xs]
  · simp [Data.xs, h.u₁_comm_u₂]
  · simp [Data.xs, h.u₂_sq]
  · simp [Data.xs, ← mul_assoc, ← h.u₁_comm_u₂]
    rw [mul_assoc, h.u₂_sq, mul_one]

theorem basG_mem [Finite G] {d₀ : G} (hd₀ : d₀ ∈ d.D₄) (j : Fin 8) : d.basG d₀ j ∈ d.D₄ := by
  have hx := h.X₁_le_normalizer_D₄ (h.xs_mem ⟨j % 4, Nat.mod_lt _ (by norm_num)⟩)
  have hc : (if (j : ℕ) < 4 then d.a₀ else d₀) ∈ d.D₄ := by
    split_ifs
    · exact h.A₄_le_D₄ h.a₀_mem
    · exact hd₀
  exact (mem_normalizer_iff.mp hx _).mp hc

theorem conj_basG_u₁ (d₀ : G) (j : Fin 8) :
    d.u₁ * d.basG d₀ j * d.u₁⁻¹ = d.basG d₀ ⟨(j : ℕ) ^^^ 1, by fin_cases j <;> decide⟩ := by
  fin_cases j <;> simp only [Data.basG, conj_mul_conj, h.u₁_mul_xs] <;> rfl

theorem conj_basG_u₂ (d₀ : G) (j : Fin 8) :
    d.u₂ * d.basG d₀ j * d.u₂⁻¹ = d.basG d₀ ⟨(j : ℕ) ^^^ 2, by fin_cases j <;> decide⟩ := by
  fin_cases j <;> simp only [Data.basG, conj_mul_conj, h.u₂_mul_xs] <;> rfl

theorem xs_mem_L (k : Fin 4) : d.xs k ∈ d.L := h.Λ_le_L (h.X₁_le_Λ (h.xs_mem k))

omit h in
theorem _root_.CFSG.EvenSmallLie.UnitarySix.YamadaD.Data.basG_lo (d₀ : G) (j : Fin 8)
    (hj : (j : ℕ) < 4) :
    d.basG d₀ j = d.xs ⟨j % 4, Nat.mod_lt _ (by norm_num)⟩ * d.a₀ *
      (d.xs ⟨j % 4, Nat.mod_lt _ (by norm_num)⟩)⁻¹ := by
  simp [Data.basG, hj]

omit h in
theorem _root_.CFSG.EvenSmallLie.UnitarySix.YamadaD.Data.basG_hi (d₀ : G) (j : Fin 8)
    (hj : ¬ (j : ℕ) < 4) :
    d.basG d₀ j = d.xs ⟨j % 4, Nat.mod_lt _ (by norm_num)⟩ * d₀ *
      (d.xs ⟨j % 4, Nat.mod_lt _ (by norm_num)⟩)⁻¹ := by
  simp [Data.basG, hj]

theorem t_conj_basG_lo (d₀ : G) (j : Fin 8) (hj : (j : ℕ) < 4) :
    d.t * d.basG d₀ j * d.t⁻¹ = d.basG d₀ j := by
  have hL : d.basG d₀ j ∈ d.L := by
    rw [d.basG_lo d₀ j hj]
    exact mul_mem (mul_mem (h.xs_mem_L _) (h.A₄_le_L h.a₀_mem)) (inv_mem (h.xs_mem_L _))
  rw [← h.comm_of_mem_L hL, mul_inv_cancel_right]

theorem t_conj_basG_hi {d₀ : G} (hθ : d₀⁻¹ * d.t * d₀ * d.t = d.a₀) (j : Fin 8)
    (hj : ¬ (j : ℕ) < 4) :
    d.t * d.basG d₀ j * d.t⁻¹ =
      d.basG d₀ j * d.basG d₀ ⟨j - 4, by omega⟩ := by
  have hk : ((j : ℕ) - 4) % 4 = (j : ℕ) % 4 := by omega
  have hlo : ((⟨j - 4, by omega⟩ : Fin 8) : ℕ) < 4 := by simp; omega
  rw [d.basG_hi d₀ j hj, d.basG_lo d₀ _ hlo]
  set x := d.xs ⟨j % 4, Nat.mod_lt _ (by norm_num)⟩ with hx
  have hx' : d.xs ⟨(j - 4) % 4, Nat.mod_lt _ (by norm_num)⟩ = x := by
    rw [hx]; congr 2
  simp only [hx']
  have hxt : x * d.t = d.t * x := h.comm_of_mem_L (h.xs_mem_L _)
  have htd : d.t * d₀ * d.t⁻¹ = d₀ * d.a₀ := by
    rw [← hθ, h.t_inv]; group
  calc d.t * (x * d₀ * x⁻¹) * d.t⁻¹ = (d.t * x) * d₀ * (d.t * x)⁻¹ := conj_mul_conj _ _ _
    _ = (x * d.t) * d₀ * (x * d.t)⁻¹ := by rw [hxt]
    _ = x * (d.t * d₀ * d.t⁻¹) * x⁻¹ := (conj_mul_conj _ _ _).symm
    _ = x * d₀ * x⁻¹ * (x * d.a₀ * x⁻¹) := by rw [htd]; group

theorem D₄_comm' [Finite G] : ∀ a ∈ d.D₄, ∀ b ∈ d.D₄, a * b = b * a :=
  fun _ ha _ hb => h.D₄_comm ha hb

@[expose] def bas [Finite G] {d₀ : G} (hd₀ : d₀ ∈ d.D₄) : Fin 8 → d.D₄ :=
  fun j => ⟨d.basG d₀ j, h.basG_mem hd₀ j⟩

@[expose] def kap [Finite G] {d₀ : G} (hd₀ : d₀ ∈ d.D₄) (v : Fin 8 → ZMod 2) : G :=
  kprod h.D₄_comm' (h.bas hd₀) v

variable [Finite G] {d₀ : G} (hd₀ : d₀ ∈ d.D₄)

theorem kap_mem (v : Fin 8 → ZMod 2) : h.kap hd₀ v ∈ d.D₄ := kprod_mem v

theorem kap_zero : h.kap hd₀ 0 = 1 := kprod_zero

theorem kap_single (j : Fin 8) : h.kap hd₀ (Pi.single j 1) = d.basG d₀ j := kprod_single j

variable (hB : HypB d) (hV : ∀ v ∈ d.V₁, v * v = 1)
include hB hV

theorem bas_sq (j : Fin 8) : ((h.bas hd₀ j : d.D₄) : G) * (h.bas hd₀ j : d.D₄) = 1 :=
  h.D₄_sq hB hV (h.bas hd₀ j).2

theorem kap_add (v w : Fin 8 → ZMod 2) :
    h.kap hd₀ (v + w) = h.kap hd₀ v * h.kap hd₀ w :=
  kprod_add (h.bas_sq hd₀ hB hV) v w

theorem kap_mul_self (v : Fin 8 → ZMod 2) : h.kap hd₀ v * h.kap hd₀ v = 1 :=
  kprod_mul_self (h.bas_sq hd₀ hB hV) v

theorem kap_inv (v : Fin 8 → ZMod 2) : (h.kap hd₀ v)⁻¹ = h.kap hd₀ v :=
  inv_eq_of_mul_eq_one_right (h.kap_mul_self hd₀ hB hV v)

theorem conj_u₁_kap (v : Fin 8 → ZMod 2) :
    d.u₁ * h.kap hd₀ v * d.u₁⁻¹ = h.kap hd₀ (mU₁.mulVec v) :=
  kprod_conj (h.bas_sq hd₀ hB hV) (h.X₁_le_normalizer_D₄ h.u₁_mem) mU₁ (fun j => by
    rw [col_mU₁]; exact (h.conj_basG_u₁ d₀ j).trans (h.kap_single hd₀ _).symm) v

theorem conj_u₂_kap (v : Fin 8 → ZMod 2) :
    d.u₂ * h.kap hd₀ v * d.u₂⁻¹ = h.kap hd₀ (mU₂.mulVec v) :=
  kprod_conj (h.bas_sq hd₀ hB hV) (h.X₁_le_normalizer_D₄ h.u₂_mem) mU₂ (fun j => by
    rw [col_mU₂]; exact (h.conj_basG_u₂ d₀ j).trans (h.kap_single hd₀ _).symm) v

theorem conj_t_kap (hθ : d₀⁻¹ * d.t * d₀ * d.t = d.a₀) (v : Fin 8 → ZMod 2) :
    d.t * h.kap hd₀ v * d.t⁻¹ = h.kap hd₀ (mT.mulVec v) :=
  kprod_conj (h.bas_sq hd₀ hB hV) h.t_mem_normalizer_D₄ mT (fun j => by
    rw [col_mT]
    split_ifs with hj
    · exact (h.t_conj_basG_lo d₀ j hj).trans (h.kap_single hd₀ _).symm
    · rw [show (kprod h.D₄_comm' (h.bas hd₀) (Pi.single j 1 + Pi.single ⟨j - 4, by omega⟩ 1)) =
          h.kap hd₀ (Pi.single j 1 + Pi.single ⟨j - 4, by omega⟩ 1) from rfl,
        h.kap_add hd₀ hB hV, h.kap_single, h.kap_single]
      exact h.t_conj_basG_hi hθ j hj) v

theorem theta_kap (hθ : d₀⁻¹ * d.t * d₀ * d.t = d.a₀) (v : Fin 8 → ZMod 2) :
    (h.kap hd₀ v)⁻¹ * d.t * h.kap hd₀ v * d.t = h.kap hd₀ (lo (hiPart v)) := by
  rw [← add_mT, h.kap_add hd₀ hB hV, ← h.conj_t_kap hd₀ hB hV hθ, h.kap_inv hd₀ hB hV, h.t_inv]
  group

omit hB hV in
theorem kap_lo_zero : h.kap hd₀ (lo 0) = 1 := by
  rw [show lo 0 = 0 by ext i; simp [lo], h.kap_zero]

theorem kap_lo_mem_A₄ (hθ : d₀⁻¹ * d.t * d₀ * d.t = d.a₀) (w : Fin 4 → ZMod 2) :
    h.kap hd₀ (lo w) ∈ d.A₄ := by
  rw [← h.D₄_inf_H]
  refine mem_inf.mpr ⟨h.kap_mem hd₀ _, mem_centralizer_singleton_iff.mpr ?_⟩
  have h1 := h.theta_kap hd₀ hB hV hθ (lo w)
  rw [show hiPart (lo w) = 0 by ext k; simp [hiPart, lo], h.kap_lo_zero hd₀] at h1
  rw [h.kap_inv hd₀ hB hV] at h1
  have h3 : h.kap hd₀ (lo w) * d.t = (h.kap hd₀ (lo w) * d.t)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← h1]; group)
  rw [mul_inv_rev, h.t_inv, h.kap_inv hd₀ hB hV] at h3
  exact h3

@[expose] def loRange : Subgroup G where
  carrier := {g | ∃ w, h.kap hd₀ (lo w) = g}
  mul_mem' := by
    rintro _ _ ⟨w, rfl⟩ ⟨w', rfl⟩
    exact ⟨w + w', by rw [lo_add, h.kap_add hd₀ hB hV]⟩
  one_mem' := ⟨0, h.kap_lo_zero hd₀⟩
  inv_mem' := by
    rintro _ ⟨w, rfl⟩
    exact ⟨w, (h.kap_inv hd₀ hB hV _).symm⟩

theorem exists_lo {a : G} (ha : a ∈ d.A₄) :
    ∃ w, h.kap hd₀ (lo w) = a := by
  have hsub : (fun x => x * d.a₀ * x⁻¹) '' (d.X₁ : Set G) ⊆ (h.loRange hd₀ hB hV : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    have key : ∀ k : Fin 4, d.xs k * d.a₀ * (d.xs k)⁻¹ ∈ h.loRange hd₀ hB hV := by
      intro k
      refine ⟨Pi.single k 1, ?_⟩
      rw [lo_single, h.kap_single, Data.basG_lo d₀ _ (by simp)]
      congr 3 <;> ext <;> simp
    rcases h.X₁_cases hx with rfl | rfl | rfl | rfl
    · exact key 0
    · exact key 1
    · exact key 2
    · exact key 3
  exact ((closure_le _).mpr hsub) (h.A₄_le_closure ha)

theorem lo_injective (hθ : d₀⁻¹ * d.t * d₀ * d.t = d.a₀) {w w' : Fin 4 → ZMod 2}
    (hw : h.kap hd₀ (lo w) = h.kap hd₀ (lo w')) : w = w' := by
  let f : (Fin 4 → ZMod 2) → d.A₄ := fun w => ⟨h.kap hd₀ (lo w), h.kap_lo_mem_A₄ hd₀ hB hV hθ w⟩
  have hf : Function.Surjective f := fun a => by
    obtain ⟨w, hw⟩ := h.exists_lo hd₀ hB hV a.2
    exact ⟨w, Subtype.ext hw⟩
  have hc : Nat.card (Fin 4 → ZMod 2) ≤ Nat.card d.A₄ := by
    rw [h.card_A₄, Nat.card_eq_fintype_card]; simp
  exact (hf.bijective_of_nat_card_le hc).1 (Subtype.ext hw)

theorem kap_eq_one (hθ : d₀⁻¹ * d.t * d₀ * d.t = d.a₀) {u : Fin 8 → ZMod 2}
    (hu : h.kap hd₀ u = 1) : u = 0 := by
  have h1 := h.theta_kap hd₀ hB hV hθ u
  rw [hu, inv_one, one_mul, mul_one, h.t_sq, ← h.kap_lo_zero hd₀] at h1
  have hhi : hiPart u = 0 := (h.lo_injective hd₀ hB hV hθ h1).symm
  have hu' := eq_lo_of_hiPart u hhi
  rw [hu', ← h.kap_lo_zero hd₀] at hu
  rw [hu', h.lo_injective hd₀ hB hV hθ hu]
  ext i; simp [lo]

theorem kap_injective (hθ : d₀⁻¹ * d.t * d₀ * d.t = d.a₀) : Function.Injective (h.kap hd₀) := by
  intro v w hvw
  have h1 : h.kap hd₀ (v + w) = 1 := by
    rw [h.kap_add hd₀ hB hV, hvw, h.kap_mul_self hd₀ hB hV]
  have h2 := h.kap_eq_one hd₀ hB hV hθ h1
  calc v = v + (v + w) := by rw [h2, add_zero]
    _ = w := by
      ext i
      simp only [Pi.add_apply, ← add_assoc]
      rw [show v i + v i = 0 by rw [← two_mul, show (2 : ZMod 2) = 0 from rfl, zero_mul],
        zero_add]

theorem exists_kap (hθ : d₀⁻¹ * d.t * d₀ * d.t = d.a₀) {x : G} (hx : x ∈ d.D₄) :
    ∃ v, h.kap hd₀ v = x := by
  let f : (Fin 8 → ZMod 2) → d.D₄ := fun v => ⟨h.kap hd₀ v, h.kap_mem hd₀ v⟩
  have hf : Function.Injective f := fun v w hvw =>
    h.kap_injective hd₀ hB hV hθ (congrArg Subtype.val hvw)
  have hc : Nat.card d.D₄ ≤ Nat.card (Fin 8 → ZMod 2) := by
    rw [h.card_D₄, Nat.card_eq_fintype_card]; simp
  obtain ⟨v, hv⟩ := (hf.bijective_of_nat_card_le hc).2 ⟨x, hx⟩
  exact ⟨v, congrArg Subtype.val hv⟩

@[expose] def kapSub (P : (Fin 8 → ZMod 2) → Prop) (h0 : P 0)
    (hadd : ∀ v w, P v → P w → P (v + w)) : Subgroup G where
  carrier := {g | ∃ v, P v ∧ h.kap hd₀ v = g}
  mul_mem' := by
    rintro _ _ ⟨v, hv, rfl⟩ ⟨w, hw, rfl⟩
    exact ⟨v + w, hadd v w hv hw, h.kap_add hd₀ hB hV v w⟩
  one_mem' := ⟨0, h0, h.kap_zero hd₀⟩
  inv_mem' := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨v, hv, (h.kap_inv hd₀ hB hV v).symm⟩

variable (hθ : d₀⁻¹ * d.t * d₀ * d.t = d.a₀)
include hθ

theorem kap_mem_kapSub_iff {P : (Fin 8 → ZMod 2) → Prop} {h0 : P 0}
    {hadd : ∀ v w, P v → P w → P (v + w)} (v : Fin 8 → ZMod 2) :
    h.kap hd₀ v ∈ h.kapSub hd₀ hB hV P h0 hadd ↔ P v := by
  constructor
  · rintro ⟨w, hw, hwv⟩
    rwa [← h.kap_injective hd₀ hB hV hθ hwv]
  · exact fun hv => ⟨v, hv, rfl⟩

theorem card_kapSub {P : (Fin 8 → ZMod 2) → Prop} [DecidablePred P] {h0 : P 0}
    {hadd : ∀ v w, P v → P w → P (v + w)} :
    Nat.card (h.kapSub hd₀ hB hV P h0 hadd) = Fintype.card {v // P v} := by
  rw [← Nat.card_eq_fintype_card]
  symm
  refine Nat.card_congr (Equiv.ofBijective (fun v => ⟨h.kap hd₀ v, v, v.2, rfl⟩) ⟨?_, ?_⟩)
  · intro v w hvw
    have e : h.kap hd₀ v = h.kap hd₀ w :=
      congrArg (fun x : h.kapSub hd₀ hB hV P h0 hadd => (x : G)) hvw
    exact Subtype.ext (h.kap_injective hd₀ hB hV hθ e)
  · rintro ⟨_, v, hv, rfl⟩
    exact ⟨⟨v, hv⟩, rfl⟩

theorem kap_mem_H_iff (v : Fin 8 → ZMod 2) : h.kap hd₀ v ∈ d.H ↔ hiPart v = 0 := by
  constructor
  · intro hv
    have h1 := h.theta_kap hd₀ hB hV hθ v
    have hc : h.kap hd₀ v * d.t = d.t * h.kap hd₀ v := (mem_centralizer_singleton_iff.mp hv)
    rw [show (h.kap hd₀ v)⁻¹ * d.t * h.kap hd₀ v * d.t = (h.kap hd₀ v)⁻¹ *
      (d.t * h.kap hd₀ v) * d.t by group, ← hc, inv_mul_cancel_left, h.t_sq,
      ← h.kap_lo_zero hd₀] at h1
    exact (h.lo_injective hd₀ hB hV hθ h1).symm
  · intro hv
    rw [eq_lo_of_hiPart v hv]
    exact h.A₄_le_L.trans h.L_le_H (h.kap_lo_mem_A₄ hd₀ hB hV hθ _)

theorem kap_mem_A₄_iff (v : Fin 8 → ZMod 2) : h.kap hd₀ v ∈ d.A₄ ↔ hiPart v = 0 := by
  rw [← h.kap_mem_H_iff hd₀ hB hV hθ, ← h.D₄_inf_H]
  exact ⟨fun hv => hv.2, fun hv => ⟨h.kap_mem hd₀ v, hv⟩⟩

theorem conj_eq_iff {g : G} {M : Matrix (Fin 8) (Fin 8) (ZMod 2)}
    (hg : ∀ v, g * h.kap hd₀ v * g⁻¹ = h.kap hd₀ (M.mulVec v)) (v : Fin 8 → ZMod 2) :
    g * h.kap hd₀ v = h.kap hd₀ v * g ↔ M.mulVec v = v := by
  constructor
  · intro e
    apply h.kap_injective hd₀ hB hV hθ
    rw [← hg v, e, mul_inv_cancel_right]
  · intro e
    have h1 := hg v
    rw [e] at h1
    calc g * h.kap hd₀ v = g * h.kap hd₀ v * g⁻¹ * g := by group
      _ = h.kap hd₀ v * g := by rw [h1]

theorem kap_mem_V₁_iff (v : Fin 8 → ZMod 2) :
    h.kap hd₀ v ∈ d.V₁ ↔ mU₁.mulVec v = v ∧ mU₂.mulVec v = v := by
  have e₁ := h.conj_eq_iff hd₀ hB hV hθ (h.conj_u₁_kap hd₀ hB hV) v
  have e₂ := h.conj_eq_iff hd₀ hB hV hθ (h.conj_u₂_kap hd₀ hB hV) v
  constructor
  · intro hv
    have hc := mem_centralizer_iff.mp (V₁_le_cent_X₁ hv)
    exact ⟨e₁.mp (hc _ h.u₁_mem), e₂.mp (hc _ h.u₂_mem)⟩
  · rintro ⟨h1, h2⟩
    refine mem_inf.mpr ⟨h.kap_mem hd₀ v, mem_centralizer_iff.mpr fun x hx => ?_⟩
    have c₁ := e₁.mpr h1
    have c₂ := e₂.mpr h2
    rcases h.X₁_cases hx with rfl | rfl | rfl | rfl
    · simp
    · exact c₁
    · exact c₂
    · rw [mul_assoc, c₂, ← mul_assoc, c₁, mul_assoc]

omit hθ in
theorem comm_kap_coords {g : G} {M : Matrix (Fin 8) (Fin 8) (ZMod 2)}
    (hg : ∀ v, g * h.kap hd₀ v * g⁻¹ = h.kap hd₀ (M.mulVec v)) (v : Fin 8 → ZMod 2) :
    g * h.kap hd₀ v * g⁻¹ * (h.kap hd₀ v)⁻¹ = h.kap hd₀ (M.mulVec v + v) := by
  rw [hg, h.kap_inv hd₀ hB hV, h.kap_add hd₀ hB hV]

theorem V₂_eq_kapSub : d.V₂ = h.kapSub hd₀ hB hV augZ augZ_zero augZ_add := by
  refine Subgroup.eq_of_le_of_card_ge (fun g hg => ?_) ?_
  · obtain ⟨v, rfl⟩ := h.exists_kap hd₀ hB hV hθ (h.V₂_le_D₄ hg)
    have c₁ := h.comm_X₁_V₂ hV h.u₁_mem hg
    have c₂ := h.comm_X₁_V₂ hV h.u₂_mem hg
    rw [h.comm_kap_coords hd₀ hB hV (h.conj_u₁_kap hd₀ hB hV),
      h.kap_mem_V₁_iff hd₀ hB hV hθ] at c₁
    rw [h.comm_kap_coords hd₀ hB hV (h.conj_u₂_kap hd₀ hB hV),
      h.kap_mem_V₁_iff hd₀ hB hV hθ] at c₂
    exact ⟨v, augZ_of_comm v c₁.1 c₁.2 c₂.1 c₂.2, rfl⟩
  · rw [h.card_kapSub hd₀ hB hV hθ, card_augZ, h.card_V₂]

theorem kap_mem_V₂_iff (v : Fin 8 → ZMod 2) : h.kap hd₀ v ∈ d.V₂ ↔ augZ v := by
  rw [h.V₂_eq_kapSub hd₀ hB hV hθ, h.kap_mem_kapSub_iff hd₀ hB hV hθ]

theorem kap_mem_Z₂S_iff (v : Fin 8 → ZMod 2) :
    h.kap hd₀ v ∈ d.Z₂S ↔ augZ v ∧ hiPart v = 0 := by
  rw [← h.V₂_inf_H, mem_inf, h.kap_mem_V₂_iff hd₀ hB hV hθ, h.kap_mem_H_iff hd₀ hB hV hθ]

omit hθ in
theorem conj_xs_kap (k : Fin 4) (v : Fin 8 → ZMod 2) :
    d.xs k * h.kap hd₀ v * (d.xs k)⁻¹ = h.kap hd₀ ((mX k).mulVec v) := by
  fin_cases k
  · simp [Data.xs, mX]
  · exact h.conj_u₁_kap hd₀ hB hV v
  · exact h.conj_u₂_kap hd₀ hB hV v
  · show d.u₁ * d.u₂ * h.kap hd₀ v * (d.u₁ * d.u₂)⁻¹ = h.kap hd₀ ((mU₁ * mU₂).mulVec v)
    rw [← Matrix.mulVec_mulVec, ← h.conj_u₁_kap hd₀ hB hV, ← h.conj_u₂_kap hd₀ hB hV]
    group

omit hθ in
theorem comm_kap_left {g : G} {M : Matrix (Fin 8) (Fin 8) (ZMod 2)}
    (hg : ∀ v, g * h.kap hd₀ v * g⁻¹ = h.kap hd₀ (M.mulVec v)) (v : Fin 8 → ZMod 2) :
    ⁅h.kap hd₀ v, g⁆ = h.kap hd₀ (v + M.mulVec v) := by
  rw [commutatorElement_def, h.kap_inv hd₀ hB hV,
    show h.kap hd₀ v * g * h.kap hd₀ v * g⁻¹ = h.kap hd₀ v * (g * h.kap hd₀ v * g⁻¹) by group,
    hg, ← h.kap_add hd₀ hB hV]

omit [Finite G] hB hV hθ in
theorem exists_xs {x : G} (hx : x ∈ d.X₁) : ∃ k, d.xs k = x := by
  rcases h.X₁_cases hx with rfl | rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩

end Hyp

end CFSG.EvenSmallLie.UnitarySix.YamadaD
