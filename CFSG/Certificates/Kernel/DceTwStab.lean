module

public import Mathlib.GroupTheory.Index
import CFSG.Certificates.Kernel.Co1DceCover
import Mathlib.Tactic.Group
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

public section

namespace CFSG.Certificates.DceTwS

variable {G : Type*} [Group G] {K : Type*} [Group K]

@[expose] def Cov (N : Subgroup G) (w : ℕ → G) (A : Finset ℕ) : Set G :=
  {y | ∃ D ∈ A, ∃ a ∈ N, ∃ b ∈ N, y = a * w D * b}

structure Hyp (N : Subgroup G) (u : G) (M : Subgroup K) (φ : M →* G) (NORD : ℕ) (Pt : Type*)
    (act : Pt → K → Pt) (θ : Pt) (ω : ℕ → Pt) (g : ℕ → M) (NO : ℕ) (w : ℕ → G) (A : Finset ℕ)
    (mD : ℕ → ℕ) : Prop where
  φN : ∀ m, φ m ∈ N
  Nφ : ∀ n ∈ N, ∃ m, φ m = n
  finM : Finite M
  cardM : Nat.card M ≤ NORD
  act_one : ∀ p, act p 1 = p
  act_mul : ∀ p a b, act (act p a) b = act p (a * b)
  orbit : ∀ j < NO, act θ (g j) = ω j
  onto : ∀ m : M, ∃ j < NO, act θ m = ω j
  usq : u * u = 1
  conj : ∀ s : M, act θ s = θ → u * φ s * u ∈ N
  zero_mem : 0 ∈ A
  w_zero : w 0 = 1
  cover : ∀ D ∈ A, ∀ j < NO, w D * ((φ (g j))⁻¹ * u * φ (g j)) ∈ Cov N w A
  stabD : ∀ D ∈ A, D ≠ 0 → 0 < mD D ∧ mD D ≤ Nat.card {m : M // w D * φ m * (w D)⁻¹ ∈ N}

variable {N : Subgroup G} {w : ℕ → G} {A : Finset ℕ}

theorem cov_mul_N {y n : G} (hy : y ∈ Cov N w A) (hn : n ∈ N) : y * n ∈ Cov N w A := by
  obtain ⟨D, hD, a, ha, b, hb, rfl⟩ := hy
  exact ⟨D, hD, a, ha, b * n, N.mul_mem hb hn, by group⟩

theorem N_mul_cov {y n : G} (hy : y ∈ Cov N w A) (hn : n ∈ N) : n * y ∈ Cov N w A := by
  obtain ⟨D, hD, a, ha, b, hb, rfl⟩ := hy
  exact ⟨D, hD, n * a, N.mul_mem hn ha, b, hb, by group⟩

theorem mem_cov {D : ℕ} (hD : D ∈ A) {a b : G} (ha : a ∈ N) (hb : b ∈ N) : a * w D * b ∈ Cov N w A :=
  ⟨D, hD, a, ha, b, hb, rfl⟩

variable {u : G} {M : Subgroup K} {φ : M →* G} {NORD : ℕ} {Pt : Type*}
  {act : Pt → K → Pt} {θ : Pt} {ω : ℕ → Pt} {g : ℕ → M} {NO : ℕ} {mD : ℕ → ℕ}

theorem cov_mul_u (h : Hyp N u M φ NORD Pt act θ ω g NO w A mD) {y : G}
    (hy : y ∈ Cov N w A) : y * u ∈ Cov N w A := by
  obtain ⟨D, hD, a, ha, b, hb, rfl⟩ := hy
  obtain ⟨m, rfl⟩ := h.Nφ b hb
  obtain ⟨j, hj, hm⟩ := h.onto m⁻¹
  have hs : act θ ((g j * m : M) : K) = θ := by
    rw [Subgroup.coe_mul, ← h.act_mul, h.orbit j hj, ← hm, h.act_mul]
    simp [h.act_one]
  have key : a * w D * φ m * u =
      a * (w D * ((φ (g j))⁻¹ * u * φ (g j))) * ((φ (g j))⁻¹ * (u * φ (g j * m) * u)) := by
    have e : (φ (g j))⁻¹ * u * φ (g j) * ((φ (g j))⁻¹ * (u * φ (g j * m) * u)) = φ m * u := by
      rw [map_mul]
      calc (φ (g j))⁻¹ * u * φ (g j) * ((φ (g j))⁻¹ * (u * (φ (g j) * φ m) * u)) =
          (φ (g j))⁻¹ * (u * u) * φ (g j) * φ m * u := by group
        _ = φ m * u := by rw [h.usq]; group
    calc a * w D * φ m * u = a * (w D * (φ m * u)) := by group
      _ = a * (w D * ((φ (g j))⁻¹ * u * φ (g j) * ((φ (g j))⁻¹ * (u * φ (g j * m) * u)))) := by
          rw [e]
      _ = _ := by group
  rw [key]
  exact cov_mul_N (N_mul_cov (h.cover D hD j hj) ha)
    (N.mul_mem (N.inv_mem (h.φN _)) (h.conj _ hs))

theorem bound (h : Hyp N u M φ NORD Pt act θ ω g NO w A mD) (X : Set G)
    (hX : ∀ x ∈ X, x ∈ N ∨ x = u ∨ x = u⁻¹) :
    Finite (Subgroup.closure X) ∧
      Nat.card (Subgroup.closure X) ≤ NORD * (1 + ∑ D ∈ A.erase 0, NORD / mD D) := by
  classical
  have _ := h.finM
  let f : M → N := fun m => ⟨φ m, h.φN m⟩
  have hf : Function.Surjective f := by
    rintro ⟨n, hn⟩
    obtain ⟨m, rfl⟩ := h.Nφ n hn
    exact ⟨m, rfl⟩
  have hNfin : Finite N := Finite.of_surjective f hf
  have hNcard : Nat.card N ≤ Nat.card M := Nat.card_le_card_of_surjective f hf
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right h.usq
  have hsub : ∀ x ∈ Subgroup.closure X, x ∈ Cov N w A := by
    intro x hx
    induction hx using Subgroup.closure_induction_right with
    | one => exact ⟨0, h.zero_mem, 1, N.one_mem, 1, N.one_mem, by rw [h.w_zero]; group⟩
    | mul_right x _ y hy ih =>
      rcases hX y hy with hy | rfl | rfl
      · exact cov_mul_N ih hy
      · exact cov_mul_u h ih
      · rw [huinv]
        exact cov_mul_u h ih
    | mul_inv_cancel x _ y hy ih =>
      rcases hX y hy with hy | rfl | rfl
      · exact cov_mul_N ih (N.inv_mem hy)
      · rw [huinv]
        exact cov_mul_u h ih
      · rw [inv_inv]
        exact cov_mul_u h ih
  let bnd : ℕ → ℕ := fun D => if D = 0 then 1 else NORD / mD D
  have hrep : ∀ D ∈ A, ∃ R : Finset G, R.card ≤ bnd D ∧
      ∀ a ∈ N, ∀ b ∈ N, ∃ a' ∈ N, ∃ r ∈ R, a * w D * b = a' * w D * r := by
    intro D hD
    by_cases hD0 : D = 0
    · subst hD0
      obtain ⟨R, hR, -, hcov⟩ := CFSG.Certificates.Co1D.dcoset_reps N (w 0) ⊤
        (fun k _ => by rw [h.w_zero, one_mul, inv_one, mul_one]; exact k.2)
      refine ⟨R, ?_, hcov⟩
      simp only [bnd, ite_true]
      rwa [Subgroup.index_top] at hR
    · let H : Subgroup N :=
        { carrier := {n | w D * (n : G) * (w D)⁻¹ ∈ N}
          one_mem' := by simp [N.one_mem]
          mul_mem' := fun {a b} ha hb => by
            have e : w D * ((a * b : N) : G) * (w D)⁻¹ =
                (w D * (a : G) * (w D)⁻¹) * (w D * (b : G) * (w D)⁻¹) := by
              simp only [Subgroup.coe_mul]
              group
            simp only [Set.mem_ofPred_eq] at ha hb ⊢
            rw [e]
            exact N.mul_mem ha hb
          inv_mem' := fun {a} ha => by
            have e : w D * ((a⁻¹ : N) : G) * (w D)⁻¹ = (w D * (a : G) * (w D)⁻¹)⁻¹ := by
              simp only [Subgroup.coe_inv]
              group
            simp only [Set.mem_ofPred_eq] at ha ⊢
            rw [e]
            exact N.inv_mem ha }
      obtain ⟨R, hR, -, hcov⟩ := CFSG.Certificates.Co1D.dcoset_reps N (w D) H (fun k hk => hk)
      refine ⟨R, hR.trans ?_, hcov⟩
      simp only [bnd, hD0, ite_false]
      let φ' : M →* N := φ.codRestrict N h.φN
      have hφ' : Function.Surjective φ' := by
        rintro ⟨n, hn⟩
        obtain ⟨m, rfl⟩ := h.Nφ n hn
        exact ⟨m, rfl⟩
      rw [← Subgroup.index_comap_of_surjective (H := H) hφ']
      have hmul := Subgroup.card_mul_index (H.comap φ')
      have hpos : 0 < Nat.card (H.comap φ') := Nat.card_pos
      obtain ⟨hm0, hmc⟩ := h.stabD D hD hD0
      have hcomap : mD D ≤ Nat.card (H.comap φ') :=
        hmc.trans (Nat.card_congr (Equiv.subtypeEquivRight
          (p := fun m : M => w D * φ m * (w D)⁻¹ ∈ N) (q := fun m => m ∈ H.comap φ')
          fun _ => Iff.rfl)).le
      calc (H.comap φ').index = Nat.card M / Nat.card (H.comap φ') := by
            rw [← hmul, Nat.mul_div_cancel_left _ hpos]
        _ ≤ Nat.card M / mD D := Nat.div_le_div_left hcomap hm0
        _ ≤ NORD / mD D := Nat.div_le_div_right h.cardM
  choose! R hRcard hRcov using hrep
  obtain ⟨hfin, hcard⟩ := CFSG.Certificates.Co1D.card_cover N A w R (Subgroup.closure X) (by
    intro x hx
    obtain ⟨D, hD, a, ha, b, hb, rfl⟩ := hsub x hx
    obtain ⟨a', ha', r, hr, e⟩ := hRcov D hD a ha b hb
    exact ⟨D, hD, a', ha', r, hr, e⟩)
  refine ⟨hfin, hcard.trans ?_⟩
  calc ∑ D ∈ A, Nat.card N * (R D).card ≤ ∑ D ∈ A, NORD * bnd D :=
        Finset.sum_le_sum fun D hD => Nat.mul_le_mul (hNcard.trans h.cardM) (hRcard D hD)
    _ = NORD * ∑ D ∈ A, bnd D := by rw [Finset.mul_sum]
    _ = NORD * (1 + ∑ D ∈ A.erase 0, NORD / mD D) := by
        rw [← Finset.add_sum_erase A bnd h.zero_mem]
        congr 2
        apply Finset.sum_congr rfl
        intro D hD
        simp only [bnd, Finset.ne_of_mem_erase hD, ite_false]

end CFSG.Certificates.DceTwS

end
