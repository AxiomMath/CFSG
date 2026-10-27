module

public import CFSG.Certificates.Kernel.DceTwCore
import all CFSG.Certificates.Kernel.DceTwCore
import CFSG.Certificates.Kernel.Co1DceCover
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Group

public section

namespace CFSG.Certificates.DceTw

variable {G : Type*} [Group G] {K : Type*} [Group K]
  {N : Subgroup G} {u : G} {M : Subgroup K} {φ : M →* G} {NORD : ℕ} {Pt : Type*}
  {act : Pt → K → Pt} {θ : Pt} {ω : ℕ → Pt} {g : ℕ → M} {NO I0 : ℕ} {σ : ℕ → M} {nT : ℕ}
  {w : ℕ → G} {A : Finset ℕ} {mD : ℕ → ℕ}

private def stabN (N : Subgroup G) (w : G) : Subgroup N where
  carrier := {n | w * (n : G) * w⁻¹ ∈ N}
  one_mem' := by simp [N.one_mem]
  mul_mem' := fun {a b} ha hb => by
    have e : w * ((a * b : N) : G) * w⁻¹ = (w * (a : G) * w⁻¹) * (w * (b : G) * w⁻¹) := by
      simp only [Subgroup.coe_mul]
      group
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [e]
    exact N.mul_mem ha hb
  inv_mem' := fun {a} ha => by
    have e : w * ((a⁻¹ : N) : G) * w⁻¹ = (w * (a : G) * w⁻¹)⁻¹ := by
      simp only [Subgroup.coe_inv]
      group
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rw [e]
    exact N.inv_mem ha

private theorem mem_stabN {w : G} {n : N} : n ∈ stabN N w ↔ w * (n : G) * w⁻¹ ∈ N := Iff.rfl

private theorem closure_sub_cov (h : Hyp N u M φ NORD Pt act θ ω g NO I0 σ nT w A mD) (X : Set G)
    (hX : ∀ x ∈ X, x ∈ N ∨ x = u ∨ x = u⁻¹) : ∀ x ∈ Subgroup.closure X, x ∈ Cov N w A := by
  intro x hx
  induction hx using Subgroup.closure_induction_right with
  | one => exact ⟨0, h.zero_mem, 1, N.one_mem, 1, N.one_mem, by rw [h.w_zero]; group⟩
  | mul_right x _ y hy ih =>
    rcases hX y hy with hy | rfl | rfl
    · exact cov_mul_N ih hy
    · exact cov_mul_u h ih
    · exact cov_mul_uinv h ih
  | mul_inv_cancel x _ y hy ih =>
    rcases hX y hy with hy | rfl | rfl
    · exact cov_mul_N ih (N.inv_mem hy)
    · exact cov_mul_uinv h ih
    · rw [inv_inv]
      exact cov_mul_u h ih

private theorem stabN_index_le (h : Hyp N u M φ NORD Pt act θ ω g NO I0 σ nT w A mD) {D : ℕ}
    (hD : D ∈ A) (hD0 : D ≠ 0) : (stabN N (w D)).index ≤ NORD / mD D := by
  obtain ⟨hMcard, -⟩ := decomp h
  have _ := h.orb.finM
  have hNORD : 0 < NORD := hMcard ▸ Nat.card_pos
  have hm : 0 < mD D := Nat.pos_of_dvd_of_pos (h.mD_dvd D hD hD0) hNORD
  let φ' : M →* N := φ.codRestrict N h.φN
  have hφ' : Function.Surjective φ' := by
    rintro ⟨n, hn⟩
    obtain ⟨m, rfl⟩ := h.Nφ n hn
    exact ⟨m, rfl⟩
  rw [← Subgroup.index_comap_of_surjective (H := stabN N (w D)) hφ']
  have hmul := Subgroup.card_mul_index ((stabN N (w D)).comap φ')
  rw [hMcard] at hmul
  have hcomap : mD D ≤ Nat.card ((stabN N (w D)).comap φ') := by
    rcases h.stabD D hD hD0 with h1 | ⟨E, hEinj, hE⟩
    · rw [h1]
      exact Nat.card_pos
    · let E' : Fin (mD D) → (stabN N (w D)).comap φ' := fun k => ⟨E k, hE k k.2⟩
      have hinj : Function.Injective E' := fun k k' hkk =>
        Fin.ext (hEinj k k.2 k' k'.2 (congrArg Subtype.val hkk))
      simpa using Nat.card_le_card_of_injective E' hinj
  rw [Nat.le_div_iff_mul_le hm, ← hmul, Nat.mul_comm (Nat.card _)]
  exact Nat.mul_le_mul_left _ hcomap

theorem dceTw_eq (h : Hyp N u M φ NORD Pt act θ ω g NO I0 σ nT w A mD) (X : Set G)
    (hX : ∀ x ∈ X, x ∈ N ∨ x = u ∨ x = u⁻¹) (hgen : Subgroup.closure X = ⊤)
    (hcard : Nat.card G = NORD * (1 + ∑ D ∈ A.erase 0, NORD / mD D)) :
    Function.Injective φ ∧ Nat.card N = NORD ∧
      (∀ x : G, ∃ D ∈ A, ∃ a ∈ N, ∃ b ∈ N, x = a * w D * b) ∧
      ∀ D ∈ A, D ≠ 0 → Nat.card {n : G // n ∈ N ∧ w D * n * (w D)⁻¹ ∈ N} = mD D := by
  classical
  obtain ⟨hNfin, hNcard⟩ := fin_N h
  obtain ⟨hMcard, -⟩ := decomp h
  have _ := h.orb.finM
  have hNORD : 0 < NORD := hMcard ▸ Nat.card_pos
  have hcov : ∀ x : G, x ∈ Cov N w A := fun x =>
    closure_sub_cov h X hX x (hgen ▸ Subgroup.mem_top x)
  let bnd : ℕ → ℕ := fun D => if D = 0 then 1 else NORD / mD D
  have hstab0 : stabN N (w 0) = ⊤ := (Subgroup.eq_top_iff' _).2 fun n => by
    rw [mem_stabN, h.w_zero, one_mul, inv_one, mul_one]
    exact n.2
  have hidx : ∀ D ∈ A, (stabN N (w D)).index ≤ bnd D := by
    intro D hD
    by_cases hD0 : D = 0
    · subst hD0
      simp [bnd, hstab0]
    · simp only [bnd, hD0, ite_false]
      exact stabN_index_le h hD hD0
  choose R hRcard hRN hRcov using fun D =>
    Co1D.dcoset_reps N (w D) (stabN N (w D)) fun _ hk => hk
  obtain ⟨-, hcardle⟩ := Co1D.card_cover N A w R ⊤ fun x _ => by
    obtain ⟨D, hD, a, ha, b, hb, rfl⟩ := hcov x
    obtain ⟨a', ha', r, hr, e⟩ := hRcov D a ha b hb
    exact ⟨D, hD, a', ha', r, hr, e⟩
  rw [Subgroup.card_top] at hcardle
  have hle : ∀ D ∈ A, Nat.card N * (stabN N (w D)).index ≤ NORD * bnd D := fun D hD =>
    Nat.mul_le_mul (hNcard.trans h.orb.cardM) (hidx D hD)
  have hsum : ∑ D ∈ A, NORD * bnd D = Nat.card G := by
    rw [hcard, ← Finset.mul_sum, ← Finset.add_sum_erase A bnd h.zero_mem]
    congr 2
    apply Finset.sum_congr rfl
    intro D hD
    simp only [bnd, Finset.ne_of_mem_erase hD, ite_false]
  have hge : ∑ D ∈ A, NORD * bnd D ≤ ∑ D ∈ A, Nat.card N * (stabN N (w D)).index := by
    rw [hsum]
    exact hcardle.trans (Finset.sum_le_sum fun D _ => Nat.mul_le_mul_left _ (hRcard D))
  have hterm := (Finset.sum_eq_sum_iff_of_le hle).1 (le_antisymm (Finset.sum_le_sum hle) hge)
  have hN : Nat.card N = NORD := by
    have := hterm 0 h.zero_mem
    simpa [bnd, hstab0] using this
  let φ' : M →* N := φ.codRestrict N h.φN
  have hφ' : Function.Surjective φ' := by
    rintro ⟨n, hn⟩
    obtain ⟨m, rfl⟩ := h.Nφ n hn
    exact ⟨m, rfl⟩
  have hbij := hφ'.bijective_of_nat_card_le (hMcard.trans hN.symm).le
  refine ⟨fun a b hab => hbij.1 (Subtype.ext hab), hN, hcov, fun D hD hD0 => ?_⟩
  have hdvd := h.mD_dvd D hD hD0
  have hq : 0 < NORD / mD D :=
    Nat.div_pos (Nat.le_of_dvd hNORD hdvd) (Nat.pos_of_dvd_of_pos hdvd hNORD)
  have hi : (stabN N (w D)).index = NORD / mD D := by
    have := hterm D hD
    simp only [bnd, hD0, ite_false, hN] at this
    exact Nat.eq_of_mul_eq_mul_left hNORD this
  have hS : Nat.card (stabN N (w D)) = mD D := by
    have hc := Subgroup.card_mul_index (stabN N (w D))
    rw [hi, hN] at hc
    apply Nat.eq_of_mul_eq_mul_right hq
    rw [hc, Nat.mul_div_cancel' hdvd]
  refine Eq.trans (Nat.card_congr ?_) hS
  exact
    { toFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
      invFun := fun y => ⟨y.1.1, y.1.2, y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem stab_exhaust [Finite G] (hφ : Function.Injective φ) {wD : G} {m : ℕ}
    (hcard : Nat.card {n : G // n ∈ N ∧ wD * n * wD⁻¹ ∈ N} = m) {E : ℕ → M}
    (hEinj : ∀ k < m, ∀ k' < m, E k = E k' → k = k')
    (hE : ∀ k < m, φ (E k) ∈ N ∧ wD * φ (E k) * wD⁻¹ ∈ N) :
    ∀ n ∈ N, wD * n * wD⁻¹ ∈ N → ∃ k < m, φ (E k) = n := by
  let f : Fin m → {n : G // n ∈ N ∧ wD * n * wD⁻¹ ∈ N} := fun k => ⟨φ (E k), hE k k.2⟩
  have hf : Function.Injective f := fun k k' hkk =>
    Fin.ext (hEinj k k.2 k' k'.2 (hφ (congrArg Subtype.val hkk)))
  have hbij := hf.bijective_of_nat_card_le (hcard.trans (Nat.card_fin m).symm).le
  intro n hn hwn
  obtain ⟨k, hk⟩ := hbij.2 ⟨n, hn, hwn⟩
  exact ⟨k.1, k.2, congrArg Subtype.val hk⟩

end CFSG.Certificates.DceTw

end
