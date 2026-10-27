module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecFuseGW
public import CFSG.LocalAnalysis.OddStandard.AltStdSecFuseGb
public import CFSG.LocalAnalysis.OddStandard.AltStdSecFuseR8
public import CFSG.LocalAnalysis.OddStandard.AltStdSecFuseGNum
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.OddStandard.AltStdSec.SylowSn

open scoped Classical in
@[expose] noncomputable def wtB (a : ℕ) (j : Fin 3) (x : W a) : R8 :=
  (if x ∈ Fb a then 1 else 0) + eR j * (if x ∈ Gb a then 1 else 0)

@[expose] noncomputable def tabB (a : ℕ) (g : W a) : R8 := trSum (fun j => wtB a j) g

theorem tabB_notMem_Gb (a : ℕ) {x : W a} (hx : x ∈ Fb a) : x ∉ Gb a :=
  fun h => Set.disjoint_left.1 (disjoint_Fb_Gb a) hx h

theorem tabB_notMem_Fb (a : ℕ) {x : W a} (hx : x ∈ Gb a) : x ∉ Fb a :=
  fun h => Set.disjoint_left.1 (disjoint_Fb_Gb a) h hx

theorem wtB_of_mem_Fb (a : ℕ) (j : Fin 3) {x : W a} (hx : x ∈ Fb a) : wtB a j x = 1 := by
  simp [wtB, hx, tabB_notMem_Gb a hx]

theorem wtB_of_mem_Gb (a : ℕ) (j : Fin 3) {x : W a} (hx : x ∈ Gb a) : wtB a j x = eR j := by
  simp [wtB, hx, tabB_notMem_Fb a hx]

theorem wtB_of_not_mem (a : ℕ) (j : Fin 3) {x : W a} (hF : x ∉ Fb a) (hG : x ∉ Gb a) :
    wtB a j x = 0 := by
  simp [wtB, hF, hG]

theorem Fb_Gb_trichotomy (a : ℕ) (x : W a) :
    (x ∈ Fb a ∧ x ∉ Gb a) ∨ (x ∉ Fb a ∧ x ∈ Gb a) ∨ (x ∉ Fb a ∧ x ∉ Gb a) := by
  by_cases h1 : x ∈ Fb a
  · exact Or.inl ⟨h1, tabB_notMem_Gb a h1⟩
  · by_cases h2 : x ∈ Gb a
    · exact Or.inr (Or.inl ⟨h1, h2⟩)
    · exact Or.inr (Or.inr ⟨h1, h2⟩)

theorem wtB_succ_one (a : ℕ) (ha : 1 ≤ a) (j : Fin 3) (u v : W a) (x : W (a + 1))
    (hx : x = wr u v 1) : wtB (a + 1) j x = wtB a j u * wtB a j v := by
  have hF1 : x ∈ Fb (a + 1) ↔ u ∈ Fb a ∧ v ∈ Fb a := by
    subst hx
    refine (mem_Fb_wr a u v 1).trans ?_
    simp [z2_ne_one.symm]
  have hG1 : x ∈ Gb (a + 1) ↔ (u ∈ Gb a ∧ v ∈ Fb a) ∨ (u ∈ Fb a ∧ v ∈ Gb a) := by
    subst hx
    refine (mem_Gb_wr a ha u v 1).trans ?_
    simp
  unfold wtB
  rw [hF1, hG1]
  rcases Fb_Gb_trichotomy a u with ⟨hu1, hu2⟩ | ⟨hu1, hu2⟩ | ⟨hu1, hu2⟩ <;>
  rcases Fb_Gb_trichotomy a v with ⟨hv1, hv2⟩ | ⟨hv1, hv2⟩ | ⟨hv1, hv2⟩ <;>
  simp [hu1, hu2, hv1, hv2, eR_mul_self]

theorem wtB_succ (a : ℕ) (ha : 1 ≤ a) (j : Fin 3) (y : W a ≀ᵣ Z2) :
    wtB (a + 1) j y = wrW (wtB a j) 1 y := by
  obtain ⟨u, v, q, rfl⟩ : ∃ (u v : W a) (q : Z2), y = wr u v q := ⟨_, _, _, (wr_eta y).symm⟩
  classical
  have hW : wrW (wtB a j) 1 (wr u v q) =
      if q = 1 then wtB a j u * wtB a j v else if v = u⁻¹ then 1 else 0 := by
    simp [wrW]
  rw [hW]
  rcases z2_cases q with rfl | rfl
  · rw [ite_eq_left rfl]
    exact wtB_succ_one a ha j u v _ rfl
  · rw [ite_eq_right z2_ne_one]
    by_cases hv : v = u⁻¹
    · rw [ite_eq_left hv]
      exact wtB_of_mem_Fb (a + 1) j ((mem_Fb_wr a u v z2).2 (Or.inr ⟨rfl, hv⟩))
    · rw [ite_eq_right hv]
      refine wtB_of_not_mem (a + 1) j (fun h => ?_) (fun h => ?_)
      · rcases (mem_Fb_wr a u v z2).1 h with ⟨h1, -⟩ | ⟨-, h2⟩
        · exact z2_ne_one h1
        · exact hv h2
      · exact z2_ne_one ((mem_Gb_wr a ha u v z2).1 h).1

open scoped Classical in
theorem wtB_sq (a : ℕ) (j : Fin 3) (x : W a) :
    wtB a j x ^ 2 = if x ∈ Fb a then 1 else 0 := by
  rcases Fb_Gb_trichotomy a x with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [wtB_of_mem_Fb a j h1, ite_eq_left h1, one_pow]
  · rw [wtB_of_mem_Gb a j h2, ite_eq_right h1, sq, eR_mul_self]
  · rw [wtB_of_not_mem a j h1 h2, ite_eq_right h1, zero_pow two_ne_zero]

open scoped Classical in
theorem tabB_finsum_ite_mem (a : ℕ) (S : Set (W a)) :
    (∑ᶠ x : W a, (if x ∈ S then (1 : R8) else 0)) = ((Nat.card S : ℕ) : R8) := by
  have : Fintype (W a) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype, Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem finsum_wtB_sq (a : ℕ) (ha : 1 ≤ a) (j : Fin 3) :
    ∑ᶠ x : W a, wtB a j x ^ 2 = ((phiB a : ℕ) : R8) := by
  rw [← card_Fb_eq a ha, ← tabB_finsum_ite_mem]
  exact finsum_congr fun x => wtB_sq a j x

theorem wtB_conj_mem_Fb (a : ℕ) (d x : W a) : d * x * d⁻¹ ∈ Fb a ↔ x ∈ Fb a := by
  refine ⟨fun h => ?_, Fb_conj d⟩
  have h' := Fb_conj d⁻¹ h
  rwa [show d⁻¹ * (d * x * d⁻¹) * d⁻¹⁻¹ = x by group] at h'

theorem wtB_conj_mem_Gb (a : ℕ) (d x : W a) : d * x * d⁻¹ ∈ Gb a ↔ x ∈ Gb a := by
  refine ⟨fun h => ?_, Gb_conj d⟩
  have h' := Gb_conj d⁻¹ h
  rwa [show d⁻¹ * (d * x * d⁻¹) * d⁻¹⁻¹ = x by group] at h'

theorem wtB_conj (a : ℕ) (j : Fin 3) (x d : W a) : wtB a j (d * x * d⁻¹) = wtB a j x := by
  unfold wtB
  rw [wtB_conj_mem_Fb, wtB_conj_mem_Gb]

theorem wtB_eq_zero_of_mul_self_ne (a : ℕ) (j : Fin 3) (x : W a) (hx : x * x ≠ 1) :
    wtB a j x = 0 :=
  wtB_of_not_mem a j (fun h => hx (Fb_sq h)) (fun h => hx (Gb_sq h))

theorem tabB_succ (a : ℕ) (ha : 1 ≤ a) (g : W a) (hg2 : g * g = 1)
    (hgc : ∀ d : W a, d * g = g * d) :
    tabB (a + 1) (diag g) = tabB a g ^ 2 + ((3 * (piB a * phiB a) : ℕ) : R8) := by
  have h := trSum_wrW_inv (fun j => wtB a j) (fun _ => (1 : R8)) g hg2 hgc
    (wtB_eq_zero_of_mul_self_ne a) (wtB_conj a)
  have e : (fun j : Fin 3 => (wtB (a + 1) j : W a ≀ᵣ Z2 → R8)) = fun j => wrW (wtB a j) 1 :=
    funext fun j => funext fun y => wtB_succ a ha j y
  have h1 : tabB (a + 1) (diag g) = trSum (fun j => wrW (wtB a j) (1 : R8)) (diag g) :=
    congrArg (fun w : Fin 3 → W a ≀ᵣ Z2 → R8 => trSum w (diag g)) e
  rw [h1, h, card_W_eq]
  simp only [finsum_wtB_sq a ha, one_mul]
  unfold tabB
  push_cast
  ring

theorem tabB_succ_of_eq (a : ℕ) (ha : 1 ≤ a) (g : W a) (g' : W (a + 1)) (hg' : g' = diag g)
    (hg2 : g * g = 1) (hgc : ∀ d : W a, d * g = g * d) :
    tabB (a + 1) g' = tabB a g ^ 2 + ((3 * (piB a * phiB a) : ℕ) : R8) := by
  subst hg'
  exact tabB_succ a ha g hg2 hgc

private def tabBTriple (α : Type*) : α × α × α ≃ (Fin 3 → α) where
  toFun p := ![p.1, p.2.1, p.2.2]
  invFun t := (t 0, t 1, t 2)
  left_inv _ := rfl
  right_inv t := by
    ext i
    fin_cases i <;> rfl

private theorem tabBTriple_apply {α : Type*} (x y z : α) :
    tabBTriple α (x, y, z) = ![x, y, z] := rfl

open scoped Classical in
theorem tabB_trSum_eq_sum {D : Type*} [Group D] [Fintype D] {R : Type*} [CommSemiring R]
    (w : Fin 3 → D → R) (g : D) :
    trSum w g = ∑ x : D, ∑ y : D, ∑ z : D, if x * y * z = g then w 0 x * w 1 y * w 2 z else 0 := by
  unfold trSum
  rw [finsum_eq_sum_of_fintype, ← Equiv.sum_comp (tabBTriple D), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun y _ => ?_
  refine Finset.sum_congr rfl fun z _ => ?_
  simp [tabBTriple_apply, Fin.prod_univ_three, mul_assoc]

theorem tabB_W1_cases (x : W 1) : x = 1 ∨ x = cc 1 :=
  eq_one_or_cc 1 le_rfl x (fun b => W_one_comm b x) (W_one_sq x)

open scoped Classical in
theorem tabB_W1_univ [Fintype (W 1)] : (Finset.univ : Finset (W 1)) = {1, cc 1} := by
  ext x
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
  exact tabB_W1_cases x

theorem wtB_one_one (j : Fin 3) : wtB 1 j 1 = eR j :=
  wtB_of_mem_Gb 1 j (by rw [Gb_one]; exact Set.mem_singleton _)

theorem wtB_one_cc (j : Fin 3) : wtB 1 j (cc 1) = 1 :=
  wtB_of_mem_Fb 1 j (cc_mem_Fb 1 le_rfl)

theorem tabB_one_one :
    tabB 1 1 = eR 0 + eR 1 + eR 2 + eR 0 * eR 1 * eR 2 := by
  classical
  have : Fintype (W 1) := Fintype.ofFinite _
  rw [tabB, tabB_trSum_eq_sum, tabB_W1_univ]
  have h1 : (1 : W 1) ≠ cc 1 := (cc_ne_one 1 le_rfl).symm
  have h2 : cc 1 ≠ (1 : W 1) := cc_ne_one 1 le_rfl
  have h3 : cc 1 * cc 1 = (1 : W 1) := cc_sq 1 le_rfl
  simp only [Finset.sum_pair h1, wtB_one_one, wtB_one_cc, mul_one, one_mul, h3, ite_true,
    ite_false, h2]
  ring

theorem tabB_one_cc : tabB 1 (cc 1) = 1 + sigR := by
  classical
  have : Fintype (W 1) := Fintype.ofFinite _
  rw [tabB, tabB_trSum_eq_sum, tabB_W1_univ]
  have h1 : (1 : W 1) ≠ cc 1 := (cc_ne_one 1 le_rfl).symm
  have h3 : cc 1 * cc 1 = (1 : W 1) := cc_sq 1 le_rfl
  simp only [Finset.sum_pair h1, wtB_one_one, wtB_one_cc, mul_one, one_mul, h3, ite_true,
    ite_false, h1]
  unfold sigR
  ring

theorem tabB_two_one :
    tabB 2 1 = ((tauB 2 : ℕ) : R8) + ((tau2B 2 : ℕ) : R8) * sigR := by
  have h := tabB_succ_of_eq 1 le_rfl 1 1 diag_one.symm (one_mul 1)
    (fun d => by rw [mul_one, one_mul])
  rw [h, tabB_one_one]
  have h6 : (3 * (piB 1 * phiB 1) : ℕ) = 6 := by decide
  have h7 : tauB 2 = 6 := by decide
  have h8 : tau2B 2 = 2 := by decide
  rw [h6, h7, h8]
  unfold sigR
  push_cast
  linear_combination (1 + 2 * eR 1 * eR 2 + eR 1 ^ 2 * eR 2 ^ 2) * eR_mul_self 0 +
    (1 + 2 * eR 0 * eR 2) * eR_mul_self 1 + (1 + 2 * eR 0 * eR 1) * eR_mul_self 2

theorem tabB_two_cc :
    tabB 2 (cc 2) = ((upsB 2 : ℕ) : R8) + ((ups2B 2 : ℕ) : R8) * sigR := by
  have h := tabB_succ_of_eq 1 le_rfl (cc 1) (cc 2) (cc_succ 1 le_rfl) (cc_sq 1 le_rfl)
    (cc_central 1 le_rfl)
  rw [h, tabB_one_cc]
  have h6 : (3 * (piB 1 * phiB 1) : ℕ) = 6 := by decide
  have h7 : upsB 2 = 7 := by decide
  have h8 : ups2B 2 = 2 := by decide
  rw [h6, h7, h8]
  push_cast
  linear_combination sigR_mul_self

theorem tabB_one (a : ℕ) (ha : 2 ≤ a) :
    tabB a 1 = ((tauB a : ℕ) : R8) + ((tau2B a : ℕ) : R8) * sigR := by
  induction a, ha using Nat.le_induction with
  | base => exact tabB_two_one
  | succ a ha ih =>
    have h := tabB_succ_of_eq a (by omega) 1 1 diag_one.symm (one_mul 1)
      (fun d => by rw [mul_one, one_mul])
    rw [h, ih, tauB_succ a (by omega), tau2B_succ a ha]
    push_cast
    linear_combination ((tau2B a : ℕ) : R8) ^ 2 * sigR_mul_self

theorem tabB_cc (a : ℕ) (ha : 2 ≤ a) :
    tabB a (cc a) = ((upsB a : ℕ) : R8) + ((ups2B a : ℕ) : R8) * sigR := by
  induction a, ha using Nat.le_induction with
  | base => exact tabB_two_cc
  | succ a ha ih =>
    have h := tabB_succ_of_eq a (by omega) (cc a) (cc (a + 1)) (cc_succ a (by omega))
      (cc_sq a (by omega)) (cc_central a (by omega))
    rw [h, ih, upsB_succ a (by omega), ups2B_succ a ha]
    push_cast
    linear_combination ((ups2B a : ℕ) : R8) ^ 2 * sigR_mul_self

theorem card_Gb_eq (a : ℕ) (ha : 1 ≤ a) : Nat.card (Gb a) = psiB a := by
  induction a, ha using Nat.le_induction with
  | base =>
    rw [Gb_one, Nat.card_coe_set_eq, Set.ncard_singleton]
    rfl
  | succ a ha ih =>
    rw [card_Gb_succ a ha, ih, card_Fb_eq a ha, psiB_succ a ha]

end CFSG.OddStandard.AltStdSec.SylowSn
