module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8cMC
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8MCFacts

public section

namespace CFSG.ComponentClassification.HSFLit.KD8c

open Sec8 Subgroup

theorem inZ_zl {x : MC} (hx : inZ x = true) : x ∈ Zl := (inZ_iff x).mp hx

theorem inR1_of_inZ {x : MC} (hx : inZ x = true) : inR1 x = true := by
  rw [inZ_iff'] at hx
  simp only [Bool.and_eq_true] at hx
  exact hx.1

theorem cidx_eq_zero_of_inZ {x : MC} (hx : inZ x = true) : cidx x = 0 := by
  rw [inZ_iff'] at hx
  simp only [Bool.and_eq_true, beq_iff_eq] at hx
  exact hx.2

theorem inZ_of_cidx {x : MC} (hx : inR1 x = true) (h : cidx x = 0) : inZ x = true := by
  rw [inZ_iff', hx, h]
  rfl

theorem zpart_central (x : MC) {g : MC} (hg : inR1 g = true) : zpart x * g = g * zpart x :=
  Zl_central _ (inZ_zl (zpart_inZ x)) g hg

theorem eq_crep_mul {x : MC} (hx : inR1 x = true) : x = crep (cidx x) * zpart x :=
  (crep_zpart x hx).symm

theorem crep_fin (x : MC) : crep (cidx x) = crep (⟨cidx x, cidx_lt x⟩ : Fin 32) := rfl

theorem cidx_mul {x y : MC} (hx : inR1 x = true) (hy : inR1 y = true) :
    cidx (x * y) = cidx x ^^^ cidx y := by
  have h1 : x * y = crep (cidx x) * crep (cidx y) * (zpart x * zpart y) := by
    conv_lhs => rw [eq_crep_mul hx, eq_crep_mul hy]
    rw [mul_assoc, ← mul_assoc (zpart x), zpart_central x (crep_inR1 ⟨cidx y, cidx_lt y⟩)]
    group
  have hr : inR1 (crep (cidx x) * crep (cidx y)) = true :=
    inR1_mul _ _ (crep_inR1 ⟨cidx x, cidx_lt x⟩) (crep_inR1 ⟨cidx y, cidx_lt y⟩)
  rw [h1, ← mul_assoc, cidx_mul_Z _ (inR1_mul _ _ hr (inR1_of_inZ (zpart_inZ x))) _
    (inZ_zl (zpart_inZ y)), cidx_mul_Z _ hr _ (inZ_zl (zpart_inZ x)), crep_fin x, crep_fin y,
    cidx_crep_mul]

theorem inR1_one' : inR1 1 = true := by decide +kernel

theorem inR1_inv' : ∀ x : MC, inR1 x = true → inR1 x⁻¹ = true := by decide +kernel

theorem cidx_one : cidx 1 = 0 := by decide +kernel

theorem cidx_inv {x : MC} (hx : inR1 x = true) : cidx x⁻¹ = cidx x := by
  have h := cidx_mul hx (inR1_inv' x hx)
  rw [mul_inv_cancel, cidx_one] at h
  have h2 := congrArg (· ^^^ cidx x) h
  simp only [Nat.zero_xor, Nat.xor_comm (cidx x) (cidx x⁻¹), Nat.xor_assoc, Nat.xor_self,
    Nat.xor_zero] at h2
  exact h2.symm

theorem inE_one : ∀ i : Fin 8, inE i 1 = true := by decide +kernel

theorem inE_mul (i : Fin 8) (x : MC) (hx : inE i x = true) (y : MC) (hy : inE i y = true) :
    inE i (x * y) = true := by
  rw [inE_iff'] at hx hy ⊢
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] at hx hy ⊢
  refine ⟨inR1_mul _ _ hx.1 hy.1, ?_⟩
  rw [cidx_mul hx.1 hy.1]
  have hc : ∀ a b : ℕ, (a = 0 ∨ a ∈ Ereps i) → (b = 0 ∨ b ∈ Ereps i) →
      a ^^^ b = 0 ∨ a ^^^ b ∈ Ereps i := by
    have key : ∀ i : Fin 8, ∀ a ∈ (0 :: Ereps i), ∀ b ∈ (0 :: Ereps i),
        a ^^^ b ∈ (0 :: Ereps i) := by decide
    intro a b ha hb
    have := key i a (List.mem_cons.mpr ha) b (List.mem_cons.mpr hb)
    exact List.mem_cons.mp this
  exact hc _ _ hx.2 hy.2

theorem inE_inv (i : Fin 8) (x : MC) (hx : inE i x = true) : inE i x⁻¹ = true := by
  rw [inE_iff'] at hx ⊢
  simp only [Bool.and_eq_true] at hx ⊢
  exact ⟨inR1_inv' x hx.1, by rw [cidx_inv hx.1]; exact hx.2⟩

@[expose] def Eh (i : Fin 8) : Subgroup MC :=
  MC.ofPred (inE i) (inE_one i) (inE_mul i) (inE_inv i)

theorem mem_Eh {i : Fin 8} {x : MC} : x ∈ Eh i ↔ inE i x = true := Iff.rfl

@[expose] def R1h : Subgroup MC :=
  MC.ofPred inR1 inR1_one' (fun x hx y hy => inR1_mul x y hx hy) inR1_inv'

theorem mem_R1h {x : MC} : x ∈ R1h ↔ inR1 x = true := Iff.rfl

theorem inZ_one : inZ 1 = true := by decide +kernel

theorem inZ_mul (x : MC) (hx : inZ x = true) (y : MC) (hy : inZ y = true) :
    inZ (x * y) = true :=
  inZ_of_cidx (inR1_mul _ _ (inR1_of_inZ hx) (inR1_of_inZ hy)) (by
    rw [cidx_mul (inR1_of_inZ hx) (inR1_of_inZ hy), cidx_eq_zero_of_inZ hx,
      cidx_eq_zero_of_inZ hy]
    rfl)

theorem inZ_inv (x : MC) (hx : inZ x = true) : inZ x⁻¹ = true :=
  inZ_of_cidx (inR1_inv' x (inR1_of_inZ hx)) (by
    rw [cidx_inv (inR1_of_inZ hx), cidx_eq_zero_of_inZ hx])

@[expose] def Zh : Subgroup MC := MC.ofPred inZ inZ_one inZ_mul inZ_inv

theorem mem_Zh {x : MC} : x ∈ Zh ↔ inZ x = true := Iff.rfl

theorem card_Eh (i : Fin 8) : Nat.card (Eh i) = 16 := by
  rw [Eh, MC.card_ofPred]
  revert i
  decide +kernel

theorem card_R1h : Nat.card R1h = 128 := by
  rw [R1h, MC.card_ofPred]
  decide +kernel

theorem card_Zh : Nat.card Zh = 4 := by
  rw [Zh, MC.card_ofPred]
  decide +kernel

theorem Eh_le_R1h (i : Fin 8) : Eh i ≤ R1h := fun x hx => by
  rw [mem_Eh, inE_iff'] at hx
  simp only [Bool.and_eq_true] at hx
  exact hx.1

theorem Zh_le_Eh (i : Fin 8) : Zh ≤ Eh i := fun x hx => by
  rw [mem_Zh] at hx
  rw [mem_Eh, inE_iff', inR1_of_inZ hx, cidx_eq_zero_of_inZ hx]
  rfl

theorem crep_mul_crep {x y : MC} (hx : inR1 x = true) (hy : inR1 y = true) :
    x * y = crep (cidx x) * crep (cidx y) * (zpart x * zpart y) := by
  conv_lhs => rw [eq_crep_mul hx, eq_crep_mul hy]
  rw [mul_assoc, ← mul_assoc (zpart x), zpart_central x (crep_inR1 ⟨cidx y, cidx_lt y⟩)]
  group

theorem zpart_sq (x : MC) : zpart x * zpart x = 1 := Zl_sq _ (inZ_zl (zpart_inZ x))

theorem crep_sq_of {x : MC} (hx : inR1 x = true) :
    crep (cidx x) * crep (cidx x) = x * x := by
  rw [crep_mul_crep hx hx, zpart_sq, mul_one]

theorem crep_comm_iff {x y : MC} (hx : inR1 x = true) (hy : inR1 y = true) :
    crep (cidx x) * crep (cidx y) = crep (cidx y) * crep (cidx x) ↔ x * y = y * x := by
  rw [crep_mul_crep hx hy, crep_mul_crep hy hx,
    show zpart y * zpart x = zpart x * zpart y from
      (zpart_central y (inR1_of_inZ (zpart_inZ x)))]
  exact ⟨fun h => by rw [h], fun h => mul_right_cancel h⟩

theorem inE_of_cidx {i : Fin 8} {x : MC} (hx : inR1 x = true)
    (h : cidx x = 0 ∨ cidx x ∈ Ereps i) : inE i x = true := by
  rw [inE_iff', hx]
  simp only [Bool.true_and, Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem]
  exact h

theorem cidx_of_inE {i : Fin 8} {x : MC} (h : inE i x = true) :
    inR1 x = true ∧ (cidx x = 0 ∨ cidx x ∈ Ereps i) := by
  rw [inE_iff'] at h
  simpa only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] using h

@[expose] def inW (c : ℕ) (x : MC) : Bool := inR1 x && (cidx x == 0 || cidx x == c)

theorem inW_mul (c : ℕ) (x : MC) (hx : inW c x = true) (y : MC) (hy : inW c y = true) :
    inW c (x * y) = true := by
  simp only [inW, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hx hy ⊢
  refine ⟨inR1_mul _ _ hx.1 hy.1, ?_⟩
  rw [cidx_mul hx.1 hy.1]
  rcases hx.2 with h1 | h1 <;> rcases hy.2 with h2 | h2 <;> rw [h1, h2] <;> simp

theorem inW_inv (c : ℕ) (x : MC) (hx : inW c x = true) : inW c x⁻¹ = true := by
  simp only [inW, Bool.and_eq_true] at hx ⊢
  exact ⟨inR1_inv' x hx.1, by rw [cidx_inv hx.1]; exact hx.2⟩

theorem inW_one (c : ℕ) : inW c 1 = true := by
  simp only [inW, inR1_one', cidx_one, Bool.true_and, beq_self_eq_true, Bool.true_or]

theorem card_W : ∀ c : Fin 32, c.val ≠ 0 →
    (Finset.univ.filter fun x : MC => inW c x = true).card = 8 := by
  decide +kernel

theorem eq_Eh_of {H : Subgroup MC} (hH : H ≤ R1h)
    (hab : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x) (hsq : ∀ x ∈ H, x * x = 1)
    (hcard : Nat.card H = 16) : ∃ i : Fin 8, H = Eh i := by
  have hZH : ¬ (H ≤ Zh) := fun hle => by
    have := Subgroup.card_le_of_le hle
    rw [hcard, card_Zh] at this
    omega
  obtain ⟨a, haH, haZ⟩ := IsConcreteLE.not_le_iff_exists.mp hZH
  have haR := mem_R1h.mp (hH haH)
  have hca : cidx a ≠ 0 := fun h => haZ (mem_Zh.mpr (inZ_of_cidx haR h))
  set W : Subgroup MC := MC.ofPred (inW (cidx a)) (inW_one _) (inW_mul _) (inW_inv _) with hW
  have hWH : ¬ (H ≤ W) := fun hle => by
    have := Subgroup.card_le_of_le hle
    rw [hcard, hW, MC.card_ofPred, card_W ⟨cidx a, cidx_lt a⟩ hca] at this
    omega
  obtain ⟨b, hbH, hbW⟩ := IsConcreteLE.not_le_iff_exists.mp hWH
  have hbR := mem_R1h.mp (hH hbH)
  have hb' : cidx b ≠ 0 ∧ cidx b ≠ cidx a := by
    constructor <;> intro h <;> apply hbW <;>
      show inW (cidx a) b = true <;> simp [inW, hbR, h]
  have hα := crep_sq_of haR
  have hβ := crep_sq_of hbR
  rw [hsq a haH] at hα
  rw [hsq b hbH] at hβ
  have hαβ := (crep_comm_iff haR hbR).mpr (hab a haH b hbH)
  obtain ⟨i, hai, hbi⟩ := pair_crep ⟨cidx a, cidx_lt a⟩ ⟨cidx b, cidx_lt b⟩ hca hb'.1
    (fun h => hb'.2 (congrArg Fin.val h).symm) hα hβ hαβ
  refine ⟨i, Subgroup.eq_of_le_of_card_ge (fun c hc => mem_Eh.mpr ?_)
    (by simp [card_Eh, hcard])⟩
  have hcR := mem_R1h.mp (hH hc)
  have h1 := (crep_comm_iff hcR haR).mpr (hab c hc a haH)
  have h2 := (crep_comm_iff hcR hbR).mpr (hab c hc b hbH)
  exact inE_of_cidx hcR (cent_crep i _ hai _ hbi (fun h => hb'.2 h.symm)
    ⟨cidx c, cidx_lt c⟩ h1 h2)

theorem R1h_conj_Eh {i : Fin 8} {g e : MC} (hg : g ∈ R1h) (he : e ∈ Eh i) :
    g * e * g⁻¹ ∈ Eh i := by
  have hgR := mem_R1h.mp hg
  obtain ⟨heR, hc⟩ := cidx_of_inE (mem_Eh.mp he)
  have h1 := inR1_mul _ _ hgR heR
  refine mem_Eh.mpr (inE_of_cidx (inR1_mul _ _ h1 (inR1_inv' g hgR)) ?_)
  rw [cidx_mul h1 (inR1_inv' g hgR), cidx_mul hgR heR, cidx_inv hgR, Nat.xor_comm (cidx g),
    Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  exact hc

@[expose] def sig21 : Fin 8 → Fin 8 := ![0, 4, 5, 3, 1, 2, 6, 7]

theorem w₂_conj_Eh : ∀ i : Fin 8, ∀ e : MC, inE i e = true →
    inE (sig21 i) (MC.w₂ * e * MC.w₂⁻¹) = true := by
  decide +kernel

@[expose] def interCard (i j : Fin 8) : ℕ :=
  if i = j then 16 else if ∃ c ∈ Ereps i, c ∈ Ereps j then 8 else 4

theorem card_inf_aux : ∀ i j : Fin 8,
    (Finset.univ.filter fun x : MC => inE i x = true ∧ inE j x = true).card = interCard i j := by
  decide +kernel

theorem card_inf (i j : Fin 8) : Nat.card (Eh i ⊓ Eh j : Subgroup MC) = interCard i j := by
  classical
  rw [← card_inf_aux i j,
    show Nat.card (Eh i ⊓ Eh j : Subgroup MC) =
      Nat.card {x : MC // inE i x = true ∧ inE j x = true} from rfl,
    Nat.card_eq_fintype_card, Fintype.card_subtype]

end CFSG.ComponentClassification.HSFLit.KD8c
