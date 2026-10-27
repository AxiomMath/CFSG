module

public import CFSG.GH74.Generic.BProg.B2.GenLocL4ThreeDb
public import CFSG.GH74.Generic.BProg.B2.GenLocBasic
public import CFSG.GH74.Generic.BProg.B2.GenLocBasicExc
public import CFSG.GH74.Generic.BProg.B2.GenLocBasicQuot

public section

open CFSG CFSG.GH74 Subgroup Matrix
open scoped MatrixGroups

namespace CFSG.GH74.Generic.BProg.B2

local notation "K3" => ZMod 3

local notation "Mat" => Matrix (Fin 4) (Fin 4) K3

namespace GenLocL4ThreeDbLoc

open GenLocL4Out GenLocL4ThreeDb
open CFSG.ComponentClassification.CatalogueBHigherLinearAction

section Counting

variable {A : Type} [Group A]

theorem card_four_of_distinct [DecidableEq A] {t s : A} (ht1 : t ≠ 1) (hs1 : s ≠ 1) (hts : t ≠ s)
    (hs2 : s * s = 1) : ({1, t, s, t * s} : Finset A).card = 4 := by
  have hab1 : t * s ≠ 1 := by
    intro h
    apply hts
    calc t = t * (s * s) := by rw [hs2, mul_one]
      _ = (t * s) * s := by rw [mul_assoc]
      _ = s := by rw [h, one_mul]
  have h1 : (1 : A) ∉ ({t, s, t * s} : Finset A) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => ht1 h.symm, fun h => hs1 h.symm, hab1.symm⟩
  have h2 : t ∉ ({s, t * s} : Finset A) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨hts, fun h => hs1 ?_⟩
    have : t * s = t * 1 := by rw [mul_one]; exact h.symm
    exact mul_left_cancel this
  have h3 : s ∉ ({t * s} : Finset A) := by
    simp only [Finset.mem_singleton]
    intro h
    apply ht1
    have : t * s = 1 * s := by rw [one_mul]; exact h.symm
    exact mul_right_cancel this
  rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2, Finset.card_insert_of_notMem h3,
    Finset.card_singleton]

theorem inner_cases [Finite A] (hA : CFSG.IsElementaryAbelian 2 A) (hcard : Nat.card A = 8) (I : Subgroup A)
    {t s u : A} (htI : t ∈ I) (hsI : s ∈ I) (hu : u ∉ I) (ht1 : t ≠ 1) (hs1 : s ≠ 1) (hts : t ≠ s) :
    I.index = 2 ∧ ∀ a ∈ I, a = 1 ∨ a = t ∨ a = s ∨ a = t * s := by
  classical
  have hs2 : s * s = 1 := WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA s
  have hproper : Nat.card I ≤ 4 := by
    have hdvd : Nat.card I ∣ 8 := hcard ▸ Subgroup.card_subgroup_dvd_card I
    have hne : Nat.card I ≠ 8 := fun h => hu (by
      have : I = ⊤ := (Subgroup.card_eq_iff_eq_top I).1 (h.trans hcard.symm)
      rw [this]; exact Subgroup.mem_top u)
    have hle : Nat.card I ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
    generalize Nat.card I = n at hdvd hne hle ⊢
    interval_cases n <;> simp_all
  set S : Finset A := {1, t, s, t * s} with hSdef
  have hS : S.card = 4 := card_four_of_distinct ht1 hs1 hts hs2
  have hSI : (S : Set A) ⊆ (I : Set A) := by
    intro x hx
    simp only [hSdef, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact I.one_mem
    · exact htI
    · exact hsI
    · exact I.mul_mem htI hsI
  have hcardI : 4 ≤ Nat.card I := by
    calc 4 = S.card := hS.symm
      _ = (S : Set A).ncard := (Set.ncard_coe_finset S).symm
      _ ≤ (I : Set A).ncard := Set.ncard_le_ncard hSI (Set.toFinite _)
      _ = Nat.card I := (Nat.card_coe_set_eq _).symm
  have hI4 : Nat.card I = 4 := le_antisymm hproper hcardI
  refine ⟨?_, ?_⟩
  · have := Subgroup.card_mul_index I
    rw [hI4, hcard] at this
    omega
  · intro a haI
    by_contra hne
    push Not at hne
    obtain ⟨h1, h2, h3, h4⟩ := hne
    have haS : a ∉ S := by simp [hSdef, h1, h2, h3, h4]
    have h5 : (insert a S).card = 5 := by rw [Finset.card_insert_of_notMem haS, hS]
    have hsub : ((insert a S : Finset A) : Set A) ⊆ (I : Set A) := by
      intro x hx
      rw [Finset.coe_insert] at hx
      rcases hx with rfl | hx
      · exact haI
      · exact hSI hx
    have : 5 ≤ Nat.card I := by
      calc 5 = (insert a S).card := h5.symm
        _ = ((insert a S : Finset A) : Set A).ncard := (Set.ncard_coe_finset _).symm
        _ ≤ (I : Set A).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
        _ = Nat.card I := (Nat.card_coe_set_eq _).symm
    omega

theorem outer_cases (I : Subgroup A) (hindex : I.index = 2) {t s u : A} (hu : u ∉ I) (hu2 : u * u = 1)
    (hcases : ∀ a ∈ I, a = 1 ∨ a = t ∨ a = s ∨ a = t * s) :
    ∀ w, w ∉ I → w = u ∨ w = t * u ∨ w = s * u ∨ w = t * s * u := by
  intro w hw
  have hwu : w * u ∈ I := (Subgroup.mul_mem_iff_of_index_two hindex).2 (by simp [hw, hu])
  have hw' : w = (w * u) * u := by rw [mul_assoc, hu2, mul_one]
  rcases hcases _ hwu with h | h | h | h
  · left; rw [hw', h, one_mul]
  · right; left; rw [hw', h]
  · right; right; left; rw [hw', h]
  · right; right; right; rw [hw', h]

theorem mul_mem_of_not_mem (I : Subgroup A) (hindex : I.index = 2) {a b : A} (ha : a ∉ I) (hb : b ∉ I) :
    a * b ∈ I :=
  (Subgroup.mul_mem_iff_of_index_two hindex).2 (by simp [ha, hb])

end Counting

section Translate

theorem fix_iff_comm {t : MulAut SL(4, K3)} {G : GL (Fin 4) K3} (ht : InnerLift t G) (x : SL(4, K3)) :
    t x = x ↔ (x : Mat) * G = G * (x : Mat) := by
  refine ⟨fun h => ?_, innerLift_fix ht x⟩
  have e : ((t x : SL(4, K3)) : Mat) = (x : Mat) := congrArg Subtype.val h
  rw [ht x] at e
  calc (x : Mat) * G = ((G : Mat) * x * ((G⁻¹ : GL (Fin 4) K3) : Mat)) * G := by rw [e]
    _ = G * x := by rw [Matrix.mul_assoc, coe_inv_mul G, Matrix.mul_one]

theorem fix_iff_form {w : MulAut SL(4, K3)} {N : GL (Fin 4) K3} (hw : GraphEq w (N : Mat)) (x : SL(4, K3)) :
    w x = x ↔ (x : Mat) * N * (x : Mat)ᵀ = N := by
  refine ⟨fun h => ?_, graphEq_fix (coe_mul_inv N) hw x⟩
  have e := hw x
  rw [h] at e
  have hxx : ((x⁻¹ : SL(4, K3)) : Mat)ᵀ * (x : Mat)ᵀ = 1 := by
    rw [← Matrix.transpose_mul]
    have : (x : Mat) * ((x⁻¹ : SL(4, K3)) : Mat) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel]; rfl
    rw [this, Matrix.transpose_one]
  calc (x : Mat) * N * (x : Mat)ᵀ = ((N : Mat) * ((x⁻¹ : SL(4, K3)) : Mat)ᵀ) * (x : Mat)ᵀ := by rw [e]
    _ = N := by rw [Matrix.mul_assoc, hxx, Matrix.mul_one]

theorem conj_commute_iff' (P : GL (Fin 4) K3) (z : SL(4, K3)) (M : Mat) :
    (((slConjugation 4 K3 P z : SL(4, K3)) : Mat) * M = M * ((slConjugation 4 K3 P z : SL(4, K3)) : Mat)) ↔
    ((z : Mat) * (((P⁻¹ : GL (Fin 4) K3) : Mat) * M * (P : Mat)) =
      (((P⁻¹ : GL (Fin 4) K3) : Mat) * M * (P : Mat)) * (z : Mat)) :=
  conj_commute_iff P z M

theorem conj_form_iff' (P : GL (Fin 4) K3) (z : SL(4, K3)) (N : Mat) :
    (((slConjugation 4 K3 P z : SL(4, K3)) : Mat) * N * ((slConjugation 4 K3 P z : SL(4, K3)) : Mat)ᵀ = N) ↔
    ((z : Mat) * (((P⁻¹ : GL (Fin 4) K3) : Mat) * N * ((P⁻¹ : GL (Fin 4) K3) : Mat)ᵀ) * (z : Mat)ᵀ =
      ((P⁻¹ : GL (Fin 4) K3) : Mat) * N * ((P⁻¹ : GL (Fin 4) K3) : Mat)ᵀ) :=
  conj_form_iff P z N

theorem inner_iff {A : Type} [Group A] (α : A →* MulAut SL(4, K3)) {i : A} {G : GL (Fin 4) K3}
    (hi : InnerLift (α i) G) (P : GL (Fin 4) K3) {c : K3} (hc : c ≠ 0) {Δ : Mat}
    (hΔ : ((P⁻¹ : GL (Fin 4) K3) : Mat) * G * (P : Mat) = c • Δ) (z : SL(4, K3)) :
    α i (slConjugation 4 K3 P z) = slConjugation 4 K3 P z ↔ (z : Mat) * Δ = Δ * (z : Mat) := by
  rw [fix_iff_comm hi, conj_commute_iff', hΔ]
  exact ⟨fun h => comm_smul_cancel hc h, fun h => comm_smul_of_comm c h⟩

theorem outer_iff {w : MulAut SL(4, K3)} {N : GL (Fin 4) K3} (hw : GraphEq w (N : Mat)) (P : GL (Fin 4) K3)
    {c : K3} (hc : c ≠ 0) {M : Mat}
    (hM : ((P⁻¹ : GL (Fin 4) K3) : Mat) * N * ((P⁻¹ : GL (Fin 4) K3) : Mat)ᵀ = c • M) (z : SL(4, K3)) :
    w (slConjugation 4 K3 P z) = slConjugation 4 K3 P z ↔ (z : Mat) * M * (z : Mat)ᵀ = M := by
  rw [fix_iff_form hw, conj_form_iff', hM]
  exact ⟨fun h => form_smul_cancel hc h, fun h => form_smul_of_form c h⟩

end Translate

theorem Gu_eq_diagonal : (Gu : Mat) = Matrix.diagonal ![1, -1, -1, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Gu]

section FrameSec

variable {A : Type} [Group A]

structure Frame (α : A →* MulAut SL(4, K3)) (t s u : A) where
  P : GL (Fin 4) K3
  d : Fin 4 → K3
  B : GL (Fin 4) K3
  Gt' : GL (Fin 4) K3
  Gs' : GL (Fin 4) K3
  ct : K3
  cs : K3
  hd : ∀ i, d i ≠ 0
  hct : ct ≠ 0
  hcs : cs ≠ 0
  hB : GraphForm (α u) B
  hBP : (B : Mat) = (P : Mat) * Matrix.diagonal d * (P : Mat)ᵀ
  hGt : InnerLift (α t) Gt'
  hGs : InnerLift (α s) Gs'
  hPt : ((P⁻¹ : GL (Fin 4) K3) : Mat) * Gt' * P = ct • (Gt : Mat)
  hPs : ((P⁻¹ : GL (Fin 4) K3) : Mat) * Gs' * P = cs • (Gs : Mat)

namespace Frame

variable {α : A →* MulAut SL(4, K3)} {t s u : A} (F : Frame α t s u)

theorem hPiB : ((F.P⁻¹ : GL (Fin 4) K3) : Mat) * F.B * ((F.P⁻¹ : GL (Fin 4) K3) : Mat)ᵀ = Matrix.diagonal F.d := by
  have hPiP : ((F.P⁻¹ : GL (Fin 4) K3) : Mat) * (F.P : Mat) = 1 := coe_inv_mul F.P
  rw [F.hBP]
  calc ((F.P⁻¹ : GL (Fin 4) K3) : Mat) * ((F.P : Mat) * Matrix.diagonal F.d * (F.P : Mat)ᵀ) *
        ((F.P⁻¹ : GL (Fin 4) K3) : Mat)ᵀ
      = (((F.P⁻¹ : GL (Fin 4) K3) : Mat) * (F.P : Mat)) * Matrix.diagonal F.d *
        ((F.P : Mat)ᵀ * ((F.P⁻¹ : GL (Fin 4) K3) : Mat)ᵀ) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hPiP, ← Matrix.transpose_mul, hPiP, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]

theorem hPiGB {G : GL (Fin 4) K3} {c : K3} {Δ : Mat}
    (hΔ : ((F.P⁻¹ : GL (Fin 4) K3) : Mat) * G * (F.P : Mat) = c • Δ) :
    ((F.P⁻¹ : GL (Fin 4) K3) : Mat) * ((G * F.B : GL (Fin 4) K3) : Mat) * ((F.P⁻¹ : GL (Fin 4) K3) : Mat)ᵀ =
      c • (Δ * Matrix.diagonal F.d) := by
  have hPP : (F.P : Mat) * ((F.P⁻¹ : GL (Fin 4) K3) : Mat) = 1 := coe_mul_inv F.P
  have e : ((F.P⁻¹ : GL (Fin 4) K3) : Mat) * ((G * F.B : GL (Fin 4) K3) : Mat) *
      ((F.P⁻¹ : GL (Fin 4) K3) : Mat)ᵀ =
      (((F.P⁻¹ : GL (Fin 4) K3) : Mat) * G * (F.P : Mat)) *
        (((F.P⁻¹ : GL (Fin 4) K3) : Mat) * F.B * ((F.P⁻¹ : GL (Fin 4) K3) : Mat)ᵀ) := by
    calc ((F.P⁻¹ : GL (Fin 4) K3) : Mat) * ((G * F.B : GL (Fin 4) K3) : Mat) * ((F.P⁻¹ : GL (Fin 4) K3) : Mat)ᵀ
        = ((F.P⁻¹ : GL (Fin 4) K3) : Mat) * G * ((F.P : Mat) * ((F.P⁻¹ : GL (Fin 4) K3) : Mat)) * F.B *
          ((F.P⁻¹ : GL (Fin 4) K3) : Mat)ᵀ := by
          rw [hPP, Matrix.mul_one, Units.val_mul]; simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [e, hΔ, F.hPiB, Matrix.smul_mul]

theorem hPts : ((F.P⁻¹ : GL (Fin 4) K3) : Mat) * ((F.Gt' * F.Gs' : GL (Fin 4) K3) : Mat) * (F.P : Mat) =
    (F.ct * F.cs) • (Gu : Mat) := by
  have hPP : (F.P : Mat) * ((F.P⁻¹ : GL (Fin 4) K3) : Mat) = 1 := coe_mul_inv F.P
  have e : ((F.P⁻¹ : GL (Fin 4) K3) : Mat) * ((F.Gt' * F.Gs' : GL (Fin 4) K3) : Mat) * (F.P : Mat) =
      (((F.P⁻¹ : GL (Fin 4) K3) : Mat) * F.Gt' * (F.P : Mat)) *
        (((F.P⁻¹ : GL (Fin 4) K3) : Mat) * F.Gs' * (F.P : Mat)) := by
    calc ((F.P⁻¹ : GL (Fin 4) K3) : Mat) * ((F.Gt' * F.Gs' : GL (Fin 4) K3) : Mat) * (F.P : Mat)
        = ((F.P⁻¹ : GL (Fin 4) K3) : Mat) * F.Gt' * ((F.P : Mat) * ((F.P⁻¹ : GL (Fin 4) K3) : Mat)) * F.Gs' *
          (F.P : Mat) := by
          rw [hPP, Matrix.mul_one, Units.val_mul]; simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [e, F.hPt, F.hPs, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Gt_mul_Gs]

theorem innerLift_ts : InnerLift (α (t * s)) (F.Gt' * F.Gs') := by
  rw [map_mul]; exact innerLift_mul F.hGt F.hGs

theorem fix_t (z : SL(4, K3)) :
    α t (slConjugation 4 K3 F.P z) = slConjugation 4 K3 F.P z ↔ (z : Mat) * Gt = Gt * (z : Mat) :=
  inner_iff α F.hGt F.P F.hct F.hPt z

theorem fix_s (z : SL(4, K3)) :
    α s (slConjugation 4 K3 F.P z) = slConjugation 4 K3 F.P z ↔ (z : Mat) * Gs = Gs * (z : Mat) :=
  inner_iff α F.hGs F.P F.hcs F.hPs z

theorem fix_ts (z : SL(4, K3)) :
    α (t * s) (slConjugation 4 K3 F.P z) = slConjugation 4 K3 F.P z ↔ (z : Mat) * Gu = Gu * (z : Mat) :=
  inner_iff α F.innerLift_ts F.P (mul_ne_zero F.hct F.hcs) F.hPts z

theorem fix_u (z : SL(4, K3)) :
    α u (slConjugation 4 K3 F.P z) = slConjugation 4 K3 F.P z ↔
      (z : Mat) * Matrix.diagonal F.d * (z : Mat)ᵀ = Matrix.diagonal F.d :=
  outer_iff F.hB.graphEq F.P one_ne_zero (by rw [F.hPiB, one_smul]) z

theorem fix_tu (z : SL(4, K3)) :
    α (t * u) (slConjugation 4 K3 F.P z) = slConjugation 4 K3 F.P z ↔
      (z : Mat) * (Gt * Matrix.diagonal F.d) * (z : Mat)ᵀ = Gt * Matrix.diagonal F.d :=
  outer_iff (N := F.Gt' * F.B) (by rw [map_mul]; exact graphEq_inner_mul F.hB F.hGt) F.P F.hct (F.hPiGB F.hPt) z

theorem fix_su (z : SL(4, K3)) :
    α (s * u) (slConjugation 4 K3 F.P z) = slConjugation 4 K3 F.P z ↔
      (z : Mat) * (Gs * Matrix.diagonal F.d) * (z : Mat)ᵀ = Gs * Matrix.diagonal F.d :=
  outer_iff (N := F.Gs' * F.B) (by rw [map_mul]; exact graphEq_inner_mul F.hB F.hGs) F.P F.hcs (F.hPiGB F.hPs) z

theorem fix_tsu (z : SL(4, K3)) :
    α (t * s * u) (slConjugation 4 K3 F.P z) = slConjugation 4 K3 F.P z ↔
      (z : Mat) * (Gu * Matrix.diagonal F.d) * (z : Mat)ᵀ = Gu * Matrix.diagonal F.d :=
  outer_iff (N := (F.Gt' * F.Gs') * F.B) (by rw [map_mul]; exact graphEq_inner_mul F.hB F.innerLift_ts) F.P
    (mul_ne_zero F.hct F.hcs) (F.hPiGB F.hPts) z

end Frame

end FrameSec

section PairSec

variable {A : Type} [Group A] {α : A →* MulAut SL(4, K3)} {t s u : A}

theorem comm_mul' {z X Y : Mat} (hX : z * X = X * z) (hY : z * Y = Y * z) : z * (X * Y) = (X * Y) * z := by
  rw [← Matrix.mul_assoc, hX, Matrix.mul_assoc, hY, Matrix.mul_assoc]

theorem comm_of_isDiag {z : Mat} (hz : z.IsDiag) (v : Fin 4 → K3) :
    z * Matrix.diagonal v = Matrix.diagonal v * z := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hij : i = j
  · subst hij; ring
  · rw [hz hij]; simp

theorem inner_pair_pow8 (F : Frame α t s u) (z : SL(4, K3)) {a b : A} (ha : a = t ∨ a = s ∨ a = t * s)
    (hb : b = t ∨ b = s ∨ b = t * s) (hab : a ≠ b)
    (hza : α a (slConjugation 4 K3 F.P z) = slConjugation 4 K3 F.P z)
    (hzb : α b (slConjugation 4 K3 F.P z) = slConjugation 4 K3 F.P z) : (z : Mat) ^ 8 = 1 := by
  have hdet : (z : Mat).det = 1 := z.2
  have ea : (a = t ∧ (z : Mat) * Gt = Gt * (z : Mat)) ∨ (a = s ∧ (z : Mat) * Gs = Gs * (z : Mat)) ∨
      (a = t * s ∧ (z : Mat) * Gu = Gu * (z : Mat)) := by
    rcases ha with h | h | h
    · rw [h] at hza; exact Or.inl ⟨h, (F.fix_t z).1 hza⟩
    · rw [h] at hza; exact Or.inr (Or.inl ⟨h, (F.fix_s z).1 hza⟩)
    · rw [h] at hza; exact Or.inr (Or.inr ⟨h, (F.fix_ts z).1 hza⟩)
  have eb : (b = t ∧ (z : Mat) * Gt = Gt * (z : Mat)) ∨ (b = s ∧ (z : Mat) * Gs = Gs * (z : Mat)) ∨
      (b = t * s ∧ (z : Mat) * Gu = Gu * (z : Mat)) := by
    rcases hb with h | h | h
    · rw [h] at hzb; exact Or.inl ⟨h, (F.fix_t z).1 hzb⟩
    · rw [h] at hzb; exact Or.inr (Or.inl ⟨h, (F.fix_s z).1 hzb⟩)
    · rw [h] at hzb; exact Or.inr (Or.inr ⟨h, (F.fix_ts z).1 hzb⟩)
  have fromTU : (z : Mat) * Gt = Gt * (z : Mat) → (z : Mat) * Gu = Gu * (z : Mat) → (z : Mat) ^ 8 = 1 := fun hT hU =>
    pow8_diag z hdet hT (by rw [← Gt_mul_Gu]; exact comm_mul' hT hU)
  have fromSU : (z : Mat) * Gs = Gs * (z : Mat) → (z : Mat) * Gu = Gu * (z : Mat) → (z : Mat) ^ 8 = 1 := fun hS hU =>
    pow8_diag z hdet (by rw [← Gs_mul_Gu]; exact comm_mul' hS hU) hS
  rcases ea with ⟨ha', hA⟩ | ⟨ha', hA⟩ | ⟨ha', hA⟩ <;> rcases eb with ⟨hb', hB⟩ | ⟨hb', hB⟩ | ⟨hb', hB⟩
  · exact absurd (ha'.trans hb'.symm) hab
  · exact pow8_diag z hdet hA hB
  · exact fromTU hA hB
  · exact pow8_diag z hdet hB hA
  · exact absurd (ha'.trans hb'.symm) hab
  · exact fromSU hA hB
  · exact fromTU hB hA
  · exact fromSU hB hA
  · exact absurd (ha'.trans hb'.symm) hab

theorem mixed_pow8 (F : Frame α t s u)
    (c1 : ∀ a, IsInnerDiag4 (α a) → a = 1 ∨ a = t ∨ a = s ∨ a = t * s)
    (c2 : ∀ w, ¬ IsInnerDiag4 (α w) → ∃ m : Fin 4 → K3, (∀ i, m i ≠ 0) ∧ ∀ z : SL(4, K3),
      α w (slConjugation 4 K3 F.P z) = slConjugation 4 K3 F.P z →
        (z : Mat) * Matrix.diagonal m * (z : Mat)ᵀ = Matrix.diagonal m)
    {i w : A} (hi : IsInnerDiag4 (α i)) (hi1 : i ≠ 1) (hw : ¬ IsInnerDiag4 (α w)) (z : SL(4, K3))
    (hzi : α i (slConjugation 4 K3 F.P z) = slConjugation 4 K3 F.P z)
    (hzw : α w (slConjugation 4 K3 F.P z) = slConjugation 4 K3 F.P z) : (z : Mat) ^ 8 = 1 := by
  obtain ⟨m, hm, hform⟩ := c2 w hw
  have hf := hform z hzw
  rcases c1 i hi with h | h | h | h
  · exact absurd h hi1
  · rw [h] at hzi; exact pow8_block01 z m hm ((F.fix_t z).1 hzi) hf
  · rw [h] at hzi; exact pow8_block02 z m hm ((F.fix_s z).1 hzi) hf
  · rw [h] at hzi; exact pow8_block03 z m hm ((F.fix_ts z).1 hzi) hf

theorem outer_form (F : Frame α t s u)
    (c2 : ∀ w, ¬ IsInnerDiag4 (α w) → w = u ∨ w = t * u ∨ w = s * u ∨ w = t * s * u) :
    ∀ w, ¬ IsInnerDiag4 (α w) → ∃ m : Fin 4 → K3, (∀ i, m i ≠ 0) ∧ ∀ z : SL(4, K3),
      α w (slConjugation 4 K3 F.P z) = slConjugation 4 K3 F.P z →
        (z : Mat) * Matrix.diagonal m * (z : Mat)ᵀ = Matrix.diagonal m := by
  intro w hw
  have hnz : ∀ δ : Fin 4 → K3, (∀ i, δ i ≠ 0) → ∀ i, δ i * F.d i ≠ 0 := fun δ hδ i =>
    mul_ne_zero (hδ i) (F.hd i)
  rcases c2 w hw with h | h | h | h
  · exact ⟨F.d, F.hd, fun z hz => (F.fix_u z).1 (by rw [h] at hz; exact hz)⟩
  · refine ⟨fun i => ![1, 1, -1, -1] i * F.d i, hnz _ (by decide), fun z hz => ?_⟩
    have := (F.fix_tu z).1 (by rw [h] at hz; exact hz)
    rwa [Gt_eq_diagonal, Matrix.diagonal_mul_diagonal] at this
  · refine ⟨fun i => ![1, -1, 1, -1] i * F.d i, hnz _ (by decide), fun z hz => ?_⟩
    have := (F.fix_su z).1 (by rw [h] at hz; exact hz)
    rwa [Gs_eq_diagonal, Matrix.diagonal_mul_diagonal] at this
  · refine ⟨fun i => ![1, -1, -1, 1] i * F.d i, hnz _ (by decide), fun z hz => ?_⟩
    have := (F.fix_tsu z).1 (by rw [h] at hz; exact hz)
    rwa [Gu_eq_diagonal, Matrix.diagonal_mul_diagonal] at this

theorem pair_pow8 (F : Frame α t s u)
    (c1 : ∀ a, IsInnerDiag4 (α a) → a = 1 ∨ a = t ∨ a = s ∨ a = t * s)
    (c2 : ∀ w, ¬ IsInnerDiag4 (α w) → w = u ∨ w = t * u ∨ w = s * u ∨ w = t * s * u)
    (c3 : ∀ a b, ¬ IsInnerDiag4 (α a) → ¬ IsInnerDiag4 (α b) → IsInnerDiag4 (α (a * b)))
    (hA2 : ∀ a : A, a * a = 1) (z : SL(4, K3)) {a b : A} (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b)
    (hza : α a (slConjugation 4 K3 F.P z) = slConjugation 4 K3 F.P z)
    (hzb : α b (slConjugation 4 K3 F.P z) = slConjugation 4 K3 F.P z) : (z : Mat) ^ 8 = 1 := by
  have c2' := outer_form F c2
  by_cases hai : IsInnerDiag4 (α a)
  · by_cases hbi : IsInnerDiag4 (α b)
    · exact inner_pair_pow8 F z ((c1 a hai).resolve_left ha1) ((c1 b hbi).resolve_left hb1) hab hza hzb
    · exact mixed_pow8 F c1 c2' hai ha1 hbi z hza hzb
  · by_cases hbi : IsInnerDiag4 (α b)
    · exact mixed_pow8 F c1 c2' hbi hb1 hai z hzb hza
    · have hab1 : a * b ≠ 1 := fun h => hab (by
        calc a = a * (b * b) := by rw [hA2 b, mul_one]
          _ = (a * b) * b := by rw [mul_assoc]
          _ = b := by rw [h, one_mul])
      have hzab : α (a * b) (slConjugation 4 K3 F.P z) = slConjugation 4 K3 F.P z := by
        rw [map_mul, MulAut.mul_apply, hzb, hza]
      exact mixed_pow8 F c1 c2' (c3 a b hai hbi) hab1 hai z hzab hza

end PairSec

section LocSec

variable {A : Type} [Group A] {α : A →* MulAut SL(4, K3)} {t s u : A}

theorem locE1_of_pair [Finite A] (hA : CFSG.IsElementaryAbelian 2 A) (hcard : Nat.card A = 8)
    (hpair : ∀ a b : A, a ≠ 1 → b ≠ 1 → a ≠ b → ∀ x : SL(4, K3), α a x = x → α b x = x → x ^ 8 = 1) :
    LocE1 α := by
  intro E hE
  refine noOddNormal_of_isPGroup ?_
  have hEi : E.index ≤ 2 := (GenLocBasic.adm_iff_index hA E).1 hE
  have hE2 : 2 < Nat.card E := by
    have h1 := Subgroup.card_mul_index E
    have hpos : 0 < E.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    rw [hcard] at h1
    interval_cases h : E.index <;> omega
  obtain ⟨a, b, haE, hbE, ha1, hb1, hab⟩ := exists_two_ne_one E hE2
  intro x
  refine ⟨3, ?_⟩
  have hx := (GenLocBasic.mem_fixedIn_map α E x).1 x.2
  have h8 := hpair a b ha1 hb1 hab x (hx a haE) (hx b hbE)
  apply Subtype.ext
  simpa using h8

theorem locE2_of_frame [Finite A] (hA : CFSG.IsElementaryAbelian 2 A) (hcard : Nat.card A = 8)
    (F : Frame α t s u) (ht1 : t ≠ 1) (hs1 : s ≠ 1) (hts : t ≠ s) : LocE2 α := by
  intro φ hodd hfix
  have hmem : ∀ z : SL(4, K3), (z : Mat).IsDiag → slConjugation 4 K3 F.P z ∈ gammaAct α := by
    intro z hz
    have hT : (z : Mat) * Gt = Gt * (z : Mat) := by
      rw [Gt_eq_diagonal]; exact comm_of_isDiag hz _
    have hS : (z : Mat) * Gs = Gs * (z : Mat) := by
      rw [Gs_eq_diagonal]; exact comm_of_isDiag hz _
    exact mem_gamma_pair hA (by omega) α ht1 hs1 hts _ ((F.fix_t z).2 hT) ((F.fix_s z).2 hS)
  obtain ⟨ψ, hψ⟩ : ∃ ψ : MulAut SL(4, K3), ψ = (slConjugation 4 K3 F.P)⁻¹ * φ * slConjugation 4 K3 F.P :=
    ⟨_, rfl⟩
  have hψfix : ∀ g : SL(4, K3), (g : Mat).IsDiag → ψ g = g := by
    intro g hg
    rw [hψ]
    show (slConjugation 4 K3 F.P)⁻¹ (φ (slConjugation 4 K3 F.P g)) = g
    rw [hfix _ (hmem g hg)]
    simp
  have h2 := sq_eq_one_of_fix_diag ψ hψfix
  have hφ2 : φ * φ = 1 := by
    have e : φ = slConjugation 4 K3 F.P * ψ * (slConjugation 4 K3 F.P)⁻¹ := by rw [hψ]; group
    calc φ * φ = slConjugation 4 K3 F.P * (ψ * ψ) * (slConjugation 4 K3 F.P)⁻¹ := by
          conv_lhs => rw [e]
          group
      _ = 1 := by rw [h2]; group
  have hdvd : orderOf φ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hφ2)
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2'
  · exact orderOf_eq_one_iff.1 h1
  · rw [h2'] at hodd
    exact absurd hodd (by decide)

theorem locE3_of_data [Finite A] (hA : CFSG.IsElementaryAbelian 2 A) (hcard : Nat.card A = 8)
    {t s : A} (ht1 : t ≠ 1) (hs1 : s ≠ 1) (hts : t ≠ s) {Gt' Gs' : GL (Fin 4) K3}
    (hGt : InnerLift (α t) Gt') (hGs : InnerLift (α s) Gs') {c : K3} {g : Mat}
    (hg : (Gt' : Mat) = c • g) (hgg : g * g = 1) (hgdet : g.det = 1) (hgs : g * Gs' = Gs' * g)
    (hnsc : ∀ l : K3, g ≠ l • (1 : Mat)) : LocE3 α := by
  have ht2 := WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA t
  have hs2 := WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA s
  have h4 := four_le_card_closure_pair t s ht1 hs1 hts ht2 hs2
  have hadm : pRank 2 A - 1 ≤ pRank 2 ↥(Subgroup.closure {t, s}) :=
    (GenLocBasic.adm_iff_index hA _).2 (index_le_two_of_card _ (by omega))
  obtain ⟨x, hx⟩ : ∃ x : SL(4, K3), (x : Mat) = g := ⟨⟨g, hgdet⟩, rfl⟩
  refine ⟨Subgroup.closure {t, s}, hadm, x, ?_, ⟨1, ?_⟩, ?_⟩
  · rw [GenLocBasic.mem_fixedIn_map]
    apply stab_closure α {t, s}
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · refine innerLift_fix hGt x ?_
      rw [hx, hg, Matrix.mul_smul, Matrix.smul_mul]
    · refine innerLift_fix hGs x ?_
      rw [hx]; exact hgs
  · have : x * x = 1 := Subtype.ext (by rw [Matrix.SpecialLinearGroup.coe_mul, hx, hgg]; rfl)
    simpa [pow_two] using this
  · by_contra hall
    push Not at hall
    obtain ⟨l, hl⟩ := GenLocL4Ext.exists_scalar_of_commute_sl (M := g) (fun y => by
      have := congrArg Subtype.val (hall y)
      rwa [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hx] at this)
    exact hnsc l hl

end LocSec

end GenLocL4ThreeDbLoc

open GenLocL4Out GenLocL4ThreeDb GenLocL4ThreeDbLoc
  CFSG.ComponentClassification.CatalogueBHigherLinearAction in
theorem rank3_Db_loc_three {A : Type} [Group A] [Finite A] (hA : CFSG.IsElementaryAbelian 2 A) (hcard : Nat.card A = 8)
    (α : A →* MulAut SL(4, K3)) (hinj : Function.Injective α) {u t s : A} (hu : ¬ GenLocL4Out.IsInnerDiag4 (α u))
    (ht1 : t ≠ 1) (hs1 : s ≠ 1) (hts : t ≠ s) {B : GL (Fin 4) K3} (hB : GraphForm (α u) B)
    (hBt : (B : Matrix (Fin 4) (Fin 4) K3)ᵀ = B) (hBd : ¬ IsSquare (B : Matrix (Fin 4) (Fin 4) K3).det)
    (htin : GenLocL4Out.IsInnerDiag4 (α t)) (hsin : GenLocL4Out.IsInnerDiag4 (α s))
    (dt : LiftData α (B : Matrix (Fin 4) (Fin 4) K3) t) (ds : LiftData α (B : Matrix (Fin 4) (Fin 4) K3) s)
    (hcomm : (dt.g : Matrix (Fin 4) (Fin 4) K3) * ds.g = ds.g * dt.g)
    (hμt : IsSquare dt.μ) (hμs : IsSquare ds.μ) : LocE1 α ∧ LocE2 α ∧ LocE3 α := by
  have _hBt := hBt
  have _hBd := hBd
  have hF4 : Nat.card K3 % 4 = 3 := by rw [Nat.card_zmod]
  have hBdet0 : (B : Mat).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 B.isUnit).ne_zero
  have hu2 : u * u = 1 := WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA u
  have hA2 : ∀ a : A, a * a = 1 := WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA
  obtain ⟨hindex, hc1⟩ := inner_cases hA hcard (innerSub α) htin hsin hu ht1 hs1 hts
  have hc2 := outer_cases (innerSub α) hindex hu hu2 hc1
  have hc3 : ∀ a b : A, ¬ IsInnerDiag4 (α a) → ¬ IsInnerDiag4 (α b) → IsInnerDiag4 (α (a * b)) :=
    fun a b ha hb => mul_mem_of_not_mem (innerSub α) hindex ha hb
  have hnsc_t : ∀ c : K3, (dt.g : Mat) ≠ c • (1 : Mat) := fun c hc =>
    ht1 (hinj (by rw [map_one]; exact eq_one_of_innerLift_scalar dt.lift c hc))
  have hnsc_s : ∀ c : K3, (ds.g : Mat) ≠ c • (1 : Mat) := fun c hc =>
    hs1 (hinj (by rw [map_one]; exact eq_one_of_innerLift_scalar ds.lift c hc))
  obtain ⟨νt, hνt0, hgg, hgdet⟩ := split_norm hF4 dt.μ_ne dt.sq dt.detsq hμt
  obtain ⟨νs, hνs0, hhh, hhdet⟩ := split_norm hF4 ds.μ_ne ds.sq ds.detsq hμs
  have hgt : (dt.g : Mat) = νt • (νt⁻¹ • (dt.g : Mat)) := by
    rw [smul_smul, mul_inv_cancel₀ hνt0, one_smul]
  have hgs : (ds.g : Mat) = νs • (νs⁻¹ • (ds.g : Mat)) := by
    rw [smul_smul, mul_inv_cancel₀ hνs0, one_smul]
  have hcomm' : (νt⁻¹ • (dt.g : Mat)) * (νs⁻¹ • (ds.g : Mat)) = (νs⁻¹ • (ds.g : Mat)) * (νt⁻¹ • (dt.g : Mat)) := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hcomm, mul_comm]
  have hBt' : ∀ (c : K3) (g : Mat), g * (B : Mat) = (B : Mat) * gᵀ → (c • g) * (B : Mat) = (B : Mat) * (c • g)ᵀ :=
    fun c g h => by rw [Matrix.smul_mul, h, Matrix.transpose_smul, Matrix.mul_smul]
  have hne1 : νs⁻¹ • (ds.g : Mat) ≠ νt⁻¹ • (dt.g : Mat) := by
    intro h
    have hg : (ds.g : Mat) = (νs * νt⁻¹) • (dt.g : Mat) := by
      calc (ds.g : Mat) = νs • (νs⁻¹ • (ds.g : Mat)) := hgs
        _ = νs • (νt⁻¹ • (dt.g : Mat)) := by rw [h]
        _ = _ := by rw [smul_smul]
    exact hts (hinj (eq_of_lift_smul ds.lift dt.lift (mul_ne_zero hνs0 (inv_ne_zero hνt0)) hg)).symm
  have hne2 : νs⁻¹ • (ds.g : Mat) ≠ -(νt⁻¹ • (dt.g : Mat)) := by
    intro h
    have hg : (ds.g : Mat) = (-(νs * νt⁻¹)) • (dt.g : Mat) := by
      calc (ds.g : Mat) = νs • (νs⁻¹ • (ds.g : Mat)) := hgs
        _ = νs • (-(νt⁻¹ • (dt.g : Mat))) := by rw [h]
        _ = _ := by rw [smul_neg, smul_smul, neg_smul]
    exact hts (hinj (eq_of_lift_smul ds.lift dt.lift (neg_ne_zero.2 (mul_ne_zero hνs0 (inv_ne_zero hνt0))) hg)).symm
  obtain ⟨P, d, hd, hBP, hgP, hhP⟩ := db_frame hF4 (B : Mat) (νt⁻¹ • (dt.g : Mat)) (νs⁻¹ • (ds.g : Mat)) hBdet0
    hgg hhh hcomm' hgdet hhdet (fun h => hnsc_t νt (by rw [hgt, h])) (fun h => hnsc_t (-νt) (by rw [hgt, h]; simp))
    (fun h => hnsc_s νs (by rw [hgs, h])) (fun h => hnsc_s (-νs) (by rw [hgs, h]; simp)) hne1 hne2
    (hBt' _ _ dt.comp) (hBt' _ _ ds.comp)
  have hPiP : ((P⁻¹ : GL (Fin 4) K3) : Mat) * (P : Mat) = 1 := coe_inv_mul P
  have eg : ((P⁻¹ : GL (Fin 4) K3) : Mat) * (νt⁻¹ • (dt.g : Mat)) * (P : Mat) = Gt := by
    rw [Matrix.mul_assoc, hgP, ← Matrix.mul_assoc, hPiP, Matrix.one_mul]
  have eh : ((P⁻¹ : GL (Fin 4) K3) : Mat) * (νs⁻¹ • (ds.g : Mat)) * (P : Mat) = Gs := by
    rw [Matrix.mul_assoc, hhP, ← Matrix.mul_assoc, hPiP, Matrix.one_mul]
  let F : Frame α t s u :=
    { P := P, d := d, B := B, Gt' := dt.g, Gs' := ds.g, ct := νt, cs := νs, hd := hd, hct := hνt0, hcs := hνs0,
      hB := hB, hBP := hBP, hGt := dt.lift, hGs := ds.lift
      hPt := by
        calc ((P⁻¹ : GL (Fin 4) K3) : Mat) * (dt.g : Mat) * (P : Mat)
            = ((P⁻¹ : GL (Fin 4) K3) : Mat) * (νt • (νt⁻¹ • (dt.g : Mat))) * (P : Mat) := by rw [← hgt]
          _ = νt • (((P⁻¹ : GL (Fin 4) K3) : Mat) * (νt⁻¹ • (dt.g : Mat)) * (P : Mat)) := by
              rw [Matrix.mul_smul, Matrix.smul_mul]
          _ = νt • (Gt : Mat) := by rw [eg]
      hPs := by
        calc ((P⁻¹ : GL (Fin 4) K3) : Mat) * (ds.g : Mat) * (P : Mat)
            = ((P⁻¹ : GL (Fin 4) K3) : Mat) * (νs • (νs⁻¹ • (ds.g : Mat))) * (P : Mat) := by rw [← hgs]
          _ = νs • (((P⁻¹ : GL (Fin 4) K3) : Mat) * (νs⁻¹ • (ds.g : Mat)) * (P : Mat)) := by
              rw [Matrix.mul_smul, Matrix.smul_mul]
          _ = νs • (Gs : Mat) := by rw [eh] }
  have hpair : ∀ a b : A, a ≠ 1 → b ≠ 1 → a ≠ b → ∀ x : SL(4, K3), α a x = x → α b x = x → x ^ 8 = 1 := by
    intro a b ha1 hb1 hab x hxa hxb
    have hx : (slConjugation 4 K3 F.P) ((slConjugation 4 K3 F.P).symm x) = x :=
      MulEquiv.apply_symm_apply _ x
    have h8 := pair_pow8 F (fun a ha => hc1 a ha) (fun w hw => hc2 w hw) hc3 hA2
      ((slConjugation 4 K3 F.P).symm x) ha1 hb1 hab (by rw [hx]; exact hxa) (by rw [hx]; exact hxb)
    have h8' : ((slConjugation 4 K3 F.P).symm x) ^ 8 = 1 := Subtype.ext (by simpa using h8)
    calc x ^ 8 = ((slConjugation 4 K3 F.P) ((slConjugation 4 K3 F.P).symm x)) ^ 8 := by rw [hx]
      _ = (slConjugation 4 K3 F.P) (((slConjugation 4 K3 F.P).symm x) ^ 8) := (map_pow _ _ _).symm
      _ = 1 := by rw [h8', map_one]
  refine ⟨locE1_of_pair hA hcard hpair, locE2_of_frame hA hcard F ht1 hs1 hts, ?_⟩
  refine locE3_of_data hA hcard ht1 hs1 hts dt.lift ds.lift hgt hgg hgdet ?_ ?_
  · rw [Matrix.smul_mul, Matrix.mul_smul, hcomm]
  · intro l hl
    exact hnsc_t (νt * l) (by rw [hgt, hl, smul_smul])

end CFSG.GH74.Generic.BProg.B2
