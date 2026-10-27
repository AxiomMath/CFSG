module

public import CFSG.ClassicalInvolution.Asc77.AscT7MU
public import CFSG.ClassicalInvolution.Asc77.AscT7MSB
public import CFSG.ClassicalInvolution.ModelFacts.Orth15RSuStd

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15.SqU4

set_option linter.unusedSectionVars false

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary
  CFSG.ClassicalInvolution.ModelFacts.Orth15.SqL4
open scoped commutatorElement

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

variable (K p f) in
@[expose] noncomputable def sU : Su K p f 4 :=
  mkSU K p f !![1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0; 0, -1, 0, 0]
    (by simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove])
    (by
      ext a b
      fin_cases a <;> fin_cases b <;> simp [conjTr, Matrix.mul_apply, Fin.sum_univ_four])

theorem suMat_sU : suMat (sU K p f) = !![1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0; 0, -1, 0, 0] :=
  suMat_mkSU _ _

theorem suMat_sU_inv : suMat (sU K p f)⁻¹ =
    !![1, 0, 0, 0; 0, 0, 0, -1; 0, 0, 1, 0; 0, 1, 0, 0] := by
  have h1 : suMat (sU K p f)⁻¹ * suMat (sU K p f) = 1 := suMat_inv_mul_suMat _
  rw [suMat_sU] at h1
  have h2 : (!![1, 0, 0, 0; 0, 0, 0, -1; 0, 0, 1, 0; 0, 1, 0, 0] : Matrix (Fin 4) (Fin 4) K) *
      !![1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0; 0, -1, 0, 0] = 1 := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_four]
  calc suMat (sU K p f)⁻¹ = suMat (sU K p f)⁻¹ * (!![1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0;
        0, -1, 0, 0] * !![1, 0, 0, 0; 0, 0, 0, -1; 0, 0, 1, 0; 0, 1, 0, 0]) := by
        have h3 : (!![1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0; 0, -1, 0, 0] : Matrix (Fin 4) (Fin 4) K) *
            !![1, 0, 0, 0; 0, 0, 0, -1; 0, 0, 1, 0; 0, 1, 0, 0] = 1 := by
          ext a b
          fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_four]
        rw [h3, Matrix.mul_one]
    _ = (suMat (sU K p f)⁻¹ * !![1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0; 0, -1, 0, 0]) *
        !![1, 0, 0, 0; 0, 0, 0, -1; 0, 0, 1, 0; 0, 1, 0, 0] := by rw [Matrix.mul_assoc]
    _ = _ := by rw [h1, Matrix.one_mul]

variable (K p f) in
@[expose] noncomputable def zA : Su K p f 4 :=
  sU K p f * ModelFacts.Orth15.InnerSu.x0 K p f * (sU K p f)⁻¹

theorem suMat_zA : suMat (zA K p f) = !![-1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, -1] := by
  rw [zA, suMat_mul, suMat_mul, suMat_sU, suMat_sU_inv, ModelFacts.Orth15.InnerSu.suMat_x0]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

theorem centre_trivial_quot {S : Type*} [Group S] (hS : CFSG.Open.IsQuasisimple S)
    (c : S ⧸ Subgroup.center S) (hc : ∀ r, c * r = r * c) : c = 1 := by
  obtain ⟨hperf, hsimple⟩ := hS
  rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center (S ⧸ Subgroup.center S)) with h | h
  · have hcm : c ∈ Subgroup.center (S ⧸ Subgroup.center S) :=
      Subgroup.mem_center_iff.mpr fun r => (hc r).symm
    rw [h] at hcm
    exact Subgroup.mem_bot.mp hcm
  · exfalso
    have h1 : ∀ x y : S ⧸ Subgroup.center S, x * y = y * x := fun x y => by
      have : x ∈ Subgroup.center (S ⧸ Subgroup.center S) := by rw [h]; exact Subgroup.mem_top x
      exact (Subgroup.mem_center_iff.mp this y).symm
    have hcomm : ∀ a b : S, ⁅a, b⁆ ∈ Subgroup.center S := by
      intro a b
      have h2 : ⁅(QuotientGroup.mk a : S ⧸ Subgroup.center S), QuotientGroup.mk b⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.mpr (h1 _ _)
      rw [← QuotientGroup.eq_one_iff]
      simpa [commutatorElement_def] using h2
    have hle : (⊤ : Subgroup S) ≤ Subgroup.center S := by
      rw [← hperf, _root_.commutator_def]
      exact Subgroup.commutator_le.mpr fun a _ b _ => hcomm a b
    obtain ⟨x, y, hxy⟩ := (hsimple.toNontrivial).exists_pair_ne
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    apply hxy
    have e1 : (QuotientGroup.mk x : S ⧸ Subgroup.center S) = 1 :=
      (QuotientGroup.eq_one_iff x).mpr (hle (Subgroup.mem_top x))
    have e2 : (QuotientGroup.mk y : S ⧸ Subgroup.center S) = 1 :=
      (QuotientGroup.eq_one_iff y).mpr (hle (Subgroup.mem_top y))
    rw [e1, e2]

theorem isQuasisimple_su4 (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f) :
    CFSG.Open.IsQuasisimple (Su K p f 4) := by
  have h := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (F := K) (p := p)
    (f := f) hK (by norm_num : 3 ≤ 4)
    (CFSG.ClassicalInvolution.Models.Transfer.pair_ne_three_two_of_five_le hq)).1
  have h' : CFSG.IsQuasisimple (Su K p f 4) :=
    isQuasisimple_of_equiv (MulEquiv.subgroupCongr (SUid_eq_statedSU hK 4)).symm h
  exact ⟨Group.isPerfect_def.mp h'.1, h'.2.1⟩

theorem centre_trivial_PU (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f) :
    ∀ c : PU K p f, (∀ r, c * r = r * c) → c = 1 :=
  fun c hc => centre_trivial_quot (isQuasisimple_su4 hK hq) c hc

theorem actsAsD_iff {φ : MulAut (PU K p f)} {j : Fin 4} :
    ActsAsD K p f φ j ↔ ActsAsM φ (dMat j) (dMat j) := by
  constructor
  · intro h
    refine ⟨dMat_mul_self j, dMat_mul_self j, fun g => ⟨suConjD K p f j g, h g, ?_⟩⟩
    rw [suMat_suConjD]
  · rintro ⟨-, -, h⟩ g
    obtain ⟨g', hg', hm⟩ := h g
    rw [hg']
    congr 1
    apply suMat_injective
    rw [hm, suMat_suConjD]

theorem zA_mul_self : zA K p f * zA K p f = 1 := by
  apply suMat_injective
  rw [suMat_mul, suMat_zA, suMat_one]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

theorem zA_inv : (zA K p f)⁻¹ = zA K p f := inv_eq_of_mul_eq_one_right zA_mul_self

theorem dMat_three_eq : (dMat 3 : Matrix (Fin 4) (Fin 4) K) =
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, -1] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [dMat, sgn]

theorem dMat_zero_eq : (dMat 0 : Matrix (Fin 4) (Fin 4) K) =
    !![-1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [dMat, sgn]

theorem actsAsM_zA : ActsAsM (MulAut.conj (QuotientGroup.mk (zA K p f) : PU K p f))
    (suMat (zA K p f)) (suMat (zA K p f)) := by
  have h := actsAsM_conj (zA K p f)
  rwa [zA_inv] at h

theorem actsAsD_zy {φ : MulAut (PU K p f)} (h : ActsAsD K p f φ 3) :
    ActsAsD K p f (MulAut.conj (QuotientGroup.mk (zA K p f) : PU K p f) * φ) 0 := by
  rw [actsAsD_iff] at h ⊢
  have h1 := actsAsM_zA.mul h
  have e : suMat (zA K p f) * dMat 3 = (dMat 0 : Matrix (Fin 4) (Fin 4) K) := by
    rw [suMat_zA, dMat_three_eq, dMat_zero_eq]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_four]
  have e' : dMat 3 * suMat (zA K p f) = (dMat 0 : Matrix (Fin 4) (Fin 4) K) := by
    rw [suMat_zA, dMat_three_eq, dMat_zero_eq]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_four]
  rwa [e, e'] at h1

end CFSG.ClassicalInvolution.ModelFacts.Orth15.SqU4
