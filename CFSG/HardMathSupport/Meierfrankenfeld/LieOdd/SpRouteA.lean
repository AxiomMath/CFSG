module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.SpOrder
public import CFSG.LargeExtraspecial.A2ModFrCMat

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open Matrix CFSG.Assembly.LowTwoRank CFSG.LargeExtraspecial.A2Mod.FrC
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

variable {K : Type} [Field K]

theorem scalar_sq_eq_one_of_mem_statedSp {r : ℕ} [NeZero r] (c : Kˣ)
    (h : Matrix.GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c ∈ StatedSp r K) : c * c = 1 := by
  rw [mem_statedSp_iff] at h
  have hs : ((Matrix.GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      (c : K) • (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
    ext i j
    by_cases hij : i = j <;>
      simp [Matrix.GeneralLinearGroup.scalar, hij]
  rw [hs] at h
  have e := congrFun (congrFun h (Sum.inl ⟨0, Nat.pos_of_ne_zero (NeZero.ne r)⟩))
    (Sum.inr ⟨0, Nat.pos_of_ne_zero (NeZero.ne r)⟩)
  simp [Matrix.fromBlocks, Matrix.smul_apply, Matrix.mul_apply, Matrix.one_apply] at e
  exact Units.ext (by simpa using e)

theorem neg_scalar_mem_statedSp {r : ℕ} :
    Matrix.GeneralLinearGroup.scalar (Fin r ⊕ Fin r) (-1 : Kˣ) ∈ StatedSp r K := by
  rw [mem_statedSp_iff]
  have hs : ((Matrix.GeneralLinearGroup.scalar (Fin r ⊕ Fin r) (-1 : Kˣ) :
      GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      ((-1 : Kˣ) : K) • (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
    ext i j
    by_cases hij : i = j <;>
      simp [Matrix.GeneralLinearGroup.scalar, hij]
  rw [hs]
  simp

theorem card_statedSp_eq_two_mul_card_proj [Finite K] (hK2 : (2 : K) ≠ 0) (r : ℕ) [NeZero r] :
    Nat.card (StatedSp r K) = 2 * Nat.card (StatedProj (StatedSp r K)) := by
  set N := (StatedScalars (Fin r ⊕ Fin r) K).subgroupOf (StatedSp r K) with hN
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup N
  have hneg1 : (-1 : Kˣ) ≠ 1 := by
    intro h1
    apply hK2
    have : ((-1 : Kˣ) : K) = ((1 : Kˣ) : K) := by rw [h1]
    simp at this
    linear_combination -this
  have hcard : Nat.card N = 2 := by
    let g : ↥(StatedSp r K) := ⟨_, neg_scalar_mem_statedSp (r := r)⟩
    have hgN : g ∈ N := by
      rw [hN, Subgroup.mem_subgroupOf]
      exact ⟨-1, rfl⟩
    rw [Nat.card_eq_two_iff]
    refine ⟨1, ⟨g, hgN⟩, ?_, ?_⟩
    · intro h1
      have h2 := congrArg (fun x : N => (x : ↥(StatedSp r K)).1) h1
      simp only [g, Subgroup.coe_one] at h2
      have h3 := congrArg (fun x : GL (Fin r ⊕ Fin r) K =>
        ((x : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
          (Sum.inl ⟨0, Nat.pos_of_ne_zero (NeZero.ne r)⟩)
          (Sum.inl ⟨0, Nat.pos_of_ne_zero (NeZero.ne r)⟩))) h2
      simp [Matrix.GeneralLinearGroup.scalar] at h3
      exact hneg1 (Units.ext (by simpa using h3.symm))
    · ext n
      simp only [Set.mem_univ, Set.mem_insert_iff, Set.mem_singleton_iff, iff_true]
      obtain ⟨c, hc⟩ := (Subgroup.mem_subgroupOf.1 n.2 : (n : ↥(StatedSp r K)).1 ∈
        StatedScalars (Fin r ⊕ Fin r) K)
      have hsq : c * c = 1 := scalar_sq_eq_one_of_mem_statedSp c (by
        rw [show Matrix.GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c =
          (n : ↥(StatedSp r K)).1 from hc]
        exact (n : ↥(StatedSp r K)).2)
      have hc1 : c = 1 ∨ c = -1 := by
        have hsq' : (c : K) * (c : K) = 1 := by simpa using congrArg Units.val hsq
        rcases mul_self_eq_one_iff.1 hsq' with h1 | h1
        · exact Or.inl (Units.ext h1)
        · exact Or.inr (Units.ext (by simpa using h1))
      rcases hc1 with rfl | rfl
      · left
        apply Subtype.ext
        apply Subtype.ext
        rw [← hc]
        simp
      · right
        apply Subtype.ext
        apply Subtype.ext
        rw [← hc]
  rw [hcard, mul_comm] at h
  exact h

theorem exists_conjAut_fieldAut [Finite K] {p e r : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ e) (hr : 2 ≤ r)
    (α : MulAut (StatedProj (StatedSp r K))) :
    ∃ (A : gsp r K) (σ : K ≃+* K), α = conjAut r K A * fieldAut r K σ := by
  have : NeZero r := ⟨by omega⟩
  rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | h3
  · have h2K : (2 : K) ≠ 0 := by
      have : Fintype K := Fintype.ofFinite K
      have : CharP K p := charP_of_card_eq_prime_pow (by
        rw [← Nat.card_eq_fintype_card]; exact hK)
      intro h
      have h2 := (CharP.cast_eq_zero_iff K p 2).mp (by exact_mod_cast h)
      exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp h2)
    exact (CFSG.RankThree.PartOne.AUTSL.SpTwo.automorphism_generation_two h2K).2 α
  · exact (automorphism_generation h3).2 α

theorem card_mulAut_psp_le_card_sp_mul [Finite K] {p e r : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ e) (hr : 2 ≤ r) :
    Nat.card (MulAut (StatedProj (StatedSp r K))) ≤ Nat.card (StatedSp r K) * e := by
  have : NeZero r := ⟨by omega⟩
  have hgen := exists_conjAut_fieldAut hp2 hK hr
  let f : (conjAut r K).range × (K ≃+* K) → MulAut (StatedProj (StatedSp r K)) :=
    fun x => (x.1 : MulAut _) * fieldAut r K x.2
  have hf : Function.Surjective f := by
    intro α
    obtain ⟨A, σ, rfl⟩ := hgen α
    exact ⟨(⟨conjAut r K A, A, rfl⟩, σ), rfl⟩
  have hfin : Finite ((conjAut r K).range × (K ≃+* K)) := by
    have : Finite (K ≃+* K) :=
      Finite.of_injective (fun σ : K ≃+* K => (σ : K → K)) (fun a b h => RingEquiv.ext (congrFun h))
    infer_instance
  have h1 := Nat.card_le_card_of_surjective f hf
  rw [Nat.card_prod] at h1
  have hAut : Nat.card (K ≃+* K) = e :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic (Fact.out : p.Prime) K hK).1
  calc Nat.card (MulAut (StatedProj (StatedSp r K)))
      ≤ Nat.card (conjAut r K).range * Nat.card (K ≃+* K) := h1
    _ ≤ Nat.card (StatedSp r K) * e := by
        rw [hAut]
        exact Nat.mul_le_mul_right _ card_range_conjAut_sp_le

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
