module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindUnitaryOdd
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindLinear

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

section Param

theorem forall_nonempty_unitaryNeighbourParam {G : Type} [Group G] [Finite G] {L : Subgroup G}
    {K : Type} [Field K] {m f : ℕ} (hset : SeitzSetting G L) (hKc : Nat.card K = 2 ^ f)
    (hf : 2 ≤ f) (hm : 3 ≤ m) (e : L ≃* StatedSp (m + 1) K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hroot : ∀ k : Fin (m + 1), RootKindSp e t f k .unitaryEven) (k : Fin (m + 1)) :
    ∃ (K' : Type) (_ : Field K') (h : UnitaryFieldData 2 f K') (_ : CharP h.fixedField 2)
      (C₀ : GL (Fin (2 * m)) K') (hC : IsPrimeFormGram C₀)
      (hC₀ : (C₀ : Matrix (Fin (2 * m)) (Fin (2 * m)) K') = blockSwapJ (2 * m) m)
      (ι : K ≃+* h.fixedField), Nonempty (UnitaryNeighbourParam h e t k hC hC₀ ι) :=
  nonempty_unitaryNeighbourParam hset hKc hf hm e
    (LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt) ht k (hroot k)

end Param

@[expose] def SpUnitaryParamCTInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (m f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], 3 ≤ m → Nat.card K = 2 ^ f →
    2 ≤ f → ∀ (e : L ≃* StatedSp (m + 1) K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin (m + 1), ∃ (K' : Type) (_ : Field K') (h : UnitaryFieldData 2 f K')
        (_ : CharP h.fixedField 2) (C₀ : GL (Fin (2 * m)) K') (hC : IsPrimeFormGram C₀)
        (hC₀ : (C₀ : Matrix (Fin (2 * m)) (Fin (2 * m)) K') = blockSwapJ (2 * m) m)
        (ι : K ≃+* h.fixedField), Nonempty (UnitaryNeighbourParam h e t k hC hC₀ ι)) →
        SpGlobalCoverType e f .unitaryEven

section Reduction

theorem spKindCoverInput_unitaryEven_of_paramCT (hCT : SpUnitaryParamCTInput) :
    SpKindCoverInput .unitaryEven := by
  intro G _ _ L hset n f K _ _ _ hn hKc hf e t ht hKt hroot
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact hCT G L hset m f K (by omega) hKc hf e t ht hKt
    (forall_nonempty_unitaryNeighbourParam hset hKc hf (by omega) e ht hKt hroot)

end Reduction

section Odd

open CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical (matrixIsometryGroup) in
theorem forall_nonempty_unitaryOddNeighbourParam {G : Type} [Group G] [Finite G]
    {L : Subgroup G} {K : Type} [Field K] {m f : ℕ} (hset : SeitzSetting G L)
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (hm : 3 ≤ m) (e : L ≃* StatedSp (m + 1) K) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hroot : ∀ k : Fin (m + 1), RootKindSp e t f k .unitaryOdd) (k : Fin (m + 1)) :
    ∃ (K' : Type) (_ : Field K') (h : UnitaryFieldData 2 f K') (_ : CharP h.fixedField 2)
      (C₀ : GL (Fin (2 * m + 1)) K') (hC : IsPrimeFormGram C₀)
      (hC₀ : ((C₀ : GL (Fin (2 * m + 1)) K') :
        Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) K') = 1),
      ∀ β : StatedSp m h.fixedField ≃*
          matrixIsometryGroup (1 : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) h.fixedField),
        ∃ ι : K ≃+* h.fixedField, Nonempty (UnitaryOddNeighbourParam h e t k hC hC₀ β ι) :=
  nonempty_unitaryOddNeighbourParam hset hKc hf hm e
    (LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt) ht k (hroot k)

end Odd

open CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical (matrixIsometryGroup) in
@[expose] def SpUnitaryOddParamCTInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (m f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], 3 ≤ m → Nat.card K = 2 ^ f →
    2 ≤ f → ∀ (e : L ≃* StatedSp (m + 1) K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin (m + 1), ∃ (K' : Type) (_ : Field K') (h : UnitaryFieldData 2 f K')
        (_ : CharP h.fixedField 2) (C₀ : GL (Fin (2 * m + 1)) K') (hC : IsPrimeFormGram C₀)
        (hC₀ : ((C₀ : GL (Fin (2 * m + 1)) K') :
          Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) K') = 1),
        ∀ β : StatedSp m h.fixedField ≃*
            matrixIsometryGroup (1 : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) h.fixedField),
          ∃ ι : K ≃+* h.fixedField, Nonempty (UnitaryOddNeighbourParam h e t k hC hC₀ β ι)) →
        SpGlobalCoverType e f .unitaryOdd

section OddReduction

theorem spKindCoverInput_unitaryOdd_of_paramCT (hCT : SpUnitaryOddParamCTInput) :
    SpKindCoverInput .unitaryOdd := by
  intro G _ _ L hset n f K _ _ _ hn hKc hf e t ht hKt hroot
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact hCT G L hset m f K (by omega) hKc hf e t ht hKt
    (forall_nonempty_unitaryOddNeighbourParam hset hKc hf (by omega) e ht hKt hroot)

end OddReduction

section Coprime

theorem center_statedSU_eq_bot_of_coprime {F : Type} [Field F] [Finite F] {f N : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f) (hN : 3 ≤ N)
    (hcop : Nat.Coprime N (2 ^ f + 1)) : center (StatedSU N (2 ^ f) F) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNq : (N, 2 ^ f) ≠ (3, 2) := fun h3 => by
    obtain ⟨h1, h2⟩ := Prod.mk.inj h3
    subst h1
    rw [h2] at hcop
    norm_num at hcop
  rw [(CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hF hN hNq).2, eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_subgroupOf] at hz
  obtain ⟨c, hc⟩ := hz
  have h : UnitaryFieldData 2 f F := ⟨Nat.prime_two, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  obtain ⟨hdet, hu⟩ := (CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff h).1 z.2
  rw [← hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at hdet hu
  rw [Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
  rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal] at hu
  have h00 := congrFun (congrFun hu ⟨0, by omega⟩) ⟨0, by omega⟩
  rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, h.bar_apply] at h00
  have hq1 : (c : F) ^ (2 ^ f + 1) = 1 := by
    rw [pow_succ]
    exact h00
  have hc1 : c = 1 := Units.ext ((pow_eq_one_iff_of_coprime hcop).1 ⟨hdet, hq1⟩)
  rw [mem_bot]
  apply Subtype.ext
  rw [← hc, hc1, map_one]
  rfl

end Coprime

end CFSG.SeitzReduction.SymplecticPilot
