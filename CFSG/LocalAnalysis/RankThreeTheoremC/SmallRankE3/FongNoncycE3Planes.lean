module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongNoncycE3Orth
public import CFSG.LocalAnalysis.SectionRank.ClassicalEven.Orthogonal

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongNoncyc

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix CFSG.SectionRank.ClassicalEven
open CFSG.SectionRank.ClassicalEven.OrthRot

theorem isPolar_hypPlus {K : Type} [Field K] {n : ℕ} (j : Fin n) :
    IsPolar (StatedQuadPlus n K) (Pi.single (Sum.inl j) 1 + Pi.single (Sum.inr j) 1)
      ((LinearMap.proj (Sum.inr j) : (Fin n ⊕ Fin n → K) →ₗ[K] K) + LinearMap.proj (Sum.inl j))
      1 :=
  (isPolar_plus_inl (K := K) j).add (isPolar_plus_inr (K := K) j) (by simp)

noncomputable def pairPlane {K : Type} [Field K] {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    Plane (StatedQuadPlus n K) where
  a := Pi.single (Sum.inl i) 1 + Pi.single (Sum.inr i) 1
  b := Pi.single (Sum.inl i) 1 + (Pi.single (Sum.inl j) 1 + Pi.single (Sum.inr j) 1)
  f := (LinearMap.proj (Sum.inr i) : (Fin n ⊕ Fin n → K) →ₗ[K] K) + LinearMap.proj (Sum.inl i)
  g := (LinearMap.proj (Sum.inr i) : (Fin n ⊕ Fin n → K) →ₗ[K] K) +
    ((LinearMap.proj (Sum.inr j) : (Fin n ⊕ Fin n → K) →ₗ[K] K) + LinearMap.proj (Sum.inl j))
  isPolar_a := isPolar_hypPlus i
  isPolar_b := (isPolar_plus_inl (K := K) i).add (isPolar_hypPlus j)
    (by simp [Pi.single_apply, hij, Ne.symm hij])
  f_b := by simp [Pi.single_apply, hij, Ne.symm hij]

theorem pairPlane_orth_twin {K : Type} [Field K] [CharP K 2] {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) : (pairPlane (K := K) hij).Orth (pairPlane (K := K) hij.symm) :=
  ⟨by simp [pairPlane, Pi.single_apply, hij, Ne.symm hij, CharTwo.add_self_eq_zero],
    by simp [pairPlane, Pi.single_apply, hij, Ne.symm hij, CharTwo.add_self_eq_zero],
    by simp [pairPlane, Pi.single_apply, hij, Ne.symm hij, CharTwo.add_self_eq_zero],
    by simp [pairPlane, Pi.single_apply, hij, Ne.symm hij, CharTwo.add_self_eq_zero]⟩

theorem pairPlane_orth_disjoint {K : Type} [Field K] {n : ℕ} {i j k l : Fin n}
    (hij : i ≠ j) (hkl : k ≠ l) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    (pairPlane (K := K) hij).Orth (pairPlane (K := K) hkl) :=
  ⟨by simp [pairPlane, Pi.single_apply, hik, hil, hjk, hjl, Ne.symm hik, Ne.symm hil,
      Ne.symm hjk, Ne.symm hjl],
    by simp [pairPlane, Pi.single_apply, hik, hil, hjk, hjl, Ne.symm hik, Ne.symm hil,
      Ne.symm hjk, Ne.symm hjl],
    by simp [pairPlane, Pi.single_apply, hik, hil, hjk, hjl, Ne.symm hik, Ne.symm hil,
      Ne.symm hjk, Ne.symm hjl],
    by simp [pairPlane, Pi.single_apply, hik, hil, hjk, hjl, Ne.symm hik, Ne.symm hil,
      Ne.symm hjk, Ne.symm hjl]⟩

theorem omegaPlus_four_le_pRank_three_F2 {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn : 4 ≤ n) :
    4 ≤ pRank 3 (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadPlus n K)))) := by
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have h02 : (⟨0, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
  have h03 : (⟨0, by omega⟩ : Fin n) ≠ ⟨3, by omega⟩ := by simp [Fin.ext_iff]
  have h12 : (⟨1, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
  have h13 : (⟨1, by omega⟩ : Fin n) ≠ ⟨3, by omega⟩ := by simp [Fin.ext_iff]
  have h23 : (⟨2, by omega⟩ : Fin n) ≠ ⟨3, by omega⟩ := by simp [Fin.ext_iff]
  exact four_planes_le_pRank_three
    (P₀ := pairPlane (K := K) h01) (P₁ := pairPlane (K := K) h01.symm)
    (P₂ := pairPlane (K := K) h23) (P₃ := pairPlane (K := K) h23.symm)
    (pairPlane_orth_twin (K := K) h01)
    (pairPlane_orth_disjoint (K := K) h01 h23 h02 h03 h12 h13)
    (pairPlane_orth_disjoint (K := K) h01 h23.symm h03 h02 h13 h12)
    (pairPlane_orth_disjoint (K := K) h01.symm h23 h12 h13 h02 h03)
    (pairPlane_orth_disjoint (K := K) h01.symm h23.symm h13 h12 h03 h02)
    (pairPlane_orth_twin (K := K) h23)

theorem isPolar_hypMinus {K : Type} [Field K] {n : ℕ} (b₀ c₀ : K) (j : Fin (n - 1)) :
    IsPolar (StatedQuadMinus n K b₀ c₀)
      (Pi.single (Sum.inl j) 1 + Pi.single (Sum.inr (Sum.inl j)) 1)
      ((LinearMap.proj (Sum.inr (Sum.inl j)) : (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) →ₗ[K] K) +
        LinearMap.proj (Sum.inl j))
      1 :=
  (isPolar_minus_inl b₀ c₀ j).add (isPolar_minus_inr b₀ c₀ j) (by simp)

noncomputable def pairPlaneMinus {K : Type} [Field K] {n : ℕ} (b₀ c₀ : K) {i j : Fin (n - 1)}
    (hij : i ≠ j) : Plane (StatedQuadMinus n K b₀ c₀) where
  a := Pi.single (Sum.inl i) 1 + Pi.single (Sum.inr (Sum.inl i)) 1
  b := Pi.single (Sum.inl i) 1 + (Pi.single (Sum.inl j) 1 + Pi.single (Sum.inr (Sum.inl j)) 1)
  f := (LinearMap.proj (Sum.inr (Sum.inl i)) :
      (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) →ₗ[K] K) + LinearMap.proj (Sum.inl i)
  g := (LinearMap.proj (Sum.inr (Sum.inl i)) :
      (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) →ₗ[K] K) +
    ((LinearMap.proj (Sum.inr (Sum.inl j)) :
      (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) →ₗ[K] K) + LinearMap.proj (Sum.inl j))
  isPolar_a := isPolar_hypMinus b₀ c₀ i
  isPolar_b := (isPolar_minus_inl b₀ c₀ i).add (isPolar_hypMinus b₀ c₀ j)
    (by simp [Pi.single_apply, hij, Ne.symm hij])
  f_b := by simp [Pi.single_apply, hij, Ne.symm hij]

theorem pairPlaneMinus_orth_twin {K : Type} [Field K] [CharP K 2] {n : ℕ} (b₀ c₀ : K)
    {i j : Fin (n - 1)} (hij : i ≠ j) :
    (pairPlaneMinus b₀ c₀ hij).Orth (pairPlaneMinus b₀ c₀ hij.symm) :=
  ⟨by simp [pairPlaneMinus, Pi.single_apply, hij, Ne.symm hij, CharTwo.add_self_eq_zero],
    by simp [pairPlaneMinus, Pi.single_apply, hij, Ne.symm hij, CharTwo.add_self_eq_zero],
    by simp [pairPlaneMinus, Pi.single_apply, hij, Ne.symm hij, CharTwo.add_self_eq_zero],
    by simp [pairPlaneMinus, Pi.single_apply, hij, Ne.symm hij, CharTwo.add_self_eq_zero]⟩

theorem pairPlaneMinus_orth_disjoint {K : Type} [Field K] {n : ℕ} (b₀ c₀ : K)
    {i j k l : Fin (n - 1)} (hij : i ≠ j) (hkl : k ≠ l) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) :
    (pairPlaneMinus b₀ c₀ hij).Orth (pairPlaneMinus b₀ c₀ hkl) :=
  ⟨by simp [pairPlaneMinus, Pi.single_apply, hik, hil, hjk, hjl, Ne.symm hik, Ne.symm hil,
      Ne.symm hjk, Ne.symm hjl],
    by simp [pairPlaneMinus, Pi.single_apply, hik, hil, hjk, hjl, Ne.symm hik, Ne.symm hil,
      Ne.symm hjk, Ne.symm hjl],
    by simp [pairPlaneMinus, Pi.single_apply, hik, hil, hjk, hjl, Ne.symm hik, Ne.symm hil,
      Ne.symm hjk, Ne.symm hjl],
    by simp [pairPlaneMinus, Pi.single_apply, hik, hil, hjk, hjl, Ne.symm hik, Ne.symm hil,
      Ne.symm hjk, Ne.symm hjl]⟩

theorem omegaMinus_four_le_pRank_three_F2 {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn : 5 ≤ n) (b c : K) :
    4 ≤ pRank 3 (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadMinus n K b c)))) := by
  have h01 : (⟨0, by omega⟩ : Fin (n - 1)) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have h02 : (⟨0, by omega⟩ : Fin (n - 1)) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
  have h03 : (⟨0, by omega⟩ : Fin (n - 1)) ≠ ⟨3, by omega⟩ := by simp [Fin.ext_iff]
  have h12 : (⟨1, by omega⟩ : Fin (n - 1)) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
  have h13 : (⟨1, by omega⟩ : Fin (n - 1)) ≠ ⟨3, by omega⟩ := by simp [Fin.ext_iff]
  have h23 : (⟨2, by omega⟩ : Fin (n - 1)) ≠ ⟨3, by omega⟩ := by simp [Fin.ext_iff]
  exact four_planes_le_pRank_three
    (P₀ := pairPlaneMinus b c h01) (P₁ := pairPlaneMinus b c h01.symm)
    (P₂ := pairPlaneMinus b c h23) (P₃ := pairPlaneMinus b c h23.symm)
    (pairPlaneMinus_orth_twin b c h01)
    (pairPlaneMinus_orth_disjoint b c h01 h23 h02 h03 h12 h13)
    (pairPlaneMinus_orth_disjoint b c h01 h23.symm h03 h02 h13 h12)
    (pairPlaneMinus_orth_disjoint b c h01.symm h23 h12 h13 h02 h03)
    (pairPlaneMinus_orth_disjoint b c h01.symm h23.symm h13 h12 h03 h02)
    (pairPlaneMinus_orth_twin b c h23)

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongNoncyc
