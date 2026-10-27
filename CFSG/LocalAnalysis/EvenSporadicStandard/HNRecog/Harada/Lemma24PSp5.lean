module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4Classify

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open CFSG.ComponentClassification.CatFactsSp4 CFSG.Open Subgroup
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open Matrix

instance instFactPrimeFiveHR4 : Fact (Nat.Prime 5) := ⟨by norm_num⟩

@[expose] def psp5Data : List (List ℕ) := [
  [0, 0, 0, 1, 0, 0, 1, 0, 0, 4, 0, 0, 4, 0, 0, 0],
  [0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0, 0],
  [0, 0, 1, 0, 0, 0, 0, 1, 4, 0, 0, 0, 0, 4, 0, 0],
  [0, 0, 1, 0, 0, 0, 0, 4, 4, 0, 0, 0, 0, 1, 0, 0],
  [0, 0, 1, 1, 0, 0, 1, 4, 2, 2, 0, 0, 2, 3, 0, 0],
  [0, 0, 1, 4, 0, 0, 4, 4, 2, 3, 0, 0, 3, 3, 0, 0],
  [0, 0, 2, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 2, 0, 0],
  [0, 0, 2, 0, 0, 0, 0, 3, 2, 0, 0, 0, 0, 3, 0, 0],
  [0, 0, 2, 2, 0, 0, 2, 3, 1, 1, 0, 0, 1, 4, 0, 0],
  [0, 0, 2, 3, 0, 0, 3, 3, 1, 4, 0, 0, 4, 4, 0, 0],
  [0, 1, 0, 0, 4, 0, 0, 0, 0, 0, 0, 1, 0, 0, 4, 0],
  [0, 1, 0, 1, 1, 0, 1, 0, 0, 3, 0, 4, 3, 0, 4, 0],
  [0, 1, 0, 2, 1, 0, 2, 0, 0, 4, 0, 4, 4, 0, 4, 0],
  [0, 1, 0, 3, 1, 0, 3, 0, 0, 1, 0, 4, 1, 0, 4, 0],
  [0, 1, 0, 4, 1, 0, 4, 0, 0, 2, 0, 4, 2, 0, 4, 0],
  [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 3, 0, 0, 3, 0],
  [0, 2, 0, 0, 2, 0, 0, 0, 0, 1, 0, 3, 1, 0, 3, 0],
  [0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 3, 2, 0, 3, 0],
  [0, 2, 0, 0, 2, 0, 0, 0, 0, 3, 0, 3, 3, 0, 3, 0],
  [0, 2, 0, 0, 2, 0, 0, 0, 0, 4, 0, 3, 4, 0, 3, 0],
  [0, 2, 0, 1, 2, 0, 1, 0, 0, 0, 0, 3, 0, 0, 3, 0],
  [0, 2, 0, 2, 2, 0, 2, 0, 0, 0, 0, 3, 0, 0, 3, 0],
  [0, 2, 0, 3, 2, 0, 3, 0, 0, 0, 0, 3, 0, 0, 3, 0],
  [0, 2, 0, 4, 2, 0, 4, 0, 0, 0, 0, 3, 0, 0, 3, 0],
  [1, 0, 1, 0, 0, 1, 0, 1, 3, 0, 4, 0, 0, 3, 0, 4],
  [1, 0, 1, 0, 0, 4, 0, 4, 3, 0, 4, 0, 0, 2, 0, 1],
  [1, 0, 2, 0, 0, 1, 0, 2, 4, 0, 4, 0, 0, 4, 0, 4],
  [1, 0, 2, 0, 0, 4, 0, 3, 4, 0, 4, 0, 0, 1, 0, 1],
  [1, 0, 3, 0, 0, 1, 0, 3, 1, 0, 4, 0, 0, 1, 0, 4],
  [1, 0, 3, 0, 0, 4, 0, 2, 1, 0, 4, 0, 0, 4, 0, 1],
  [1, 0, 4, 0, 0, 1, 0, 4, 2, 0, 4, 0, 0, 2, 0, 4],
  [1, 0, 4, 0, 0, 4, 0, 1, 2, 0, 4, 0, 0, 3, 0, 1],
  [1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 4, 4, 1, 4, 4, 1],
  [1, 1, 2, 2, 1, 4, 2, 3, 3, 3, 4, 4, 3, 2, 4, 1],
  [1, 1, 3, 3, 1, 4, 3, 2, 2, 2, 4, 4, 2, 3, 4, 1],
  [1, 1, 4, 4, 1, 4, 4, 1, 4, 4, 4, 4, 4, 1, 4, 1],
  [1, 4, 1, 4, 4, 4, 4, 4, 1, 4, 4, 1, 4, 4, 1, 1],
  [1, 4, 2, 3, 4, 4, 3, 3, 3, 2, 4, 1, 2, 2, 1, 1],
  [1, 4, 3, 2, 4, 4, 2, 2, 2, 3, 4, 1, 3, 3, 1, 1],
  [1, 4, 4, 1, 4, 4, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1],
  [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0, 0, 0, 3],
  [2, 0, 0, 0, 0, 2, 0, 0, 1, 0, 3, 0, 0, 1, 0, 3],
  [2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 3, 0, 0, 2, 0, 3],
  [2, 0, 0, 0, 0, 2, 0, 0, 3, 0, 3, 0, 0, 3, 0, 3],
  [2, 0, 0, 0, 0, 2, 0, 0, 4, 0, 3, 0, 0, 4, 0, 3],
  [2, 0, 0, 0, 0, 3, 0, 0, 0, 0, 3, 0, 0, 0, 0, 2],
  [2, 0, 0, 0, 0, 3, 0, 0, 1, 0, 3, 0, 0, 4, 0, 2],
  [2, 0, 0, 0, 0, 3, 0, 0, 2, 0, 3, 0, 0, 3, 0, 2],
  [2, 0, 0, 0, 0, 3, 0, 0, 3, 0, 3, 0, 0, 2, 0, 2],
  [2, 0, 0, 0, 0, 3, 0, 0, 4, 0, 3, 0, 0, 1, 0, 2],
  [2, 0, 1, 0, 0, 2, 0, 1, 0, 0, 3, 0, 0, 0, 0, 3],
  [2, 0, 1, 0, 0, 3, 0, 4, 0, 0, 3, 0, 0, 0, 0, 2],
  [2, 0, 2, 0, 0, 2, 0, 2, 0, 0, 3, 0, 0, 0, 0, 3],
  [2, 0, 2, 0, 0, 3, 0, 3, 0, 0, 3, 0, 0, 0, 0, 2],
  [2, 0, 3, 0, 0, 2, 0, 3, 0, 0, 3, 0, 0, 0, 0, 3],
  [2, 0, 3, 0, 0, 3, 0, 2, 0, 0, 3, 0, 0, 0, 0, 2],
  [2, 0, 4, 0, 0, 2, 0, 4, 0, 0, 3, 0, 0, 0, 0, 3],
  [2, 0, 4, 0, 0, 3, 0, 1, 0, 0, 3, 0, 0, 0, 0, 2],
  [2, 2, 1, 1, 2, 3, 1, 4, 3, 3, 3, 3, 3, 2, 3, 2],
  [2, 2, 2, 2, 2, 3, 2, 3, 4, 4, 3, 3, 4, 1, 3, 2],
  [2, 2, 3, 3, 2, 3, 3, 2, 1, 1, 3, 3, 1, 4, 3, 2],
  [2, 2, 4, 4, 2, 3, 4, 1, 2, 2, 3, 3, 2, 3, 3, 2],
  [2, 3, 1, 4, 3, 3, 4, 4, 3, 2, 3, 2, 2, 2, 2, 2],
  [2, 3, 2, 3, 3, 3, 3, 3, 4, 1, 3, 2, 1, 1, 2, 2],
  [2, 3, 3, 2, 3, 3, 2, 2, 1, 4, 3, 2, 4, 4, 2, 2],
  [2, 3, 4, 1, 3, 3, 1, 1, 2, 3, 3, 2, 3, 3, 2, 2]
]

private def idx (s : Fin 2 ⊕ Fin 2) : ℕ :=
  match s with
  | Sum.inl i => (i : ℕ)
  | Sum.inr i => 2 + (i : ℕ)

private def mat (i : Fin 66) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 5) :=
  Matrix.of fun r c => ((psp5Data.getD (i : ℕ) []).getD (4 * idx r + idx c) 0 : ZMod 5)

set_option maxRecDepth 1000000 in
private theorem mat_symplectic_all : ∀ i : Fin 66,
    (mat i)ᵀ * formJ 2 (ZMod 5) * mat i = formJ 2 (ZMod 5) := by
  decide +kernel

set_option maxRecDepth 1000000 in
private theorem mat_sq_all : ∀ i : Fin 66, mat i * mat i = -1 := by
  decide +kernel

set_option maxRecDepth 1000000 in
private theorem mat_comm_all : ∀ i : Fin 66,
    mat i * kron 1 J₁ = kron 1 J₁ * mat i ∨
      mat i * kron 1 J₁ = -(kron 1 J₁ * mat i) := by
  decide +kernel

set_option maxRecDepth 1000000 in
private theorem mat_distinct_all : ∀ i j : Fin 66, i ≠ j →
    mat i ≠ mat j ∧ mat i ≠ -mat j := by
  decide +kernel

private noncomputable def S (i : Fin 66) : StatedSp 2 (ZMod 5) :=
  toSp (mat i) (mat_symplectic_all i)

private noncomputable def c (i : Fin 66) : StatedProj (StatedSp 2 (ZMod 5)) := proj 2 (ZMod 5) (S i)

private noncomputable def negS : StatedSp 2 (ZMod 5) := toSp (-1) (by decide +kernel)

private theorem proj_negS : proj 2 (ZMod 5) negS = 1 := by
  rw [← MonoidHom.mem_ker, ker_proj]
  exact (mem_spScalars_iff _).mpr (Or.inr rfl)

private theorem c_mem_centralizer (i : Fin 66) :
    c i ∈ centralizer ({u2 (ZMod 5)} : Set (StatedProj (StatedSp 2 (ZMod 5)))) := by
  rw [mem_centralizer_singleton_iff]
  change proj 2 (ZMod 5) (S i) * proj 2 (ZMod 5) (T2 (ZMod 5)) =
    proj 2 (ZMod 5) (T2 (ZMod 5)) * proj 2 (ZMod 5) (S i)
  rw [← map_mul, ← map_mul]
  rcases mat_comm_all i with h | h
  · rw [show S i * T2 (ZMod 5) = T2 (ZMod 5) * S i from by
        apply sp_ext
        simp only [Subgroup.coe_mul, Units.val_mul, S, coe_toSp, coe_T2]
        exact h]
  · rw [show S i * T2 (ZMod 5) = negS * (T2 (ZMod 5) * S i) from by
        apply sp_ext
        simp only [Subgroup.coe_mul, Units.val_mul, S, coe_toSp, coe_T2, negS, coe_toSp]
        rw [h]
        exact (neg_one_mul _).symm,
      map_mul, proj_negS, one_mul]

private theorem c_sq (i : Fin 66) : c i ^ 2 = 1 := by
  have hmem : S i * S i ∈ spScalars 2 (ZMod 5) := by
    rw [mem_spScalars_iff]
    right
    simp only [Subgroup.coe_mul, Units.val_mul, S, coe_toSp]
    exact mat_sq_all i
  have h1 : proj 2 (ZMod 5) (S i * S i) = 1 := by
    rw [← MonoidHom.mem_ker, ker_proj]
    exact hmem
  change (proj 2 (ZMod 5) (S i)) ^ 2 = 1
  rw [pow_two, ← map_mul]
  exact h1

private theorem u2_ne_one : u2 (ZMod 5) ≠ 1 := by
  intro h
  have hmem : T2 (ZMod 5) ∈ spScalars 2 (ZMod 5) := by
    rw [← ker_proj, MonoidHom.mem_ker]
    exact h
  rw [mem_spScalars_iff] at hmem
  have hL : (kron 1 J₁ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 5))
      (Sum.inl 0) (Sum.inl 1) = 1 := by decide
  rcases hmem with h1 | h1
  · have hR : ((1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 5))
        (Sum.inl 0) (Sum.inl 1)) = 0 := by decide
    have hh := congrFun (congrFun h1 (Sum.inl 0)) (Sum.inl 1)
    exact (by decide : (1 : ZMod 5) ≠ 0) (hL.symm.trans (hh.trans hR))
  · have hR : ((-1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 5))
        (Sum.inl 0) (Sum.inl 1)) = 0 := by decide
    have hh := congrFun (congrFun h1 (Sum.inl 0)) (Sum.inl 1)
    exact (by decide : (1 : ZMod 5) ≠ 0) (hL.symm.trans (hh.trans hR))

private theorem c_conj (i : Fin 66) : IsConj (u2 (ZMod 5)) (c i) := by
  obtain ⟨g, hg⟩ := exists_conj_T2 (K := ZMod 5) (by decide : (2 : ZMod 5) ≠ 0) (S i)
    (by
      rw [show ((S i : GL (Fin 2 ⊕ Fin 2) (ZMod 5)) :
            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 5)) =
          mat i from coe_toSp (mat i) (mat_symplectic_all i)]
      exact mat_sq_all i)
  rw [isConj_iff]
  refine ⟨proj 2 (ZMod 5) g, ?_⟩
  have h2 : (proj 2 (ZMod 5) g)⁻¹ * c i * proj 2 (ZMod 5) g = u2 (ZMod 5) := by
    change (proj 2 (ZMod 5) g)⁻¹ * proj 2 (ZMod 5) (S i) * proj 2 (ZMod 5) g =
      proj 2 (ZMod 5) (T2 (ZMod 5))
    rw [← map_inv, ← map_mul, ← map_mul, hg]
  calc proj 2 (ZMod 5) g * u2 (ZMod 5) * (proj 2 (ZMod 5) g)⁻¹
      = proj 2 (ZMod 5) g * ((proj 2 (ZMod 5) g)⁻¹ * c i * proj 2 (ZMod 5) g) *
          (proj 2 (ZMod 5) g)⁻¹ := by rw [h2]
    _ = c i := by group

private theorem c_ne_one (i : Fin 66) : c i ≠ 1 := by
  intro h
  have hconj : IsConj (u2 (ZMod 5)) (1 : StatedProj (StatedSp 2 (ZMod 5))) := h ▸ c_conj i
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  have hu2 : u2 (ZMod 5) = 1 := by
    calc u2 (ZMod 5) = g⁻¹ * (g * u2 (ZMod 5) * g⁻¹) * g := by group
      _ = 1 := by rw [hg]; group
  exact u2_ne_one hu2

private theorem c_injective : Function.Injective c := by
  intro i j hij
  by_contra hne
  have hdist := mat_distinct_all i j hne
  have hproj : proj 2 (ZMod 5) (S i) = proj 2 (ZMod 5) (S j) := hij
  rcases eq_or_eq_neg_of_proj_eq hproj with h | h
  · exact hdist.1 (by simpa only [S, coe_toSp] using h.symm)
  · apply hdist.2
    show ((S i : GL (Fin 2 ⊕ Fin 2) (ZMod 5)) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 5)) =
      -((S j : GL (Fin 2 ⊕ Fin 2) (ZMod 5)) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 5))
    rw [h]
    exact (neg_neg _).symm

theorem psp5_u2_count :
    47 ≤ Set.ncard {c : StatedProj (StatedSp 2 (ZMod 5)) |
      c ∈ centralizer ({u2 (ZMod 5)} : Set (StatedProj (StatedSp 2 (ZMod 5)))) ∧ c ^ 2 = 1 ∧
        c ≠ 1 ∧ IsConj (u2 (ZMod 5)) c} := by
  let T : Set (StatedProj (StatedSp 2 (ZMod 5))) :=
    {c | c ∈ centralizer ({u2 (ZMod 5)} : Set (StatedProj (StatedSp 2 (ZMod 5)))) ∧ c ^ 2 = 1 ∧
        c ≠ 1 ∧ IsConj (u2 (ZMod 5)) c}
  change 47 ≤ T.ncard
  have hsub : Set.image c Set.univ ⊆ T := by
    rintro _ ⟨i, -, rfl⟩
    exact ⟨c_mem_centralizer i, c_sq i, c_ne_one i, c_conj i⟩
  have hcard : (Set.image c Set.univ).ncard = 66 := by
    rw [Set.ncard_image_of_injective _ c_injective, Set.ncard_univ, Nat.card_fin]
  have hle : 66 ≤ T.ncard := by
    rw [← hcard]
    exact Set.ncard_le_ncard hsub
  exact le_trans (by norm_num : 47 ≤ 66) hle

end CFSG.EvenSporadicStandard.HNRecog.Harada
