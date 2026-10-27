module

public import CFSG.LieType.Universal.Spin.PlusCT.Basic

public section

namespace CFSG.LieType.Universal.Spin

open CliffordAlgebra QuadraticMap CFSG.LieType.RootSystem CFSG.LieType.CurtisTits CoxeterSystem
open CFSG.LieType.Universal.Spin.PlusCT

variable {n : ℕ} {K : Type} [Field K]

theorem plusDatum_n_mem (hn : 3 ≤ n) : ∀ i, weylD K hn i ∈ rankOne (plusRootGroup n K hn) i :=
  fun k => rankOneD_mem_rankOne hn k (weylSL2 1)

theorem plusDatum_H_le (hn : 3 ≤ n) :
    ∀ i, (torusD K hn i).range ≤ rankOne (plusRootGroup n K hn) i := by
  rintro k _ ⟨τ, rfl⟩
  exact rankOneD_mem_rankOne hn k (diagSL2 τ)

theorem plusDatum_sq_mem (hn : 3 ≤ n) : ∀ i, weylD K hn i ^ 2 ∈ (torusD K hn i).range :=
  fun k => ⟨-1, by rw [pow_two, weylD_mul_self]⟩

theorem plusDatum_conj_mem (hn : 3 ≤ n) :
    ∀ i, ∀ γ ∈ roots (isFiniteType_cartanD n) ∅, ∀ x ∈ plusRootGroup n K hn γ,
      weylD K hn i * x * (weylD K hn i)⁻¹ ∈ plusRootGroup n K hn
        (weylAction (isFiniteType_cartanD n)
          ((coxeterMatrix (isFiniteType_cartanD n)).toCoxeterSystem.simple i) γ) := by
  intro k γ hγ x hx
  obtain ⟨i, j, hij, s, t, hγ', -⟩ := exists_plusRootGroup_eq (K := K) hn hγ
  obtain ⟨c, rfl⟩ := (mem_plusRootGroup_iff hn hij s t hγ').mp hx
  rw [weylAction_simple, weylD_conj_longRoot]
  exact longRoot_mem_plusRootGroup hn _ _ _ (toStdD_reflection_eq (by omega) k hγ') _

theorem plusDatum_H_conj_mem (hn : 3 ≤ n) :
    ∀ k, ∀ γ ∈ roots (isFiniteType_cartanD n) ∅, ∀ h ∈ (torusD K hn k).range,
      ∀ x ∈ plusRootGroup n K hn γ, h * x * h⁻¹ ∈ plusRootGroup n K hn γ := by
  rintro k γ hγ _ ⟨τ, rfl⟩ x hx
  obtain ⟨i, j, hij, s, t, hγ', -⟩ := exists_plusRootGroup_eq (K := K) hn hγ
  obtain ⟨c, rfl⟩ := (mem_plusRootGroup_iff hn hij s t hγ').mp hx
  rw [torusD_conj_longRoot]
  exact longRoot_mem_plusRootGroup hn hij s t hγ' _

theorem plusDatum_conj_H_mem (hn : 3 ≤ n) :
    ∀ j k, ∀ h ∈ (torusD K hn k).range,
      weylD K hn j * h * (weylD K hn j)⁻¹ ∈ (torusD K hn j).range ⊔ (torusD K hn k).range := by
  rintro j k _ ⟨τ, rfl⟩
  exact weylD_conj_torusD_mem K hn j k τ

theorem plusDatum_le_rankOne (hn : 3 ≤ n) :
    ∀ i, ∀ γ ∈ roots (isFiniteType_cartanD n) ∅, (∀ k, k ≠ i → γ k = 0) →
      plusRootGroup n K hn γ ≤ rankOne (plusRootGroup n K hn) i := by
  intro i γ hγ hsupp
  obtain ⟨c, rfl⟩ : ∃ c : ℤ, γ = c • Pi.single i 1 := by
    refine ⟨γ i, funext fun k => ?_⟩
    by_cases hk : k = i
    · subst hk
      simp
    · simp [hsupp k hk, hk]
  obtain ⟨p, q, hpq, s, t, hγ', -⟩ := exists_plusRootGroup_eq (K := K) hn hγ
  have hval : toStdD n (c • Pi.single i 1) (rootIdxD n i) = c := by
    rw [toStdD_smul, toStdD_single_eq (by omega), Pi.smul_apply,
      single_add_single_apply_left (rootIdxD_ne n (by omega) i), boolSign_true, smul_eq_mul,
      mul_one]
  have hmem := single_add_single_apply_mem hpq s t (rootIdxD n i)
  rw [← hγ', hval] at hmem
  have hne : c ≠ 0 := by
    rintro rfl
    have h1 := congrFun hγ' p
    rw [zero_smul, toStdD_zero, Pi.zero_apply, single_add_single_apply_left hpq] at h1
    exact boolSign_ne_zero s h1.symm
  rcases hmem with h | h | h
  · exact absurd h hne
  · rw [h, one_smul]
    exact le_sup_left
  · rw [h, neg_one_zsmul]
    exact le_sup_right

private theorem coxeterMatrix_cartanD_apply (i j : Fin n) :
    coxeterMatrix (isFiniteType_cartanD n) i j =
      TauCeti.coxeterOrder (cartanD n i j * cartanD n j i) :=
  TauCeti.coxeterMatrixOfCartanMatrix_apply _ _ _ i j

private theorem coxeterMatrix_cartanD_of_adj {i j : Fin n} (hij : i ≠ j)
    (h : (i.val + 1 = j.val ∧ j.val + 1 < n) ∨ (j.val + 1 = i.val ∧ i.val + 1 < n) ∨
      (i.val + 3 = n ∧ j.val + 1 = n) ∨ (j.val + 3 = n ∧ i.val + 1 = n)) :
    coxeterMatrix (isFiniteType_cartanD n) i j = 3 := by
  have h' : (j.val + 1 = i.val ∧ i.val + 1 < n) ∨ (i.val + 1 = j.val ∧ j.val + 1 < n) ∨
      (j.val + 3 = n ∧ i.val + 1 = n) ∨ (i.val + 3 = n ∧ j.val + 1 = n) := by
    rcases h with h | h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inr (Or.inl h))
  have h1 : cartanD n i j = -1 := by
    simp only [cartanD, Matrix.of_apply, ite_eq_right hij, ite_eq_left h]
  have h2 : cartanD n j i = -1 := by
    simp only [cartanD, Matrix.of_apply, ite_eq_right (Ne.symm hij), ite_eq_left h']
  rw [coxeterMatrix_cartanD_apply, h1, h2, show (-1 : ℤ) * -1 = 1 by norm_num,
    TauCeti.coxeterOrder_one]

private theorem coxeterMatrix_cartanD_of_not_adj {i j : Fin n} (hij : i ≠ j)
    (h : ¬((i.val + 1 = j.val ∧ j.val + 1 < n) ∨ (j.val + 1 = i.val ∧ i.val + 1 < n) ∨
      (i.val + 3 = n ∧ j.val + 1 = n) ∨ (j.val + 3 = n ∧ i.val + 1 = n))) :
    coxeterMatrix (isFiniteType_cartanD n) i j = 2 := by
  have h1 : cartanD n i j = 0 := by
    simp only [cartanD, Matrix.of_apply, ite_eq_right hij, ite_eq_right h]
  rw [coxeterMatrix_cartanD_apply, h1, zero_mul, TauCeti.coxeterOrder_zero]

theorem plusDatum_braid (hn : 3 ≤ n) :
    ∀ i j, ((braidWord (coxeterMatrix (isFiniteType_cartanD n)) i j).map (weylD K hn)).prod =
      ((braidWord (coxeterMatrix (isFiniteType_cartanD n)) j i).map (weylD K hn)).prod := by
  intro i j
  by_cases hij : i = j
  · rw [hij]
  have hsymm := (coxeterMatrix (isFiniteType_cartanD n)).symmetric j i
  rw [braidWord, braidWord, hsymm]
  by_cases hadj : (i.val + 1 = j.val ∧ j.val + 1 < n) ∨ (j.val + 1 = i.val ∧ i.val + 1 < n) ∨
      (i.val + 3 = n ∧ j.val + 1 = n) ∨ (j.val + 3 = n ∧ i.val + 1 = n)
  · rw [show (coxeterMatrix (isFiniteType_cartanD n)).M i j = 3 from
      coxeterMatrix_cartanD_of_adj hij hadj]
    show ([j, i, j].map (weylD K hn)).prod = ([i, j, i].map (weylD K hn)).prod
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, ← mul_assoc]
    rcases hadj with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact (weylD_braid_of_succ K hn h1 h2).symm
    · exact weylD_braid_of_succ K hn h1 h2
    · exact (weylD_braid_last K hn h1 h2).symm
    · exact weylD_braid_last K hn h1 h2
  · rw [show (coxeterMatrix (isFiniteType_cartanD n)).M i j = 2 from
      coxeterMatrix_cartanD_of_not_adj hij hadj]
    show ([i, j].map (weylD K hn)).prod = ([j, i].map (weylD K hn)).prod
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    exact (weylD_commute K hn hij (fun h => hadj (Or.inl h)) (fun h => hadj (Or.inr (Or.inl h)))
      (fun h => hadj (Or.inr (Or.inr (Or.inl h)))) (fun h => hadj (Or.inr (Or.inr (Or.inr h))))).eq

theorem plusDatum_isCTGroupDatum (hn : 3 ≤ n)
    (hgen : ⨆ γ ∈ roots (isFiniteType_cartanD n) ∅, plusRootGroup n K hn γ = ⊤) :
    IsCTGroupDatum (coxeterMatrix (isFiniteType_cartanD n)).toCoxeterSystem
      (weylAction (isFiniteType_cartanD n)) (roots (isFiniteType_cartanD n) ∅)
      (plusRootGroup n K hn) (weylD K hn) (fun k => (torusD K hn k).range) where
  n_mem := plusDatum_n_mem hn
  conj_mem := plusDatum_conj_mem hn
  braid := plusDatum_braid hn
  H_le := plusDatum_H_le hn
  sq_mem := plusDatum_sq_mem hn
  H_conj_mem := plusDatum_H_conj_mem hn
  conj_H_mem := plusDatum_conj_H_mem hn
  le_rankOne := plusDatum_le_rankOne hn
  iSup_eq_top := hgen

end CFSG.LieType.Universal.Spin
