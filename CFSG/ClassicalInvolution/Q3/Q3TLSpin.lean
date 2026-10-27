module

public import CFSG.ClassicalInvolution.Orders.OrthogonalNeg
public import CFSG.ClassicalInvolution.Q3.Q3TLLin
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalWittFlags
import TauCeti.Algebra.Group.Units.Basic

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T

open TauCeti QuadraticMap CliffordAlgebra CFSG.ClassicalGroups.Orthogonal
  CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.ModelFacts
open Module CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.Orthogonal.Small

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  [FiniteDimensional K V]

theorem isSquare_prod_of_prod_reflect_mem [Finite K] [Invertible (2 : K)]
    (hQ : (polarBilin Q).Nondegenerate) {P₁ P₂ P₃ : HypPair Q} (h₁₂ : P₁.Orth P₂)
    (h₁₃ : P₁.Orth P₃) (h₂₃ : P₂.Orth P₃) {l : List V} (hl0 : ∀ a ∈ l, Q a ≠ 0)
    (hmem : (l.map (reflect Q)).prod ∈ elementaryGroup Q) : IsSquare (l.map Q).prod := by
  classical
  have hQ' : Q.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mp hQ
  have hgO : (l.map (reflect Q)).prod ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    elementaryGroup_le_orthogonalGroup Q hmem
  obtain ⟨-, hiff⟩ := orthogonalGroup_index_four hQ h₁₂ h₁₃ h₂₃
  have hΦ := (hiff ⟨_, hgO⟩).1 hmem
  rw [detSpinorNorm_apply] at hΦ
  have hθ1 : orthogonalSpinorNorm Q hQ' ⟨_, hgO⟩ = 1 := congrArg Prod.snd hΦ
  let reflO : V → TauCeti.QuadraticMap.orthogonalGroup Q :=
    fun v => ⟨reflect Q v, reflect_mem_orthogonalGroup Q v⟩
  let unitQ : V → Kˣ := fun v => if h : Q v = 0 then 1 else Units.mk0 (Q v) h
  have hgprod : (⟨_, hgO⟩ : TauCeti.QuadraticMap.orthogonalGroup Q) = (l.map reflO).prod := by
    apply Subtype.ext
    rw [Subgroup.val_list_prod, List.map_map]
    rfl
  have hfactor : ∀ v ∈ l, orthogonalSpinorNorm Q hQ' (reflO v) = squareClassHom (unitQ v) := by
    intro v hv
    have hv0 : Q v ≠ 0 := hl0 v hv
    let _ : Invertible (Q v) := invertibleOfNonzero hv0
    have hr : reflO v = TauCeti.QuadraticMap.reflectionOrthogonal Q v :=
      Subtype.ext (coe_reflectionOrthogonal_eq_reflect v).symm
    rw [hr, orthogonalSpinorNorm_reflectionOrthogonal]
    congr 1
    apply Units.ext
    simp [unitQ, hv0]
  have hθ : orthogonalSpinorNorm Q hQ' (l.map reflO).prod =
      squareClassHom (l.map unitQ).prod := by
    rw [map_list_prod, map_list_prod, List.map_map, List.map_map]
    congr 1
    exact List.map_congr_left fun v hv => hfactor v hv
  rw [hgprod, hθ] at hθ1
  have hker : (l.map unitQ).prod ∈ (squareClassHom (K := K)).ker := hθ1
  rw [ker_squareClassHom, Subgroup.mem_square, ← isSquare_units_val_iff] at hker
  have hval : (((l.map unitQ).prod : Kˣ) : K) = (l.map Q).prod := by
    have := map_list_prod (Units.coeHom K) (l.map unitQ)
    rw [List.map_map] at this
    change (((l.map unitQ).prod : Kˣ) : K) = _ at this
    rw [this]
    congr 1
    refine List.map_congr_left fun v hv => ?_
    simp [unitQ, hl0 v hv]
  rwa [hval] at hker

omit [FiniteDimensional K V] in
theorem linearIndependent_get_of_pairwise (h2 : (2 : K) ≠ 0) {l : List V}
    (hl0 : ∀ a ∈ l, Q a ≠ 0) (hpair : l.Pairwise (fun u v => polar Q u v = 0)) :
    LinearIndependent K l.get := by
  have hortho : LinearMap.BilinForm.iIsOrtho (polarBilin Q) l.get := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact List.pairwise_iff_get.1 hpair i j h
    · change polar Q (l.get i) (l.get j) = 0
      rw [polar_comm]
      exact List.pairwise_iff_get.1 hpair j i h
  refine LinearMap.BilinForm.linearIndependent_of_iIsOrtho hortho fun i => ?_
  change polar Q (l.get i) (l.get i) ≠ 0
  rw [QuadraticMap.polar_self, nsmul_eq_mul, Nat.cast_ofNat]
  exact mul_ne_zero h2 (hl0 _ (List.get_mem l i))

def pmList {m : ℕ} (P : Fin m → HypPair Q) : List V :=
  (List.finRange m).map (fun i => (P i).e + (1 : K) • (P i).f) ++
    (List.finRange m).map (fun i => (P i).e + (-1 : K) • (P i).f)

omit [FiniteDimensional K V] in
theorem pmList_map_ne_zero {m : ℕ} {P : Fin m → HypPair Q} (a : V) (ha : a ∈ pmList P) :
    Q a ≠ 0 := by
  simp only [pmList, List.mem_append, List.mem_map] at ha
  rcases ha with ⟨i, -, rfl⟩ | ⟨i, -, rfl⟩
  · rw [map_hypPair_add_smul]
    exact one_ne_zero
  · rw [map_hypPair_add_smul]
    exact neg_ne_zero.2 one_ne_zero

omit [FiniteDimensional K V] in
theorem pmList_pairwise {m : ℕ} {P : Fin m → HypPair Q} (hP : ∀ i j, i ≠ j → (P i).Orth (P j)) :
    (pmList P).Pairwise (fun u v => polar Q u v = 0) := by
  have hf : ∀ ε δ : K, ∀ i j : Fin m, i ≠ j →
      polar Q ((P i).e + ε • (P i).f) ((P j).e + δ • (P j).f) = 0 := fun ε δ i j hij =>
    CFSG.ClassicalInvolution.polar_hyp_hyp_of_orth (hP i j hij) ε δ
  rw [pmList, List.pairwise_append]
  refine ⟨?_, ?_, ?_⟩
  · refine List.pairwise_map.2 (List.Nodup.pairwise_of_forall_ne (List.nodup_finRange m) ?_)
    intro i _ j _ hij
    exact hf 1 1 i j hij
  · refine List.pairwise_map.2 (List.Nodup.pairwise_of_forall_ne (List.nodup_finRange m) ?_)
    intro i _ j _ hij
    exact hf (-1) (-1) i j hij
  · intro x hx y hy
    simp only [List.mem_map] at hx hy
    obtain ⟨i, -, rfl⟩ := hx
    obtain ⟨j, -, rfl⟩ := hy
    by_cases hij : i = j
    · subst hij
      exact CFSG.ClassicalInvolution.polar_hyp_add_hyp_sub (P i)
    · exact hf 1 (-1) i j hij

omit [FiniteDimensional K V] in
theorem pmList_length {m : ℕ} {P : Fin m → HypPair Q} : (pmList P).length = 2 * m := by
  simp [pmList, two_mul]

omit [FiniteDimensional K V] in
theorem pmList_prod_map {m : ℕ} {P : Fin m → HypPair Q} : ((pmList P).map Q).prod = (-1) ^ m := by
  rw [pmList, List.map_append, List.prod_append, List.map_map, List.map_map]
  have h1 : (List.map (⇑Q ∘ fun i => (P i).e + (1 : K) • (P i).f) (List.finRange m)).prod = 1 := by
    refine List.prod_eq_one fun x hx => ?_
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    exact map_hypPair_add_smul (P i) 1
  have h2 : (List.map (⇑Q ∘ fun i => (P i).e + (-1 : K) • (P i).f) (List.finRange m)).prod =
      (-1) ^ m := by
    have : List.map (⇑Q ∘ fun i => (P i).e + (-1 : K) • (P i).f) (List.finRange m) =
        List.replicate m (-1 : K) := by
      refine List.eq_replicate_iff.2 ⟨by simp, fun x hx => ?_⟩
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
      exact map_hypPair_add_smul (P i) (-1)
    rw [this, List.prod_replicate]
  rw [h1, h2, one_mul]

theorem eq_prod_reflect_hypList (h2 : (2 : K) ≠ 0) {i : V ≃ₗ[K] V}
    (hi : i ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hii : i * i = 1) {k : ℕ}
    (hdim : finrank K (minusSp i) = 2 * k) {P : Fin k → HypPair Q}
    (hPm : ∀ j, (P j).e ∈ minusSp i ∧ (P j).f ∈ minusSp i)
    (hP : ∀ j j', j ≠ j' → (P j).Orth (P j')) :
    i = ((pmList P).map (reflect Q)).prod := by
  set l := pmList P with hl
  have hl0 : ∀ a ∈ l, Q a ≠ 0 := pmList_map_ne_zero
  have hpair := pmList_pairwise hP
  have hlm : ∀ a ∈ l, a ∈ minusSp i := by
    intro a ha
    simp only [hl, pmList, List.mem_append, List.mem_map] at ha
    rcases ha with ⟨j, -, rfl⟩ | ⟨j, -, rfl⟩ <;>
      exact Submodule.add_mem _ (hPm j).1 (Submodule.smul_mem _ _ (hPm j).2)
  have hset : {v | v ∈ l} = Set.range l.get := by
    ext v
    simp [List.mem_iff_get]
  have hspan : Submodule.span K {v | v ∈ l} = minusSp i := by
    refine Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.mpr hlm) ?_
    rw [hset, finrank_span_eq_card (linearIndependent_get_of_pairwise h2 hl0 hpair),
      Fintype.card_fin, hl, pmList_length, hdim]
  have hneg : ∀ w ∈ minusSp i, (l.map (reflect Q)).prod w = -w := by
    intro w hw
    rw [← hspan] at hw
    induction hw using Submodule.span_induction with
    | mem x hx => exact CFSG.ClassicalInvolution.prod_map_reflect_apply_of_mem hl0 hpair hx
    | zero => rw [map_zero, neg_zero]
    | add x y _ _ hx hy => rw [map_add, hx, hy, neg_add]
    | smul c x _ hx => rw [map_smul, hx, smul_neg]
  refine LinearEquiv.ext fun x => ?_
  obtain ⟨u, hu, w, hw, rfl⟩ := exists_add_of_isCompl' (isCompl_plusSp_minusSp h2 hii) x
  have hfix : (l.map (reflect Q)).prod u = u :=
    CFSG.ClassicalInvolution.prod_map_reflect_apply_of_forall_polar_eq_zero fun a ha => by
      rw [polar_comm]
      exact polar_plusSp_minusSp h2 hi hu (hlm a ha)
  rw [map_add, map_add, hfix, hneg w hw, mem_plusSp.mp hu, mem_minusSp.mp hw]

theorem even_of_mem_elementaryGroup [Finite K] (hK : Nat.card K = 3)
    (hQ : (polarBilin Q).Nondegenerate) {P₁ P₂ P₃ : HypPair Q} (h₁₂ : P₁.Orth P₂)
    (h₁₃ : P₁.Orth P₃) (h₂₃ : P₂.Orth P₃) {i : V ≃ₗ[K] V} (hiE : i ∈ elementaryGroup Q)
    (hii : i * i = 1) {k : ℕ} (hdim : finrank K (minusSp i) = 2 * k) {U : Submodule K V}
    (hUle : U ≤ minusSp i) (hU : ∀ x ∈ U, Q x = 0) (hUk : k ≤ finrank K U) : Even k := by
  obtain ⟨-, h2⟩ := three_eq_zero_two_ne_zero_of_card_eq_three hK
  let _ : Invertible (2 : K) := invertibleOfNonzero h2
  have hi : i ∈ TauCeti.QuadraticMap.orthogonalGroup Q := elementaryGroup_le_orthogonalGroup Q hiE
  have hc := isCompl_plusSp_minusSp h2 hii
  have horth' : ∀ u ∈ minusSp i, ∀ w ∈ plusSp i, polar Q u w = 0 := fun u hu w hw => by
    rw [polar_comm]
    exact polar_plusSp_minusSp h2 hi hw hu
  obtain ⟨P, hPm, hP, -⟩ := exists_hypPairs_of_flag k (minusSp i)
    (polarNondegOn_of_isCompl hQ hc.symm horth') hdim U hUle hU hUk 0 (Nat.zero_le k) (fun _ => ⊥)
    bot_le (fun j hj => by rw [Nat.le_zero.mp hj, finrank_bot]) (fun j hj => absurd hj (by omega))
    (fun x hx => by rw [(Submodule.mem_bot K).mp hx, QuadraticMap.map_zero])
  have hprod := eq_prod_reflect_hypList h2 hi hii hdim hPm hP
  have hsq := isSquare_prod_of_prod_reflect_mem hQ h₁₂ h₁₃ h₂₃ pmList_map_ne_zero (hprod ▸ hiE)
  rw [pmList_prod_map] at hsq
  by_contra hk
  rw [Nat.not_even_iff_odd] at hk
  rw [hk.neg_one_pow] at hsq
  exact not_isSquare_neg_one_of_card_three hK hsq

end CFSG.ClassicalInvolution.Q3.Q3T
