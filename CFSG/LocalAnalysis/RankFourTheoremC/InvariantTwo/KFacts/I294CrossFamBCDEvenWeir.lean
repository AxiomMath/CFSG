module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamBCDEvenSp
public import CFSG.GroupTheory.WeirSylow.Orthogonal

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open Subgroup CFSG.GroupTheory.WeirSylow Module QuadraticMap
open CFSG.LieType.Universal.Spin (quadPlus quadMinus)

section Types

variable {K : Type} [Field K] [Finite K]

private def minusHalfMap (n : ℕ) (K : Type) [Field K] :
    (Fin (n - 1) → K) →ₗ[K] (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) where
  toFun y := Sum.elim y (0 : Fin (n - 1) ⊕ Fin 2 → K)
  map_add' _ _ := by
    funext i
    rcases i with i | i <;> simp
  map_smul' _ _ := by
    funext i
    rcases i with i | i <;> simp

theorem isMinusType_quadMinus' {n : ℕ} (hn : 1 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : IsMinusType (quadMinus n K b c) := by
  refine ⟨?_, not_isPlusType_quadMinus hn hirr⟩
  have hj : Function.Injective (minusHalfMap n K) := fun x y hxy =>
    funext fun i => congrFun hxy (.inl i)
  refine ⟨LinearMap.range (minusHalfMap n K), ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj hj, Module.finrank_fin_fun, finrank_quadMinus_space hn]
    omega
  · rintro _ ⟨y, rfl⟩
    rw [CFSG.LieType.Universal.Spin.quadMinus_apply]
    simp [minusHalfMap]

theorem IsMinusType.of_isometryEquiv' {V V' : Type} [AddCommGroup V] [Module K V]
    [AddCommGroup V'] [Module K V'] {Q : QuadraticForm K V} {Q' : QuadraticForm K V'}
    (e : Q.IsometryEquiv Q') (h : IsMinusType Q) : IsMinusType Q' := by
  obtain ⟨⟨W, hW, hWs⟩, hnp⟩ := h
  refine ⟨⟨W.map e.toLinearEquiv.toLinearMap, ?_, ?_⟩, fun h' => hnp ((isPlusType_congr e).2 h')⟩
  · rw [LinearEquiv.finrank_map_eq, ← e.toLinearEquiv.finrank_eq]
    exact hW
  · rintro _ ⟨x, hx, rfl⟩
    change Q' (e x) = 0
    rw [e.map_app]
    exact hWs x hx

theorem isPlusType_or_isMinusType {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : QuadraticForm K V) (hQ : (polarBilin Q).Nondegenerate) {n : ℕ} (hn : 1 ≤ n)
    (hdim : finrank K V = 2 * n) : IsPlusType Q ∨ IsMinusType Q := by
  rcases exists_isometry_quadPlus_or_quadMinus Q hQ hn hdim with he | ⟨b, c, hirr, he⟩
  · obtain ⟨e⟩ := he
    exact Or.inl ((isPlusType_congr e).2 (isPlusType_quadPlus K n))
  · obtain ⟨e⟩ := he
    exact Or.inr (IsMinusType.of_isometryEquiv' e.symm (isMinusType_quadMinus' hn hirr))

end Types

section Rank

variable {p : ℕ} [hp : Fact p.Prime] {K : Type} [Field K] [Finite K]

theorem pRank_top_eq_of_sylow_mulEquiv {G G' : Type} [Group G] [Finite G] [Group G'] [Finite G']
    (P : Sylow p G) (P' : Sylow p G') (φ : P ≃* P') :
    CFSG.Open.pRank p (⊤ : Subgroup G) = CFSG.Open.pRank p (⊤ : Subgroup G') := by
  have h1 := (CFSG.SectionRank.pRank_sylow P).1
  have h2 := (CFSG.SectionRank.pRank_sylow P').1
  calc CFSG.Open.pRank p (⊤ : Subgroup G) = CFSG.Open.pRank p (P : Subgroup G) := h1.symm
    _ = CFSG.Open.pRank p (⊤ : Subgroup P) :=
        CFSG.SectionRank.pRank_eq_pRank_top_subgroup (P : Subgroup G)
    _ = CFSG.Open.pRank p (⊤ : Subgroup P') :=
        CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.out.one_lt φ
    _ = CFSG.Open.pRank p (P' : Subgroup G') :=
        (CFSG.SectionRank.pRank_eq_pRank_top_subgroup (P' : Subgroup G')).symm
    _ = CFSG.Open.pRank p (⊤ : Subgroup G') := h2

theorem le_pRank_statedSp {e : ℕ} (he : 0 < e) (hee : Even e) (hpe : p ∣ Nat.card K ^ e - 1)
    {k r : ℕ} (hk : k * e ≤ 2 * r) :
    k ≤ CFSG.Open.pRank p (⊤ : Subgroup (StatedSp r K)) := by
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.out.one_lt (statedSpEquiv r K)]
  exact BCDEven.le_pRank_isometryGroup he hee hpe k _
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.pairedSympForm_isAlt
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.pairedSympForm_nondegenerate
    (by rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.finrank_standard]; exact hk)

theorem le_pRank_orthogonalGroup_even (hp2 : p ≠ 2) (hpK : ¬ p ∣ Nat.card K) {e : ℕ} (he : 0 < e)
    (hee : Even e) (hpe : p ∣ Nat.card K ^ e - 1) {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : QuadraticForm K V) (hQ : (polarBilin Q).Nondegenerate)
    {n : ℕ} (hdim : finrank K V = 2 * n) {k : ℕ} (hk : k * e + 2 ≤ 2 * n) :
    k ≤ CFSG.Open.pRank p (⊤ : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)) := by
  haveI : Fintype K := Fintype.ofFinite K
  have hp1 : Odd p := hp.out.odd_of_ne_two hp2
  have hpK' : ¬ p ∣ Fintype.card K := by rwa [← Nat.card_eq_fintype_card]
  have hn : 1 ≤ n := by omega
  have hε : ∃ ε : ℤ, (ε = 1 ∧ IsPlusType Q) ∨ (ε = -1 ∧ IsMinusType Q) := by
    rcases isPlusType_or_isMinusType Q hQ hn hdim with h | h
    · exact ⟨1, Or.inl ⟨rfl, h⟩⟩
    · exact ⟨-1, Or.inr ⟨rfl, h⟩⟩
  obtain ⟨ε, hε⟩ := hε
  obtain ⟨P⟩ : Nonempty (Sylow p (TauCeti.QuadraticMap.orthogonalGroup Q)) := inferInstance
  obtain ⟨h1, h2, h3⟩ := sylow_orthogonal_even hp1 hpK' hn hdim Q hQ hε P
  rcases h3 with h3 | h3
  · obtain ⟨P'⟩ : Nonempty (Sylow p (StatedSp n K)) := inferInstance
    obtain ⟨φ⟩ := h1 h3 P'
    rw [pRank_top_eq_of_sylow_mulEquiv P P' φ]
    exact le_pRank_statedSp he hee hpe (by omega)
  · obtain ⟨P'⟩ : Nonempty (Sylow p (StatedSp (n - 1) K)) := inferInstance
    obtain ⟨φ⟩ := h2 h3 P'
    rw [pRank_top_eq_of_sylow_mulEquiv P P' φ]
    exact le_pRank_statedSp he hee hpe (by omega)

theorem le_pRank_orthogonalGroup_odd (hp2 : p ≠ 2) (hpK : ¬ p ∣ Nat.card K) {e : ℕ} (he : 0 < e)
    (hee : Even e) (hpe : p ∣ Nat.card K ^ e - 1) (hK : Odd (Nat.card K)) {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (Q : QuadraticForm K V)
    (hQ : (polarBilin Q).Nondegenerate) {n : ℕ} (hdim : finrank K V = 2 * n + 1) {k : ℕ}
    (hk : k * e ≤ 2 * n) :
    k ≤ CFSG.Open.pRank p (⊤ : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)) := by
  haveI : Fintype K := Fintype.ofFinite K
  have hp1 : Odd p := hp.out.odd_of_ne_two hp2
  have hpK' : ¬ p ∣ Fintype.card K := by rwa [← Nat.card_eq_fintype_card]
  have hK' : Odd (Fintype.card K) := by rwa [← Nat.card_eq_fintype_card]
  obtain ⟨P⟩ : Nonempty (Sylow p (TauCeti.QuadraticMap.orthogonalGroup Q)) := inferInstance
  obtain ⟨P'⟩ : Nonempty (Sylow p (StatedSp n K)) := inferInstance
  obtain ⟨φ⟩ := sylow_orthogonal_odd hp1 hK' hpK' hdim Q hQ P P'
  rw [pRank_top_eq_of_sylow_mulEquiv P P' φ]
  exact le_pRank_statedSp he hee hpe hk

end Rank

end CFSG.LocalAnalysis.RankFourTheoremC
