module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofFrameRecog
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofF4FrameC3
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddOrthLow

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits CFSG.Timmesfeld
open scoped MatrixGroups

@[expose] def pairSpan (τ : Tag)
    (K : Type) [Field K] (S : Set (Fin τ.rank → ℤ)) : Subgroup (ModGL τ K) :=
  ⨆ β ∈ S, (rootSubgroup τ K β ⊔ rootSubgroup τ K (-β))

theorem pairSpan_singleton
    (τ : Tag) (K : Type) [Field K] (β : Fin τ.rank → ℤ) :
    pairSpan τ K {β} = rootSubgroup τ K β ⊔ rootSubgroup τ K (-β) := by
  rw [pairSpan, iSup_singleton]

theorem map_subtype_iSup_rootPair
    {τ : Tag} {K : Type} [Field K] {r : ℕ} (rt : Fin r → Fin τ.rank → ℤ)
    (hrt : ∀ k, IsRoot τ (rt k)) :
    (⨆ k, ((adjDatum (rootOperatorFamily τ) K).rootGroup (rt k) ⊔
        (adjDatum (rootOperatorFamily τ) K).rootGroup (-rt k))).map (adjointGroup τ K).subtype =
      pairSpan τ K (Set.range rt) := by
  rw [Subgroup.map_iSup, pairSpan, iSup_range]
  refine iSup_congr fun k => ?_
  rw [Subgroup.map_sup]
  exact congrArg₂ (· ⊔ ·) (map_subtype_rootGroup _ (hrt k))
    (map_subtype_rootGroup _ (IsRoot.neg (hrt k)))

theorem lieModel_pairSpan_of_frame
    {τ : Tag} {K : Type} [Field K] {r : ℕ} (rt : Fin r → Fin τ.rank → ℤ)
    (hrt : ∀ k, IsRoot τ (rt k)) {t : StatedLieTag} {n p f : ℕ}
    (hlie : Blueprint.LieModel (↥(⨆ k, ((adjDatum (rootOperatorFamily τ) K).rootGroup (rt k) ⊔
        (adjDatum (rootOperatorFamily τ) K).rootGroup (-rt k))) ⧸ Subgroup.center
          ↥(⨆ k, ((adjDatum (rootOperatorFamily τ) K).rootGroup (rt k) ⊔
            (adjDatum (rootOperatorFamily τ) K).rootGroup (-rt k)))) t n p f) :
    Blueprint.LieModel (↥(pairSpan τ K (Set.range rt)) ⧸
      Subgroup.center ↥(pairSpan τ K (Set.range rt))) t n p f := by
  set U := ⨆ k, ((adjDatum (rootOperatorFamily τ) K).rootGroup (rt k) ⊔
    (adjDatum (rootOperatorFamily τ) K).rootGroup (-rt k)) with hU
  let e : U ≃* pairSpan τ K (Set.range rt) :=
    (U.equivMapOfInjective _ (adjointGroup τ K).subtype_injective).trans
      (MulEquiv.subgroupCongr (map_subtype_iSup_rootPair rt hrt))
  exact lieModel_of_mulEquiv (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)) hlie

theorem oddLieCentralQuotient_pairSpan_of_frame
    {τ : Tag} {K : Type} [Field K] {r : ℕ} (rt : Fin r → Fin τ.rank → ℤ)
    (hrt : ∀ k, IsRoot τ (rt k)) {t : StatedLieTag} {n p f : ℕ}
    (hadm : StatedLieAdmissible t n p f)
    (hlie : Blueprint.LieModel (↥(⨆ k, ((adjDatum (rootOperatorFamily τ) K).rootGroup (rt k) ⊔
        (adjDatum (rootOperatorFamily τ) K).rootGroup (-rt k))) ⧸ Subgroup.center
          ↥(⨆ k, ((adjDatum (rootOperatorFamily τ) K).rootGroup (rt k) ⊔
            (adjDatum (rootOperatorFamily τ) K).rootGroup (-rt k)))) t n p f) :
    OddLieCentralQuotient p (pairSpan τ K (Set.range rt)) :=
  ⟨t, n, f, hadm, lieModel_pairSpan_of_frame rt hrt hlie⟩

@[expose] def e7Node (i : Fin 7) : Fin (Tag.rank .E7) := i

theorem e7_neighbour : ∀ i : Fin (Tag.rank .E7), ∃ l,
    Tag.cartan .E7 i l = -1 ∧ Tag.cartan .E7 l i = -1 := by
  intro i
  fin_cases i <;> decide

theorem exists_e7_chevalleyExtras
    (K : Type) [Field K] :
    ∃ (O : CommOrder (RootSystem.ofCartan (adjDatum (rootOperatorFamily .E7) K).isFiniteType
        (adjDatum (rootOperatorFamily .E7) K).divisible))
      (C : (Fin (Tag.rank .E7) → ℤ) → (Fin (Tag.rank .E7) → ℤ) → ℕ × ℕ → ℤ),
      ChevalleyExtras (adjDatum (rootOperatorFamily .E7) K) K (xPar (rootOperatorFamily .E7))
        C O := by
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (adjDatum (rootOperatorFamily .E7) K).isFiniteType
    (Dv := (adjDatum (rootOperatorFamily .E7) K).divisible) rfl
  exact ⟨O, _, adjDatum_chevalleyExtras _ K e7AdjData_valid noG2_E7 e7_neighbour O
    (commC (rootOperatorFamily .E7) e7AdjData_valid)
    (commutatorFormula_commC e7AdjData_valid noG2_E7 _ (adjDatum_roots _ K) O)⟩

theorem e7_adj : ∀ i j : Fin 7, edgeE 7 i j → e7Node i ≠ e7Node j ∧
    Tag.cartan .E7 (e7Node i) (e7Node j) = -1 ∧ Tag.cartan .E7 (e7Node j) (e7Node i) = -1 ∧
    ∃ l : Fin 7,
      ¬ (3 : ℤ) ∣ Tag.cartan .E7 (e7Node i) l + 2 * Tag.cartan .E7 (e7Node j) l := by
  decide

theorem e7_nadj : ∀ i j : Fin 7, i ≠ j → ¬ edgeE 7 i j → ¬ edgeE 7 j i →
    e7Node i ≠ e7Node j ∧ Tag.cartan .E7 (e7Node i) (e7Node j) = 0 ∧
    Tag.cartan .E7 (e7Node j) (e7Node i) = 0 := by
  decide

@[expose] def e7SimpleRoot (k : Fin 7) : Fin (Tag.rank .E7) → ℤ := Pi.single (e7Node k) 1

theorem oddLieCentralQuotient_pairSpan_E7
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) :
    OddLieCentralQuotient p (pairSpan .E7 K (Set.range e7SimpleRoot)) := by
  obtain ⟨hf, -⟩ := one_le_and_three_le_of_card hp hp2 hK
  have : Fact p.Prime := ⟨hp⟩
  have hadm : StatedLieAdmissible .E7 0 p f := ⟨hp, hf, rfl⟩
  obtain ⟨O, C, hE⟩ := exists_e7_chevalleyExtras K
  obtain ⟨ρ, hρ, hcomm, hψ⟩ := exists_levi_frame hE rfl e7Node e7_adj e7_nadj
  obtain ⟨-, -, -, -, hlie⟩ := e7_frame_subgroup hadm hK hcomm hρ hψ
  exact oddLieCentralQuotient_pairSpan_of_frame e7SimpleRoot (fun k => isRoot_single _ _) hadm
    hlie

@[expose] def e7D6Node : Fin 6 → Fin (Tag.rank .E7) :=
  ![e7Node 6, e7Node 5, e7Node 4, e7Node 3, e7Node 2, e7Node 1]

theorem e7D6_adj : ∀ i j : Fin 6, edgeD 6 i j → e7D6Node i ≠ e7D6Node j ∧
    Tag.cartan .E7 (e7D6Node i) (e7D6Node j) = -1 ∧
    Tag.cartan .E7 (e7D6Node j) (e7D6Node i) = -1 ∧
    ∃ l : Fin 7,
      ¬ (3 : ℤ) ∣ Tag.cartan .E7 (e7D6Node i) l + 2 * Tag.cartan .E7 (e7D6Node j) l := by
  decide

theorem e7D6_nadj : ∀ i j : Fin 6, i ≠ j → ¬ edgeD 6 i j → ¬ edgeD 6 j i →
    e7D6Node i ≠ e7D6Node j ∧ Tag.cartan .E7 (e7D6Node i) (e7D6Node j) = 0 ∧
    Tag.cartan .E7 (e7D6Node j) (e7D6Node i) = 0 := by
  decide

@[expose] def e7D6Root (k : Fin 6) : Fin (Tag.rank .E7) → ℤ := Pi.single (e7D6Node k) 1

theorem oddLieCentralQuotient_pairSpan_D6
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) :
    OddLieCentralQuotient p (pairSpan .E7 K (Set.range e7D6Root)) := by
  obtain ⟨hf, -⟩ := one_le_and_three_le_of_card hp hp2 hK
  have hadm : StatedLieAdmissible .POmegaPlus 6 p f := ⟨hp, hf, by norm_num⟩
  obtain ⟨O, C, hE⟩ := exists_e7_chevalleyExtras K
  obtain ⟨ρ, hρ, hcomm, hψ⟩ := exists_levi_frame hE rfl e7D6Node e7D6_adj e7D6_nadj
  obtain ⟨-, -, -, -, hlie⟩ := spinPlus_frame_subgroup hadm (by norm_num) hK hcomm hρ hψ
  exact oddLieCentralQuotient_pairSpan_of_frame e7D6Root (fun k => isRoot_single _ _) hadm hlie

@[expose] def e7Theta : Fin (Tag.rank .E7) → ℤ := ![2, 2, 3, 4, 3, 2, 1]

theorem isRoot_e7Theta :
    IsRoot .E7 e7Theta := by
  rw [RootCertificate.isRoot_iff (Tag.rootCertificate_check .E7)]
  decide +kernel

theorem oddLieCentralQuotient_pairSpan_A1
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (hq : IsQuasisimple (pairSpan .E7 K {e7Theta})) :
    OddLieCentralQuotient p (pairSpan .E7 K {e7Theta}) := by
  obtain ⟨hf, h3⟩ := one_le_and_three_le_of_card hp hp2 hK
  have : CharP K p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  obtain ⟨-, ⟨eQ⟩, -, hfin⟩ := odd_arbitrary_root_pair_SL2_p_components .E7 K hK2 isRoot_e7Theta
  let e₀ : pairSpan .E7 K {e7Theta} ≃*
      (rootSubgroup .E7 K e7Theta ⊔ rootSubgroup .E7 K (-e7Theta) : Subgroup (ModGL .E7 K)) :=
    MulEquiv.subgroupCongr (pairSpan_singleton .E7 K e7Theta)
  by_cases h5 : 5 ≤ Nat.card K
  · let e : pairSpan .E7 K {e7Theta} ≃* SL2 K := e₀.trans eQ.symm
    exact oddLieCentralQuotient_of_equiv_psl_two hp hf hK (by omega) (by omega)
      (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e))
  · exfalso
    have h3' : Nat.card K = 3 := by
      have hodd : Odd (Nat.card K) := by
        rw [hK]
        exact (hp.eq_two_or_odd'.resolve_left hp2).pow
      obtain ⟨k, hk⟩ := hodd
      omega
    have := (hfin.1 h3').1
    exact LocalAnalysis.ComponentInitial.not_isSolvable_of_isQuasisimple hq
      (Group.isSolvable_of_isSolvable_injective (f := e₀.toMonoidHom) e₀.injective)

end CFSG.ComponentClassification.CatLeafProof
