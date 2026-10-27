module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE8D8
public import CFSG.LieType.Chevalley.E7SupportedBruhat
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddPSp

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits

@[expose] def e8BitsD8 : Fin (Tag.rank .E8) → Bool :=
  listMask [true, false, false, false, false, false, false, false]

theorem e8BitsD8_eq_false : ∀ j : Fin (Tag.rank .E8), j ≠ e8Node 0 → e8BitsD8 j = false := by
  decide

theorem maskPairing_e8BitsD8 (α : Fin (Tag.rank .E8) → ℤ) :
    maskPairing e8BitsD8 α = α (e8Node 0) := by
  rw [maskPairing, Finset.sum_eq_single (e8Node 0)]
  · simp [show e8BitsD8 (e8Node 0) = true from by decide]
  · intro j _ hj
    simp [e8BitsD8_eq_false j hj]
  · intro h
    exact absurd (Finset.mem_univ _) h

@[expose] def e8D7Node (k : Fin 7) : Fin (Tag.rank .E8) := e8Node k.succ

@[expose] def e8D8Data : List (List (Fin 8) × (Fin (Tag.rank .E8) → ℤ)) :=
  [([], ![2, 2, 3, 4, 3, 2, 1, 0]),
    ([7], ![2, 2, 3, 4, 3, 2, 1, 1]),
    ([6, 7], ![2, 2, 3, 4, 3, 2, 2, 1]),
    ([5, 6, 7], ![2, 2, 3, 4, 3, 3, 2, 1]),
    ([4, 5, 6, 7], ![2, 2, 3, 4, 4, 3, 2, 1]),
    ([3, 4, 5, 6, 7], ![2, 2, 3, 5, 4, 3, 2, 1]),
    ([2, 3, 4, 5, 6, 7], ![2, 2, 4, 5, 4, 3, 2, 1]),
    ([1, 3, 4, 5, 6, 7], ![2, 3, 3, 5, 4, 3, 2, 1]),
    ([2, 1, 3, 4, 5, 6, 7], ![2, 3, 4, 5, 4, 3, 2, 1]),
    ([3, 2, 1, 3, 4, 5, 6, 7], ![2, 3, 4, 6, 4, 3, 2, 1]),
    ([4, 3, 2, 1, 3, 4, 5, 6, 7], ![2, 3, 4, 6, 5, 3, 2, 1]),
    ([5, 4, 3, 2, 1, 3, 4, 5, 6, 7], ![2, 3, 4, 6, 5, 4, 2, 1]),
    ([6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 7], ![2, 3, 4, 6, 5, 4, 3, 1]),
    ([7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 7], ![2, 3, 4, 6, 5, 4, 3, 2])]

theorem e8D8Data_wordReflect : ∀ d ∈ e8D8Data,
    wordReflect .E8 (d.1.map e8Node) e8D8Root = d.2 := by
  decide

theorem e8D8Data_letters : ∀ d ∈ e8D8Data, ∀ i ∈ d.1.map e8Node, ∃ k, e8D7Node k = i := by
  decide

theorem e8_even_zero_cases : ∀ γ ∈ rootFinset .E8, Even (γ (e8Node 0)) →
    γ (e8Node 0) = 0 ∨ ∃ d ∈ e8D8Data, γ = d.2 ∨ γ = -d.2 := by
  decide +kernel

theorem e8D7Node_ne_zero : ∀ k : Fin 7, e8D7Node k ≠ e8Node 0 := by decide

theorem eq_zero_of_forall_e8D7Node_ne :
    ∀ i : Fin (Tag.rank .E8), (∀ k, e8D7Node k ≠ i) → i = e8Node 0 := by
  decide

theorem mem_parabolicRoots_e8D7 {α : Fin (Tag.rank .E8) → ℤ} :
    α ∈ parabolicRoots .E8 (Set.range e8D7Node) ↔ IsRoot .E8 α ∧ α (e8Node 0) = 0 := by
  refine and_congr_right fun _ => ⟨fun h => h _ ?_, fun h i hi => ?_⟩
  · rintro ⟨k, hk⟩
    exact e8D7Node_ne_zero k hk
  · rw [eq_zero_of_forall_e8D7Node_ne i fun k hk => hi ⟨k, hk⟩]
    exact h

theorem e8D7Node_mem : ∀ k : Fin 7, ∃ j : Fin 8, j ≠ 0 ∧ e8D8Node j = e8D7Node k := by decide

theorem e8D8Node_ne_zero : ∀ j : Fin 8, j ≠ 0 → e8D8Node j ≠ e8Node 0 := by decide

theorem map_subtype_iSup_e8D8Chain_eq_rootSpan
    {K : Type} [Field K] :
    (⨆ k, e8D8Chain K k).map (adjointGroup .E8 K).subtype =
      rootSpan .E8 K {γ | IsRoot .E8 γ ∧ Even (γ (e8Node 0))} := by
  have hpair : ∀ γ : Fin (Tag.rank .E8) → ℤ, IsRoot .E8 γ →
      ((e8Datum K).rootGroup γ ⊔ (e8Datum K).rootGroup (-γ)).map (adjointGroup .E8 K).subtype =
        rootSubgroup .E8 K γ ⊔ rootSubgroup .E8 K (-γ) := fun γ hγ => by
    rw [Subgroup.map_sup]
    exact congrArg₂ (· ⊔ ·) (map_subtype_rootGroup _ hγ) (map_subtype_rootGroup _ (IsRoot.neg hγ))
  have hU0 : e8D8Chain K 0 =
      (e8Datum K).rootGroup e8D8Root ⊔ (e8Datum K).rootGroup (-e8D8Root) := by
    simp [e8D8Chain]
  have hUk : ∀ k, k ≠ 0 → e8D8Chain K k = rankOne (e8Datum K).rootGroup (e8D8Node k) :=
    fun k hk => by simp [e8D8Chain, hk]
  have hD7 : ⨆ k, rankOne (e8Datum K).rootGroup (e8D7Node k) ≤ ⨆ k, e8D8Chain K k := by
    refine iSup_le fun k => ?_
    obtain ⟨j, hj0, hj⟩ := e8D7Node_mem k
    rw [← hj, ← hUk j hj0]
    exact le_iSup (e8D8Chain K) j
  have hβev : Even (e8D8Root (e8Node 0)) := by decide
  apply le_antisymm
  · rw [Subgroup.map_iSup]
    refine iSup_le fun k => ?_
    by_cases hk : k = 0
    · rw [hk, hU0, hpair _ isRoot_e8D8Root]
      exact sup_le (le_iSup₂_of_le e8D8Root ⟨isRoot_e8D8Root, hβev⟩ le_rfl)
        (le_iSup₂_of_le (-e8D8Root)
          ⟨IsRoot.neg isRoot_e8D8Root, by rw [Pi.neg_apply]; exact hβev.neg⟩ le_rfl)
    · rw [hUk k hk]
      change ((e8Datum K).rootGroup (Pi.single (e8D8Node k) 1) ⊔
        (e8Datum K).rootGroup (-Pi.single (e8D8Node k) 1)).map _ ≤ _
      have h0 : (Pi.single (e8D8Node k) 1 : Fin (Tag.rank .E8) → ℤ) (e8Node 0) = 0 :=
        Pi.single_eq_of_ne (e8D8Node_ne_zero k hk).symm 1
      rw [hpair _ (isRoot_single _ _)]
      exact sup_le (le_iSup₂_of_le _ ⟨isRoot_single _ _, by rw [h0]; decide⟩ le_rfl)
        (le_iSup₂_of_le _ ⟨IsRoot.neg (isRoot_single _ _), by rw [Pi.neg_apply, h0]; decide⟩
          le_rfl)
  ·
    have hconj : ∀ d ∈ e8D8Data, ((e8Datum K).rootGroup d.2 ⊔ (e8Datum K).rootGroup (-d.2)) ≤
        ⨆ k, e8D8Chain K k := by
      intro d hd
      have hn : weylWordElt .E8 K (d.1.map e8Node) ∈ ⨆ k, e8D8Chain K k :=
        hD7 (weylWordElt_mem_iSup e8D7Node _ (e8D8Data_letters d hd))
      rw [← e8D8Data_wordReflect d hd, ← map_conj_weylWordElt_rootPair _ isRoot_e8D8Root]
      rintro _ ⟨x, hx, rfl⟩
      have hx' : x ∈ ⨆ k, e8D8Chain K k := le_iSup (e8D8Chain K) 0 (by rw [hU0]; exact hx)
      exact mul_mem (mul_mem hn hx') (inv_mem hn)
    refine iSup₂_le fun γ hγ => ?_
    obtain ⟨hγr, hev⟩ := hγ
    rcases e8_even_zero_cases γ (mem_rootFinset.2 hγr) hev with h0 | ⟨d, hd, rfl | rfl⟩
    · calc rootSubgroup .E8 K γ ≤ rootSpan .E8 K (parabolicRoots .E8 (Set.range e8D7Node)) :=
            le_iSup₂_of_le γ (mem_parabolicRoots_e8D7.2 ⟨hγr, h0⟩) le_rfl
        _ = subsystemGroup .E8 K (Set.range e8D7Node) := (subsystemGroup_eq_rootSpan _).symm
        _ = (⨆ k, rankOne (e8Datum K).rootGroup (e8D7Node k)).map (adjointGroup .E8 K).subtype :=
            (map_subtype_iSup_rankOne e8D7Node).symm
        _ ≤ (⨆ k, e8D8Chain K k).map (adjointGroup .E8 K).subtype := Subgroup.map_mono hD7
    · have hd2 : IsRoot .E8 d.2 := hγr
      calc rootSubgroup .E8 K d.2 ≤ rootSubgroup .E8 K d.2 ⊔ rootSubgroup .E8 K (-d.2) :=
            le_sup_left
        _ = ((e8Datum K).rootGroup d.2 ⊔ (e8Datum K).rootGroup (-d.2)).map
            (adjointGroup .E8 K).subtype := (hpair _ hd2).symm
        _ ≤ (⨆ k, e8D8Chain K k).map (adjointGroup .E8 K).subtype :=
            Subgroup.map_mono (hconj d hd)
    · have hd2 : IsRoot .E8 d.2 := by simpa using IsRoot.neg hγr
      calc rootSubgroup .E8 K (-d.2) ≤ rootSubgroup .E8 K d.2 ⊔ rootSubgroup .E8 K (-d.2) :=
            le_sup_right
        _ = ((e8Datum K).rootGroup d.2 ⊔ (e8Datum K).rootGroup (-d.2)).map
            (adjointGroup .E8 K).subtype := (hpair _ hd2).symm
        _ ≤ (⨆ k, e8D8Chain K k).map (adjointGroup .E8 K).subtype :=
            Subgroup.map_mono (hconj d hd)

theorem map_subtype_iSup_e8D8Chain
    {K : Type} [Field K] (hK2 : ringChar K ≠ 2) :
    (⨆ k, e8D8Chain K k).map (adjointGroup .E8 K).subtype =
      rootSpan .E8 K (rootCharKernel (bitsTuple (K := K) e8BitsD8)) := by
  have hker : rootCharKernel (bitsTuple (K := K) e8BitsD8) =
      {γ | IsRoot .E8 γ ∧ Even (γ (e8Node 0))} := by
    rw [rootCharKernel_eq_kernelRoots hK2 (bitsTuple_mem _), signTupleBits_bitsTuple hK2]
    ext γ
    rw [mem_kernelRoots_maskChar, maskPairing_e8BitsD8]
    rfl
  rw [hker]
  exact map_subtype_iSup_e8D8Chain_eq_rootSpan

theorem e8_toral_D8_component
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f)
    {M : Subgroup (toralCentralizer .E8 K (bitsTuple e8BitsD8))} (hM : IsComponent M) :
    OddLieCentralQuotient p M := by
  classical
  obtain ⟨hf, -⟩ := one_le_and_three_le_of_card hp hp2 hK
  have : CharP K p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have hadm : StatedLieAdmissible .POmegaPlus 8 p f := ⟨hp, hf, by norm_num⟩
  obtain ⟨hSX, hSn, hsolv, -, -⟩ :=
    odd_toral_involution_centralizer_p_component_root_reduction .E8 K hK2 _
      (bitsTuple_mem (K := K) e8BitsD8)
  obtain ⟨-, -, -, hqs, hlie⟩ := exists_psi_D8_E8 hp hp2 hK
  let e₁ : ↥(⨆ k, e8D8Chain K k) ≃*
      rootSpan .E8 K (rootCharKernel (bitsTuple (K := K) e8BitsD8)) :=
    ((⨆ k, e8D8Chain K k).equivMapOfInjective _ (adjointGroup .E8 K).subtype_injective).trans
      (MulEquiv.subgroupCongr (map_subtype_iSup_e8D8Chain hK2))
  let e₂ := Subgroup.subgroupOfEquivOfLe hSX
  have hq := LocalCores.isQuasisimple_of_mulEquiv (e₂.trans e₁.symm).symm hqs
  have hMeq := eq_of_isComponent_of_normal_quasisimple hq hsolv hM
  let e : M ≃* ↥(⨆ k, e8D8Chain K k) := (MulEquiv.subgroupCongr hMeq).trans (e₂.trans e₁.symm)
  exact ⟨.POmegaPlus, 8, f, hadm, lieModel_of_mulEquiv
    (QuotientGroup.congr _ _ e.symm (Subgroup.map_center_eq e.symm)) hlie⟩

end CFSG.ComponentClassification.CatLeafProof
