module

public import CFSG.LieType.Chevalley.TwistedE6NormalForm
public import CFSG.LocalAnalysis.RankThreeTheoremC.OutCyclicNine

open Matrix

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley

section SL2

variable {F : Type*} [Field F]

@[expose] def sl2OrderThree (F : Type*) [Field F] : SpecialLinearGroup (Fin 2) F :=
  ⟨!![0, -1; 1, -1], by simp [Matrix.det_fin_two]⟩

@[expose] def sl2UOne (F : Type*) [Field F] : SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩

theorem coe_sl2OrderThree :
    (sl2OrderThree F : Matrix (Fin 2) (Fin 2) F) = !![0, -1; 1, -1] := rfl

theorem coe_sl2UOne : (sl2UOne F : Matrix (Fin 2) (Fin 2) F) = !![1, 1; 0, 1] := rfl

theorem sl2OrderThree_pow_three : (sl2OrderThree F) ^ 3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, coe_sl2OrderThree, Matrix.mul_apply, Fin.sum_univ_two]

theorem coe_sl2OrderThree_sq :
    (sl2OrderThree F : Matrix (Fin 2) (Fin 2) F) ^ 2 = !![-1, 1; -1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, coe_sl2OrderThree, Matrix.mul_apply, Fin.sum_univ_two]

theorem sl2OrderThree_pow_ne_smul {n : ℕ} (hn : ¬ 3 ∣ n) (l : F) :
    ((sl2OrderThree F ^ n : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) ≠
      l • 1 := by
  rw [pow_eq_pow_mod n sl2OrderThree_pow_three]
  have : n % 3 = 1 ∨ n % 3 = 2 := by omega
  intro h
  rcases this with h1 | h1
  · rw [h1, pow_one, coe_sl2OrderThree] at h
    have := congrFun (congrFun h 0) 1
    simp at this
  · rw [h1, Matrix.SpecialLinearGroup.coe_pow, coe_sl2OrderThree_sq] at h
    have := congrFun (congrFun h 0) 1
    simp at this

theorem sl2UOne_mul_pow_ne_smul {n : ℕ} (hn : ¬ 3 ∣ n) (l : F) :
    ((sl2UOne F * sl2OrderThree F ^ n : SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) ≠
      l • ((sl2OrderThree F ^ n * sl2UOne F : SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) := by
  rw [pow_eq_pow_mod n sl2OrderThree_pow_three]
  have : n % 3 = 1 ∨ n % 3 = 2 := by omega
  intro h
  rcases this with h1 | h1
  · rw [h1, pow_one] at h
    have := congrFun (congrFun h 0) 0
    simp [coe_sl2OrderThree, coe_sl2UOne, Matrix.mul_apply, Fin.sum_univ_two] at this
  · rw [h1] at h
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_pow,
      coe_sl2OrderThree_sq, coe_sl2UOne] at h
    have := congrFun (congrFun h 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at this

theorem independent_of_commuting_sl2 {G : Type*} [Group G] {F₁ F₂ : Type*} [Field F₁]
    [Field F₂] (R₁ : SpecialLinearGroup (Fin 2) F₁ →* G) (R₂ : SpecialLinearGroup (Fin 2) F₂ →* G)
    (hcomm : ∀ g h, Commute (R₁ g) (R₂ h))
    (hk₁ : ∀ g ∈ R₁.ker, ∃ l : F₁, (g : Matrix (Fin 2) (Fin 2) F₁) = l • 1)
    (hk₂ : ∀ g ∈ R₂.ker, ∃ l : F₂, (g : Matrix (Fin 2) (Fin 2) F₂) = l • 1) :
    ∀ a b : ℕ, (R₁ (sl2OrderThree F₁)) ^ a * (R₂ (sl2OrderThree F₂)) ^ b = 1 → 3 ∣ a ∧ 3 ∣ b := by
  intro a b hab
  rw [← map_pow, ← map_pow] at hab
  have ha : 3 ∣ a := by
    by_contra ha
    have h1 : R₁ (sl2OrderThree F₁ ^ a) = (R₂ (sl2OrderThree F₂ ^ b))⁻¹ :=
      eq_inv_of_mul_eq_one_left hab
    have hc : Commute (R₁ (sl2OrderThree F₁ ^ a)) (R₁ (sl2UOne F₁)) := by
      rw [h1]
      exact ((hcomm _ _).inv_right).symm
    have h2 : R₁ ((sl2OrderThree F₁ ^ a * sl2UOne F₁)⁻¹ *
        (sl2UOne F₁ * sl2OrderThree F₁ ^ a)) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul, hc.eq, inv_mul_cancel]
    obtain ⟨l, hl⟩ := hk₁ _ (MonoidHom.mem_ker.2 h2)
    have h3 : ((sl2OrderThree F₁ ^ a * sl2UOne F₁ : SpecialLinearGroup (Fin 2) F₁) :
        Matrix (Fin 2) (Fin 2) F₁) *
        (((sl2OrderThree F₁ ^ a * sl2UOne F₁)⁻¹ * (sl2UOne F₁ * sl2OrderThree F₁ ^ a) :
          SpecialLinearGroup (Fin 2) F₁) : Matrix (Fin 2) (Fin 2) F₁) =
        ((sl2UOne F₁ * sl2OrderThree F₁ ^ a : SpecialLinearGroup (Fin 2) F₁) :
          Matrix (Fin 2) (Fin 2) F₁) := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel_left]
    rw [hl, Matrix.mul_smul, mul_one] at h3
    exact sl2UOne_mul_pow_ne_smul ha l h3.symm
  obtain ⟨k, rfl⟩ := ha
  rw [pow_mul, sl2OrderThree_pow_three, one_pow, map_one, one_mul] at hab
  refine ⟨⟨k, rfl⟩, ?_⟩
  by_contra hb
  obtain ⟨l, hl⟩ := hk₂ _ (MonoidHom.mem_ker.2 hab)
  exact sl2OrderThree_pow_ne_smul hb l hl

end SL2

section Orbits

theorem orbit_three_orth_orbit_zero :
    ∀ k < (TwistTag.E6.orbit ⟨3, by decide⟩).card, ∀ l < (TwistTag.E6.orbit ⟨0, by decide⟩).card,
      (Pi.single ((TwistTag.E6.perm ^ k) (TwistTag.E6.orbitMin ⟨3, by decide⟩)) 1 :
          Fin TwistTag.E6.tag.rank → ℤ) ⬝ᵥ
        (TwistTag.E6.tag.symmetrizedCartan *ᵥ (Pi.single ((TwistTag.E6.perm ^ l)
          (TwistTag.E6.orbitMin ⟨0, by decide⟩)) 1 : Fin TwistTag.E6.tag.rank → ℤ)) = 0 := by
  decide


theorem commute_rankOneHom_of_orth {K : Type} [Field K] {i j : Fin TwistTag.E6.tag.rank}
    (horth : (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ) ⬝ᵥ
      (TwistTag.E6.tag.symmetrizedCartan *ᵥ (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ)) = 0)
    (g g' : SL2 K) :
    Commute (rankOneHom TwistTag.E6 K i g) (rankOneHom TwistTag.E6 K j g') := by
  have hgen : ∀ x ∈ Set.range (xUnit TwistTag.E6.tag K i) ∪ Set.range (yUnit TwistTag.E6.tag K i),
      ∀ y ∈ Set.range (xUnit TwistTag.E6.tag K j) ∪ Set.range (yUnit TwistTag.E6.tag K j),
        Commute x y := by
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩) _ (⟨d, rfl⟩ | ⟨d, rfl⟩)
    · rw [← pinnedX_single, ← pinnedX_single]
      exact commute_pinnedX_of_rootForm_eq_zero K (isRoot_single _ i) (isRoot_single _ j) horth c d
    · rw [← pinnedX_single, ← pinnedX_neg_single]
      refine commute_pinnedX_of_rootForm_eq_zero K (isRoot_single _ i) (isRoot_neg_single _ j)
        ?_ c d
      rw [mulVec_neg, dotProduct_neg, horth, neg_zero]
    · rw [← pinnedX_neg_single, ← pinnedX_single]
      refine commute_pinnedX_of_rootForm_eq_zero K (isRoot_neg_single _ i) (isRoot_single _ j)
        ?_ c d
      rw [neg_dotProduct, horth, neg_zero]
    · rw [← pinnedX_neg_single, ← pinnedX_neg_single]
      refine commute_pinnedX_of_rootForm_eq_zero K (isRoot_neg_single _ i)
        (isRoot_neg_single _ j) ?_ c d
      rw [mulVec_neg, dotProduct_neg, neg_dotProduct, neg_neg, horth]
  have hle : Subgroup.closure (Set.range (xUnit TwistTag.E6.tag K i) ∪
        Set.range (yUnit TwistTag.E6.tag K i)) ≤
      Subgroup.centralizer (Subgroup.closure (Set.range (xUnit TwistTag.E6.tag K j) ∪
        Set.range (yUnit TwistTag.E6.tag K j)) : Set (ModGL TwistTag.E6.tag K)) := by
    refine (Subgroup.closure_le _).2 fun x hx => ?_
    have hle' : Subgroup.closure (Set.range (xUnit TwistTag.E6.tag K j) ∪
        Set.range (yUnit TwistTag.E6.tag K j)) ≤ Subgroup.centralizer {x} :=
      (Subgroup.closure_le _).2 fun y hy z hz => by
        rw [Set.mem_singleton_iff] at hz
        subst hz
        exact (hgen z hx y hy).eq
    exact Subgroup.mem_centralizer_iff.2 fun y hy => (hle' hy x rfl).symm
  have hg : rankOneHom TwistTag.E6 K i g ∈ (rankOneHom TwistTag.E6 K i).range := ⟨g, rfl⟩
  have hg' : rankOneHom TwistTag.E6 K j g' ∈ (rankOneHom TwistTag.E6 K j).range := ⟨g', rfl⟩
  rw [rankOneHom_range] at hg hg'
  exact ((Subgroup.mem_centralizer_iff.1 (hle hg)) _ hg').symm

theorem commute_orbitRankOneHom_E6 {K : Type} [Field K] (σ : K →+* K)
    (g : SL2 (orbitField TwistTag.E6 K σ ⟨3, by decide⟩))
    (g' : SL2 (orbitField TwistTag.E6 K σ ⟨0, by decide⟩)) :
    Commute (orbitRankOneHom TwistTag.E6 K σ ⟨3, by decide⟩ g)
      (orbitRankOneHom TwistTag.E6 K σ ⟨0, by decide⟩ g') := by
  rw [orbitRankOneHom_apply, orbitRankOneHom_apply]
  refine Commute.list_prod_left _ _ fun x hx => Commute.list_prod_right _ _ fun y hy => ?_
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hy
  exact commute_rankOneHom_of_orth
    (orbit_three_orth_orbit_zero k (List.mem_range.1 hk) l (List.mem_range.1 hl)) _ _

theorem orbitRankOneHom_mem_graphFixedRootGroup {K : Type} [Field K] (σ : K →+* K)
    (a : Fin TwistTag.E6.foldedTag.rank) (g : SL2 (orbitField TwistTag.E6 K σ a)) :
    orbitRankOneHom TwistTag.E6 K σ a g ∈ graphFixedRootGroup TwistTag.E6 K σ := by
  have h : orbitRankOneHom TwistTag.E6 K σ a g ∈ (orbitRankOneHom TwistTag.E6 K σ a).range :=
    ⟨g, rfl⟩
  rw [orbitRankOneHom_range] at h
  refine (Subgroup.closure_le _).2 ?_ h
  rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · exact graphFixedPosUnipotent_le_graphFixedRootGroup _ K σ
      (orbitX_mem_graphFixedPosUnipotent _ σ a c)
  · exact graphFixedNegUnipotent_le_graphFixedRootGroup _ K σ
      (orbitY_mem_graphFixedNegUnipotent _ σ a c)

theorem exists_nine_graphFixedRootGroup_E6 {K : Type} [Field K] (σ : K →+* K) :
    ∃ A : Subgroup ↥(graphFixedRootGroup TwistTag.E6 K σ),
      CFSG.Open.IsElemAbelian 3 A ∧ Nat.card A = 3 ^ 2 := by
  have hker : ∀ (a : Fin TwistTag.E6.foldedTag.rank),
      ∀ g ∈ (orbitRankOneHom TwistTag.E6 K σ a).ker,
        ∃ l : orbitField TwistTag.E6 K σ a,
          (g : Matrix (Fin 2) (Fin 2) (orbitField TwistTag.E6 K σ a)) = l • 1 := fun a g hg => by
    obtain ⟨l, -, hl⟩ := eq_smul_one_of_mem_ker_orbitRankOneHom hg
    exact ⟨l, hl⟩
  have hind := independent_of_commuting_sl2 (orbitRankOneHom TwistTag.E6 K σ ⟨3, by decide⟩)
    (orbitRankOneHom TwistTag.E6 K σ ⟨0, by decide⟩) (commute_orbitRankOneHom_E6 σ) (hker _)
    (hker _)
  refine exists_isElemAbelian_card_nine_of_commute
    (⟨orbitRankOneHom TwistTag.E6 K σ ⟨3, by decide⟩ (sl2OrderThree _),
      orbitRankOneHom_mem_graphFixedRootGroup σ _ _⟩ : ↥(graphFixedRootGroup TwistTag.E6 K σ))
    ⟨orbitRankOneHom TwistTag.E6 K σ ⟨0, by decide⟩ (sl2OrderThree _),
      orbitRankOneHom_mem_graphFixedRootGroup σ _ _⟩ ?_ ?_ ?_ ?_
  · refine Subtype.ext ?_
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← map_pow, sl2OrderThree_pow_three, map_one]
  · refine Subtype.ext ?_
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← map_pow, sl2OrderThree_pow_three, map_one]
  · exact Subtype.ext (commute_orbitRankOneHom_E6 σ _ _).eq
  · intro a b h
    refine hind a b ?_
    have := congrArg Subtype.val h
    simpa using this

theorem exists_nine_of_twistedE6 {ℓ f : ℕ} {X : Type} [Group X]
    (h : ChevalleyExceptionalModel X .twistedE6 ℓ f) :
    ∃ A : Subgroup X, CFSG.Open.IsElemAbelian 3 A ∧ Nat.card A = 3 ^ 2 := by
  obtain ⟨⟨hℓ, hf1, -⟩, hm⟩ := h
  have hm' : TwistedChevalleyModel X .E6 (ℓ ^ f) := hm
  obtain ⟨K, _, _, hcard, σ, hσ, ⟨e⟩⟩ := hm'
  obtain ⟨σ', hσ', -⟩ := finite_graph_field_parameter_fields .E6 hℓ hf1 K hcard
  have hσσ' : σ'.toRingHom = σ := RingHom.ext fun c => by
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ', hσ]
  subst hσσ'
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, ⟨E⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf1 K hcard σ' hσ'
  exact exists_isElemAbelian_of_mulEquiv (e.trans E).symm
    (exists_nine_graphFixedRootGroup_E6 σ'.toRingHom)

end Orbits

end CFSG.LocalAnalysis.RankThreeTheoremC
