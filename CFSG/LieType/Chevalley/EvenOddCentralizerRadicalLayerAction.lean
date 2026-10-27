module

public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalLayer

public noncomputable section

namespace CFSG.LieType.Chevalley.EvenOddRadical

open CFSG.Blueprint.Chevalley
open scoped commutatorElement

variable {τ : Tag} {K : Type} [Field K]

theorem card_layer
    [Finite K] (J : Set (Fin τ.rank)) (n : ℕ) :
    Nat.card (Layer τ K J n) = Nat.card K ^ (layerRoots τ J (n + 1)).ncard := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((levelRadical τ K J (n + 1 + 1)).subgroupOf (levelRadical τ K J (n + 1)))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (levelRadical_succ_le J _)).toEquiv,
    card_levelRadical, card_levelRadical, ncard_levelRoots J (n + 1), pow_add] at h1
  have hq : 0 < Nat.card K ^ (levelRoots τ J (n + 1 + 1)).ncard := pow_pos Nat.card_pos _
  exact (Nat.eq_of_mul_eq_mul_right hq h1).symm

theorem labelWt_mem_layerRoots
    {J : Set (Fin τ.rank)} {n : ℕ} {b : Label τ}
    (hb : b ∈ gradedLabels τ J (n + 1)) : labelWt τ b ∈ layerRoots τ J (n + 1) := by
  obtain ⟨α, hα, rfl⟩ := mem_layerRoots_of_mem_gradedLabels hb
  exact hα

theorem eq_inr_of_mem_gradedLabels
    {J : Set (Fin τ.rank)} {n : ℕ} {b : Label τ}
    (hb : b ∈ gradedLabels τ J (n + 1)) :
    b = Sum.inr ⟨labelWt τ b, (labelWt_mem_layerRoots hb).1⟩ := by
  obtain ⟨α, hα, rfl⟩ := mem_layerRoots_of_mem_gradedLabels hb
  rfl

@[expose] def gradedLabelsEquiv
    (J : Set (Fin τ.rank)) (n : ℕ) :
    gradedLabels τ J (n + 1) ≃ layerRoots τ J (n + 1) where
  toFun b := ⟨labelWt τ b.1, labelWt_mem_layerRoots b.2⟩
  invFun α := ⟨Sum.inr ⟨α.1, α.2.1⟩, by
    simp only [gradedLabels, Set.mem_ofPred_eq, labelWt]
    exact α.2.2.2⟩
  left_inv b := Subtype.ext (eq_inr_of_mem_gradedLabels b.2).symm
  right_inv α := rfl

instance finite_rootModule
    [Finite K] : Finite (RootModule τ K) :=
  Finite.of_injective _ (Finsupp.equivFunOnFinite (α := Label τ) (M := K)).injective

theorem card_parabolicGraded
    [Finite K] (J : Set (Fin τ.rank)) (n : ℕ) :
    Nat.card (parabolicGraded τ K J (n + 1)) = Nat.card K ^ (layerRoots τ J (n + 1)).ncard := by
  rw [Nat.card_congr
      (LinearEquiv.ofEq _ _ (parabolicGraded_eq_supported (K := K) J (n + 1))).toEquiv,
    Nat.card_congr (Finsupp.supportedEquivFinsupp (M := K) (R := K) _).toEquiv,
    Nat.card_congr Finsupp.equivFunOnFinite, Nat.card_fun,
    Nat.card_congr (gradedLabelsEquiv J n), Nat.card_coe_set_eq]

theorem layerMap_bijective
    [Finite K] (J : Set (Fin τ.rank)) (n : ℕ) :
    Function.Bijective fun x : parabolicGraded τ K J (n + 1) =>
      layerMap J n (x : RootModule τ K) := by
  refine (Nat.bijective_iff_surjective_and_card _).2 ⟨fun ℓ => ?_, ?_⟩
  · obtain ⟨x, hx, rfl⟩ := exists_layerMap_eq J n ℓ
    exact ⟨⟨x, hx⟩, rfl⟩
  · rw [card_parabolicGraded, card_layer]

theorem layerMap_injOn
    [Finite K] (J : Set (Fin τ.rank)) (n : ℕ) {x y : RootModule τ K}
    (hx : x ∈ parabolicGraded τ K J (n + 1)) (hy : y ∈ parabolicGraded τ K J (n + 1))
    (h : layerMap J n x = layerMap J n y) : x = y :=
  congrArg Subtype.val ((layerMap_bijective J n).1 (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) h)

@[expose] def conjRestrict {G : Type*} [Group G] {H : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) : H →* H where
  toFun u := ⟨g * u * g⁻¹, (Subgroup.mem_normalizer_iff.1 hg u).1 u.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' u v := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem coe_conjRestrict {G : Type*} [Group G] {H : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) (u : H) :
    (conjRestrict hg u : G) = g * u * g⁻¹ :=
  rfl

theorem one_le_succ (n : ℕ) : (1 : ℤ) ≤ n + 1 := by omega

theorem one_le_succ_succ (n : ℕ) : (1 : ℤ) ≤ n + 1 + 1 := by omega

@[expose] def levelConj
    (J : Set (Fin τ.rank)) (n : ℕ) {g : ModGL τ K}
    (hg : g ∈ parabolicLevi τ K J) : Layer τ K J n →* Layer τ K J n :=
  QuotientGroup.map _ _ (conjRestrict (parabolicLevi_le_normalizer J (one_le_succ n) hg))
    fun u hu => by
      rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, coe_conjRestrict]
      exact (Subgroup.mem_normalizer_iff.1
        (parabolicLevi_le_normalizer J (one_le_succ_succ n) hg) u).1 (Subgroup.mem_subgroupOf.1 hu)

theorem levelConj_mk
    (J : Set (Fin τ.rank)) (n : ℕ) {g : ModGL τ K}
    (hg : g ∈ parabolicLevi τ K J) (u : levelRadical τ K J (n + 1)) :
    levelConj J n hg (u : Layer τ K J n) =
      ((conjRestrict (parabolicLevi_le_normalizer J (one_le_succ n) hg) u :
        levelRadical τ K J (n + 1)) : Layer τ K J n) :=
  rfl

theorem levelConj_one
    (J : Set (Fin τ.rank)) (n : ℕ) (ℓ : Layer τ K J n) :
    levelConj J n (one_mem (parabolicLevi τ K J)) ℓ = ℓ := by
  induction ℓ using QuotientGroup.induction_on with | _ u => ?_
  rw [levelConj_mk]
  exact congrArg _ (Subtype.ext (by simp [coe_conjRestrict]))

theorem levelConj_mul
    (J : Set (Fin τ.rank)) (n : ℕ) {g h : ModGL τ K}
    (hg : g ∈ parabolicLevi τ K J) (hh : h ∈ parabolicLevi τ K J) (ℓ : Layer τ K J n) :
    levelConj J n (mul_mem hg hh) ℓ = levelConj J n hg (levelConj J n hh ℓ) := by
  induction ℓ using QuotientGroup.induction_on with | _ u => ?_
  rw [levelConj_mk, levelConj_mk, levelConj_mk]
  exact congrArg _ (Subtype.ext (by simp only [coe_conjRestrict]; group))

theorem smul_rootVec_mem_layerRoots
    {J : Set (Fin τ.rank)} {j : Fin τ.rank} (hj : j ∈ J)
    {n : ℕ} {α : Fin τ.rank → ℤ} (hα : α ∈ layerRoots τ J (n + 1)) {m : ℤ}
    (h : IsRoot τ (α + m • Pi.single j 1)) : α + m • Pi.single j 1 ∈ layerRoots τ J (n + 1) := by
  have hd : parabolicDegree τ J (α + m • Pi.single j 1) = n + 1 := by
    rw [parabolicDegree_add, ← Pi.single_smul, smul_eq_mul, mul_one]
    have : parabolicDegree τ J (Pi.single j m) = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      split_ifs with hi
      · rfl
      · exact Pi.single_eq_of_ne (fun h' => hi (by rw [h']; exact hj)) _
    rw [this, add_zero, hα.2.2]
  exact ⟨h, height_pos_of_degree (J := J) h (by omega), hd⟩

theorem ne_single_of_mem_layerRoots
    {J : Set (Fin τ.rank)} {j : Fin τ.rank} (hj : j ∈ J)
    {n : ℕ} {α : Fin τ.rank → ℤ} (hα : α ∈ layerRoots τ J (n + 1)) :
    α ≠ Pi.single j 1 ∧ α ≠ -Pi.single j 1 ∧ Pi.single j 1 ≠ α ∧ Pi.single j 1 ≠ -α ∧
      -Pi.single j 1 ≠ α ∧ -Pi.single j 1 ≠ -α := by
  have h0 := parabolicDegree_single_of_mem (τ := τ) hj
  have hd := hα.2.2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h
  · rw [h, h0] at hd; omega
  · rw [h, parabolicDegree_neg, h0] at hd; omega
  · rw [← h, h0] at hd; omega
  · rw [neg_eq_iff_eq_neg.1 h.symm, parabolicDegree_neg, h0] at hd; omega
  · rw [← h, parabolicDegree_neg, h0] at hd; omega
  · rw [← neg_inj.1 h, h0] at hd; omega

theorem layerMap_torusElt
    (J : Set (Fin τ.rank)) (n : ℕ) (i : Fin τ.rank) (t : Kˣ)
    (hg : torusElt τ K i t ∈ parabolicLevi τ K J) {α : Fin τ.rank → ℤ}
    (hα : α ∈ layerRoots τ J (n + 1)) (c : K) :
    layerMap J n ((torusElt τ K i t : Module.End K (RootModule τ K)) (c • rootVec τ K α)) =
      levelConj J n hg (layerMap J n (c • rootVec τ K α)) := by
  rw [map_smul, torusElt_rootVec i t hα.1, smul_smul, layerMap_smul_rootVec J n hα,
    layerMap_smul_rootVec J n hα, levelConj_mk]
  congr 1
  refine Subtype.ext ?_
  rw [coe_conjRestrict]
  simp only
  rw [root_torus_conjugation i hα.1 t c, mul_comm]

theorem layerMap_xUnit
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (h2 : (2 : K) = 0)
    {J : Set (Fin τ.rank)} (n : ℕ) {j : Fin τ.rank} (hj : j ∈ J) (c' : K)
    (hg : xUnit τ K j c' ∈ parabolicLevi τ K J) {α : Fin τ.rank → ℤ}
    (hα : α ∈ layerRoots τ J (n + 1)) (c : K) :
    layerMap J n ((xUnit τ K j c' : Module.End K (RootModule τ K)) (c • rootVec τ K α)) =
      levelConj J n hg (layerMap J n (c • rootVec τ K α)) := by
  obtain ⟨h₁, h₂, h₃, h₄, -, -⟩ := ne_single_of_mem_layerRoots hj hα
  rw [map_smul, coe_xUnit, xOp_rootVec hτ j c' hα.1 h₁ h₂, smul_add, smul_smul, layerMap_add,
    layerMap_smul_rootVec J n hα, levelConj_mk]
  by_cases hr : IsRoot τ (α + Pi.single j 1)
  · have hr' : α + Pi.single j 1 ∈ layerRoots τ J (n + 1) := by
      have := smul_rootVec_mem_layerRoots hj hα (m := 1) (by rwa [one_smul])
      rwa [one_smul] at this
    rw [layerMap_smul_rootVec J n hr', mul_comm, ← QuotientGroup.mk_mul]
    congr 1
    refine Subtype.ext ?_
    rw [coe_conjRestrict]
    simp only [Subgroup.coe_mul]
    rw [← pinnedX_single, pinnedX_conj_of_isRoot hτ h2 (isRoot_single τ j) hα.1 h₃ h₄
      (by rwa [add_comm]), add_comm, mul_comm c c']
  · rw [rootVec_of_not hr, smul_zero, layerMap_zero, mul_one]
    congr 1
    refine Subtype.ext ?_
    rw [coe_conjRestrict]
    simp only
    rw [← pinnedX_single, pinnedX_conj_of_not hτ (isRoot_single τ j) hα.1 h₃ h₄
      (by rwa [add_comm])]

theorem layerMap_yUnit
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (h2 : (2 : K) = 0)
    {J : Set (Fin τ.rank)} (n : ℕ) {j : Fin τ.rank} (hj : j ∈ J) (c' : K)
    (hg : yUnit τ K j c' ∈ parabolicLevi τ K J) {α : Fin τ.rank → ℤ}
    (hα : α ∈ layerRoots τ J (n + 1)) (c : K) :
    layerMap J n ((yUnit τ K j c' : Module.End K (RootModule τ K)) (c • rootVec τ K α)) =
      levelConj J n hg (layerMap J n (c • rootVec τ K α)) := by
  obtain ⟨h₁, h₂, -, -, h₅, h₆⟩ := ne_single_of_mem_layerRoots hj hα
  rw [map_smul, coe_yUnit, yOp_rootVec hτ j c' hα.1 h₁ h₂, smul_add, smul_smul, layerMap_add,
    layerMap_smul_rootVec J n hα, levelConj_mk]
  by_cases hr : IsRoot τ (α - Pi.single j 1)
  · have hr' : α - Pi.single j 1 ∈ layerRoots τ J (n + 1) := by
      have := smul_rootVec_mem_layerRoots hj hα (m := -1)
        (by rwa [neg_smul, one_smul, ← sub_eq_add_neg])
      rwa [neg_smul, one_smul, ← sub_eq_add_neg] at this
    rw [layerMap_smul_rootVec J n hr', mul_comm, ← QuotientGroup.mk_mul]
    congr 1
    refine Subtype.ext ?_
    rw [coe_conjRestrict]
    simp only [Subgroup.coe_mul]
    rw [← pinnedX_neg_single, pinnedX_conj_of_isRoot hτ h2 (isRoot_neg_single τ j) hα.1 h₅ h₆
      (by rwa [neg_add_eq_sub]), neg_add_eq_sub, mul_comm c c']
  · rw [rootVec_of_not hr, smul_zero, layerMap_zero, mul_one]
    congr 1
    refine Subtype.ext ?_
    rw [coe_conjRestrict]
    simp only
    rw [← pinnedX_neg_single, pinnedX_conj_of_not hτ (isRoot_neg_single τ j) hα.1 h₅ h₆
      (by rwa [neg_add_eq_sub])]

theorem layerMap_of_basis
    (J : Set (Fin τ.rank)) (n : ℕ) {g : ModGL τ K}
    (hg : g ∈ parabolicLevi τ K J)
    (hbasis : ∀ α ∈ layerRoots τ J (n + 1), ∀ c : K,
      layerMap J n ((g : Module.End K (RootModule τ K)) (c • rootVec τ K α)) =
        levelConj J n hg (layerMap J n (c • rootVec τ K α)))
    {x : RootModule τ K} (hx : x ∈ parabolicGraded τ K J (n + 1)) :
    layerMap J n ((g : Module.End K (RootModule τ K)) x) = levelConj J n hg (layerMap J n x) := by
  rw [parabolicGraded_eq_supported, Finsupp.mem_supported] at hx
  have hterm : ∀ b ∈ x.support, layerMap J n ((g : Module.End K (RootModule τ K))
      (Finsupp.single b (x b))) = levelConj J n hg (layerMap J n (Finsupp.single b (x b))) := by
    intro b hb
    obtain ⟨α, hα, rfl⟩ := mem_layerRoots_of_mem_gradedLabels (hx hb)
    have e : Finsupp.single (Sum.inr ⟨α, hα.1⟩ : Label τ) (x (Sum.inr ⟨α, hα.1⟩)) =
        x (Sum.inr ⟨α, hα.1⟩) • rootVec τ K α := by
      rw [rootVec_of_isRoot hα.1, Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [e]
    exact hbasis α hα _
  conv_lhs => rw [← Finsupp.sum_single x]
  conv_rhs => rw [← Finsupp.sum_single x]
  rw [Finsupp.sum, map_sum, layerMap_sum, layerMap_sum, map_prod]
  exact Finset.prod_congr rfl hterm

theorem layerMap_parabolicLevi
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (h2 : (2 : K) = 0) (J : Set (Fin τ.rank)) (n : ℕ) {g : ModGL τ K}
    (hg : g ∈ parabolicLevi τ K J) {x : RootModule τ K}
    (hx : x ∈ parabolicGraded τ K J (n + 1)) :
    layerMap J n ((g : Module.End K (RootModule τ K)) x) = levelConj J n hg (layerMap J n x) := by
  have hM : parabolicLevi τ K J = Subgroup.closure
      (Set.range (fun p : Fin τ.rank × Kˣ => torusElt τ K p.1 p.2) ∪
        {g | ∃ j ∈ J, ∃ c : K, g = xUnit τ K j c ∨ g = yUnit τ K j c}) := by
    rw [Subgroup.closure_union]
    rfl
  have hgen : ∀ g ∈ Set.range (fun p : Fin τ.rank × Kˣ => torusElt τ K p.1 p.2) ∪
      {g | ∃ j ∈ J, ∃ c : K, g = xUnit τ K j c ∨ g = yUnit τ K j c},
      ∀ hg : g ∈ parabolicLevi τ K J, ∀ x ∈ parabolicGraded τ K J (n + 1),
        layerMap J n ((g : Module.End K (RootModule τ K)) x) =
          levelConj J n hg (layerMap J n x) := by
    rintro g (⟨⟨i, t⟩, rfl⟩ | ⟨j, hj, c', rfl | rfl⟩) hg x hx
    · exact layerMap_of_basis J n hg (fun α hα c => layerMap_torusElt J n i t hg hα c) hx
    · exact layerMap_of_basis J n hg (fun α hα c => layerMap_xUnit hτ h2 n hj c' hg hα c) hx
    · exact layerMap_of_basis J n hg (fun α hα c => layerMap_yUnit hτ h2 n hj c' hg hα c) hx
  have hinv : ∀ g ∈ Set.range (fun p : Fin τ.rank × Kˣ => torusElt τ K p.1 p.2) ∪
      {g | ∃ j ∈ J, ∃ c : K, g = xUnit τ K j c ∨ g = yUnit τ K j c},
      g⁻¹ ∈ Set.range (fun p : Fin τ.rank × Kˣ => torusElt τ K p.1 p.2) ∪
        {g | ∃ j ∈ J, ∃ c : K, g = xUnit τ K j c ∨ g = yUnit τ K j c} := by
    rintro g (⟨⟨i, t⟩, rfl⟩ | ⟨j, hj, c', rfl | rfl⟩)
    · refine Or.inl ⟨⟨i, t⁻¹⟩, ?_⟩
      simp only
      rw [eq_inv_iff_mul_eq_one, ← torusElt_mul, inv_mul_cancel, torusElt_one]
    · exact Or.inr ⟨j, hj, -c', Or.inl (xUnit_neg j c').symm⟩
    · exact Or.inr ⟨j, hj, -c', Or.inr (yUnit_neg j c').symm⟩
  have hmain : ∀ g (hg' : g ∈ Subgroup.closure
      (Set.range (fun p : Fin τ.rank × Kˣ => torusElt τ K p.1 p.2) ∪
        {g | ∃ j ∈ J, ∃ c : K, g = xUnit τ K j c ∨ g = yUnit τ K j c})),
      ∀ x ∈ parabolicGraded τ K J (n + 1),
        layerMap J n ((g : Module.End K (RootModule τ K)) x) =
          levelConj J n (hM ▸ hg') (layerMap J n x) := by
    intro g hg'
    induction hg' using Subgroup.closure_induction'' with
    | mem g hgs => exact hgen g hgs _
    | inv_mem g hgs => exact hgen g⁻¹ (hinv g hgs) _
    | one =>
      intro x _
      rw [Units.val_one, Module.End.one_apply]
      exact (levelConj_one J n _).symm
    | mul g h hg₁ hh₁ ihg ihh =>
      intro x hx
      have hgM : g ∈ parabolicLevi τ K J := hM ▸ hg₁
      have hhM : h ∈ parabolicLevi τ K J := hM ▸ hh₁
      rw [Units.val_mul, Module.End.mul_apply, ihg _ (parabolicLevi_preserves hhM _ hx),
        ihh x hx]
      exact (levelConj_mul J n hgM hhM _).symm
  exact hmain g (hM ▸ hg) x hx

theorem exists_fixed_vector_of_fixed
    [Finite K]
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (h2 : (2 : K) = 0) (J : Set (Fin τ.rank))
    (n : ℕ) {S : Subgroup (ModGL τ K)} (hS : S ≤ parabolicLevi τ K J) {u : ModGL τ K}
    (hu : u ∈ levelRadical τ K J (n + 1)) (hu' : u ∉ levelRadical τ K J (n + 1 + 1))
    (hfix : ∀ s ∈ S, s * u * s⁻¹ = u) :
    ∃ x ∈ parabolicGraded τ K J (n + 1), x ≠ 0 ∧
      ∀ s ∈ S, (s : Module.End K (RootModule τ K)) x = x := by
  obtain ⟨x, hx, hxu⟩ := exists_layerMap_eq J n ((⟨u, hu⟩ : levelRadical τ K J (n + 1)) :
    Layer τ K J n)
  refine ⟨x, hx, fun h0 => ?_, fun s hs => ?_⟩
  · rw [h0, layerMap_zero] at hxu
    exact hu' (Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 hxu.symm))
  · refine layerMap_injOn J n (parabolicLevi_preserves (hS hs) _ hx) hx ?_
    rw [layerMap_parabolicLevi hτ h2 J n (hS hs) hx, hxu, levelConj_mk]
    congr 1
    exact Subtype.ext (by rw [coe_conjRestrict]; exact hfix s hs)

theorem exists_invariant_coset_of_fixed_vector
    [Finite K]
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (h2 : (2 : K) = 0) (J : Set (Fin τ.rank))
    (n : ℕ) {S : Subgroup (ModGL τ K)} (hS : S ≤ parabolicLevi τ K J) {x : RootModule τ K}
    (hx : x ∈ parabolicGraded τ K J (n + 1)) (hx0 : x ≠ 0)
    (hfix : ∀ s ∈ S, (s : Module.End K (RootModule τ K)) x = x) :
    ∃ u ∈ levelRadical τ K J (n + 1), u ∉ levelRadical τ K J (n + 1 + 1) ∧
      ∀ s ∈ S, u⁻¹ * (s * u * s⁻¹) ∈ levelRadical τ K J (n + 1 + 1) := by
  obtain ⟨⟨u, hu⟩, hux⟩ := QuotientGroup.mk_surjective (layerMap J n x)
  refine ⟨u, hu, fun hu' => hx0 ?_, fun s hs => ?_⟩
  · refine layerMap_injOn J n hx (Submodule.zero_mem _) ?_
    rw [layerMap_zero, ← hux]
    exact (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hu')
  · have h1 := layerMap_parabolicLevi hτ h2 J n (hS hs) hx
    rw [hfix s hs, ← hux, levelConj_mk] at h1
    have h3 := QuotientGroup.eq.1 h1
    rw [Subgroup.mem_subgroupOf] at h3
    simpa [coe_conjRestrict] using h3

end CFSG.LieType.Chevalley.EvenOddRadical
