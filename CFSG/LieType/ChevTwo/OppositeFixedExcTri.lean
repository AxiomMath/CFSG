module

public import CFSG.LieType.ChevTwo.OppositeFixedExcE78
public import CFSG.LieType.Chevalley.EvenTrialityAutomorphismNormalForm
public import CFSG.LieType.Chevalley.E6GraphInvertedRootRotation
public import CFSG.RankThree.PartOne.Q1327T.Item7D4W

public section

namespace CFSG.LieType.ChevTwo.Semi

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.EvenOddRadical CFSG.Open CFSG.LieType.BorelTits

theorem eq_one_of_mul_self_of_twoTri {K : Type} [Field K] (h2 : (2 : K) = 0) {ε : K}
    (h : ε * ε = 1) : ε = 1 := by
  have h' : (ε - 1) * (ε - 1) = 0 := by linear_combination h + (1 - ε) * h2
  exact sub_eq_zero.1 (mul_self_eq_zero.1 h')

theorem symm_mem_iff_of_stableTri {ι : Type*} {π : Equiv.Perm ι} {A : Set ι}
    (hA : ∀ i, π i ∈ A ↔ i ∈ A) (i : ι) : π.symm i ∈ A ↔ i ∈ A := by
  have h := hA (π.symm i)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

theorem parabolicDegree_permLattice_of_stable {τ : Tag} {π : Equiv.Perm (Fin τ.rank)}
    {A : Set (Fin τ.rank)} (hA : ∀ i, π i ∈ A ↔ i ∈ A) (v : Fin τ.rank → ℤ) :
    parabolicDegree τ A (permLattice π v) = parabolicDegree τ A v := by
  unfold parabolicDegree
  refine Fintype.sum_equiv π.symm _ _ fun i => ?_
  have hi := symm_mem_iff_of_stableTri hA i
  by_cases h : i ∈ A
  · rw [if_pos h, if_pos (hi.2 h)]
  · rw [if_neg h, if_neg (mt hi.1 h)]
    rfl

theorem perm_mem_orbitUnion_iff {t : TwistTag} (J : Set (Fin t.foldedTag.rank))
    (i : Fin t.tag.rank) : t.perm i ∈ t.orbitUnion J ↔ i ∈ t.orbitUnion J := by
  rw [mem_orbitUnion_iff_orbitIndex, mem_orbitUnion_iff_orbitIndex, t.orbitIndex_perm]

section Cert


section Roots

variable {τ : Tag}

theorem permLattice_mem_levelRoots_of_stable {π : Equiv.Perm (Fin τ.rank)}
    (hπ : ∀ i j, τ.cartan (π i) (π j) = τ.cartan i j) {A : Set (Fin τ.rank)}
    (hA : ∀ i, π i ∈ A ↔ i ∈ A) {d : ℤ} {α : Fin τ.rank → ℤ} (hα : α ∈ levelRoots τ A d) :
    permLattice π α ∈ levelRoots τ A d :=
  ⟨hα.1.permLattice hπ, by rw [height_permLattice]; exact hα.2.1,
    by rw [parabolicDegree_permLattice_of_stable hA]; exact hα.2.2⟩

theorem permLattice_mem_layerRoots_of_stable {π : Equiv.Perm (Fin τ.rank)}
    (hπ : ∀ i j, τ.cartan (π i) (π j) = τ.cartan i j) {A : Set (Fin τ.rank)}
    (hA : ∀ i, π i ∈ A ↔ i ∈ A) {d : ℤ} {α : Fin τ.rank → ℤ} (hα : α ∈ layerRoots τ A d) :
    permLattice π α ∈ layerRoots τ A d :=
  ⟨hα.1.permLattice hπ, by rw [height_permLattice]; exact hα.2.1,
    by rw [parabolicDegree_permLattice_of_stable hA]; exact hα.2.2⟩

end Roots

section Diagram

variable {t : TwistTag} {K : Type} [Field K]

theorem twistHom_id_eq_conj :
    twistHom t K (RingHom.id K) = (MulAut.conj (diagramMap t K)).toMonoidHom := by
  refine MonoidHom.ext fun g => ?_
  rw [twistHom_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    show Units.map (entrywiseHom (RingHom.id K)) g = g from
      Units.ext (entrywise_id (g : Module.End K (RootModule t.tag K)))]

theorem diagramMap_mem_normalizer_rootSpan {S : Set (Fin t.tag.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot t.tag α) (h₁ : ∀ α ∈ S, permLattice t.perm α ∈ S)
    (h₂ : ∀ α ∈ S, permLattice t.perm.symm α ∈ S) :
    diagramMap t K ∈ Subgroup.normalizer (rootSpan t.tag K S : Set (ModGL t.tag K)) := by
  have hmap := map_twistHom_rootSpan_of_stable (K := K) (σ := RingHom.id K)
    (fun c => ⟨c, rfl⟩) hS h₁ h₂
  rw [twistHom_id_eq_conj] at hmap
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    rw [← hmap]
    exact ⟨h, hh, rfl⟩
  · intro hh
    rw [← hmap] at hh
    obtain ⟨h', hh', he⟩ := hh
    have he' : diagramMap t K * h' * (diagramMap t K)⁻¹ =
        diagramMap t K * h * (diagramMap t K)⁻¹ := he
    have e : h' = h := mul_left_cancel (mul_right_cancel he')
    exact e ▸ hh'

theorem diagramMap_mem_normalizer_levelRadical {A : Set (Fin t.tag.rank)}
    (hA : ∀ i, t.perm i ∈ A ↔ i ∈ A) (d : ℤ) :
    diagramMap t K ∈ Subgroup.normalizer (levelRadical t.tag K A d : Set (ModGL t.tag K)) :=
  diagramMap_mem_normalizer_rootSpan (fun _ h => h.1)
    (fun _ h => permLattice_mem_levelRoots_of_stable t.cartan_perm hA h)
    (fun _ h => permLattice_mem_levelRoots_of_stable (cartan_perm_symm t.cartan_perm)
      (symm_mem_iff_of_stableTri hA) h)

theorem diagramMap_mem_parabolicGraded {A : Set (Fin t.tag.rank)}
    (hA : ∀ i, t.perm i ∈ A ↔ i ∈ A) {d : ℤ} {x : RootModule t.tag K}
    (hx : x ∈ parabolicGraded t.tag K A d) :
    (diagramMap t K : Module.End K (RootModule t.tag K)) x ∈ parabolicGraded t.tag K A d := by
  have hle : parabolicGraded t.tag K A d ≤ (parabolicGraded t.tag K A d).comap
      (diagramMap t K : Module.End K (RootModule t.tag K)) := by
    unfold parabolicGraded
    rw [Submodule.span_le]
    rintro x (⟨α, hα, hd, rfl⟩ | ⟨hd, i, rfl⟩)
    · rw [SetLike.mem_coe, Submodule.mem_comap, diagramMap_apply_rootVec]
      exact Submodule.subset_span (Or.inl ⟨permLattice t.perm α, hα.permLattice t.cartan_perm,
        by rw [parabolicDegree_permLattice_of_stable hA, hd], rfl⟩)
    · rw [SetLike.mem_coe, Submodule.mem_comap, diagramMap_hVec]
      exact Submodule.subset_span (Or.inr ⟨hd, t.perm i, rfl⟩)
  exact hle hx

@[expose] noncomputable def layerConjTri {τ : Tag} {J : Set (Fin τ.rank)} {n : ℕ}
    {g : ModGL τ K}
    (h1 : g ∈ Subgroup.normalizer (levelRadical τ K J (n + 1) : Set (ModGL τ K)))
    (h2 : g ∈ Subgroup.normalizer (levelRadical τ K J (n + 1 + 1) : Set (ModGL τ K))) :
    Layer τ K J n →* Layer τ K J n :=
  QuotientGroup.map _ _ (EvenOddRadical.conjRestrict h1) fun u hu => by
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, EvenOddRadical.coe_conjRestrict]
    exact (Subgroup.mem_normalizer_iff.1 h2 u).1 (Subgroup.mem_subgroupOf.1 hu)

theorem layerConjTri_mk {τ : Tag} {J : Set (Fin τ.rank)} {n : ℕ} {g : ModGL τ K}
    (h1 : g ∈ Subgroup.normalizer (levelRadical τ K J (n + 1) : Set (ModGL τ K)))
    (h2 : g ∈ Subgroup.normalizer (levelRadical τ K J (n + 1 + 1) : Set (ModGL τ K)))
    (u : levelRadical τ K J (n + 1)) :
    layerConjTri h1 h2 (u : Layer τ K J n) =
      ((EvenOddRadical.conjRestrict h1 u : levelRadical τ K J (n + 1)) : Layer τ K J n) :=
  rfl

theorem layerMap_of_basis_hom {τ : Tag} {J : Set (Fin τ.rank)} {n : ℕ}
    (f : Module.End K (RootModule τ K)) (φ : Layer τ K J n →* Layer τ K J n)
    (hbasis : ∀ α ∈ layerRoots τ J (n + 1), ∀ c : K,
      layerMap J n (f (c • rootVec τ K α)) = φ (layerMap J n (c • rootVec τ K α)))
    {x : RootModule τ K} (hx : x ∈ parabolicGraded τ K J (n + 1)) :
    layerMap J n (f x) = φ (layerMap J n x) := by
  rw [parabolicGraded_eq_supported, Finsupp.mem_supported] at hx
  have hterm : ∀ b ∈ x.support, layerMap J n (f (Finsupp.single b (x b))) =
      φ (layerMap J n (Finsupp.single b (x b))) := by
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

theorem layerMap_diagramMap (h2 : (2 : K) = 0) {A : Set (Fin t.tag.rank)}
    (hA : ∀ i, t.perm i ∈ A ↔ i ∈ A) (n : ℕ) {x : RootModule t.tag K}
    (hx : x ∈ parabolicGraded t.tag K A (n + 1)) {u : ModGL t.tag K}
    (hu : u ∈ levelRadical t.tag K A (n + 1))
    (hgu : diagramMap t K * u * (diagramMap t K)⁻¹ ∈ levelRadical t.tag K A (n + 1))
    (hxu : layerMap A n x = QuotientGroup.mk (⟨u, hu⟩ : levelRadical t.tag K A (n + 1))) :
    layerMap A n ((diagramMap t K : Module.End K (RootModule t.tag K)) x) =
      QuotientGroup.mk (⟨diagramMap t K * u * (diagramMap t K)⁻¹, hgu⟩ :
        levelRadical t.tag K A (n + 1)) := by
  have h1 := diagramMap_mem_normalizer_levelRadical (K := K) hA (n + 1)
  have h1' := diagramMap_mem_normalizer_levelRadical (K := K) hA (n + 1 + 1)
  have hbasis : ∀ α ∈ layerRoots t.tag A (n + 1), ∀ c : K,
      layerMap A n ((diagramMap t K : Module.End K (RootModule t.tag K)) (c • rootVec t.tag K α)) =
        layerConjTri h1 h1' (layerMap A n (c • rootVec t.tag K α)) := by
    intro α hα c
    obtain ⟨ε, hε, hεc⟩ := diagramMap_conj_pinnedX (K := K) t hα.1
    have hε1 := eq_one_of_mul_self_of_twoTri h2 hε
    rw [map_smul, diagramMap_apply_rootVec,
      layerMap_smul_rootVec A n (permLattice_mem_layerRoots_of_stable t.cartan_perm hA hα) c,
      layerMap_smul_rootVec A n hα c, layerConjTri_mk]
    congr 1
    refine Subtype.ext ?_
    rw [EvenOddRadical.coe_conjRestrict, hεc c, hε1, one_mul]
  rw [layerMap_of_basis_hom _ (layerConjTri h1 h1') hbasis hx, hxu]
  rfl

theorem rootPairing_diagramMap {A : Set (Fin t.tag.rank)} (n : ℕ) {x y : RootModule t.tag K}
    (hx : x ∈ parabolicGraded t.tag K A (n + 1)) (hy : y ∈ parabolicGraded t.tag K A (-(n + 1))) :
    rootPairing t.tag K ((diagramMap t K : Module.End K (RootModule t.tag K)) x)
        ((diagramMap t K : Module.End K (RootModule t.tag K)) y) = rootPairing t.tag K x y := by
  refine rootPairing_map_of_basis _ (fun α _ β _ => ?_) hx hy
  rw [diagramMap_apply_rootVec, diagramMap_apply_rootVec, rootPairing_rootVec,
    rootPairing_rootVec]
  have hiff : (IsRoot t.tag (permLattice t.perm α) ∧
      permLattice t.perm α + permLattice t.perm (-β) = 0) ↔ (IsRoot t.tag α ∧ α + -β = 0) := by
    rw [isRoot_permLattice_iff t.cartan_perm]
    refine and_congr_right fun _ => ⟨fun h => ?_, fun h => ?_⟩
    · apply permLattice_injective t.perm
      rw [permLattice_add, h]
      rfl
    · rw [← permLattice_add, h]
      rfl
  by_cases h : IsRoot t.tag α ∧ α + -β = 0
  · rw [if_pos (hiff.2 h), if_pos h]
  · rw [if_neg (mt hiff.1 h), if_neg h]

end Diagram

section Good

variable {τ : Tag} {K : Type} [Field K]

variable (τ K) in
@[expose] def LayerGood (A : Set (Fin τ.rank)) (g : ModGL τ K) : Prop :=
  (∀ d : ℤ, ∀ x ∈ parabolicGraded τ K A d,
    (g : Module.End K (RootModule τ K)) x ∈ parabolicGraded τ K A d) ∧
  (∀ d : ℤ, 1 ≤ d → g ∈ Subgroup.normalizer (levelRadical τ K A d : Set (ModGL τ K))) ∧
  (∀ (n : ℕ) (x : RootModule τ K) (u : ModGL τ K) (hu : u ∈ levelRadical τ K A (n + 1))
    (hgu : g * u * g⁻¹ ∈ levelRadical τ K A (n + 1)), x ∈ parabolicGraded τ K A (n + 1) →
    layerMap A n x = QuotientGroup.mk (⟨u, hu⟩ : levelRadical τ K A (n + 1)) →
    layerMap A n ((g : Module.End K (RootModule τ K)) x) =
      QuotientGroup.mk (⟨g * u * g⁻¹, hgu⟩ : levelRadical τ K A (n + 1))) ∧
  (∀ (n : ℕ) (x y : RootModule τ K), x ∈ parabolicGraded τ K A (n + 1) →
    y ∈ parabolicGraded τ K A (-(n + 1)) →
    rootPairing τ K ((g : Module.End K (RootModule τ K)) x)
      ((g : Module.End K (RootModule τ K)) y) = rootPairing τ K x y)

theorem LayerGood.mul {A : Set (Fin τ.rank)} {g h : ModGL τ K} (hg : LayerGood τ K A g)
    (hh : LayerGood τ K A h) : LayerGood τ K A (g * h) := by
  obtain ⟨hg1, hg2, hg3, hg4⟩ := hg
  obtain ⟨hh1, hh2, hh3, hh4⟩ := hh
  refine ⟨fun d x hx => ?_, fun d hd => mul_mem (hg2 d hd) (hh2 d hd),
    fun n x u hu hgu hx hxu => ?_, fun n x y hx hy => ?_⟩
  · rw [Units.val_mul, Module.End.mul_apply]
    exact hg1 d _ (hh1 d x hx)
  · have hhu : h * u * h⁻¹ ∈ levelRadical τ K A (n + 1) :=
      (Subgroup.mem_normalizer_iff.1 (hh2 _ (one_le_succ n)) u).1 hu
    have hghu : g * (h * u * h⁻¹) * g⁻¹ ∈ levelRadical τ K A (n + 1) :=
      (Subgroup.mem_normalizer_iff.1 (hg2 _ (one_le_succ n)) _).1 hhu
    rw [Units.val_mul, Module.End.mul_apply,
      hg3 n _ (h * u * h⁻¹) hhu hghu (hh1 _ x hx) (hh3 n x u hu hhu hx hxu)]
    exact congrArg QuotientGroup.mk (Subtype.ext (by group))
  · rw [Units.val_mul, Module.End.mul_apply, Module.End.mul_apply,
      hg4 n _ _ (hh1 _ x hx) (hh1 _ y hy), hh4 n x y hx hy]

theorem layerGood_of_mem_parabolicLevi (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (h2 : (2 : K) = 0) {A : Set (Fin τ.rank)} {g : ModGL τ K} (hg : g ∈ parabolicLevi τ K A) :
    LayerGood τ K A g := by
  refine ⟨fun d x hx => parabolicLevi_preserves hg d hx,
    fun d hd => parabolicLevi_le_normalizer A hd hg, fun n x u hu hgu hx hxu => ?_,
    fun n x y hx hy => rootPairing_parabolicLevi hτ h2 A n hg hx hy⟩
  rw [layerMap_parabolicLevi hτ h2 A n hg hx, hxu, levelConj_mk]
  rfl

theorem layerGood_diagramMap {t : TwistTag} (h2 : (2 : K) = 0) {A : Set (Fin t.tag.rank)}
    (hA : ∀ i, t.perm i ∈ A ↔ i ∈ A) : LayerGood t.tag K A (diagramMap t K) :=
  ⟨fun _ _ hx => diagramMap_mem_parabolicGraded hA hx,
    fun d _ => diagramMap_mem_normalizer_levelRadical hA d,
    fun n _ _ hu hgu hx hxu => layerMap_diagramMap h2 hA n hx hu hgu hxu,
    fun n _ _ hx hy => rootPairing_diagramMap n hx hy⟩

theorem layerGood_mul_pow {t : TwistTag} (hτ : t.tag = .D4 ∨ t.tag = .E6 ∨ t.tag = .E7 ∨
    t.tag = .E8) (h2 : (2 : K) = 0) {A : Set (Fin t.tag.rank)}
    (hA : ∀ i, t.perm i ∈ A ↔ i ∈ A) {m : ModGL t.tag K} (hm : m ∈ parabolicLevi t.tag K A)
    (i : ℕ) : LayerGood t.tag K A (m * diagramMap t K ^ i) := by
  induction i with
  | zero =>
    rw [pow_zero, mul_one]
    exact layerGood_of_mem_parabolicLevi hτ h2 hm
  | succ i ih =>
    rw [pow_succ, ← mul_assoc]
    exact ih.mul (layerGood_diagramMap h2 hA)

theorem smul_mem_graded_good {A : Set (Fin τ.rank)} {s : GamL τ K}
    (hs : LayerGood τ K A s.left) (d : ℤ) {x : RootModule τ K}
    (hx : x ∈ parabolicGraded τ K A d) : s • x ∈ parabolicGraded τ K A d :=
  hs.1 d _ (vtw_mem_graded s.right hx)

theorem conjAct_mem_levelRadical_good {A : Set (Fin τ.rank)} {s : GamL τ K}
    (hs : LayerGood τ K A s.left) {d : ℤ} (hd : 1 ≤ d) {u : ModGL τ K}
    (hu : u ∈ levelRadical τ K A d) : conjAct τ K s u ∈ levelRadical τ K A d := by
  rw [conjAct_apply]
  exact (Subgroup.mem_normalizer_iff.1 (hs.2.1 d hd) _).1 (fieldAut_mem_levelRadical s.right hu)

theorem layerMap_smul_good {A : Set (Fin τ.rank)} (n : ℕ) {s : GamL τ K}
    (hs : LayerGood τ K A s.left) {x : RootModule τ K}
    (hx : x ∈ parabolicGraded τ K A (n + 1)) {u : ModGL τ K}
    (hu : u ∈ levelRadical τ K A (n + 1))
    (hxu : layerMap A n x = QuotientGroup.mk (⟨u, hu⟩ : levelRadical τ K A (n + 1))) :
    layerMap A n (s • x) = QuotientGroup.mk (⟨conjAct τ K s u,
      conjAct_mem_levelRadical_good hs (one_le_succ n) hu⟩ : levelRadical τ K A (n + 1)) := by
  have hvu : layerMap A n (vtw s.right x) = QuotientGroup.mk (⟨fieldAutHom τ K s.right u,
      fieldAut_mem_levelRadical s.right hu⟩ : levelRadical τ K A (n + 1)) := by
    rw [layerMap_vtw, hxu, phiLayer_mk]
  have hgu : s.left * fieldAutHom τ K s.right u * s.left⁻¹ ∈ levelRadical τ K A (n + 1) :=
    conjAct_mem_levelRadical_good hs (one_le_succ n) hu
  rw [smul_def, hs.2.2.1 n _ _ _ hgu (vtw_mem_graded s.right hx) hvu]
  rfl

theorem pairing_smul_good {A : Set (Fin τ.rank)} (n : ℕ) {s : GamL τ K}
    (hs : LayerGood τ K A s.left) {x y : RootModule τ K}
    (hx : x ∈ parabolicGraded τ K A (n + 1)) (hy : y ∈ parabolicGraded τ K A (-(n + 1))) :
    trK (rootPairing τ K (s • x) (s • y)) = trK (rootPairing τ K x y) := by
  rw [smul_def, smul_def, hs.2.2.2 n _ _ (vtw_mem_graded _ hx) (vtw_mem_graded _ hy),
    rootPairing_vtw, trK_ringAut]

theorem exists_fixed_vector_good [Finite K] {A : Set (Fin τ.rank)} (n : ℕ)
    {S : Subgroup (GamL τ K)} (hS : ∀ s ∈ S, LayerGood τ K A s.left) {u : ModGL τ K}
    (hu : u ∈ levelRadical τ K A (n + 1)) (hu' : u ∉ levelRadical τ K A (n + 1 + 1))
    (hfix : ∀ s ∈ S, conjAct τ K s u = u) :
    ∃ x ∈ parabolicGraded τ K A (n + 1), x ≠ 0 ∧ ∀ s ∈ S, s • x = x := by
  obtain ⟨x, hx, hxu⟩ := exists_layerMap_eq A n
    ((⟨u, hu⟩ : levelRadical τ K A (n + 1)) : Layer τ K A n)
  refine ⟨x, hx, fun h0 => ?_, fun s hs => ?_⟩
  · rw [h0, layerMap_zero] at hxu
    exact hu' (Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 hxu.symm))
  · refine layerMap_injOn A n (smul_mem_graded_good (hS s hs) _ hx) hx ?_
    rw [layerMap_smul_good n (hS s hs) hx hu hxu, hxu]
    congr 1
    exact Subtype.ext (hfix s hs)

theorem exists_invariant_coset_good [Finite K] {A : Set (Fin τ.rank)} (n : ℕ)
    {S : Subgroup (GamL τ K)} (hS : ∀ s ∈ S, LayerGood τ K A s.left) {x : RootModule τ K}
    (hx : x ∈ parabolicGraded τ K A (n + 1)) (hx0 : x ≠ 0) (hfix : ∀ s ∈ S, s • x = x) :
    ∃ u ∈ levelRadical τ K A (n + 1), u ∉ levelRadical τ K A (n + 1 + 1) ∧
      ∀ s ∈ S, u⁻¹ * conjAct τ K s u ∈ levelRadical τ K A (n + 1 + 1) := by
  obtain ⟨⟨u, hu⟩, hux⟩ := QuotientGroup.mk_surjective (layerMap A n x)
  refine ⟨u, hu, fun hu' => hx0 ?_, fun s hs => ?_⟩
  · refine layerMap_injOn A n hx (Submodule.zero_mem _) ?_
    rw [layerMap_zero, ← hux]
    exact (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hu')
  · have h1 := layerMap_smul_good n (hS s hs) hx hu hux.symm
    rw [hfix s hs, ← hux] at h1
    have h3 := QuotientGroup.eq.1 h1
    rw [Subgroup.mem_subgroupOf] at h3
    simpa using h3

theorem exists_fixed_neg_good [Finite K] (h2 : (2 : K) = 0) {A : Set (Fin τ.rank)} (n : ℕ)
    {S : Subgroup (GamL τ K)} (hS : ∀ s ∈ S, LayerGood τ K A s.left)
    (hodd : Odd (Nat.card S)) {x : RootModule τ K} (hx : x ∈ parabolicGraded τ K A (n + 1))
    (hx0 : x ≠ 0) (hfix : ∀ s ∈ S, s • x = x) :
    ∃ y ∈ parabolicGraded τ K A (-(n + 1)), y ≠ 0 ∧ ∀ s ∈ S, s • y = y := by
  classical
  have : Finite S := Nat.finite_of_card_ne_zero (Nat.pos_of_ne_zero (by
    rintro h; rw [h] at hodd; exact absurd hodd (by decide))).ne'
  let _ : Fintype S := Fintype.ofFinite S
  obtain ⟨b, hb⟩ : ∃ b, x b ≠ 0 := by
    by_contra h
    push Not at h
    exact hx0 (Finsupp.ext h)
  have hbL : b ∈ gradedLabels τ A (n + 1) := by
    have hx' := hx
    rw [parabolicGraded_eq_supported] at hx'
    exact (Finsupp.mem_supported K x).1 hx' (Finsupp.mem_support_iff.2 hb)
  obtain ⟨α, hα, hbeq⟩ := mem_layerRoots_of_mem_gradedLabels hbL
  have hαr : IsRoot τ α := hα.1
  have hb' : x (Sum.inr ⟨α, hαr⟩) ≠ 0 := by rw [hbeq] at hb; exact hb
  obtain ⟨c, hc⟩ := exists_trK_ne_zero hb'
  have hy₀ : c • rootVec τ K (-α) ∈ parabolicGraded τ K A (-(n + 1)) :=
    Submodule.smul_mem _ _ (rootVec_mem_parabolicGraded (IsRoot.neg hαr)
      (by rw [parabolicDegree_neg, hα.2.2]))
  set y₀ : RootModule τ K := c • rootVec τ K (-α) with hy₀def
  set y : RootModule τ K := ∑ s : S, (s : GamL τ K) • y₀ with hy
  have hyG : y ∈ parabolicGraded τ K A (-(n + 1)) :=
    Submodule.sum_mem _ fun s _ => smul_mem_graded_good (hS s s.2) _ hy₀
  have hpr : rootPairing τ K x (rootVec τ K (-α)) = x (Sum.inr ⟨α, hαr⟩) :=
    rootPairing_rootVec_neg hαr x
  have hterm : ∀ s : S, trK (rootPairing τ K x ((s : GamL τ K) • y₀)) =
      trK (x (Sum.inr ⟨α, hαr⟩) * c) := fun s => by
    conv_lhs => rw [← hfix s s.2]
    rw [pairing_smul_good n (hS s s.2) hx hy₀, hy₀def, map_smul, hpr, smul_eq_mul, mul_comm]
  have hsum : rootPairing τ K x y = ∑ s : S, rootPairing τ K x ((s : GamL τ K) • y₀) := by
    rw [hy, map_sum]
  have htr : trK (rootPairing τ K x y) =
      ∑ s : S, trK (rootPairing τ K x ((s : GamL τ K) • y₀)) := by
    rw [hsum]
    exact map_sum trKHom _ Finset.univ
  have hpair : trK (rootPairing τ K x y) = trK (x (Sum.inr ⟨α, hαr⟩) * c) := by
    rw [htr, Finset.sum_congr rfl fun s _ => hterm s, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, Fintype.card_eq_nat_card, natCast_eq_one_of_odd h2 hodd, one_mul]
  refine ⟨y, hyG, fun h0 => hc ?_, fun s hs => ?_⟩
  · rw [← hpair, h0, map_zero, trK_zero]
  · rw [hy, smul_sum']
    refine Fintype.sum_equiv (Equiv.mulLeft (⟨s, hs⟩ : S)) _ _ fun t => ?_
    simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, mul_smul]

end Good

section Longest

variable {K : Type} [Field K]

theorem d4NegOne_mul_self :
    CFSG.RankThree.PartOne.Q1327T.d4NegOne * CFSG.RankThree.PartOne.Q1327T.d4NegOne = 1 :=
  ext_single fun i => by
    rw [mul_smul, CFSG.RankThree.PartOne.Q1327T.d4NegOne_smul,
      CFSG.RankThree.PartOne.Q1327T.d4NegOne_smul, neg_neg, one_smul]

theorem reversesSigns_d4NegOne : ReversesSigns CFSG.RankThree.PartOne.Q1327T.d4NegOne :=
  fun α _ hα => by
    rw [CFSG.RankThree.PartOne.Q1327T.d4NegOne_smul, height_neg]
    omega

theorem diagramMap_conj_canonicalRep_d4NegOne :
    diagramMap TwistTag.D4 K *
        canonicalRep (coxeterSystem TwistTag.D4.tag) K CFSG.RankThree.PartOne.Q1327T.d4NegOne *
        (diagramMap TwistTag.D4 K)⁻¹ =
      canonicalRep (coxeterSystem TwistTag.D4.tag) K CFSG.RankThree.PartOne.Q1327T.d4NegOne := by
  have h := twistHom_canonicalRep TwistTag.D4 K (RingHom.id K)
    CFSG.RankThree.PartOne.Q1327T.d4NegOne
  rw [twistHom_id_eq_conj, CFSG.RankThree.PartOne.Q1327T.weylTwist_d4NegOne] at h
  exact h

theorem exists_fixed_mem_oppRadical_tri [Finite K] [CharP K 2]
    {A : Set (Fin TwistTag.D4.tag.rank)} (hA : ∀ i, TwistTag.D4.perm i ∈ A ↔ i ∈ A)
    {S : Subgroup (GamL TwistTag.D4.tag K)}
    (hS : ∀ s ∈ S, ∃ m ∈ parabolicLevi TwistTag.D4.tag K A, ∃ i : ℕ,
      s.left = m * diagramMap TwistTag.D4 K ^ i)
    (hodd : Odd (Nat.card S)) {u : ModGL TwistTag.D4.tag K}
    (hu : u ∈ parabolicRadical TwistTag.D4.tag K A) (hu1 : u ≠ 1)
    (hfix : ∀ s ∈ S, conjAct TwistTag.D4.tag K s u = u) :
    ∃ v ∈ oppRadical TwistTag.D4.tag K A, v ≠ 1 ∧
      ∀ s ∈ S, conjAct TwistTag.D4.tag K s v = v := by
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_modGL (τ := TwistTag.D4.tag) (K := K)
  have hτ : TwistTag.D4.tag = .D4 ∨ TwistTag.D4.tag = .E6 ∨ TwistTag.D4.tag = .E7 ∨
      TwistTag.D4.tag = .E8 := Or.inl rfl
  have hgood : ∀ s ∈ S, LayerGood TwistTag.D4.tag K A s.left := by
    intro s hs
    obtain ⟨m, hm, i, he⟩ := hS s hs
    rw [he]
    exact layerGood_mul_pow hτ h2 hA hm i
  obtain ⟨n, hun, hun'⟩ := exists_level hu hu1
  obtain ⟨x, hx, hx0, hxS⟩ := exists_fixed_vector_good n hgood hun hun' hfix
  obtain ⟨y, hy, hy0, hyS⟩ := exists_fixed_neg_good h2 n hgood hodd hx hx0 hxS
  set w₀ := CFSG.RankThree.PartOne.Q1327T.d4NegOne with hw₀
  have hinj : Function.Injective (id : Fin TwistTag.D4.tag.rank → Fin TwistTag.D4.tag.rank) :=
    Function.injective_id
  have hδ : ∀ i, w₀ • (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ) = -Pi.single (id i) 1 :=
    CFSG.RankThree.PartOne.Q1327T.d4NegOne_smul_single
  set n₀ := canonicalRep (coxeterSystem TwistTag.D4.tag) K w₀ with hn₀
  have hn₀σ : ∀ σ : RingAut K, fieldAutHom TwistTag.D4.tag K σ n₀ = n₀ := fun σ =>
    entrywise_canonicalRep σ w₀
  have hcomm : Commute n₀ (diagramMap TwistTag.D4 K) :=
    (mul_inv_eq_iff_eq_mul.1 (diagramMap_conj_canonicalRep_d4NegOne (K := K))).symm
  set c₀ : GamL TwistTag.D4.tag K := SemidirectProduct.inl n₀ with hc₀
  set S' : Subgroup (GamL TwistTag.D4.tag K) := S.map (MulAut.conj c₀).toMonoidHom with hS'
  have hS'M : ∀ s' ∈ S', LayerGood TwistTag.D4.tag K A s'.left := by
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨m, hm, i, he⟩ := hS s hs
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hc₀, inl_conj_left n₀ hn₀σ, he]
    have hm' : n₀ * m * n₀⁻¹ ∈ parabolicLevi TwistTag.D4.tag K A := by
      have h := map_conj_parabolicLevi_le (δ := id) hδ A (Subgroup.mem_map.2 ⟨m, hm, rfl⟩)
      rw [Set.image_id] at h
      exact h
    have e : n₀ * (m * diagramMap TwistTag.D4 K ^ i) * n₀⁻¹ =
        n₀ * m * n₀⁻¹ * diagramMap TwistTag.D4 K ^ i := by
      calc n₀ * (m * diagramMap TwistTag.D4 K ^ i) * n₀⁻¹ =
          n₀ * m * n₀⁻¹ * (n₀ * diagramMap TwistTag.D4 K ^ i * n₀⁻¹) := by group
        _ = n₀ * m * n₀⁻¹ * diagramMap TwistTag.D4 K ^ i := by
          rw [(hcomm.pow_right i).eq, mul_inv_cancel_right]
    rw [e]
    exact layerGood_mul_pow hτ h2 hA hm' i
  have hodd' : Odd (Nat.card S') := by
    rwa [hS', Subgroup.card_map_of_injective (MulAut.conj c₀).injective]
  have hx' : (n₀ : Module.End K (RootModule TwistTag.D4.tag K)) y ∈
      parabolicGraded TwistTag.D4.tag K A (n + 1) := by
    have h := longest_mem_parabolicGraded hinj hδ A (n + 1) hy
    rw [Set.image_id] at h
    exact h
  have hx'0 : (n₀ : Module.End K (RootModule TwistTag.D4.tag K)) y ≠ 0 := fun h => hy0 (by
    rw [← units_inv_apply_apply n₀ y, h, map_zero])
  have hc₀y : c₀ • y = (n₀ : Module.End K (RootModule TwistTag.D4.tag K)) y := by
    rw [smul_def, hc₀, SemidirectProduct.left_inl, SemidirectProduct.right_inl, vtw_one]
  have hx'S : ∀ s' ∈ S', s' • ((n₀ : Module.End K (RootModule TwistTag.D4.tag K)) y) =
      (n₀ : Module.End K (RootModule TwistTag.D4.tag K)) y := by
    rintro _ ⟨s, hs, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← hc₀y, ← mul_smul, inv_mul_cancel_right, mul_smul, hyS s hs]
  obtain ⟨u', hu', hu'', hcos⟩ := exists_invariant_coset_good n hS'M hx' hx'0 hx'S
  have hN1 : ∀ b ∈ S', ∀ z ∈ levelRadical TwistTag.D4.tag K A (n + 1),
      conjAct TwistTag.D4.tag K b z ∈ levelRadical TwistTag.D4.tag K A (n + 1) :=
    fun b hb z hz => conjAct_mem_levelRadical_good (hS'M b hb) (one_le_succ n) hz
  have hN2 : ∀ b ∈ S', ∀ z ∈ levelRadical TwistTag.D4.tag K A (n + 1 + 1),
      conjAct TwistTag.D4.tag K b z ∈ levelRadical TwistTag.D4.tag K A (n + 1 + 1) :=
    fun b hb z hz => conjAct_mem_levelRadical_good (hS'M b hb) (one_le_succ_succ n) hz
  letI : MulDistribMulAction S' (levelRadical TwistTag.D4.tag K A (n + 1)) :=
    actSub S' _ hN1
  have hinv : CFSG.IsInvariant S' (levelRadical TwistTag.D4.tag K A (n + 1))
      ((levelRadical TwistTag.D4.tag K A (n + 1 + 1)).subgroupOf
        (levelRadical TwistTag.D4.tag K A (n + 1))) :=
    CFSG.SolvableHall.isInvariant_of_forall_smul_mem fun a z hz => by
      rw [Subgroup.mem_subgroupOf] at hz ⊢
      exact hN2 a a.2 z hz
  have hp : IsPGroup 2 ((levelRadical TwistTag.D4.tag K A (n + 1 + 1)).subgroupOf
      (levelRadical TwistTag.D4.tag K A (n + 1))) :=
    (isPGroup_levelRadical A (n + 1 + 1)).of_equiv
      (Subgroup.subgroupOfEquivOfLe (levelRadical_succ_le A (n + 1))).symm
  have hsolv : Group.IsSolvable ((levelRadical TwistTag.D4.tag K A (n + 1 + 1)).subgroupOf
      (levelRadical TwistTag.D4.tag K A (n + 1))) := by
    have := hp.isNilpotent
    infer_instance
  have hcop : Nat.Coprime (Nat.card S')
      (Nat.card ((levelRadical TwistTag.D4.tag K A (n + 1 + 1)).subgroupOf
        (levelRadical TwistTag.D4.tag K A (n + 1)))) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hp
    rw [hk]
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.2 hodd')
  have : Finite S' := Nat.finite_of_card_ne_zero (by
    rintro h; rw [h] at hodd'; exact absurd hodd' (by decide))
  obtain ⟨c, hc, hcu⟩ := CFSG.SolvableHall.exists_fixed_of_coset_fixed
    ((levelRadical TwistTag.D4.tag K A (n + 1 + 1)).subgroupOf
      (levelRadical TwistTag.D4.tag K A (n + 1)))
    hinv hsolv hcop ⟨u', hu'⟩ fun b => by
      rw [Subgroup.mem_subgroupOf]
      exact hcos b b.2
  have hcN : (c : ModGL TwistTag.D4.tag K) ∉ levelRadical TwistTag.D4.tag K A (n + 1 + 1) :=
    fun h => hu'' (by
      have h' := Subgroup.mem_subgroupOf.1 hcu
      have e : u' = (c : ModGL TwistTag.D4.tag K) *
          ((c⁻¹ * ⟨u', hu'⟩ : levelRadical TwistTag.D4.tag K A (n + 1)) :
            ModGL TwistTag.D4.tag K) := by simp
      rw [e]
      exact mul_mem h h')
  have hconjc : conjAct TwistTag.D4.tag K c₀⁻¹ = MulAut.conj n₀⁻¹ := by
    rw [map_inv, hc₀, conjAct_inl, ← map_inv]
  refine ⟨n₀⁻¹ * c * n₀, ?_, fun h => hcN ?_, fun s hs => ?_⟩
  · have hcQ : (c : ModGL TwistTag.D4.tag K) ∈ parabolicRadical TwistTag.D4.tag K A :=
      levelRadical_le_parabolicRadical _ (one_le_succ n) c.2
    have hle := map_conj_longest_parabolicRadical_le (K := K) hinj hδ d4NegOne_mul_self
      reversesSigns_d4NegOne A
    rw [Set.image_id] at hle
    have := hle (Subgroup.mem_map_of_mem _ hcQ)
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using this
  · have e : (c : ModGL TwistTag.D4.tag K) = n₀ * (n₀⁻¹ * c * n₀) * n₀⁻¹ := by group
    rw [e, h, mul_one, mul_inv_cancel]
    exact one_mem _
  · have hcs := congrArg Subtype.val (hc ⟨c₀ * s * c₀⁻¹, ⟨s, hs, rfl⟩⟩)
    change conjAct TwistTag.D4.tag K (c₀ * s * c₀⁻¹) (c : ModGL TwistTag.D4.tag K) = c at hcs
    rw [map_mul, map_mul, hconjc, hc₀, conjAct_inl] at hcs
    simp only [MulAut.mul_apply, MulAut.conj_apply] at hcs
    calc conjAct TwistTag.D4.tag K s (n₀⁻¹ * c * n₀) =
        n₀⁻¹ * (n₀ * conjAct TwistTag.D4.tag K s (n₀⁻¹ * c * n₀) * n₀⁻¹) * n₀ := by group
      _ = n₀⁻¹ * c * n₀ := by
        rw [show n₀ * conjAct TwistTag.D4.tag K s (n₀⁻¹ * c * n₀) * n₀⁻¹ = c from hcs]

end Longest

section LiftOn

variable {τ : Tag} {K : Type} [Field K]

variable (H : Subgroup (ModGL τ K)) in
@[expose] def UniqueNormalFormOn : Prop :=
  ∀ α : MulAut ↥H, ∃! gσ : ↥H × RingAut K, ∀ h : ↥H, ((α h : ↥H) : ModGL τ K) =
    (gσ.1 : ModGL τ K) * Units.map (entrywiseHom (gσ.2 : K →+* K)) (h : ModGL τ K) *
      (gσ.1 : ModGL τ K)⁻¹

variable {H : Subgroup (ModGL τ K)} (hNF : UniqueNormalFormOn H)

@[expose] noncomputable def liftAutOn (α : MulAut ↥H) : GamL τ K :=
  ⟨((hNF α).choose.1 : ModGL τ K), (hNF α).choose.2⟩

theorem liftAutOn_left_mem (α : MulAut ↥H) : (liftAutOn hNF α).left ∈ H :=
  (hNF α).choose.1.2

theorem liftAutOn_spec (α : MulAut ↥H) (h : ↥H) :
    ((α h : ↥H) : ModGL τ K) = conjAct τ K (liftAutOn hNF α) (h : ModGL τ K) := by
  rw [conjAct_apply]
  exact (hNF α).choose_spec.1 h

theorem liftAutOn_unique (α : MulAut ↥H) (g : GamL τ K) (hg : g.left ∈ H)
    (hspec : ∀ h : ↥H, ((α h : ↥H) : ModGL τ K) = conjAct τ K g (h : ModGL τ K)) :
    liftAutOn hNF α = g := by
  have h : (hNF α).choose = ((⟨g.left, hg⟩ : ↥H), g.right) :=
    (hNF α).unique (hNF α).choose_spec.1 (fun h => by
      rw [hspec h, conjAct_apply])
  refine SemidirectProduct.ext ?_ ?_
  · exact congrArg (fun p : ↥H × RingAut K => (p.1 : ModGL τ K)) h
  · exact congrArg (fun p : ↥H × RingAut K => p.2) h

theorem liftAutOn_one : liftAutOn hNF 1 = 1 :=
  liftAutOn_unique hNF 1 1 (one_mem _) fun h => by
    rw [map_one, MulAut.one_apply]
    rfl

theorem liftAutOn_mul (hH : ∀ σ : RingAut K, ∀ h ∈ H, fieldAutHom τ K σ h ∈ H)
    (α β : MulAut ↥H) : liftAutOn hNF (α * β) = liftAutOn hNF α * liftAutOn hNF β := by
  refine liftAutOn_unique hNF _ _ ?_ fun h => ?_
  · change (liftAutOn hNF α).left *
      fieldAutHom τ K (liftAutOn hNF α).right (liftAutOn hNF β).left ∈ _
    exact mul_mem (liftAutOn_left_mem hNF α) (hH _ _ (liftAutOn_left_mem hNF β))
  · rw [MulAut.mul_apply, liftAutOn_spec hNF α, liftAutOn_spec hNF β, map_mul, MulAut.mul_apply]

@[expose] noncomputable def liftHomOn (hH : ∀ σ : RingAut K, ∀ h ∈ H, fieldAutHom τ K σ h ∈ H) :
    MulAut ↥H →* GamL τ K where
  toFun := liftAutOn hNF
  map_one' := liftAutOn_one hNF
  map_mul' := liftAutOn_mul hNF hH

theorem liftHomOn_injective (hH : ∀ σ : RingAut K, ∀ h ∈ H, fieldAutHom τ K σ h ∈ H) :
    Function.Injective (liftHomOn hNF hH) := fun α β h => by
  refine MulEquiv.ext fun x => Subtype.ext ?_
  rw [liftAutOn_spec hNF α, liftAutOn_spec hNF β]
  exact congrArg (fun s => conjAct τ K s (x : ModGL τ K)) h

end LiftOn

section Triality

variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K)

theorem fieldAut_mem_graphFixedRootGroupTri {t : TwistTag} (δ : RingAut K)
    {h : ModGL t.tag K} (hh : h ∈ graphFixedRootGroup t K σ.toRingHom) :
    fieldAutHom t.tag K δ h ∈ graphFixedRootGroup t K σ.toRingHom :=
  units_map_entrywiseHom_mem_graphFixedRootGroup (fun c => ringEquiv_comm_of_finite σ δ c) hh

theorem fieldAut_mem_twistedFixedGroupTri {t : TwistTag} (δ : RingAut K)
    {h : ModGL t.tag K} (hh : h ∈ twistedFixedGroup t K σ.toRingHom) :
    fieldAutHom t.tag K δ h ∈ twistedFixedGroup t K σ.toRingHom :=
  units_map_entrywiseHom_mem_twistedFixedGroup (fun c => ringEquiv_comm_of_finite σ δ c) hh

theorem fieldAut_mem_graphFixedParabolicRadicalTri {t : TwistTag} (δ : RingAut K)
    {J : Set (Fin t.foldedTag.rank)} {h : ModGL t.tag K}
    (hh : h ∈ graphFixedParabolicRadical t K σ.toRingHom J) :
    fieldAutHom t.tag K δ h ∈ graphFixedParabolicRadical t K σ.toRingHom J :=
  Subgroup.mem_inf.2 ⟨fieldAut_mem_parabolicRadical δ (Subgroup.mem_inf.1 hh).1,
    fieldAut_mem_twistedFixedGroupTri σ δ (Subgroup.mem_inf.1 hh).2⟩

theorem fieldAut_mem_graphFixedParabolicTri {t : TwistTag} (δ : RingAut K)
    {J : Set (Fin t.foldedTag.rank)} {h : ModGL t.tag K}
    (hh : h ∈ graphFixedParabolic t K σ.toRingHom J) :
    fieldAutHom t.tag K δ h ∈ graphFixedParabolic t K σ.toRingHom J := by
  rw [← parabolicSubgroup_inf_graphFixedRootGroup (σ := σ.toRingHom) σ.surjective J] at hh ⊢
  exact Subgroup.mem_inf.2 ⟨fieldAut_mem_parabolicSubgroup δ (Subgroup.mem_inf.1 hh).1,
    fieldAut_mem_graphFixedRootGroupTri σ δ (Subgroup.mem_inf.1 hh).2⟩

theorem fieldAut_mem_graphFixedParabolicLeviTri {t : TwistTag} (δ : RingAut K)
    {J : Set (Fin t.foldedTag.rank)} {h : ModGL t.tag K}
    (hh : h ∈ graphFixedParabolicLevi t K σ.toRingHom J) :
    fieldAutHom t.tag K δ h ∈ graphFixedParabolicLevi t K σ.toRingHom J :=
  Subgroup.mem_inf.2 ⟨fieldAut_mem_parabolicLevi δ (Subgroup.mem_inf.1 hh).1,
    fieldAut_mem_graphFixedRootGroupTri σ δ (Subgroup.mem_inf.1 hh).2⟩

theorem uniqueNormalFormOn_D4 {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    UniqueNormalFormOn (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  obtain ⟨-, hNF, -⟩ := even_triality_exact_automorphism_normal_form hf K hK σ hσ
  intro α
  obtain ⟨gδ, hα, huniq⟩ := hNF α
  refine ⟨gδ, fun h => ?_, fun gδ' hgδ' => huniq gδ' ?_⟩
  · rw [hα]
    rfl
  · refine MulEquiv.ext fun h => Subtype.ext ?_
    rw [hgδ' h]
    rfl

variable (K) in
@[expose] noncomputable def radTri (J : Set (Fin TwistTag.D4.foldedTag.rank)) :
    Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
  (graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom J).subgroupOf
    (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)

variable (K) in
@[expose] noncomputable def parTri (J : Set (Fin TwistTag.D4.foldedTag.rank)) :
    Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
  (graphFixedParabolic TwistTag.D4 K σ.toRingHom J).subgroupOf
    (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)

theorem liftAutOn_left_mem_graphFixedParabolic
    (hNF : UniqueNormalFormOn (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (J : Set (Fin TwistTag.D4.foldedTag.rank))
    {α : MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)}
    (hα : (radTri K σ J).map α.toMonoidHom = radTri K σ J)
    (hNQ : Subgroup.normalizer ((radTri K σ J : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K
      σ.toRingHom)) : Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) = parTri K σ J) :
    (liftAutOn hNF α).left ∈ graphFixedParabolic TwistTag.D4 K σ.toRingHom J := by
  set s := liftAutOn hNF α with hs
  have hm : s.left ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom := liftAutOn_left_mem hNF α
  have hmem : (⟨s.left, hm⟩ : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ∈
      Subgroup.normalizer ((radTri K σ J : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K
        σ.toRingHom)) : Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    let x'' : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
      ⟨fieldAutHom TwistTag.D4.tag K s.right⁻¹ (x : ModGL TwistTag.D4.tag K),
        fieldAut_mem_graphFixedRootGroupTri σ _ x.2⟩
    have hαx : ((α x'' : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
        ModGL TwistTag.D4.tag K) = s.left * (x : ModGL TwistTag.D4.tag K) * s.left⁻¹ := by
      rw [liftAutOn_spec hNF α, conjAct_apply]
      change s.left * fieldAutHom TwistTag.D4.tag K s.right
        (fieldAutHom TwistTag.D4.tag K s.right⁻¹ (x : ModGL TwistTag.D4.tag K)) * s.left⁻¹ = _
      rw [fieldAut_mul_inv_apply]
    have e : (⟨s.left, hm⟩ * x * (⟨s.left, hm⟩ : ↥(graphFixedRootGroup TwistTag.D4 K
        σ.toRingHom))⁻¹ : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) = α x'' :=
      Subtype.ext (by rw [hαx]; rfl)
    have h1 : (α x'' ∈ radTri K σ J) ↔ x'' ∈ radTri K σ J := by
      constructor
      · intro h
        rw [← hα] at h
        obtain ⟨q, hq, hqe⟩ := Subgroup.mem_map.1 h
        have : q = x'' := α.injective hqe
        exact this ▸ hq
      · intro h
        rw [← hα]
        exact Subgroup.mem_map_of_mem _ h
    have h2 : x'' ∈ radTri K σ J ↔ x ∈ radTri K σ J := by
      rw [radTri, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      constructor
      · intro h
        have := fieldAut_mem_graphFixedParabolicRadicalTri σ s.right h
        rwa [fieldAut_mul_inv_apply] at this
      · exact fun h => fieldAut_mem_graphFixedParabolicRadicalTri σ _ h
    rw [e]
    exact h2.symm.trans h1.symm
  rw [hNQ] at hmem
  exact Subgroup.mem_subgroupOf.1 hmem

theorem exists_conj_into_graphFixedLevi [CharP K 2] (J : Set (Fin TwistTag.D4.foldedTag.rank))
    {T : Subgroup (GamL TwistTag.D4.tag K)}
    (hT : ∀ s ∈ T, s.left ∈ graphFixedParabolic TwistTag.D4 K σ.toRingHom J)
    (hodd : ¬ 2 ∣ Nat.card T) :
    ∃ y ∈ graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom J, ∀ s ∈ T,
      ((SemidirectProduct.inl y : GamL TwistTag.D4.tag K) * s *
        (SemidirectProduct.inl y)⁻¹).left ∈ graphFixedParabolicLevi TwistTag.D4 K σ.toRingHom J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_modGL (τ := TwistTag.D4.tag) (K := K)
  have hfinσ : Finite (RingAut K) :=
    Finite.of_injective (fun σ : RingAut K => (σ : K → K)) fun a b h => RingEquiv.ext (congrFun h)
  have hfinΓ : Finite (GamL TwistTag.D4.tag K) :=
    Finite.of_equiv (ModGL TwistTag.D4.tag K × RingAut K) (SemidirectProduct.equivProd).symm
  obtain ⟨-, -, -, -, -, -, -, -, hQ₀P, hQ₀n, -, hdec, -⟩ :=
    diagram_fixed_parabolic_root_radical_Levi_factors TwistTag.D4 K σ J
  have hPQ₀ := (Subgroup.normal_subgroupOf_iff_le_normalizer hQ₀P).1 hQ₀n
  have hQ₀A : graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom J ≤
      parabolicRadical TwistTag.D4.tag K (TwistTag.D4.orbitUnion J) := inf_le_left
  have hL₀A : graphFixedParabolicLevi TwistTag.D4 K σ.toRingHom J ≤
      parabolicLevi TwistTag.D4.tag K (TwistTag.D4.orbitUnion J) := inf_le_left
  have hQ₀L₀ : graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom J ⊓
      graphFixedParabolicLevi TwistTag.D4 K σ.toRingHom J = ⊥ :=
    eq_bot_iff.2 fun x hx => by
      rw [← parabolicRadical_inf_parabolicLevi (K := K) (TwistTag.D4.orbitUnion J)]
      exact Subgroup.mem_inf.2 ⟨hQ₀A (Subgroup.mem_inf.1 hx).1, hL₀A (Subgroup.mem_inf.1 hx).2⟩
  have hQ₀2 : IsPGroup 2 (graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom J) :=
    (isPGroup_posUnipotent 2 TwistTag.D4.tag).to_le
      (hQ₀A.trans (parabolicRadical_le_posUnipotent _))
  let Ppar : Subgroup (GamL TwistTag.D4.tag K) :=
    gamSub (graphFixedParabolic TwistTag.D4 K σ.toRingHom J)
      fun δ _ hh => fieldAut_mem_graphFixedParabolicTri σ δ hh
  let Mlev : Subgroup (GamL TwistTag.D4.tag K) :=
    gamSub (graphFixedParabolicLevi TwistTag.D4 K σ.toRingHom J)
      fun δ _ hh => fieldAut_mem_graphFixedParabolicLeviTri σ δ hh
  let Qrad : Subgroup (GamL TwistTag.D4.tag K) :=
    (graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom J).map SemidirectProduct.inl
  have hQrad2 : IsPGroup 2 Qrad := hQ₀2.map _
  have hQradPpar : Qrad ≤ Ppar := by
    rintro _ ⟨q, hq, rfl⟩
    exact hQ₀P hq
  have hPparN : Ppar ≤ Subgroup.normalizer (Qrad : Set (GamL TwistTag.D4.tag K)) := by
    refine le_normalizer_of_conj_mem fun s hs y hy => ?_
    obtain ⟨q, hq, rfl⟩ := hy
    rw [conj_inl]
    refine ⟨conjAct TwistTag.D4.tag K s q, ?_, rfl⟩
    rw [conjAct_apply]
    exact (Subgroup.mem_normalizer_iff.1 (hPQ₀ hs) _).1
      (fieldAut_mem_graphFixedParabolicRadicalTri σ s.right hq)
  have hQradMlev : Qrad ⊓ Mlev = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    obtain ⟨⟨q, hq, rfl⟩, hxM⟩ := Subgroup.mem_inf.1 hx
    have : q = 1 := Subgroup.mem_bot.1 (hQ₀L₀ ▸ Subgroup.mem_inf.2 ⟨hq, hxM⟩)
    rw [this, map_one]
    exact Subgroup.one_mem _
  have hdec' : ∀ g ∈ Ppar, ∃ q ∈ Qrad, ∃ m ∈ Mlev, q * m = g := by
    intro g hg
    obtain ⟨qm, ⟨hq, hm, hx⟩, -⟩ := hdec g.left hg
    refine ⟨SemidirectProduct.inl qm.1, ⟨qm.1, hq, rfl⟩, ⟨qm.2, g.right⟩, hm, ?_⟩
    refine SemidirectProduct.ext ?_ ?_
    · rw [SemidirectProduct.mul_left, SemidirectProduct.left_inl, SemidirectProduct.right_inl,
        map_one, MulAut.one_apply]
      exact hx.symm
    · rw [SemidirectProduct.mul_right, SemidirectProduct.right_inl, one_mul]
  obtain ⟨y, hyQ, hyM⟩ := exists_conj_le_of_complement (p := 2) (P := Ppar) (Q := Qrad)
    (M := Mlev) hQrad2 hQradPpar hPparN hQradMlev hdec' hT hodd
  obtain ⟨y₀, hy₀, rfl⟩ := hyQ
  refine ⟨y₀, hy₀, fun s hs => ?_⟩
  exact hyM (Subgroup.mem_map_of_mem _ hs)

theorem autCentralizer_inf_radC_eq_bot [CharP K 2] (hσ3 : σ ^ 3 = 1)
    (hNF : UniqueNormalFormOn (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (J : Set (Fin TwistTag.D4.foldedTag.rank)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {R : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))} (hR : IsPGroup p R)
    (hQR : ∀ α ∈ R, (radTri K σ J).map α.toMonoidHom = radTri K σ J)
    (hNQ : Subgroup.normalizer ((radTri K σ J : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K
      σ.toRingHom)) : Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) = parTri K σ J)
    (hC : autCentralizer R ≤ parTri K σ J) :
    autCentralizer R ⊓ radTri K σ J = ⊥ := by
  classical
  have hfinM : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hfinσ : Finite (RingAut K) :=
    Finite.of_injective (fun σ : RingAut K => (σ : K → K)) fun a b h => RingEquiv.ext (congrFun h)
  have hfinΓ : Finite (GamL TwistTag.D4.tag K) :=
    Finite.of_equiv (ModGL TwistTag.D4.tag K × RingAut K) (SemidirectProduct.equivProd).symm
  have : Fact p.Prime := ⟨hp⟩
  have hH : ∀ δ : RingAut K, ∀ h ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      fieldAutHom TwistTag.D4.tag K δ h ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    fun δ _ hh => fieldAut_mem_graphFixedRootGroupTri σ δ hh
  by_contra hne
  obtain ⟨⟨w₁, hw⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  obtain ⟨hwC, hwQ⟩ := Subgroup.mem_inf.1 hw
  have hw1' : (w₁ : ModGL TwistTag.D4.tag K) ≠ 1 := fun h => hw1 (Subtype.ext (Subtype.ext h))
  obtain ⟨-, -, -, -, -, -, -, -, hQ₀P, hQ₀n, -⟩ :=
    diagram_fixed_parabolic_root_radical_Levi_factors TwistTag.D4 K σ J
  have hPQ₀ := (Subgroup.normal_subgroupOf_iff_le_normalizer hQ₀P).1 hQ₀n
  have hQ₀A : graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom J ≤
      parabolicRadical TwistTag.D4.tag K (TwistTag.D4.orbitUnion J) := inf_le_left
  have hL₀A : graphFixedParabolicLevi TwistTag.D4 K σ.toRingHom J ≤
      parabolicLevi TwistTag.D4.tag K (TwistTag.D4.orbitUnion J) := inf_le_left
  set T : Subgroup (GamL TwistTag.D4.tag K) := R.map (liftHomOn hNF hH) with hT
  have hTcard : Nat.card T = Nat.card R :=
    Subgroup.card_map_of_injective (liftHomOn_injective hNF hH)
  have hRodd : Nat.card R % 2 = 1 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hR
    rw [hk]
    exact Nat.odd_iff.1 ((hp.eq_two_or_odd'.resolve_left hp2).pow)
  have hTodd : ¬ 2 ∣ Nat.card T := by
    rw [hTcard]; exact Nat.two_dvd_ne_zero.2 hRodd
  have hTP : ∀ s ∈ T, s.left ∈ graphFixedParabolic TwistTag.D4 K σ.toRingHom J := by
    rintro _ ⟨α, hα, rfl⟩
    exact liftAutOn_left_mem_graphFixedParabolic σ hNF J (hQR α hα) hNQ
  obtain ⟨y₀, hy₀, hyM⟩ := exists_conj_into_graphFixedLevi σ J hTP hTodd
  set y : GamL TwistTag.D4.tag K := SemidirectProduct.inl y₀ with hy
  set S : Subgroup (GamL TwistTag.D4.tag K) := T.map (MulAut.conj y).toMonoidHom with hS
  have hSL : ∀ s ∈ S, s.left ∈ graphFixedParabolicLevi TwistTag.D4 K σ.toRingHom J := by
    rintro _ ⟨s, hs, rfl⟩
    exact hyM s hs
  have hSodd : Odd (Nat.card S) := by
    rw [hS, Subgroup.card_map_of_injective (MulAut.conj y).injective, hTcard]
    exact Nat.odd_iff.2 hRodd
  have hconjy : ∀ g : ModGL TwistTag.D4.tag K, conjAct TwistTag.D4.tag K y g = y₀ * g * y₀⁻¹ :=
    fun g => by rw [hy, conjAct_inl, MulAut.conj_apply]
  have hconjyinv : ∀ g : ModGL TwistTag.D4.tag K,
      conjAct TwistTag.D4.tag K y⁻¹ g = y₀⁻¹ * g * y₀ := fun g => by
    rw [map_inv, hy, conjAct_inl, ← map_inv, MulAut.conj_apply, inv_inv]
  have hu : (w₁ : ModGL TwistTag.D4.tag K) ∈ graphFixedParabolicRadical TwistTag.D4 K
      σ.toRingHom J := Subgroup.mem_subgroupOf.1 hwQ
  have hy₀P : y₀ ∈ graphFixedParabolic TwistTag.D4 K σ.toRingHom J := hQ₀P hy₀
  have hu' : y₀ * (w₁ : ModGL TwistTag.D4.tag K) * y₀⁻¹ ∈
      graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom J :=
    (Subgroup.mem_normalizer_iff.1 (hPQ₀ hy₀P) _).1 hu
  have hu'1 : y₀ * (w₁ : ModGL TwistTag.D4.tag K) * y₀⁻¹ ≠ 1 := fun h => hw1' (by
    have := congrArg (fun z => y₀⁻¹ * z * y₀) h
    simpa [mul_assoc] using this)
  have hfixT : ∀ s ∈ T, conjAct TwistTag.D4.tag K s (w₁ : ModGL TwistTag.D4.tag K) = w₁ := by
    rintro _ ⟨α, hα, rfl⟩
    change conjAct TwistTag.D4.tag K (liftAutOn hNF α) _ = _
    rw [← liftAutOn_spec hNF α, hwC α hα]
  have hfix : ∀ s ∈ S, conjAct TwistTag.D4.tag K s (y₀ * (w₁ : ModGL TwistTag.D4.tag K) * y₀⁻¹) =
      y₀ * (w₁ : ModGL TwistTag.D4.tag K) * y₀⁻¹ := by
    rintro _ ⟨s, hs, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have h1 : conjAct TwistTag.D4.tag K y⁻¹ (y₀ * (w₁ : ModGL TwistTag.D4.tag K) * y₀⁻¹) =
        w₁ := by
      rw [hconjyinv]; group
    rw [conjAct_conj, h1, hfixT s hs, hconjy]
  set fF : GamL TwistTag.D4.tag K := ⟨diagramMap TwistTag.D4 K, σ⟩ with hfF
  have hPσ : ∀ δ : RingAut K, fieldAutHom TwistTag.D4.tag K δ (diagramMap TwistTag.D4 K) =
      diagramMap TwistTag.D4 K := fun δ => units_map_entrywiseHom_diagramMap (δ : K →+* K)
  have hfpow : ∀ k : ℕ, fF ^ k = ⟨diagramMap TwistTag.D4 K ^ k, σ ^ k⟩ := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ, ih]
      refine SemidirectProduct.ext ?_ ?_
      · show diagramMap TwistTag.D4 K ^ k *
          fieldAutHom TwistTag.D4.tag K (σ ^ k) (diagramMap TwistTag.D4 K) =
            diagramMap TwistTag.D4 K ^ (k + 1)
        rw [hPσ, pow_succ]
      · show σ ^ k * σ = σ ^ (k + 1)
        rw [pow_succ]
  have hf3 : fF ^ 3 = 1 := by
    rw [hfpow, show diagramMap TwistTag.D4 K ^ 3 = 1 from diagramMap_pow_order TwistTag.D4 K,
      hσ3]
    rfl
  have hconjF : ∀ g : ModGL TwistTag.D4.tag K,
      conjAct TwistTag.D4.tag K fF g = twistHom TwistTag.D4 K σ.toRingHom g := fun g => by
    rw [conjAct_apply, twistHom_apply]
    rfl
  have hfcomm : ∀ s ∈ S, fF * s = s * fF := by
    intro s hs
    have hsC : s.left ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
      graphFixedParabolicLevi_le TwistTag.D4 K σ.toRingHom J (hSL s hs)
    have hsF : twistHom TwistTag.D4 K σ.toRingHom s.left = s.left :=
      ((mem_twistedFixedGroup_iff_twistHom TwistTag.D4 K σ.toRingHom).1
        (graphFixedRootGroup_le TwistTag.D4 K σ.toRingHom hsC)).2
    refine SemidirectProduct.ext ?_ ?_
    · show diagramMap TwistTag.D4 K * fieldAutHom TwistTag.D4.tag K σ s.left =
        s.left * fieldAutHom TwistTag.D4.tag K s.right (diagramMap TwistTag.D4 K)
      rw [hPσ]
      calc diagramMap TwistTag.D4 K * fieldAutHom TwistTag.D4.tag K σ s.left
          = diagramMap TwistTag.D4 K * fieldAutHom TwistTag.D4.tag K σ s.left *
              (diagramMap TwistTag.D4 K)⁻¹ * diagramMap TwistTag.D4 K := by group
        _ = twistHom TwistTag.D4 K σ.toRingHom s.left * diagramMap TwistTag.D4 K := rfl
        _ = s.left * diagramMap TwistTag.D4 K := by rw [hsF]
    · show σ * s.right = s.right * σ
      exact CFSG.LocalAnalysis.ComponentInitial.ringAut_mul_comm K σ s.right
  have hcommS : ∀ (a : S) (b : Subgroup.zpowers fF),
      Commute (S.subtype a) ((Subgroup.zpowers fF).subtype b) := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact Commute.zpow_right (hfcomm a ha).symm k
  set ψ := MonoidHom.noncommCoprod S.subtype (Subgroup.zpowers fF).subtype hcommS with hψ
  set S₂ : Subgroup (GamL TwistTag.D4.tag K) := ψ.range with hS₂
  have hS₂odd : Odd (Nat.card S₂) := by
    have h1 : Nat.card S₂ ∣ Nat.card (S × Subgroup.zpowers fF) := Subgroup.card_range_dvd ψ
    rw [Nat.card_prod, Nat.card_zpowers] at h1
    have h3 : orderOf fF ∣ 3 := orderOf_dvd_of_pow_eq_one hf3
    exact Odd.of_dvd_nat (Nat.odd_mul.2 ⟨hSodd, Odd.of_dvd_nat ⟨1, rfl⟩ h3⟩) h1
  have hS₂mem : ∀ x ∈ S₂, ∃ s ∈ S, ∃ k : ℕ, x = s * fF ^ k := by
    rintro _ ⟨⟨⟨s, hs⟩, ⟨z, hz⟩⟩, rfl⟩
    obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 ((mem_powers_iff_mem_zpowers).2 hz)
    exact ⟨s, hs, k, rfl⟩
  have hSS₂ : S ≤ S₂ := fun s hs => ⟨(⟨s, hs⟩, 1), mul_one s⟩
  have hfS₂ : fF ∈ S₂ := ⟨(1, ⟨fF, Subgroup.mem_zpowers fF⟩), one_mul fF⟩
  have hS₂form : ∀ x ∈ S₂, ∃ m ∈ parabolicLevi TwistTag.D4.tag K (TwistTag.D4.orbitUnion J),
      ∃ i : ℕ, x.left = m * diagramMap TwistTag.D4 K ^ i := by
    intro x hx
    obtain ⟨s, hs, k, rfl⟩ := hS₂mem x hx
    refine ⟨s.left, hL₀A (hSL s hs), k, ?_⟩
    rw [SemidirectProduct.mul_left, hfpow k]
    show s.left * fieldAutHom TwistTag.D4.tag K s.right (diagramMap TwistTag.D4 K ^ k) =
      s.left * diagramMap TwistTag.D4 K ^ k
    rw [map_pow, hPσ]
  have hu'C : y₀ * (w₁ : ModGL TwistTag.D4.tag K) * y₀⁻¹ ∈
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedParabolicRadical_le_graphFixedRootGroup TwistTag.D4 K σ.toRingHom J hu'
  have hFu : twistHom TwistTag.D4 K σ.toRingHom (y₀ * (w₁ : ModGL TwistTag.D4.tag K) * y₀⁻¹) =
      y₀ * (w₁ : ModGL TwistTag.D4.tag K) * y₀⁻¹ :=
    ((mem_twistedFixedGroup_iff_twistHom TwistTag.D4 K σ.toRingHom).1
      (graphFixedRootGroup_le TwistTag.D4 K σ.toRingHom hu'C)).2
  have hfixpow : ∀ k : ℕ, conjAct TwistTag.D4.tag K (fF ^ k)
      (y₀ * (w₁ : ModGL TwistTag.D4.tag K) * y₀⁻¹) = y₀ * (w₁ : ModGL TwistTag.D4.tag K) * y₀⁻¹ := by
    intro k
    induction k with
    | zero => rw [pow_zero, map_one, MulAut.one_apply]
    | succ k ih =>
      rw [pow_succ, map_mul (conjAct TwistTag.D4.tag K), MulAut.mul_apply, hconjF, hFu, ih]
  have hfix₂ : ∀ x ∈ S₂, conjAct TwistTag.D4.tag K x (y₀ * (w₁ : ModGL TwistTag.D4.tag K) * y₀⁻¹) =
      y₀ * (w₁ : ModGL TwistTag.D4.tag K) * y₀⁻¹ := by
    intro x hx
    obtain ⟨s, hs, k, rfl⟩ := hS₂mem x hx
    rw [map_mul (conjAct TwistTag.D4.tag K), MulAut.mul_apply, hfixpow, hfix s hs]
  obtain ⟨v, hvQ, hv1, hvfix⟩ := exists_fixed_mem_oppRadical_tri (perm_mem_orbitUnion_iff J)
    hS₂form hS₂odd (hQ₀A hu') hu'1 hfix₂
  have hvF : twistHom TwistTag.D4 K σ.toRingHom v = v := (hconjF v).symm.trans (hvfix fF hfS₂)
  have hvG : v ∈ adjointGroup TwistTag.D4.tag K := rootSpan_le_adjointGroup K _ hvQ
  have hvC : v ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedNegUnipotent_le_graphFixedRootGroup TwistTag.D4 K σ.toRingHom
      (Subgroup.mem_inf.2 ⟨oppRadical_le_negUnipotent _ hvQ,
        (mem_twistedFixedGroup_iff_twistHom TwistTag.D4 K σ.toRingHom).2 ⟨hvG, hvF⟩⟩)
  have hy₀C : y₀ ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedParabolicRadical_le_graphFixedRootGroup TwistTag.D4 K σ.toRingHom J hy₀
  have hwG : y₀⁻¹ * v * y₀ ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    mul_mem (mul_mem (inv_mem hy₀C) hvC) hy₀C
  have hwfix : ∀ s ∈ T, conjAct TwistTag.D4.tag K s (y₀⁻¹ * v * y₀) = y₀⁻¹ * v * y₀ := by
    intro s hs
    have h := hvfix _ (hSS₂ (Subgroup.mem_map_of_mem (MulAut.conj y).toMonoidHom hs))
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
    rw [conjAct_conj, hconjyinv, hconjy] at h
    calc conjAct TwistTag.D4.tag K s (y₀⁻¹ * v * y₀) =
        y₀⁻¹ * (y₀ * conjAct TwistTag.D4.tag K s (y₀⁻¹ * v * y₀) * y₀⁻¹) * y₀ := by group
      _ = y₀⁻¹ * v * y₀ := by rw [h]
  have hwC' : (⟨y₀⁻¹ * v * y₀, hwG⟩ : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ∈
      autCentralizer R := by
    intro α hα
    refine Subtype.ext ?_
    rw [liftAutOn_spec hNF α]
    exact hwfix (liftHomOn hNF hH α) ⟨α, hα, rfl⟩
  have hwP : y₀⁻¹ * v * y₀ ∈ graphFixedParabolic TwistTag.D4 K σ.toRingHom J :=
    Subgroup.mem_subgroupOf.1 (hC hwC')
  have hvP : v ∈ graphFixedParabolic TwistTag.D4 K σ.toRingHom J := by
    have e : v = y₀ * (y₀⁻¹ * v * y₀) * y₀⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem hy₀P hwP) (inv_mem hy₀P)
  have h0 := Subgroup.mem_inf.2 ⟨graphFixedParabolic_le_parabolicSubgroup J hvP, hvQ⟩
  rw [parabolicSubgroup_inf_oppRadical] at h0
  exact hv1 (Subgroup.mem_bot.1 h0)

theorem oppositeFixed_graphFixedRootGroup_D4 {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    OppositeFixed ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  intro p hp hp2 R hR Q hQ0 hQ2 hcore hne hRQ hC
  classical
  have hK3 : Nat.card K = 2 ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  haveI : CharP K 2 := charP_two_of_card_two_pow hK3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hσ3 : σ ^ 3 = 1 := RingEquiv.ext fun c => by
    rw [pow_succ, pow_two]
    exact ringEquiv_cube_apply_eq hK hσ c
  have hσ3' : σ ^ TwistTag.D4.order = 1 := hσ3
  have hNF := uniqueNormalFormOn_D4 σ hf hK hσ
  have hfinM : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hQ₀ne : Q.map (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype ≠ ⊥ := fun h =>
    hQ0 ((Subgroup.map_eq_bot_iff_of_injective Q
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype_injective).1 h)
  obtain ⟨g, hg, J, hP, hQJ⟩ := exists_optimal_radical_fixed TwistTag.D4 σ hσ3'
    (Subgroup.map_subtype_le Q) (hQ2.map (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype)
    hQ₀ne
  obtain ⟨-, -, -, -, -, -, -, -, hQ₀P, hQ₀n, -⟩ :=
    diagram_fixed_parabolic_root_radical_Levi_factors TwistTag.D4 K σ J
  have hQ₀C : graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom J ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedParabolicRadical_le_graphFixedRootGroup TwistTag.D4 K σ.toRingHom J
  have hQJ2 : IsPGroup 2 (radTri K σ J) := by
    have h2 : IsPGroup 2 (graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom J) :=
      (isPGroup_posUnipotent 2 TwistTag.D4.tag).to_le
        ((inf_le_left : graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom J ≤
          parabolicRadical TwistTag.D4.tag K (TwistTag.D4.orbitUnion J)).trans
          (parabolicRadical_le_posUnipotent _))
    exact h2.of_equiv (Subgroup.subgroupOfEquivOfLe hQ₀C).symm
  have hPQ₀ := (Subgroup.normal_subgroupOf_iff_le_normalizer hQ₀P).1 hQ₀n
  have hPJ : parTri K σ J ≤ Subgroup.normalizer ((radTri K σ J : Subgroup ↥(graphFixedRootGroup
      TwistTag.D4 K σ.toRingHom)) : Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hx' := hPQ₀ (Subgroup.mem_subgroupOf.1 hx)
    simp only [radTri, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.1 hx' _
  have hN : ∀ x ∈ Subgroup.normalizer (Q : Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
      (⟨g, hg⟩ : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))⁻¹ * x * ⟨g, hg⟩ ∈
        parTri K σ J :=
    fun x hx => Subgroup.mem_subgroupOf.2 (hP x x.2 (mem_normalizer_map_subtype hx))
  have hQ : ∀ q ∈ Q, (⟨g, hg⟩ : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))⁻¹ * q *
      ⟨g, hg⟩ ∈ radTri K σ J :=
    fun q hq => Subgroup.mem_subgroupOf.2 (hQJ q ⟨q, hq, rfl⟩)
  obtain ⟨hQ', hNQ⟩ := std_position (⟨g, hg⟩ : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    hcore hQJ2 hPJ hN hQ
  set γ : MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    MulAut.conj (⟨g, hg⟩ : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))⁻¹ with hγ
  set R' : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :=
    R.map (MulAut.conj γ).toMonoidHom with hR'
  have hR'p : IsPGroup p R' := hR.map _
  have hQmap : Q.map γ.toMonoidHom = radTri K σ J := hQ'
  have hQR' : ∀ α' ∈ R', (radTri K σ J).map α'.toMonoidHom = radTri K σ J := by
    rintro _ ⟨α, hα, rfl⟩
    have e : ((MulAut.conj γ).toMonoidHom α).toMonoidHom.comp γ.toMonoidHom =
        γ.toMonoidHom.comp α.toMonoidHom :=
      MonoidHom.ext fun y => congrArg γ (congrArg α (MulAut.inv_apply_self _ γ y))
    rw [← hQmap, Subgroup.map_map, e, ← Subgroup.map_map, hRQ α hα]
  have hC' : autCentralizer R' ≤ parTri K σ J := by
    intro x hx
    have hx' : γ⁻¹ x ∈ autCentralizer R := by
      intro α hα
      have h := hx ((MulAut.conj γ).toMonoidHom α) ⟨α, hα, rfl⟩
      have h2 : γ (α (γ⁻¹ x)) = x := h
      calc α (γ⁻¹ x) = γ⁻¹ (γ (α (γ⁻¹ x))) := (MulAut.inv_apply_self _ γ _).symm
        _ = γ⁻¹ x := by rw [h2]
    have hN' : γ⁻¹ x ∈ Subgroup.normalizer (Q : Set ↥(graphFixedRootGroup TwistTag.D4 K
      σ.toRingHom)) := hC hx'
    have h3 : x ∈ Subgroup.normalizer ((Q.map γ.toMonoidHom : Subgroup ↥(graphFixedRootGroup
        TwistTag.D4 K σ.toRingHom)) : Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
      rw [← Subgroup.map_equiv_normalizer_eq Q γ]
      exact ⟨γ⁻¹ x, hN', MulAut.apply_inv_self _ γ x⟩
    rw [hQmap, hNQ] at h3
    exact h3
  have key := autCentralizer_inf_radC_eq_bot σ hσ3 hNF J hp hp2 hR'p hQR' hNQ hC'
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨hzC, hzQ⟩ := Subgroup.mem_inf.1 hz
  have hz1 : γ z ∈ autCentralizer R' ⊓ radTri K σ J := by
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rintro _ ⟨α, hα, rfl⟩
      have h := hzC α hα
      change (γ * α * γ⁻¹) (γ z) = γ z
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply, h]
    · rw [← hQmap]
      exact Subgroup.mem_map_of_mem _ hzQ
  rw [key] at hz1
  exact Subgroup.mem_bot.2 ((MulEquiv.map_eq_one_iff γ).1 (Subgroup.mem_bot.1 hz1))

end Triality

theorem oppositeFixed_of_twistedChevalleyModel_D4 {S : Type} [Group S] {f : ℕ} (hf : 1 ≤ f)
    (h : TwistedChevalleyModel S .D4 (2 ^ f)) : OppositeFixed S := by
  obtain ⟨K, _, hfin, hcard, σ, hσ, ⟨e⟩⟩ := h
  obtain ⟨σ', rfl⟩ : ∃ σ' : K ≃+* K, σ'.toRingHom = σ :=
    ⟨RingEquiv.ofBijective σ ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩,
      RingHom.ext fun _ => rfl⟩
  have hK : Nat.card K = (2 ^ f) ^ 3 := hcard
  obtain ⟨-, -, -, -, -, -, -, ⟨e'⟩⟩ := even_triality_exact_automorphism_normal_form hf K hK σ' hσ
  exact oppositeFixed_of_mulEquiv (e.trans e') (oppositeFixed_graphFixedRootGroup_D4 σ' hf hK hσ)

end Cert

end CFSG.LieType.ChevTwo.Semi
