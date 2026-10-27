module

public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.BigCell
import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.EntryLemma
public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.Entry
public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.HighestRoot

open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg.Adjoint
open CFSG.RankThree.PartOne.CTP

public section

namespace CFSG.LieType.SeitzGeneration.ExcOuterLeOne



section BigCellConj

variable {τ : Tag} {K : Type} [Field K]

@[expose] noncomputable def posUnip (τ : Tag) (K : Type) [Field K] : Subgroup ↥(adjointGroup τ K) :=
  ⨆ γ ∈ {γ : Fin τ.rank → ℤ | IsRoot τ γ ∧ 0 < height γ}, rootGroup (rootOperatorFamily τ) K γ

@[expose] noncomputable def borelSub (τ : Tag) (K : Type) [Field K] : Subgroup ↥(adjointGroup τ K) :=
  (⨆ i : Fin τ.rank, torus (τ := τ) K i) ⊔ posUnip τ K

noncomputable def wordProd (τ : Tag) (K : Type) [Field K] (w : List (Fin τ.rank)) :
    ↥(adjointGroup τ K) :=
  (w.map (CFSG.LieType.Chevalley.weylElement τ K)).prod

private theorem bruhat_wordProd_val (ω : List (Fin τ.rank)) :
    ((wordProd τ K ω : ↥(adjointGroup τ K)) : ModGL τ K) =
      (ω.map fun i => weylElt τ K i 1).prod := by
  have h := map_list_prod (adjointGroup τ K).subtype
    (ω.map (CFSG.LieType.Chevalley.weylElement τ K))
  rw [List.map_map] at h
  exact h

private theorem bruhat_torusElt_mem (i : Fin τ.rank) (t : Kˣ) :
    torusElt τ K i t ∈ (borelSub τ K).map (adjointGroup τ K).subtype := by
  have hT : CFSG.LieType.Chevalley.torusElement τ K i t ∈ borelSub τ K := by
    unfold borelSub
    exact Subgroup.mem_sup_left (Subgroup.mem_iSup_of_mem i (MonoidHom.mem_range.2 ⟨t, rfl⟩))
  exact Subgroup.mem_map.2 ⟨_, hT, rfl⟩

private theorem bruhat_pinnedX_mem {α : Fin τ.rank → ℤ} (hα : IsRoot τ α ∧ 0 < height α) (c : K) :
    pinnedX τ K α c ∈ (borelSub τ K).map (adjointGroup τ K).subtype := by
  have hX : pinnedX τ K α c ∈ CFSG.Blueprint.Chevalley.posUnipotent τ K :=
    Subgroup.mem_iSup_of_mem α (Subgroup.mem_iSup_of_mem hα (Subgroup.subset_closure ⟨c, rfl⟩))
  have hG : pinnedX τ K α c ∈ adjointGroup τ K := posUnipotent_le_adjointGroup hX
  have hr : (⟨pinnedX τ K α c, hG⟩ : ↥(adjointGroup τ K)) ∈
      rootGroup (rootOperatorFamily τ) K α := by
    rw [rootGroup_of_isRoot hα.1, ← (rootOperatorFamily τ).subgroupOf_rootSubgroup_eq K ⟨α, hα.1⟩,
      Subgroup.mem_subgroupOf]
    exact Subgroup.subset_closure ⟨c, rfl⟩
  have hP : (⟨pinnedX τ K α c, hG⟩ : ↥(adjointGroup τ K)) ∈ posUnip τ K :=
    Subgroup.mem_iSup_of_mem α (Subgroup.mem_iSup_of_mem hα hr)
  have hB : (⟨pinnedX τ K α c, hG⟩ : ↥(adjointGroup τ K)) ∈ borelSub τ K := by
    unfold borelSub
    exact Subgroup.mem_sup_right hP
  exact Subgroup.mem_map.2 ⟨_, hB, rfl⟩

private theorem bruhat_borelGroup_le :
    CFSG.LieType.Chevalley.borelGroup τ K ≤ (borelSub τ K).map (adjointGroup τ K).subtype := by
  unfold CFSG.LieType.Chevalley.borelGroup
  refine sup_le ?_ ?_
  · unfold CFSG.LieType.Chevalley.torusGroup
    rw [Subgroup.closure_le]
    rintro _ ⟨⟨i, t⟩, rfl⟩
    exact bruhat_torusElt_mem i t
  · unfold CFSG.Blueprint.Chevalley.posUnipotent CFSG.Blueprint.Chevalley.rootSpan
    refine iSup₂_le fun α hα => ?_
    unfold CFSG.Blueprint.Chevalley.rootSubgroup
    rw [Subgroup.closure_le]
    rintro _ ⟨c, rfl⟩
    exact bruhat_pinnedX_mem (α := α) hα c

theorem exists_bruhat_decomp (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4) (g : ↥(adjointGroup τ K)) :
    ∃ (w : List (Fin τ.rank)) (b₁ b₂ : ↥(adjointGroup τ K)), b₁ ∈ borelSub τ K ∧ b₂ ∈ borelSub τ K ∧
      g = b₁ * wordProd τ K w * b₂ := by
  clear hτ
  have hg : (g : ModGL τ K) ∈ (adjointGroup τ K : Set (ModGL τ K)) := g.2
  rw [adjointGroup_eq_iUnion_bruhatCell] at hg
  obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hg
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem τ).exists_isReduced w
  obtain ⟨b, hb, b', hb', hx⟩ := mem_bruhatCell.1 hw
  rw [canonicalRep_wordProd hω] at hx
  obtain ⟨b₁, hb₁, hb₁e⟩ := Subgroup.mem_map.1 (bruhat_borelGroup_le hb)
  obtain ⟨b₂, hb₂, hb₂e⟩ := Subgroup.mem_map.1 (bruhat_borelGroup_le hb')
  have e₁ : ((b₁ : ↥(adjointGroup τ K)) : ModGL τ K) = b := hb₁e
  have e₂ : ((b₂ : ↥(adjointGroup τ K)) : ModGL τ K) = b' := hb₂e
  refine ⟨ω, b₁, b₂, hb₁, hb₂, Subtype.ext ?_⟩
  rw [Subgroup.coe_mul, Subgroup.coe_mul, bruhat_wordProd_val, e₁, e₂]
  exact hx.symm

private theorem height_neg_aux (v : Fin τ.rank → ℤ) : height (-v) = -height v := by
  simp [height, Finset.sum_neg_distrib]

private theorem height_nsmul_aux (k : ℕ) (v : Fin τ.rank → ℤ) : height (k • v) = k * height v := by
  simp [height, Finset.mul_sum]

private theorem labelWt_height_le {θ : Fin τ.rank → ℤ} (hθ : IsMaxHeightRoot τ θ) (a : Label τ) :
    height (labelWt τ a) ≤ height θ := by
  rcases a with l | ⟨α, hα⟩
  · have h0 : height (0 : Fin τ.rank → ℤ) = 0 := by simp [height]
    have h1 := hθ.height_pos
    show height (0 : Fin τ.rank → ℤ) ≤ height θ
    rw [h0]
    omega
  · exact hθ.2 α hα

private theorem neg_height_le_labelWt {θ : Fin τ.rank → ℤ} (hθ : IsMaxHeightRoot τ θ) (a : Label τ) :
    -height θ ≤ height (labelWt τ a) := by
  rcases a with l | ⟨α, hα⟩
  · have h0 : height (0 : Fin τ.rank → ℤ) = 0 := by simp [height]
    have h1 := hθ.height_pos
    show -height θ ≤ height (0 : Fin τ.rank → ℤ)
    rw [h0]
    omega
  · have h := hθ.2 (-α) (CFSG.LieType.Chevalley.IsRoot.neg hα)
    rw [height_neg_aux] at h
    show -height θ ≤ height α
    omega

theorem posRoot_fix (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4) {θ : Fin τ.rank → ℤ}
    (hθ : IsMaxHeightRoot τ θ) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hpos : 0 < height γ) (c : K) :
    endHom K (xPar (rootOperatorFamily τ) γ c) (rootVec τ K θ) = rootVec τ K θ ∧
      ∀ x : RootModule τ K, (endHom K (xPar (rootOperatorFamily τ) γ c) x) (negLabel hθ.1) =
        x (negLabel hθ.1) := by
  have e : ∀ x : RootModule τ K, endHom K (xPar (rootOperatorFamily τ) γ c) x =
      (rootOperatorFamily τ).elt K ⟨γ, hγ⟩ c x := fun x => by
    rw [xPar_of_isRoot hγ, endHom_eltElement]
  constructor
  · rw [e, rootVec_eq_single hθ.1]
    refine Finsupp.ext fun a => ?_
    by_contra hne
    obtain ⟨k, hk, hwt⟩ := (rootOperatorFamily τ).elt_weight_shift ⟨γ, hγ⟩ c a (rootLabel hθ.1)
      (sub_ne_zero.2 hne)
    have hwt' : labelWt τ a = θ + k • γ := hwt
    have h1 : height (labelWt τ a) = height θ + k * height γ := by
      rw [hwt', height_add_eq, height_nsmul_aux]
    have h2 := labelWt_height_le hθ a
    have h3 : (1 : ℤ) ≤ k := by exact_mod_cast hk
    nlinarith [h3, hpos]
  · intro x
    rw [e]
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy => rw [map_add, Finsupp.add_apply, hx, hy, Finsupp.add_apply]
    | single b r =>
      rw [← Finsupp.smul_single_one, map_smul, Finsupp.smul_apply, Finsupp.smul_apply]
      congr 1
      by_contra hne
      obtain ⟨k, hk, hwt⟩ := (rootOperatorFamily τ).elt_weight_shift ⟨γ, hγ⟩ c (negLabel hθ.1) b
        (sub_ne_zero.2 hne)
      have hwt' : -θ = labelWt τ b + k • γ := hwt
      have h1 : height (-θ) = height (labelWt τ b) + k * height γ := by
        rw [hwt', height_add_eq, height_nsmul_aux]
      rw [height_neg_aux] at h1
      have h2 := neg_height_le_labelWt hθ b
      have h3 : (1 : ℤ) ≤ k := by exact_mod_cast hk
      nlinarith [h3, hpos]

private theorem exists_adjData_four {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4) :
    ∃ D : AdjData τ, D.Valid ∧ NoG2 τ := by
  rcases hτ with rfl | rfl | rfl | rfl
  · exact exists_adjData_valid_E (Or.inl rfl)
  · exact exists_adjData_valid_E (Or.inr (Or.inl rfl))
  · exact exists_adjData_valid_E (Or.inr (Or.inr rfl))
  · exact ⟨_, f4Data_valid, noG2_F4⟩

private def stabSub {θ : Fin τ.rank → ℤ} (hθ : IsRoot τ θ) : Subgroup ↥(adjointGroup τ K) where
  carrier := {b : ↥(adjointGroup τ K) | ∃ χ : Kˣ, endHom K b (rootVec τ K θ) = (χ : K) • rootVec τ K θ ∧
    (∀ x : RootModule τ K, (endHom K b x) (negLabel hθ) = ((χ⁻¹ : Kˣ) : K) * x (negLabel hθ)) ∧
    ∀ c : K, b * xPar (rootOperatorFamily τ) θ c * b⁻¹ = xPar (rootOperatorFamily τ) θ ((χ : K) * c)}
  mul_mem' := by
    rintro a b ⟨χ₁, a1, b1, c1⟩ ⟨χ₂, a2, b2, c2⟩
    refine ⟨χ₁ * χ₂, ?_, ?_, ?_⟩
    · rw [map_mul, Module.End.mul_apply, a2, map_smul, a1, smul_smul, Units.val_mul, mul_comm]
    · intro x
      rw [map_mul, Module.End.mul_apply, b1, b2, mul_inv, Units.val_mul]
      ring
    · intro c
      rw [show a * b * xPar (rootOperatorFamily τ) θ c * (a * b)⁻¹ =
          a * (b * xPar (rootOperatorFamily τ) θ c * b⁻¹) * a⁻¹ by group, c2 c,
        c1 ((χ₂ : K) * c), Units.val_mul, mul_assoc]
  one_mem' := by
    refine ⟨1, ?_, ?_, ?_⟩
    · simp
    · intro x; simp
    · intro c; simp
  inv_mem' := by
    rintro a ⟨χ, a1, b1, c1⟩
    refine ⟨χ⁻¹, ?_, ?_, ?_⟩
    · have h : rootVec τ K θ = (χ : K) • endHom K a⁻¹ (rootVec τ K θ) := by
        have h0 := congrArg (endHom K a⁻¹) a1
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply,
          map_smul] at h0
        exact h0
      calc endHom K a⁻¹ (rootVec τ K θ)
          = ((χ⁻¹ : Kˣ) : K) • ((χ : K) • endHom K a⁻¹ (rootVec τ K θ)) := by
            rw [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
        _ = ((χ⁻¹ : Kˣ) : K) • rootVec τ K θ := by rw [← h]
    · intro x
      have h := b1 (endHom K a⁻¹ x)
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at h
      rw [inv_inv, h, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
    · intro c
      have h := c1 (((χ⁻¹ : Kˣ) : K) * c)
      rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul] at h
      rw [inv_inv]
      calc a⁻¹ * xPar (rootOperatorFamily τ) θ c * a
          = a⁻¹ * (a * xPar (rootOperatorFamily τ) θ (((χ⁻¹ : Kˣ) : K) * c) * a⁻¹) * a := by rw [h]
        _ = xPar (rootOperatorFamily τ) θ (((χ⁻¹ : Kˣ) : K) * c) := by group

private theorem mem_stabSub_iff {θ : Fin τ.rank → ℤ} (hθ : IsRoot τ θ) {b : ↥(adjointGroup τ K)} :
    b ∈ stabSub (K := K) hθ ↔ ∃ χ : Kˣ, endHom K b (rootVec τ K θ) = (χ : K) • rootVec τ K θ ∧
      (∀ x : RootModule τ K, (endHom K b x) (negLabel hθ) = ((χ⁻¹ : Kˣ) : K) * x (negLabel hθ)) ∧
      ∀ c : K, b * xPar (rootOperatorFamily τ) θ c * b⁻¹ = xPar (rootOperatorFamily τ) θ ((χ : K) * c) :=
  Iff.rfl

private theorem torusElement_mem_stabSub {θ : Fin τ.rank → ℤ} (hθ : IsRoot τ θ) (i : Fin τ.rank) (t : Kˣ) :
    torusElement τ K i t ∈ stabSub (K := K) hθ := by
  refine (mem_stabSub_iff hθ).2 ⟨t ^ (∑ j, τ.cartan i j * θ j), ?_, ?_, ?_⟩
  · exact torusElt_rootVec i t hθ
  · intro x
    have hw : labelWt τ (negLabel hθ) = -θ := rfl
    have h := torusElt_apply i t x (negLabel hθ)
    have hs : (∑ j, τ.cartan i j * labelWt τ (negLabel hθ) j) = -(∑ j, τ.cartan i j * θ j) := by
      simp [hw, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
    rw [hs, zpow_neg] at h
    exact h
  · intro c
    rw [xPar_of_isRoot hθ, xPar_of_isRoot hθ, RootOperatorFamily.torusElement_mul_eltElement_mul_inv]

private theorem posRoot_mem_stabSub (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4) {θ : Fin τ.rank → ℤ}
    (hθ : IsMaxHeightRoot τ θ) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hpos : 0 < height γ) (c : K) :
    xPar (rootOperatorFamily τ) γ c ∈ stabSub (K := K) hθ.1 := by
  obtain ⟨D, hD, hG⟩ := exists_adjData_four hτ
  obtain ⟨h1, h2⟩ := posRoot_fix hτ hθ hγ hpos c
  refine (mem_stabSub_iff hθ.1).2 ⟨1, ?_, ?_, ?_⟩
  · rw [h1, Units.val_one, one_smul]
  · intro x
    rw [h2 x, inv_one, Units.val_one, one_mul]
  · intro c'
    have hcom : xPar (rootOperatorFamily τ) γ c * xPar (rootOperatorFamily τ) θ c' =
        xPar (rootOperatorFamily τ) θ c' * xPar (rootOperatorFamily τ) γ c :=
      (IsMaxHeightRoot.commute_xPar hD hG hθ hγ hpos c' c).eq.symm
    rw [hcom, mul_assoc, mul_inv_cancel, mul_one, Units.val_one, one_mul]

theorem borel_stab (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4) {θ : Fin τ.rank → ℤ}
    (hθ : IsMaxHeightRoot τ θ) {b : ↥(adjointGroup τ K)} (hb : b ∈ borelSub τ K) :
    ∃ χ : Kˣ, endHom K b (rootVec τ K θ) = (χ : K) • rootVec τ K θ ∧
      (∀ x : RootModule τ K, (endHom K b x) (negLabel hθ.1) = ((χ⁻¹ : Kˣ) : K) * x (negLabel hθ.1)) ∧
      ∀ c : K, b * xPar (rootOperatorFamily τ) θ c * b⁻¹ = xPar (rootOperatorFamily τ) θ ((χ : K) * c) := by
  have hle : borelSub τ K ≤ stabSub (K := K) hθ.1 := by
    unfold borelSub
    refine sup_le ?_ ?_
    · refine iSup_le fun i => ?_
      rintro _ ⟨t, rfl⟩
      exact torusElement_mem_stabSub hθ.1 i t
    · unfold posUnip
      refine iSup₂_le fun γ hγ => ?_
      obtain ⟨hγR, hγp⟩ := hγ
      intro x hx
      obtain ⟨c, rfl⟩ := (mem_rootGroup_iff hγR x).1 hx
      exact posRoot_mem_stabSub hτ hθ hγR hγp c
  exact (mem_stabSub_iff hθ.1).1 (hle hb)

theorem wordProd_stab (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4) {θ : Fin τ.rank → ℤ}
    (hθ : IsMaxHeightRoot τ θ) (w : List (Fin τ.rank)) :
    ∃ (θ' : Fin τ.rank → ℤ) (hθ' : IsRoot τ θ') (ε ε' : ℤ), (ε = 1 ∨ ε = -1) ∧ (ε' = 1 ∨ ε' = -1) ∧
      rootNorm τ θ' = rootNorm τ θ ∧
      endHom K (wordProd τ K w) (rootVec τ K θ) = (ε : K) • rootVec τ K θ' ∧
      ∀ c : K, wordProd τ K w * xPar (rootOperatorFamily τ) θ c * (wordProd τ K w)⁻¹ =
        xPar (rootOperatorFamily τ) θ' ((ε' : K) * c) := by
  classical
  have hwe : ∀ i : Fin τ.rank,
      CFSG.LieType.Steinberg.weylElement (xPar (rootOperatorFamily τ)) i (1 : Kˣ) =
        CFSG.LieType.Chevalley.weylElement τ K i := fun i => by
    rw [CFSG.LieType.Steinberg.Adjoint.weylElement_xPar, torusElement_one_eq, one_mul]
  have e : ∀ n W X : ↥(adjointGroup τ K), n * W * X * (n * W)⁻¹ = n * (W * X * W⁻¹) * n⁻¹ :=
    fun n W X => by group
  induction w with
  | nil =>
    refine ⟨θ, hθ.1, 1, 1, Or.inl rfl, Or.inl rfl, rfl, ?_, ?_⟩
    · simp [wordProd]
    · intro c
      simp [wordProd]
  | cons i w ih =>
    obtain ⟨θ', hθ', ε, ε', hε, hε', hn, hv, hx⟩ := ih
    obtain ⟨s, hs, hsv, -⟩ := weyl_step_explicit (K := K) i hθ'
    obtain ⟨s', hs', hsx⟩ := weylElement_xPar_conj (F := rootOperatorFamily τ) (K := K) i hθ'
    have hw : wordProd τ K (i :: w) =
        CFSG.LieType.Steinberg.weylElement (xPar (rootOperatorFamily τ)) i (1 : Kˣ) * wordProd τ K w := by
      rw [hwe i]
      simp [wordProd]
    refine ⟨reflect τ i θ', IsRoot.reflect i hθ', ε * s, s' * ε', ?_, ?_, ?_, ?_, ?_⟩
    · rcases hε with rfl | rfl <;> rcases hs with rfl | rfl <;> norm_num
    · rcases hs' with rfl | rfl <;> rcases hε' with rfl | rfl <;> norm_num
    · rw [rootNorm_reflect]
      exact hn
    · rw [hw, map_mul, Module.End.mul_apply, hv, map_smul, hsv, smul_smul, Int.cast_mul]
    · intro c
      have hc := hsx 1 ((ε' : K) * c)
      simp only [Units.val_one, one_zpow, mul_one] at hc
      have hrefl : CFSG.LieType.RootSystem.reflection τ.cartan i θ' = reflect τ i θ' := by
        rw [CFSG.LieType.RootSystem.reflection_apply]
        rfl
      rw [hrefl] at hc
      rw [hw, e, hx c, hc]
      congr 1
      push_cast
      ring

theorem bigCell_conj_b (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4) {θ : Fin τ.rank → ℤ}
    (hθ : IsMaxHeightRoot τ θ) (g : ↥(adjointGroup τ K))
    (hlam : entry g (negLabel hθ.1) (rootLabel hθ.1) ≠ 0) :
    ∃ (b : ↥(adjointGroup τ K)) (χ μ : K), χ ≠ 0 ∧
      (∀ c : K, b * xPar (rootOperatorFamily τ) θ c * b⁻¹ = xPar (rootOperatorFamily τ) θ (χ * c)) ∧
      (χ⁻¹ * μ = entry g (negLabel hθ.1) (rootLabel hθ.1) ∨
        χ⁻¹ * μ = -entry g (negLabel hθ.1) (rootLabel hθ.1)) ∧
      ∀ c : K, g * xPar (rootOperatorFamily τ) θ c * g⁻¹ =
        b * xPar (rootOperatorFamily τ) (-θ) (μ * c) * b⁻¹ := by
  classical
  obtain ⟨w, b₁, b₂, hb₁, hb₂, hg⟩ := exists_bruhat_decomp hτ g
  obtain ⟨χ₁, hv₁, hz₁, hc₁⟩ := borel_stab hτ hθ hb₁
  obtain ⟨χ₂, hv₂, hz₂, hc₂⟩ := borel_stab hτ hθ hb₂
  obtain ⟨θ', hθ', ε, ε', hε, hε', hn, hvw, hxw⟩ := wordProd_stab (K := K) hτ hθ w
  have hentry : entry g (negLabel hθ.1) (rootLabel hθ.1) =
      (χ₂ : K) * ε * (((χ₁⁻¹ : Kˣ) : K) * (rootVec τ K θ') (negLabel hθ.1)) := by
    unfold entry
    have hv : (Finsupp.single (rootLabel hθ.1) (1 : K) : RootModule τ K) = rootVec τ K θ :=
      (rootVec_eq_single hθ.1).symm
    rw [hv, hg, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hv₂, map_smul, hvw,
      map_smul, map_smul, Finsupp.smul_apply, Finsupp.smul_apply, hz₁]
    simp only [smul_eq_mul]
    ring
  have hθ'eq : θ' = -θ := by
    by_contra hne
    apply hlam
    rw [hentry]
    have : (rootVec τ K θ') (negLabel hθ.1) = 0 := by
      rw [rootVec_eq_single hθ', Finsupp.single_apply, if_neg]
      intro h
      apply hne
      have h' := h
      simp only [negLabel, rootLabel, Sum.inr.injEq, Subtype.mk.injEq] at h'
      exact h'
    rw [this]
    simp
  subst hθ'eq
  have hone : (rootVec τ K (-θ)) (negLabel hθ.1) = 1 := by
    rw [rootVec_eq_single hθ']
    simp [negLabel, rootLabel]
  rw [hone] at hentry
  refine ⟨b₁, (χ₁ : K), (ε' : K) * χ₂, Units.ne_zero _, hc₁, ?_, fun c => ?_⟩
  · have hχ : ((χ₁⁻¹ : Kˣ) : K) = (χ₁ : K)⁻¹ := by simp
    have hlamE : entry g (negLabel hθ.1) (rootLabel hθ.1) = (χ₂ : K) * ε * (χ₁ : K)⁻¹ := by
      rw [hentry, hχ]
      ring
    have hχ0 : (χ₁ : K) ≠ 0 := Units.ne_zero _
    rcases hε with rfl | rfl <;> rcases hε' with rfl | rfl
    · left; rw [hlamE]; push_cast; field_simp
    · right; rw [hlamE]; push_cast; field_simp
    · right; rw [hlamE]; push_cast; field_simp
    · left; rw [hlamE]; push_cast; field_simp
  · have e : g * xPar (rootOperatorFamily τ) θ c * g⁻¹ =
        b₁ * (wordProd τ K w * (b₂ * xPar (rootOperatorFamily τ) θ c * b₂⁻¹) * (wordProd τ K w)⁻¹) *
          b₁⁻¹ := by
      rw [hg]
      group
    rw [e, hc₂, hxw]
    congr 3
    ring

theorem bigCell' (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4) {θ : Fin τ.rank → ℤ}
    (hθ : IsMaxHeightRoot τ θ) (g : ↥(adjointGroup τ K))
    (hlam : entry g (negLabel hθ.1) (rootLabel hθ.1) ≠ 0) :
    ∃ (ψ : Matrix.SpecialLinearGroup (Fin 2) K →* ↥(adjointGroup τ K)) (μ₁ μ₂ : K), μ₁ ≠ 0 ∧
      (μ₁ * μ₂ = entry g (negLabel hθ.1) (rootLabel hθ.1) ∨
        μ₁ * μ₂ = -entry g (negLabel hθ.1) (rootLabel hθ.1)) ∧
      ∀ c : K, ψ (u2 (μ₁ * c)) = xPar (rootOperatorFamily τ) θ c ∧
        ψ (l2 (μ₂ * c)) = g * xPar (rootOperatorFamily τ) θ c * g⁻¹ := by
  obtain ⟨b, χ, μ, hχ, hb, hμ, hg⟩ := bigCell_conj_b hτ hθ g hlam
  obtain ⟨φ, ε₁, ε₂, h1, h2, hφ⟩ := exists_rootSL2 (K := K) hθ.1
  have hε1 : (ε₁ : K) * ε₁ = 1 := by rcases h1 with rfl | rfl <;> simp
  have hε2 : (ε₂ : K) * ε₂ = 1 := by rcases h2 with rfl | rfl <;> simp
  have hconjX : ∀ x : ↥(adjointGroup τ K), (MulAut.conj b).toMonoidHom x = b * x * b⁻¹ := fun x => rfl
  refine ⟨(MulAut.conj b).toMonoidHom.comp φ, (ε₁ : K) * χ⁻¹, (ε₂ : K) * μ, ?_, ?_, fun c => ⟨?_, ?_⟩⟩
  · exact mul_ne_zero (by rcases h1 with rfl | rfl <;> simp) (inv_ne_zero hχ)
  · have e : ((ε₁ : K) * χ⁻¹) * ((ε₂ : K) * μ) = ((ε₁ : K) * ε₂) * (χ⁻¹ * μ) := by ring
    rw [e]
    rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> rcases hμ with h | h <;> simp [h]
  · simp only [MonoidHom.comp_apply, hconjX, (hφ _).1]
    rw [hb]
    congr 1
    calc (χ : K) * ((ε₁ : K) * ((ε₁ : K) * χ⁻¹ * c)) = ((ε₁ : K) * ε₁) * (χ * χ⁻¹) * c := by ring
      _ = c := by rw [hε1, mul_inv_cancel₀ hχ]; ring
  · simp only [MonoidHom.comp_apply, hconjX, (hφ _).2]
    rw [hg c]
    congr 3
    calc (ε₂ : K) * ((ε₂ : K) * μ * c) = ((ε₂ : K) * ε₂) * μ * c := by ring
      _ = μ * c := by rw [hε2]; ring


end BigCellConj

end CFSG.LieType.SeitzGeneration.ExcOuterLeOne
