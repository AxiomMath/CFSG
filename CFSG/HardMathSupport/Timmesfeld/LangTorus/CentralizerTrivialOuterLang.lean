module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialOuterNorm
public import CFSG.HardMathSupport.Timmesfeld.RootAut.Linear
public import CFSG.RankThree.PartOne.KE.A1Fixed

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Classical CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.RootAut
open scoped MatrixGroups

set_option linter.unusedSectionVars false


section Pinned

variable {τ : Tag} {L : Type} [Field L]

variable [IsAlgClosed L]

theorem OuterPinned.mem_rankOne {φ₁ : ModGL τ L →* ModGL τ L}
    {g : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ} {Q : ℕ} (h : OuterPinned φ₁ g Q)
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hneg : g (-β) = -g β) {x : ModGL τ L}
    (hx : x ∈ rootRankOneGroup τ L β) : φ₁ x ∈ rootRankOneGroup τ L (g β) := by
  have hgβ : IsRoot τ (g β) := (h β hβ).1
  rw [rootRankOneGroup, range_rootSL2_of_isRoot hβ] at hx
  rw [rootRankOneGroup, range_rootSL2_of_isRoot hgβ]
  have hle : (rootSubgroup τ L β ⊔ rootSubgroup τ L (-β)).map φ₁ ≤
      rootSubgroup τ L (g β) ⊔ rootSubgroup τ L (-g β) := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rw [rootSubgroup, MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
      obtain ⟨-, μ, -, hf⟩ := h β hβ
      rw [hf]
      exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨_, rfl⟩)
    · rw [rootSubgroup, MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
      obtain ⟨-, μ, -, hf⟩ := h (-β) (IsRoot.neg hβ)
      rw [hf, hneg]
      exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨_, rfl⟩)
  exact hle ⟨x, hx, rfl⟩

theorem outerPinned_step {p : ℕ} (S : LangSetup τ L p) (n : ℕ) :
    OuterPinned (iterHom S.D.step n) ((S.ρ : (Fin τ.rank → ℤ) → _)^[n]) (S.D.q ^ n) := by
  intro β hβ
  obtain ⟨μ, hμ, h⟩ := iter_step_pinnedX S n hβ
  exact ⟨S.iterate_isRoot n hβ, μ, hμ, fun t => by rw [iterHom_eq_iterate, h]⟩

theorem outerPinned_conj {n : ModGL τ L} (hn : n ∈ monomialSubgroup τ L) :
    OuterPinned (MulAut.conj n).toMonoidHom (weylQuotientHom τ L ⟨n, hn⟩ • ·) 1 := by
  intro β hβ
  obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX hn hβ
  exact ⟨IsRoot.smul hβ _, μ, μ.ne_zero, fun t => by rw [pow_one, ← hμ]; rfl⟩

theorem outer_rankOne_le_rootSpan {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {i : KernelComponent χ} {δ : Fin τ.rank → ℤ}
    (hδ : δ ∈ componentRoots χ i) :
    rootRankOneGroup τ L δ ≤ rootSpan τ L (componentRoots χ i) := by
  rw [rootRankOneGroup, range_rootSL2_of_isRoot (isRoot_of_mem_componentRoots hδ)]
  exact sup_le (rootSubgroup_le_rootSpan hδ)
    (rootSubgroup_le_rootSpan ((isRootComponent_componentRoots i).neg_mem _ hδ))

end Pinned

section Commute

theorem outer_commute_closure {G : Type*} [Group G] {S T : Set G}
    (h : ∀ a ∈ S, ∀ b ∈ T, Commute a b) :
    ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure T, Commute x y := by
  have h1 : ∀ a ∈ S, ∀ y ∈ Subgroup.closure T, Commute a y := by
    intro a ha y hy
    induction hy using Subgroup.closure_induction with
    | mem b hb => exact h a ha b hb
    | one => exact Commute.one_right a
    | mul b c _ _ hb hc => exact hb.mul_right hc
    | inv b _ hb => exact hb.inv_right
  intro x hx y hy
  induction hx using Subgroup.closure_induction with
  | mem a ha => exact h1 a ha y hy
  | one => exact Commute.one_left y
  | mul b c _ _ hb hc => exact hb.mul_left hc
  | inv b _ hb => exact hb.inv_left

theorem outer_noG2 {τ : Tag} (hτ : τ ≠ .G2) : NoG2 τ := by
  cases τ with
  | G2 => exact absurd rfl hτ
  | F4 => exact noG2_F4
  | D4 => exact fun _ => Or.inl (by simp [Tag.symmetrizer])
  | E6 => exact fun _ => Or.inl (by simp [Tag.symmetrizer])
  | E7 => exact fun _ => Or.inl (by simp [Tag.symmetrizer])
  | E8 => exact noG2_E8

variable {τ : Tag} {L : Type} [Field L]

theorem outer_iform_neg_left (x y : Fin τ.rank → ℤ) : iform (-x) y = -iform x y :=
  iform_neg_left_aux x y

theorem outer_iform_neg_right (x y : Fin τ.rank → ℤ) : iform x (-y) = -iform x y :=
  iform_neg_right_aux x y

theorem outer_not_isRoot_nsmul_add_nsmul {α α' : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (hα' : IsRoot τ α') (h0 : iform α α' = 0) (hadd : ¬ IsRoot τ (α + α')) {i j : ℕ}
    (hi : 1 ≤ i) (hj : 1 ≤ j) : ¬ IsRoot τ (i • α + j • α') := by
  intro hr
  have hpos : 0 < iform α α := iform_self_pos_of_isRoot hα
  have hne : α ≠ α' := fun h => by rw [← h] at h0; omega
  have hne' : α ≠ -α' := fun h => by
    rw [h, outer_iform_neg_left] at h0
    have : 0 < iform α' α' := iform_self_pos_of_isRoot hα'
    omega
  by_cases hG : τ = .G2
  · subst hG
    have hn : ∀ γ, IsRoot Tag.G2 γ → iform γ γ = 2 ∨ iform γ γ = 6 := by
      intro γ hγ
      obtain ⟨k, hk⟩ := iform_self_of_isRoot hγ
      have hs : ∀ k : Fin Tag.G2.rank, Tag.G2.symmetrizer k k = 3 ∨
          Tag.G2.symmetrizer k k = 1 := by decide
      rcases hs k with h | h <;> rw [h] at hk <;> omega
    have e := iform_nsmul_add_nsmul i j α α'
    rw [h0, mul_zero, add_zero] at e
    have hI : (1 : ℤ) ≤ i := by exact_mod_cast hi
    have hJ : (1 : ℤ) ≤ j := by exact_mod_cast hj
    have hI2 : (1 : ℤ) ≤ (i : ℤ) ^ 2 := by nlinarith
    have hJ2 : (1 : ℤ) ≤ (j : ℤ) ^ 2 := by nlinarith
    rcases hn _ hr with h | h <;> rcases hn _ hα with h1 | h1 <;>
      rcases hn _ hα' with h2 | h2 <;> rw [h, h1, h2] at e
    all_goals first
      | nlinarith
      | (rcases (show i = 1 ∨ 2 ≤ i by omega) with rfl | hi2
         · rcases (show j = 1 ∨ 2 ≤ j by omega) with rfl | hj2
           · norm_num at e
           · have : (4 : ℤ) ≤ (j : ℤ) ^ 2 := by
               have : (2 : ℤ) ≤ j := by exact_mod_cast hj2
               nlinarith
             nlinarith
         · have : (4 : ℤ) ≤ (i : ℤ) ^ 2 := by
             have : (2 : ℤ) ≤ i := by exact_mod_cast hi2
             nlinarith
           nlinarith)
  · rcases exponent_pair_cases (outer_noG2 hG) hα hα' hne hne' hi hj hr with h | h | h
    · obtain ⟨rfl, rfl⟩ := h
      rw [one_smul, one_smul] at hr
      exact hadd hr
    · omega
    · omega

theorem outer_commute_pinnedX {α α' : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (hα' : IsRoot τ α') (h0 : iform α α' = 0) (hadd : ¬ IsRoot τ (α + α')) (c d : L) :
    Commute (pinnedX τ L α c) (pinnedX τ L α' d) := by
  have hpos : 0 < iform α α := iform_self_pos_of_isRoot hα
  have hne : α ≠ α' := fun h => by rw [← h] at h0; omega
  have hne' : α ≠ -α' := fun h => by
    rw [h, outer_iform_neg_left] at h0
    have : 0 < iform α' α' := iform_self_pos_of_isRoot hα'
    omega
  obtain ⟨-, hmem, -, -, hF⟩ := root_commutator_formula τ hα hα' hne hne'
  have hnil : commPairs τ α α' = [] := List.eq_nil_iff_forall_not_mem.2 fun q hq => by
    obtain ⟨h1, h2, hr⟩ := (hmem q).1 hq
    exact outer_not_isRoot_nsmul_add_nsmul hα hα' h0 hadd h1 h2 hr
  have hF' := hF L c d
  rw [hnil, List.map_nil, List.prod_nil, ← pinnedX_neg, ← pinnedX_neg, ← commutatorElement_def,
    commutatorElement_eq_one_iff_mul_comm] at hF'
  exact hF'

theorem outer_commute_rankOne {β β' : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (hβ' : IsRoot τ β') (h0 : iform β β' = 0) (hadd : ¬ IsRoot τ (β + β'))
    (hsub : ¬ IsRoot τ (β - β')) :
    ∀ x ∈ rootRankOneGroup τ L β, ∀ y ∈ rootRankOneGroup τ L β', Commute x y := by
  have hnegroot : ∀ x : Fin τ.rank → ℤ, IsRoot τ (-x) → IsRoot τ x := fun x h => by
    simpa using IsRoot.neg h
  have hQ : ∀ {α : Fin τ.rank → ℤ}, IsRoot τ α → rootRankOneGroup τ L α =
      Subgroup.closure (Set.range (pinnedX τ L α) ∪ Set.range (pinnedX τ L (-α))) := by
    intro α hα
    rw [rootRankOneGroup, range_rootSL2_of_isRoot hα, rootSubgroup, rootSubgroup,
      Subgroup.closure_union]
  rw [hQ hβ, hQ hβ']
  refine outer_commute_closure ?_
  rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩) _ (⟨d, rfl⟩ | ⟨d, rfl⟩)
  · exact outer_commute_pinnedX hβ hβ' h0 hadd c d
  · refine outer_commute_pinnedX hβ (IsRoot.neg hβ')
      (by rw [outer_iform_neg_right, h0, neg_zero]) (by rwa [← sub_eq_add_neg]) c d
  · refine outer_commute_pinnedX (IsRoot.neg hβ) hβ' (by rw [outer_iform_neg_left, h0, neg_zero])
      (fun h => hsub (hnegroot _ (by rwa [neg_sub, sub_eq_neg_add]))) c d
  · refine outer_commute_pinnedX (IsRoot.neg hβ) (IsRoot.neg hβ')
      (by rw [outer_iform_neg_left, outer_iform_neg_right, h0, neg_zero, neg_zero])
      (fun h => hadd (hnegroot _ (by rwa [neg_add]))) c d

end Commute

section Return

variable {τ : Tag} {L : Type} [Field L]

theorem outer_return_fix {φ₁ : ModGL τ L →* ModGL τ L} (σ : L ≃+* L) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) {μ μ' : L} (hμ : μ ≠ 0) (hμ' : μ' ≠ 0)
    (hu : ∀ t, φ₁ (pinnedX τ L γ t) = pinnedX τ L γ (μ * σ t))
    (hv : ∀ t, φ₁ (pinnedX τ L (-γ) t) = pinnedX τ L (-γ) (μ' * σ t)) :
    ∃ a : Lˣ, ∀ B : SL2 L, φ₁ (rootSL2 τ L γ B) =
      rootSL2 τ L γ (conjSL (diagUnitOne a) (Matrix.SpecialLinearGroup.map σ.toRingHom B)) := by
  classical
  have hinj := rootSL2_injective_of_field (τ := τ) (K := L) γ
  have hQ : ∀ B : SL2 L, φ₁ (rootSL2 τ L γ B) ∈ (rootSL2 τ L γ).range := by
    intro B
    rw [range_rootSL2_of_isRoot hγ]
    have hle : (rootSubgroup τ L γ ⊔ rootSubgroup τ L (-γ)).map φ₁ ≤
        rootSubgroup τ L γ ⊔ rootSubgroup τ L (-γ) := by
      rw [Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rw [rootSubgroup, MonoidHom.map_closure, Subgroup.closure_le]
        rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
        rw [hu]
        exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨_, rfl⟩)
      · rw [rootSubgroup, MonoidHom.map_closure, Subgroup.closure_le]
        rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
        rw [hv]
        exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨_, rfl⟩)
    have hB : rootSL2 τ L γ B ∈ rootSubgroup τ L γ ⊔ rootSubgroup τ L (-γ) := by
      rw [← range_rootSL2_of_isRoot hγ]
      exact ⟨B, rfl⟩
    exact hle ⟨_, hB, rfl⟩
  let T : SL2 L →* SL2 L := (MonoidHom.ofInjective hinj).symm.toMonoidHom.comp
    ((φ₁.comp (rootSL2 τ L γ)).codRestrict _ hQ)
  have hT : ∀ B, rootSL2 τ L γ (T B) = φ₁ (rootSL2 τ L γ B) := fun B => by
    have := (MonoidHom.ofInjective hinj).apply_symm_apply ⟨φ₁ (rootSL2 τ L γ B), hQ B⟩
    exact congrArg Subtype.val this
  set ε : ℤ := (pinnedData τ γ).2.2 with hε
  have hεε : ∀ c : L, ε • ε • c = c := by
    intro c
    rcases pinnedSign_eq τ γ with h | h <;> rw [hε, h] <;> simp
  obtain ⟨η, hη, hvη⟩ := exists_rootSL2_vSL_eq (K := L) hγ
  have hση : σ η = η := sq_eq_one_fixed σ hη
  have hTu : ∀ c, T (sl2Upper L c) = sl2Upper L (μ * σ c) := by
    intro c
    apply hinj
    rw [hT]
    change φ₁ (rootSL2 τ L γ (uSL c)) = rootSL2 τ L γ (uSL _)
    rw [rootSL2_uSL_eq, rootSL2_uSL_eq, hu, ← hε, map_zsmul]
    congr 1
    rw [mul_smul_comm]
  have hTv : ∀ c, T (sl2Lower L c) = sl2Lower L (μ' * σ c) := by
    intro c
    apply hinj
    rw [hT]
    change φ₁ (rootSL2 τ L γ (vSL c)) = rootSL2 τ L γ (vSL _)
    rw [hvη, hvη, hv, map_mul, hση]
    congr 1
    ring
  obtain ⟨-, M, hM, hTM⟩ := sl2_semilinear_root_compatibility σ (Units.mk0 μ hμ)
    (Units.mk0 μ' hμ') T hTu hTv
  refine ⟨Units.mk0 μ hμ, fun B => ?_⟩
  rw [← hT]
  congr 1
  apply Subtype.ext
  rw [hTM B, coe_conjSL]
  have hMe : M = diagUnitOne (Units.mk0 μ hμ) := Units.ext (by rw [hM, coe_diagUnitOne])
  rw [hMe]
  rfl

theorem outer_return_neg {φ₁ : ModGL τ L →* ModGL τ L} (σ : L ≃+* L) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) {μ μ' : L} (hμ : μ ≠ 0) (hμ' : μ' ≠ 0)
    (hu : ∀ t, φ₁ (pinnedX τ L γ t) = pinnedX τ L (-γ) (μ * σ t))
    (hv : ∀ t, φ₁ (pinnedX τ L (-γ) t) = pinnedX τ L γ (μ' * σ t)) :
    ∃ a : Lˣ, ∀ B : SL2 L, φ₁ (rootSL2 τ L γ B) = rootSL2 τ L γ
      (conjSL (RankThree.Classical.swapGL * diagUnitOne a)
        (Matrix.SpecialLinearGroup.map σ.toRingHom B)) := by
  classical
  have hinj := rootSL2_injective_of_field (τ := τ) (K := L) γ
  have hQ : ∀ B : SL2 L, φ₁ (rootSL2 τ L γ B) ∈ (rootSL2 τ L γ).range := by
    intro B
    rw [range_rootSL2_of_isRoot hγ]
    have hle : (rootSubgroup τ L γ ⊔ rootSubgroup τ L (-γ)).map φ₁ ≤
        rootSubgroup τ L γ ⊔ rootSubgroup τ L (-γ) := by
      rw [Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rw [rootSubgroup, MonoidHom.map_closure, Subgroup.closure_le]
        rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
        rw [hu]
        exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨_, rfl⟩)
      · rw [rootSubgroup, MonoidHom.map_closure, Subgroup.closure_le]
        rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
        rw [hv]
        exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨_, rfl⟩)
    have hB : rootSL2 τ L γ B ∈ rootSubgroup τ L γ ⊔ rootSubgroup τ L (-γ) := by
      rw [← range_rootSL2_of_isRoot hγ]
      exact ⟨B, rfl⟩
    exact hle ⟨_, hB, rfl⟩
  let T : SL2 L →* SL2 L := (MonoidHom.ofInjective hinj).symm.toMonoidHom.comp
    ((φ₁.comp (rootSL2 τ L γ)).codRestrict _ hQ)
  have hT : ∀ B, rootSL2 τ L γ (T B) = φ₁ (rootSL2 τ L γ B) := fun B => by
    have := (MonoidHom.ofInjective hinj).apply_symm_apply ⟨φ₁ (rootSL2 τ L γ B), hQ B⟩
    exact congrArg Subtype.val this
  set ε : ℤ := (pinnedData τ γ).2.2 with hε
  have hεε : ∀ c : L, ε • ε • c = c := by
    intro c
    rcases pinnedSign_eq τ γ with h | h <;> rw [hε, h] <;> simp
  have hε0 : ((ε : ℤ) : L) * (ε : L) = 1 := by
    have := hεε 1
    simp only [zsmul_eq_mul, mul_one] at this
    exact this
  obtain ⟨η, hη, hvη⟩ := exists_rootSL2_vSL_eq (K := L) hγ
  have hση : σ η = η := sq_eq_one_fixed σ hη
  have hη0 : η ≠ 0 := fun h => by rw [h, zero_mul] at hη; exact zero_ne_one hη
  have hε0' : ((ε : ℤ) : L) ≠ 0 := fun h => by rw [h, zero_mul] at hε0; exact zero_ne_one hε0
  set aT : L := η * (μ * ε) with haT
  set bT : L := ε * (μ' * η) with hbT
  have haT0 : aT ≠ 0 := mul_ne_zero hη0 (mul_ne_zero hμ hε0')
  have hbT0 : bT ≠ 0 := mul_ne_zero hε0' (mul_ne_zero hμ' hη0)
  have hTu : ∀ c, T (sl2Upper L c) = sl2Lower L (aT * σ c) := by
    intro c
    apply hinj
    rw [hT]
    change φ₁ (rootSL2 τ L γ (uSL c)) = rootSL2 τ L γ (vSL _)
    rw [rootSL2_uSL_eq, hvη, hu, ← hε, map_zsmul]
    congr 1
    rw [haT, zsmul_eq_mul]
    linear_combination (-(μ * (ε : L) * σ c)) * hη
  have hTv : ∀ c, T (sl2Lower L c) = sl2Upper L (bT * σ c) := by
    intro c
    apply hinj
    rw [hT]
    change φ₁ (rootSL2 τ L γ (vSL c)) = rootSL2 τ L γ (uSL _)
    rw [hvη, rootSL2_uSL_eq, hv, map_mul, hση, ← hε, hbT, zsmul_eq_mul]
    congr 1
    linear_combination (-(μ' * η * σ c)) * hε0
  obtain ⟨-, M, hM, hTM⟩ := sl2_semilinear_exchanged_root_compatibility σ (Units.mk0 aT haT0)
    (Units.mk0 bT hbT0) T hTu hTv
  refine ⟨Units.mk0 aT haT0, fun B => ?_⟩
  rw [← hT]
  congr 1
  apply Subtype.ext
  rw [hTM B, coe_conjSL]
  have hMe : M = RankThree.Classical.swapGL * diagUnitOne (Units.mk0 aT haT0) :=
    Units.ext (by rw [hM, coe_swapGL_mul_diagUnitOne])
  rw [hMe]
  rfl

end Return

section Iter

variable {τ : Tag}

theorem outer_iterate_neg_mem {Ψ : Set (Fin τ.rank → ℤ)} {g : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ}
    (hmaps : ∀ β ∈ Ψ, g β ∈ Ψ) (hneg : ∀ β ∈ Ψ, g (-β) = -g β) :
    ∀ n : ℕ, ∀ β ∈ Ψ, g^[n] (-β) = -g^[n] β ∧ g^[n] β ∈ Ψ
  | 0 => fun _ hβ => ⟨rfl, hβ⟩
  | n + 1 => fun β hβ => by
    obtain ⟨h1, h2⟩ := outer_iterate_neg_mem hmaps hneg n β hβ
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', h1, hneg _ h2]
    exact ⟨rfl, hmaps _ h2⟩

variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)

theorem outer_isIsometry_rho {Ψ : Set (Fin τ.rank → ℤ)} {s : ℕ}
    (hs : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' Ψ = Ψ) :
    IsIsometry Ψ ((S.ρ : (Fin τ.rank → ℤ) → _)^[s]) := by
  have hinj : Function.Injective ((S.ρ : (Fin τ.rank → ℤ) → _)^[s]) :=
    S.ρ.injective.iterate s
  have hform : ∀ n : ℕ, ∀ γ δ, iform ((S.ρ : (Fin τ.rank → ℤ) → _)^[n] γ)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[n] δ) = iform γ δ := by
    intro n
    induction n with
    | zero => intro γ δ; rfl
    | succ n ih =>
      intro γ δ
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', S.frob.iform_eq, ih]
  have hneg : ∀ n : ℕ, ∀ γ, (S.ρ : (Fin τ.rank → ℤ) → _)^[n] (-γ) =
      -(S.ρ : (Fin τ.rank → ℤ) → _)^[n] γ := by
    intro n
    induction n with
    | zero => intro γ; rfl
    | succ n ih =>
      intro γ
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, S.frob.neg_eq]
  refine ⟨⟨fun γ hγ => ?_, hinj.injOn, fun γ hγ => ?_⟩, fun γ _ δ _ => hform s γ δ,
    fun γ _ => hneg s γ⟩
  · rw [← hs]
    exact Set.mem_image_of_mem _ hγ
  · rw [hs]
    exact hγ

theorem outer_exists_frob (n : ℕ) : ∃ σm : L ≃+* L, ∀ c, σm c = c ^ (S.D.q ^ n) := by
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨σ, hσ⟩ := exists_ringEquiv_frob (L := L) r (e * n)
  refine ⟨σ, fun c => ?_⟩
  have h1 : σ c = iterateFrobenius L r (e * n) c := by
    rw [← hσ]
    rfl
  rw [h1, iterateFrobenius_def, hq, ← pow_mul]

theorem outer_card_fixSubfield (σm : L ≃+* L) {n : ℕ} (hn : 0 < n)
    (hσm : ∀ c, σm c = c ^ (S.D.q ^ n)) :
    Finite (fixSubfield σm) ∧ Nat.card (fixSubfield σm) = S.D.q ^ n := by
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  have : Fact r.Prime := ⟨hr⟩
  have hen : 0 < e * n := Nat.mul_pos he hn
  have hσm' : ∀ c, σm c = c ^ (r ^ (e * n)) := fun c => by rw [hσm, hq, ← pow_mul]
  obtain ⟨hfinset, hcardset⟩ := ncard_pow_eq_self (L := L) r (e * n) hen
  have hset : (fixSubfield σm : Set L) = {c : L | c ^ (r ^ (e * n)) = c} := by
    ext c
    show c ∈ fixSubfield σm ↔ _
    rw [mem_fixSubfield, hσm']
    rfl
  refine ⟨?_, ?_⟩
  · have h1 : (fixSubfield σm : Set L).Finite := by rw [hset]; exact hfinset
    exact h1.to_subtype
  · have h1 : Nat.card (fixSubfield σm) = (fixSubfield σm : Set L).ncard :=
      Nat.card_coe_set_eq (fixSubfield σm : Set L)
    rw [h1, hset, hcardset, hq, ← pow_mul]

end Iter

section SL2Lang

variable {L : Type} [Field L] [IsAlgClosed L]

theorem outer_sl2_lang {K : Type} [Field K] [Finite K] [Algebra K L] (σ : L ≃+* L)
    (hσ : ∀ c, σ c = c ^ Nat.card K) (a : Lˣ) :
    ∃ (B : SL2 L) (x : Lˣ),
      conjSL (diagUnitOne a) (Matrix.SpecialLinearGroup.map σ.toRingHom B) = B * nSL x := by
  classical
  obtain ⟨P, hP⟩ := exists_twist_diag (K := K) σ.toRingHom hσ a
  obtain ⟨R, hR⟩ := CFSG.RankThree.PartOne.KGD.exists_twist_antidiag (K := K) σ.toRingHom hσ 1 1
    RankThree.Classical.swapGL (by rw [coe_swapGL, Units.val_one])
  set F := Matrix.GeneralLinearGroup.map (n := Fin 2) σ.toRingHom with hF
  set B₀ : GL (Fin 2) L := P * R⁻¹ with hB₀
  have hB : diagUnitOne a * F B₀ = B₀ * RankThree.Classical.swapGL := by
    rw [← hP, ← hR, hB₀]
    simp only [map_mul, map_inv]
    group
  have hdet : ((B₀ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L).det ≠ 0 :=
    Matrix.det_ne_zero_of_right_inverse (B := ((B₀⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L))
      (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one])
  obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_pow_nat_eq ((B₀ : Matrix (Fin 2) (Fin 2) L).det) two_pos
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero] at hμ
    exact hdet hμ.symm
  have hdet' : (μ⁻¹ • (B₀ : Matrix (Fin 2) (Fin 2) L)).det = 1 := by
    rw [Matrix.det_smul, Fintype.card_fin, inv_pow, ← hμ, inv_mul_cancel₀ (pow_ne_zero 2 hμ0)]
  set B : SL2 L := ⟨μ⁻¹ • (B₀ : Matrix (Fin 2) (Fin 2) L), hdet'⟩ with hBdef
  have hσμ : σ μ ≠ 0 := (map_ne_zero σ).2 hμ0
  set u : L := μ * (σ μ)⁻¹ with hu
  have hu0 : u ≠ 0 := mul_ne_zero hμ0 (inv_ne_zero hσμ)
  have hDm : (diagUnitOne a : Matrix (Fin 2) (Fin 2) L) * (F B₀ : Matrix (Fin 2) (Fin 2) L) =
      (B₀ : Matrix (Fin 2) (Fin 2) L) * !![0, 1; 1, 0] := by
    have := congrArg (fun g : GL (Fin 2) L => (g : Matrix (Fin 2) (Fin 2) L)) hB
    simpa only [Units.val_mul, coe_swapGL] using this
  have hmapB : ((Matrix.SpecialLinearGroup.map σ.toRingHom B : SL2 L) :
      Matrix (Fin 2) (Fin 2) L) = σ μ⁻¹ • (F B₀ : Matrix (Fin 2) (Fin 2) L) := by
    ext i j
    change σ ((μ⁻¹ • (B₀ : Matrix (Fin 2) (Fin 2) L)) i j) =
      σ μ⁻¹ * σ ((B₀ : Matrix (Fin 2) (Fin 2) L) i j)
    rw [Matrix.smul_apply, smul_eq_mul, map_mul]
  have e1 : !![(0 : L), u; u * ((a⁻¹ : Lˣ) : L), 0] =
      u • (!![(0 : L), 1; 1, 0] * !![((a⁻¹ : Lˣ) : L), 0; 0, 1]) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mul_comm]
  have hcalc : (diagUnitOne a : Matrix (Fin 2) (Fin 2) L) *
      ((Matrix.SpecialLinearGroup.map σ.toRingHom B : SL2 L) : Matrix (Fin 2) (Fin 2) L) *
      (↑(diagUnitOne a)⁻¹ : Matrix (Fin 2) (Fin 2) L) =
      (B : Matrix (Fin 2) (Fin 2) L) * !![(0 : L), u; u * ((a⁻¹ : Lˣ) : L), 0] := by
    rw [hmapB, Matrix.mul_smul, Matrix.smul_mul, hDm, coe_diagUnitOne_inv, e1,
      show (B : Matrix (Fin 2) (Fin 2) L) = μ⁻¹ • (B₀ : Matrix (Fin 2) (Fin 2) L) from rfl,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc, map_inv₀]
    congr 1
    rw [hu, ← mul_assoc, inv_mul_cancel₀ hμ0, one_mul]
  have hdetN : (!![(0 : L), u; u * ((a⁻¹ : Lˣ) : L), 0]).det = 1 := by
    have h1 := (conjSL (diagUnitOne a) (Matrix.SpecialLinearGroup.map σ.toRingHom B)).2
    rw [coe_conjSL, hcalc, Matrix.det_mul, B.2, one_mul] at h1
    exact h1
  have h' : u * (u * ((a⁻¹ : Lˣ) : L)) = -1 := by
    rw [Matrix.det_fin_two_of] at hdetN
    linear_combination -hdetN
  have hy : u * (a : L)⁻¹ = -u⁻¹ := by
    have h2 : u * (u * (a : L)⁻¹) = u * (-u⁻¹) := by
      rw [mul_neg, mul_inv_cancel₀ hu0, ← Units.val_inv_eq_inv_val, h']
    exact mul_left_cancel₀ hu0 h2
  refine ⟨B, Units.mk0 u hu0, Subtype.ext ?_⟩
  rw [coe_conjSL, hcalc, Matrix.SpecialLinearGroup.coe_mul]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nSL, hy]

end SL2Lang

section LangStep

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)

theorem outer_exists_lang_conj {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus) {s : ℕ}
    (hs : 0 < s) {c : ModGL τ L} (hc : c ∈ rootSpan τ L (kernelRoots (rootCharHom a))) :
    ∃ z₀ : ModGL τ L, (∀ j : KernelComponent (rootCharHom a), ∀ g : ModGL τ L,
        g ∈ rootSpan τ L (componentRoots (rootCharHom a) j) ↔
          z₀ * g * z₀⁻¹ ∈ rootSpan τ L (componentRoots (rootCharHom a) j)) ∧
      ∀ g : ModGL τ L, iterHom S.D.step s (z₀ * g * z₀⁻¹) =
        z₀ * iterHom S.D.step s (c * g * c⁻¹) * z₀⁻¹ := by
  have hφc : iterHom S.D.step s c ∈
      torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a)) := by
    refine Subgroup.mem_sup_right ?_
    have hmap : (rootSpan τ L (kernelRoots (rootCharHom a))).map (iterHom S.D.step s) ≤
        rootSpan τ L (kernelRoots (rootCharHom a)) := by
      refine map_rootSpan_le_of_forall fun γ hγ x => ?_
      obtain ⟨μ, -, hμ⟩ := iter_step_pinnedX S s hγ.1
      rw [iterHom_eq_iterate, hμ]
      exact pinnedX_mem_rootSpan (outer_iterate_mem_kernelRoots S hT s hγ) _
    exact hmap ⟨c, hc, rfl⟩
  obtain ⟨z, hz, hnorm⟩ := outer_exists_lang S hT hs hφc
  refine ⟨z, hnorm, fun g => ?_⟩
  simp only [map_mul, map_inv]
  rw [hz]
  group

end LangStep

end CFSG.HardMathSupport.Timmesfeld.LangTorus
