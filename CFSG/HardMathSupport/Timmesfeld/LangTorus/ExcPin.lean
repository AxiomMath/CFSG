module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompAlcove
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcKacCount
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.RankThree.Lattice.SteinbergBIRoots

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.Lattice
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups
open scoped Matrix

section Roots

variable {τ : Tag} (K : KacData τ)

theorem neg_θ_le_and_le_θ (hK : K.Facts) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (j : Fin τ.rank) : -K.θ j ≤ γ j ∧ γ j ≤ K.θ j := by
  rcases hγ.nonneg_or_nonpos with h | h
  · exact ⟨by linarith [h j, hK.θ_pos j], hK.le_θ γ hγ h j⟩
  · have h' := hK.le_θ (-γ) (IsRoot.neg hγ) (fun k => by
      simp only [Pi.neg_apply]
      linarith [h k]) j
    simp only [Pi.neg_apply] at h'
    exact ⟨by linarith, by linarith [h j, hK.θ_pos j]⟩

theorem mem_rootsOf_iff (hK : K.Facts) {C : Finset (Option (Fin τ.rank))} (hC : ∃ x, x ∉ C)
    {γ : Fin τ.rank → ℤ} :
    γ ∈ K.rootsOf (C : Set (Option (Fin τ.rank))) ↔ IsRoot τ γ ∧ kacTest K.θ C γ := by
  classical
  constructor
  · rintro ⟨hγ, n, hn, hγn⟩
    refine ⟨hγ, ?_⟩
    have hoffn : ∀ j, some j ∉ C → n (some j) = 0 := fun j hj => by
      by_contra h
      exact hj (hn _ h)
    by_cases h0 : n none = 0
    · left
      intro j hj
      rcases hγn with rfl | rfl
      · rw [K.combo_apply_of_none h0, hoffn j hj, Nat.cast_zero]
      · rw [Pi.neg_apply, K.combo_apply_of_none h0, hoffn j hj, Nat.cast_zero, neg_zero]
    · right
      have hnone : none ∈ C := hn none h0
      obtain ⟨x, hx⟩ := hC
      obtain ⟨j₀, rfl⟩ : ∃ j₀, x = some j₀ := by
        cases x with
        | none => exact absurd hnone hx
        | some j₀ => exact ⟨j₀, rfl⟩
      have hoff : ∀ j, some j ∉ C → K.combo n j = -(n none : ℤ) * K.θ j := fun j hj => by
        rw [K.combo_apply, hoffn j hj, Nat.cast_zero, add_zero]
      have hb := neg_θ_le_and_le_θ K hK hγ j₀
      have hθ := hK.θ_pos j₀
      have hn1 : (1 : ℤ) ≤ n none := by exact_mod_cast Nat.one_le_iff_ne_zero.2 h0
      refine ⟨hnone, ?_⟩
      rcases hγn with rfl | rfl
      · left
        have h1 : (n none : ℤ) = 1 := by
          have := hb.1
          rw [hoff j₀ hx] at this
          nlinarith
        intro j hj
        rw [hoff j hj, h1]
        ring
      · right
        have h1 : (n none : ℤ) = 1 := by
          have := hb.2
          rw [Pi.neg_apply, hoff j₀ hx] at this
          nlinarith
        intro j hj
        rw [Pi.neg_apply, hoff j hj, h1]
        ring
  · rintro ⟨hγ, h | ⟨hnone, h | h⟩⟩
    · refine ⟨hγ, ?_⟩
      rcases hγ.nonneg_or_nonpos with hpos | hneg
      · refine ⟨fun x => Option.elim x 0 fun j => (γ j).toNat, fun x hx => ?_,
          Or.inl (K.combo_of_nonneg hpos).symm⟩
        cases x with
        | none => exact absurd rfl hx
        | some j =>
          by_contra hj
          exact hx (by simp [h j hj])
      · have hpos' : ∀ j, 0 ≤ (-γ) j := fun j => by
          simp only [Pi.neg_apply]
          linarith [hneg j]
        refine ⟨fun x => Option.elim x 0 fun j => ((-γ) j).toNat, fun x hx => ?_, Or.inr ?_⟩
        · cases x with
          | none => exact absurd rfl hx
          | some j =>
            by_contra hj
            exact hx (by simp [h j hj])
        · rw [K.combo_of_nonneg hpos', neg_neg]
    · refine ⟨hγ, fun x => Option.elim x 1 fun j => (γ j + K.θ j).toNat, fun x hx => ?_,
        Or.inl ?_⟩
      · cases x with
        | none => exact hnone
        | some j =>
          by_contra hj
          exact hx (by simp [h j hj])
      · funext j
        rw [K.combo_apply]
        simp only [Option.elim_none, Option.elim_some, Nat.cast_one]
        rw [Int.toNat_of_nonneg (by linarith [(neg_θ_le_and_le_θ K hK hγ j).1])]
        ring
    · refine ⟨hγ, fun x => Option.elim x 1 fun j => (K.θ j - γ j).toNat, fun x hx => ?_,
        Or.inr ?_⟩
      · cases x with
        | none => exact hnone
        | some j =>
          by_contra hj
          exact hx (by simp [h j hj])
      · funext j
        rw [Pi.neg_apply, K.combo_apply]
        simp only [Option.elim_none, Option.elim_some, Nat.cast_one]
        rw [Int.toNat_of_nonneg (by linarith [(neg_θ_le_and_le_θ K hK hγ j).2])]
        ring

theorem ncard_rootsOf (hK : K.Facts) {C : Finset (Option (Fin τ.rank))} (hC : ∃ x, x ∉ C) :
    (K.rootsOf (C : Set (Option (Fin τ.rank)))).ncard = kacCount τ K.θ C := by
  have h : K.rootsOf (C : Set (Option (Fin τ.rank))) = {v | IsRoot τ v ∧ kacTest K.θ C v} := by
    ext γ
    exact mem_rootsOf_iff K hK hC
  rw [h, ncard_isRoot_and]
  rfl

theorem rootsOf_mono {C C' : Set (Option (Fin τ.rank))} (h : C ⊆ C') :
    K.rootsOf C ⊆ K.rootsOf C' := by
  rintro γ ⟨hγ, n, hn, hγn⟩
  exact ⟨hγ, n, fun x hx => h (hn x hx), hγn⟩

theorem extRoot_mem_rootsOf {C : Set (Option (Fin τ.rank))} {x : Option (Fin τ.rank)}
    (hx : x ∈ C) : K.extRoot x ∈ K.rootsOf C := by
  classical
  refine ⟨K.isRoot_extRoot x, fun y => if y = x then 1 else 0, fun y hy => ?_, Or.inl ?_⟩
  · by_cases h : y = x
    · rw [h]
      exact hx
    · exact absurd (by simp [h]) hy
  · rw [KacData.combo, Finset.sum_eq_single x (fun b _ hb => by simp [hb]) (by simp)]
    simp

end Roots

section Rank

variable {τ : Tag}

@[expose] noncomputable def weylLin (w : WeylGroup τ) :
    (Fin τ.rank → ℚ) →ₗ[ℚ] (Fin τ.rank → ℚ) :=
  Matrix.toLin' (Matrix.of fun i j => (((w • (Pi.single j 1 : Fin τ.rank → ℤ)) i : ℤ) : ℚ))

theorem weylLin_apply (w : WeylGroup τ) (γ : Fin τ.rank → ℤ) :
    weylLin w (fun i => (γ i : ℚ)) = fun i => ((w • γ) i : ℚ) := by
  have hγ : γ = ∑ j, γ j • (Pi.single j 1 : Fin τ.rank → ℤ) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  have hw : w • γ = ∑ j, γ j • (w • (Pi.single j 1 : Fin τ.rank → ℤ)) := by
    conv_lhs => rw [hγ]
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => smul_comm w (γ j) _
  funext i
  rw [weylLin, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, hw]
  simp only [Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Int.cast_sum,
    Int.cast_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem compRank_image_le (w : WeylGroup τ) (Ψ : Set (Fin τ.rank → ℤ)) :
    compRank ((fun α => w • α) '' Ψ) ≤ compRank Ψ := by
  unfold compRank
  have h : (fun γ (i : Fin τ.rank) => (γ i : ℚ)) '' ((fun α => w • α) '' Ψ) =
      weylLin w '' ((fun γ (i : Fin τ.rank) => (γ i : ℚ)) '' Ψ) := by
    rw [Set.image_image, Set.image_image]
    exact Set.image_congr fun γ _ => (weylLin_apply w γ).symm
  rw [h, Submodule.span_image]
  exact Submodule.finrank_map_le _ _

theorem compRank_image (w : WeylGroup τ) (Ψ : Set (Fin τ.rank → ℤ)) :
    compRank ((fun α => w • α) '' Ψ) = compRank Ψ := by
  refine le_antisymm (compRank_image_le w Ψ) ?_
  have h := compRank_image_le w⁻¹ ((fun α => w • α) '' Ψ)
  rwa [Set.image_image, show (fun x => w⁻¹ • w • x) = id from funext fun x => inv_smul_smul w x,
    Set.image_id] at h

theorem ncard_image_smul (w : WeylGroup τ) (Ψ : Set (Fin τ.rank → ℤ)) :
    ((fun α => w • α) '' Ψ).ncard = Ψ.ncard :=
  Set.ncard_image_of_injective _ (MulAction.injective w)

variable (K : KacData τ)

theorem linearIndependent_extRoot (hK : K.Facts) {C : Finset (Option (Fin τ.rank))}
    (hC : ∃ x, x ∉ C) :
    LinearIndependent ℚ fun x : C => fun i =>
      ((K.extRoot (x : Option (Fin τ.rank)) i : ℤ) : ℚ) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hcoord : ∀ j : Fin τ.rank,
      ∑ x : C, g x * ((K.extRoot (x : Option (Fin τ.rank)) j : ℤ) : ℚ) = 0 := by
    intro j
    have h := congrFun hg j
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using h
  have hext : ∀ k j : Fin τ.rank, K.extRoot (some k) j = if j = k then 1 else 0 := by
    intro k j
    simp [KacData.extRoot, Pi.single_apply]
  have hnone : ∀ h : none ∈ C, g ⟨none, h⟩ = 0 := by
    intro h
    obtain ⟨x, hx⟩ := hC
    obtain ⟨j₀, rfl⟩ : ∃ j₀, x = some j₀ := by
      cases x with
      | none => exact absurd h hx
      | some j₀ => exact ⟨j₀, rfl⟩
    have h1 := hcoord j₀
    rw [Fintype.sum_eq_single ⟨none, h⟩ (fun y hy => ?_)] at h1
    · change g ⟨none, h⟩ * ((-K.θ j₀ : ℤ) : ℚ) = 0 at h1
      have hθ : ((K.θ j₀ : ℤ) : ℚ) ≠ 0 := by exact_mod_cast (hK.θ_pos j₀).ne'
      rw [Int.cast_neg, mul_neg, neg_eq_zero] at h1
      exact (mul_eq_zero.1 h1).resolve_right hθ
    · obtain ⟨y, hyC⟩ := y
      cases y with
      | none => exact absurd (Subtype.ext rfl) hy
      | some k =>
        have hk : j₀ ≠ k := fun e => hx (e ▸ hyC)
        change g _ * ((K.extRoot (some k) j₀ : ℤ) : ℚ) = 0
        simp [hext, hk]
  intro x
  obtain ⟨y, hy⟩ := x
  cases y with
  | none => exact hnone hy
  | some j =>
    have h1 := hcoord j
    rw [Fintype.sum_eq_single ⟨some j, hy⟩ (fun z hz => ?_)] at h1
    · change g _ * ((K.extRoot (some j) j : ℤ) : ℚ) = 0 at h1
      simpa [hext] using h1
    · obtain ⟨z, hzC⟩ := z
      cases z with
      | none =>
        change g _ * _ = 0
        rw [hnone hzC, zero_mul]
      | some k =>
        have hk : j ≠ k := fun e => hz (by subst e; rfl)
        change g _ * ((K.extRoot (some k) j : ℤ) : ℚ) = 0
        simp [hext, hk]

theorem compRank_rootsOf (hK : K.Facts) {C : Finset (Option (Fin τ.rank))} (hC : ∃ x, x ∉ C) :
    compRank (K.rootsOf (C : Set (Option (Fin τ.rank)))) = C.card := by
  classical
  set b : C → (Fin τ.rank → ℚ) := fun x i => ((K.extRoot (x : Option (Fin τ.rank)) i : ℤ) : ℚ)
    with hb
  have hspan : Submodule.span ℚ ((fun γ (i : Fin τ.rank) => (γ i : ℚ)) ''
      K.rootsOf (C : Set (Option (Fin τ.rank)))) = Submodule.span ℚ (Set.range b) := by
    refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨γ, ⟨-, n, hn, hγn⟩, rfl⟩
      have hc : (fun i => ((K.combo n i : ℤ) : ℚ)) ∈ Submodule.span ℚ (Set.range b) := by
        have e : (fun i => ((K.combo n i : ℤ) : ℚ)) =
            ∑ x, (n x : ℚ) • fun i => ((K.extRoot x i : ℤ) : ℚ) := by
          funext i
          simp [KacData.combo, Finset.sum_apply, Pi.smul_apply]
        rw [e]
        refine Submodule.sum_mem _ fun x _ => ?_
        by_cases h0 : n x = 0
        · rw [h0, Nat.cast_zero, zero_smul]
          exact Submodule.zero_mem _
        · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨x, hn x h0⟩, rfl⟩)
      rcases hγn with rfl | rfl
      · exact hc
      · have e : (fun i => (((-K.combo n) i : ℤ) : ℚ)) = -(fun i => ((K.combo n i : ℤ) : ℚ)) := by
          funext i
          simp
        change (fun i => (((-K.combo n) i : ℤ) : ℚ)) ∈ Submodule.span ℚ (Set.range b)
        rw [e]
        exact Submodule.neg_mem _ hc
    · rintro _ ⟨x, rfl⟩
      exact Submodule.subset_span ⟨K.extRoot x, extRoot_mem_rootsOf K x.2, rfl⟩
  unfold compRank
  rw [hspan, finrank_span_eq_card (linearIndependent_extRoot K hK hC), Fintype.card_coe]

end Rank

end CFSG.HardMathSupport.Timmesfeld.LangTorus
