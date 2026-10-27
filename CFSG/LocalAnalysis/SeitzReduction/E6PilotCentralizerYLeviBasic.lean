module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCentralizerY

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

section Parabolic

variable {τ : Tag} {K : Type} [Field K]


variable (τ K) in
@[expose] def simpleGens (J : Set (Fin τ.rank)) : Set (ModGL τ K) :=
  {g | ∃ j ∈ J, ∃ c : K, g = xUnit τ K j c ∨ g = yUnit τ K j c}

theorem canonicalRep_mem_closure_simpleGens {J : Set (Fin τ.rank)} {w : WeylGroup τ}
    (hw : w ∈ parabolicWeylGroup τ J) :
    canonicalRep (coxeterSystem τ) K w ∈ closure (simpleGens τ K J) := by
  obtain ⟨ω, hω, rfl, hletters⟩ := (parabolic_Weyl_coordinate_stabilizer τ J).2.1 w hw
  rw [canonicalRep_wordProd hω]
  refine list_prod_mem fun x hx => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
  rw [CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul]
  exact mul_mem (mul_mem (subset_closure ⟨i, hletters i hi, _, Or.inl rfl⟩)
    (subset_closure ⟨i, hletters i hi, _, Or.inr rfl⟩))
    (subset_closure ⟨i, hletters i hi, _, Or.inl rfl⟩)

theorem rootSpan_parabolicRoots_eq_closure (J : Set (Fin τ.rank)) :
    rootSpan τ K (parabolicRoots τ J) = closure (simpleGens τ K J) := by
  refine le_antisymm (iSup₂_le fun γ hγ => ?_) ((closure_le _).2 ?_)
  · have hsingle : ∀ j ∈ J, rootSubgroup τ K (Pi.single j 1) ≤ closure (simpleGens τ K J) :=
      fun j hj => (closure_le _).2 (by
        rintro _ ⟨c, rfl⟩
        rw [SetLike.mem_coe, pinnedX_single]
        exact subset_closure ⟨j, hj, c, Or.inl rfl⟩)
    have hnegsingle : ∀ j ∈ J,
        rootSubgroup τ K (-Pi.single j 1) ≤ closure (simpleGens τ K J) :=
      fun j hj => (closure_le _).2 (by
        rintro _ ⟨c, rfl⟩
        rw [SetLike.mem_coe, pinnedX_neg_single]
        exact subset_closure ⟨j, hj, c, Or.inr rfl⟩)
    rcases IsRoot.height_pos_or_neg hγ.1 with hpos | hneg
    · obtain ⟨w, hw, j, hj, hwj⟩ := exists_mem_parabolicWeylGroup_smul _ γ rfl ⟨hγ, hγ.1, hpos⟩
      rw [← hwj]
      exact F4Pilot.rootSubgroup_smul_le_of_canonicalRep_mem
        (canonicalRep_mem_closure_simpleGens hw) (isRoot_single τ j) (hsingle j hj)
    · have hneg' : -γ ∈ parabolicPosRoots τ J :=
        ⟨⟨IsRoot.neg hγ.1, fun i hi => by rw [Pi.neg_apply, hγ.2 i hi, neg_zero]⟩,
          IsRoot.neg hγ.1, by rw [height_neg]; omega⟩
      obtain ⟨w, hw, j, hj, hwj⟩ := exists_mem_parabolicWeylGroup_smul _ (-γ) rfl hneg'
      have e : γ = w • (-Pi.single j 1 : Fin τ.rank → ℤ) := by rw [smul_neg, hwj, neg_neg]
      rw [e]
      exact F4Pilot.rootSubgroup_smul_le_of_canonicalRep_mem
        (canonicalRep_mem_closure_simpleGens hw) (isRoot_neg_single τ j) (hnegsingle j hj)
  · rintro _ ⟨j, hj, c, rfl | rfl⟩
    · rw [← pinnedX_single]
      exact pinnedX_mem_rootSpan (S := parabolicRoots τ J) ⟨isRoot_single τ j, fun i hi =>
        Pi.single_eq_of_ne (show i ≠ j from fun h => hi (h ▸ hj)) _⟩ c
    · rw [← pinnedX_neg_single]
      exact pinnedX_mem_rootSpan (S := parabolicRoots τ J) ⟨isRoot_neg_single τ j, fun i hi => by
        rw [Pi.neg_apply, Pi.single_eq_of_ne (show i ≠ j from fun h => hi (h ▸ hj)), neg_zero]⟩ c

end Parabolic

local instance e6CentralizerYLeviBasicNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

local instance e6CentralizerYLeviBasicNeZeroRankF4 : NeZero Tag.F4.rank := ⟨by decide⟩

local instance e6CentralizerYLeviBasicNeZeroRankTw : NeZero TwistTag.E6.tag.rank := ⟨by decide⟩

@[expose] def yAlphaAS : Fin Tag.E6.rank → ℤ := ![1, 1, 2, 2, 1, 1]

@[expose] def yBetaAS : Fin Tag.E6.rank → ℤ := ![1, 1, 1, 2, 2, 1]

@[expose] def yFixedRootsAS : Set (Fin Tag.E6.rank → ℤ) :=
  {γ | IsRoot .E6 γ ∧ iform γ yAlphaAS = 0 ∧ iform γ yBetaAS = 0}

@[expose] def yPairRootsAS : Set (Fin Tag.E6.rank → ℤ) :=
  {γ | IsRoot .E6 γ ∧ iform γ yAlphaAS = 1 ∧ iform γ yBetaAS = -1}

@[expose] def yPartnerAS (δ : Fin Tag.E6.rank → ℤ) : Fin Tag.E6.rank → ℤ := δ - yAlphaAS + yBetaAS

@[expose] def yStep (j : ℕ) (v : Fin Tag.E6.rank → ℤ) : Fin Tag.E6.rank → ℤ :=
  if j = 1 then reflect .E6 1 v else if j = 3 then reflect .E6 3 v
  else reflect .E6 2 (reflect .E6 4 v)

@[expose] def yWord (ω : List ℕ) (v : Fin Tag.E6.rank → ℤ) : Fin Tag.E6.rank → ℤ :=
  ω.foldl (fun v j => yStep j v) v

@[expose] def yFixedTable : List ((Fin Tag.E6.rank → ℤ) × List ℕ) :=
  [(Pi.single 3 1, []), (Pi.single 1 1, []), (Pi.single 1 1, [3]), (Pi.single 3 1, [24]),
    (Pi.single 1 1, [3, 24]), (Pi.single 1 1, [3, 24, 3]), (Pi.single 3 1, [3]),
    (Pi.single 1 1, [1]), (Pi.single 1 1, [1, 3]), (Pi.single 3 1, [3, 24]),
    (Pi.single 1 1, [1, 3, 24]), (Pi.single 1 1, [1, 3, 24, 3])]

@[expose] def yPairTable : List (List ℕ) :=
  [[], [3], [24], [3, 1], [24, 3], [24, 3, 1]]

theorem yWordCheck :
    (∀ γ ∈ rootFinset .E6, iform γ yAlphaAS = 0 → iform γ yBetaAS = 0 →
      ∃ p ∈ yFixedTable, yWord p.2 p.1 = γ) ∧
    (∀ p ∈ yFixedTable, (p.1 = Pi.single 1 1 ∨ p.1 = Pi.single 3 1)) ∧
    (∀ γ ∈ rootFinset .E6, iform γ yAlphaAS = 1 → iform γ yBetaAS = -1 →
      ∃ ω ∈ yPairTable, (yWord ω (Pi.single 2 1) = γ ∧ yWord ω (Pi.single 4 1) = yPartnerAS γ) ∨
        (yWord ω (Pi.single 4 1) = γ ∧ yWord ω (Pi.single 2 1) = yPartnerAS γ)) := by
  decide +kernel

theorem yGenCheck :
    (∀ δ ∈ ([Pi.single 1 1, -Pi.single 1 1, Pi.single 3 1, -Pi.single 3 1] :
        List (Fin Tag.E6.rank → ℤ)), iform δ yAlphaAS = 0 ∧ iform δ yBetaAS = 0) ∧
    (iform (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) yAlphaAS = 1 ∧
      iform (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) yBetaAS = -1 ∧
      yPartnerAS (Pi.single 2 1) = Pi.single 4 1) ∧
    (iform (-Pi.single 4 1 : Fin Tag.E6.rank → ℤ) yAlphaAS = 1 ∧
      iform (-Pi.single 4 1 : Fin Tag.E6.rank → ℤ) yBetaAS = -1 ∧
      yPartnerAS (-Pi.single 4 1) = -Pi.single 2 1) ∧
    iform (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) (Pi.single 4 1) = 0 ∧
    e6ASFrame 1 = [yAlphaAS, yBetaAS] := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, rfl⟩

section Gens

variable (K : Type) [Field K]

@[expose] def yLeviF4Gens : Set (ModGL .E6 K) :=
  {g | ∃ j : Fin Tag.F4.rank, j ≠ 3 ∧ ∃ c : K, g = f4OrbitXUnit K j c ∨ g = f4OrbitYUnit K j c}

@[expose] noncomputable def yLeviF4 : Subgroup (ModGL .E6 K) :=
  closure (yLeviF4Gens K)

variable {K}

theorem f4OrbitXUnit_zero (c : K) : f4OrbitXUnit K 0 c = xUnit .E6 K 1 c := by
  have h : TwistTag.E6.orbitWord (f4FoldedIndex 0) = [1] := by decide
  simp only [f4OrbitXUnit, h, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one]
  rfl

theorem f4OrbitXUnit_one (c : K) : f4OrbitXUnit K 1 c = xUnit .E6 K 3 c := by
  have h : TwistTag.E6.orbitWord (f4FoldedIndex 1) = [3] := by decide
  simp only [f4OrbitXUnit, h, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one]
  rfl

theorem f4OrbitXUnit_two (c : K) : f4OrbitXUnit K 2 c = xUnit .E6 K 2 c * xUnit .E6 K 4 c := by
  have h : TwistTag.E6.orbitWord (f4FoldedIndex 2) = [2, 4] := by decide
  simp only [f4OrbitXUnit, h, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one]
  rfl

theorem f4OrbitYUnit_zero (c : K) : f4OrbitYUnit K 0 c = yUnit .E6 K 1 c := by
  have h : TwistTag.E6.orbitWord (f4FoldedIndex 0) = [1] := by decide
  simp only [f4OrbitYUnit, h, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one]
  rfl

theorem f4OrbitYUnit_one (c : K) : f4OrbitYUnit K 1 c = yUnit .E6 K 3 c := by
  have h : TwistTag.E6.orbitWord (f4FoldedIndex 1) = [3] := by decide
  simp only [f4OrbitYUnit, h, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one]
  rfl

theorem f4OrbitYUnit_two (c : K) : f4OrbitYUnit K 2 c = yUnit .E6 K 2 c * yUnit .E6 K 4 c := by
  have h : TwistTag.E6.orbitWord (f4FoldedIndex 2) = [2, 4] := by decide
  simp only [f4OrbitYUnit, h, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one]
  rfl

end Gens

section Words

variable {K : Type} [Field K]


theorem simple_mem_yLeviF4 (c : K) :
    xUnit .E6 K 1 c ∈ yLeviF4 K ∧ yUnit .E6 K 1 c ∈ yLeviF4 K ∧ xUnit .E6 K 3 c ∈ yLeviF4 K ∧
      yUnit .E6 K 3 c ∈ yLeviF4 K ∧ xUnit .E6 K 2 c * xUnit .E6 K 4 c ∈ yLeviF4 K ∧
      yUnit .E6 K 2 c * yUnit .E6 K 4 c ∈ yLeviF4 K := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← f4OrbitXUnit_zero]; exact subset_closure ⟨0, by decide, c, Or.inl rfl⟩
  · rw [← f4OrbitYUnit_zero]; exact subset_closure ⟨0, by decide, c, Or.inr rfl⟩
  · rw [← f4OrbitXUnit_one]; exact subset_closure ⟨1, by decide, c, Or.inl rfl⟩
  · rw [← f4OrbitYUnit_one]; exact subset_closure ⟨1, by decide, c, Or.inr rfl⟩
  · rw [← f4OrbitXUnit_two]; exact subset_closure ⟨2, by decide, c, Or.inl rfl⟩
  · rw [← f4OrbitYUnit_two]; exact subset_closure ⟨2, by decide, c, Or.inr rfl⟩

theorem weylElt_mem_yLeviF4 {j : Fin Tag.E6.rank} (hj : j = 1 ∨ j = 3) :
    weylElt .E6 K j 1 ∈ yLeviF4 K := by
  rw [CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul]
  rcases hj with rfl | rfl
  · exact mul_mem (mul_mem (simple_mem_yLeviF4 _).1 (simple_mem_yLeviF4 _).2.1)
      (simple_mem_yLeviF4 _).1
  · exact mul_mem (mul_mem (simple_mem_yLeviF4 _).2.2.1 (simple_mem_yLeviF4 _).2.2.2.1)
      (simple_mem_yLeviF4 _).2.2.1

theorem weylElt_two_mul_weylElt_four_mem_yLeviF4 :
    weylElt .E6 K 2 1 * weylElt .E6 K 4 1 ∈ yLeviF4 K := by
  have h0 := yGenCheck.2.2.2.1
  have r2 : IsRoot .E6 (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) := isRoot_single Tag.E6 2
  have r4 : IsRoot .E6 (Pi.single 4 1 : Fin Tag.E6.rank → ℤ) := isRoot_single Tag.E6 4
  have cXX : ∀ a b : K, Commute (xUnit .E6 K 2 a) (xUnit .E6 K 4 b) := fun a b => by
    rw [← pinnedX_single, ← pinnedX_single]
    exact classD4_commute_pinnedX e6_simplyLaced r2 r4 h0.ge a b
  have cYX : ∀ a b : K, Commute (yUnit .E6 K 2 a) (xUnit .E6 K 4 b) := fun a b => by
    rw [← pinnedX_neg_single, ← pinnedX_single]
    exact classD4_commute_pinnedX e6_simplyLaced (IsRoot.neg r2) r4
      (by rw [iform_neg_left, h0]; norm_num) a b
  have cXY : ∀ a b : K, Commute (xUnit .E6 K 2 a) (yUnit .E6 K 4 b) := fun a b => by
    rw [← pinnedX_single, ← pinnedX_neg_single]
    exact classD4_commute_pinnedX e6_simplyLaced r2 (IsRoot.neg r4)
      (by rw [iform_neg_right, h0]; norm_num) a b
  rw [CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul, CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul,
    Units.val_one]
  set u : K := -((1⁻¹ : Kˣ) : K)
  have e : xUnit .E6 K 2 1 * yUnit .E6 K 2 u * xUnit .E6 K 2 1 *
      (xUnit .E6 K 4 1 * yUnit .E6 K 4 u * xUnit .E6 K 4 1) =
      xUnit .E6 K 2 1 * xUnit .E6 K 4 1 * (yUnit .E6 K 2 u * yUnit .E6 K 4 u) *
        (xUnit .E6 K 2 1 * xUnit .E6 K 4 1) := by
    calc xUnit .E6 K 2 1 * yUnit .E6 K 2 u * xUnit .E6 K 2 1 *
          (xUnit .E6 K 4 1 * yUnit .E6 K 4 u * xUnit .E6 K 4 1)
        = xUnit .E6 K 2 1 * yUnit .E6 K 2 u * (xUnit .E6 K 2 1 * xUnit .E6 K 4 1) *
          (yUnit .E6 K 4 u * xUnit .E6 K 4 1) := by group
      _ = xUnit .E6 K 2 1 * yUnit .E6 K 2 u * (xUnit .E6 K 4 1 * xUnit .E6 K 2 1) *
          (yUnit .E6 K 4 u * xUnit .E6 K 4 1) := by rw [(cXX 1 1).eq]
      _ = xUnit .E6 K 2 1 * (yUnit .E6 K 2 u * xUnit .E6 K 4 1) *
          (xUnit .E6 K 2 1 * yUnit .E6 K 4 u) * xUnit .E6 K 4 1 := by group
      _ = xUnit .E6 K 2 1 * (xUnit .E6 K 4 1 * yUnit .E6 K 2 u) *
          (yUnit .E6 K 4 u * xUnit .E6 K 2 1) * xUnit .E6 K 4 1 := by
          rw [(cYX u 1).eq, (cXY 1 u).eq]
      _ = _ := by group
  rw [e]
  exact mul_mem (mul_mem (simple_mem_yLeviF4 _).2.2.2.2.1 (simple_mem_yLeviF4 _).2.2.2.2.2)
    (simple_mem_yLeviF4 _).2.2.2.2.1

theorem weylElt_conj_pinnedX_charTwo [CharP K 2] (i : Fin Tag.E6.rank)
    {δ : Fin Tag.E6.rank → ℤ} (hδ : IsRoot .E6 δ) (c : K) :
    weylElt .E6 K i 1 * pinnedX .E6 K δ c * (weylElt .E6 K i 1)⁻¹ =
      pinnedX .E6 K (reflect .E6 i δ) c := by
  obtain ⟨ε, hε, h⟩ := weylElt_mul_pinnedX_mul_inv K i hδ
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hε1 : ε = 1 := by
    have hsq : (ε - 1) ^ 2 = 0 := by linear_combination hε - (ε - 1) * h2
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hsq)
  rw [h, hε1, one_mul]

theorem pinnedX_yStep_mem [CharP K 2] (j : ℕ) {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot .E6 γ)
    (h : ∀ c : K, pinnedX .E6 K γ c ∈ yLeviF4 K) (c : K) :
    pinnedX .E6 K (yStep j γ) c ∈ yLeviF4 K := by
  unfold yStep
  split_ifs with h1 h3
  · rw [← weylElt_conj_pinnedX_charTwo 1 hγ c]
    exact mul_mem (mul_mem (weylElt_mem_yLeviF4 (Or.inl rfl)) (h c))
      (inv_mem (weylElt_mem_yLeviF4 (Or.inl rfl)))
  · rw [← weylElt_conj_pinnedX_charTwo 3 hγ c]
    exact mul_mem (mul_mem (weylElt_mem_yLeviF4 (Or.inr rfl)) (h c))
      (inv_mem (weylElt_mem_yLeviF4 (Or.inr rfl)))
  · rw [← weylElt_conj_pinnedX_charTwo 2 (IsRoot.reflect 4 hγ) c,
      ← weylElt_conj_pinnedX_charTwo 4 hγ c]
    have e : weylElt .E6 K 2 1 * (weylElt .E6 K 4 1 * pinnedX .E6 K γ c * (weylElt .E6 K 4 1)⁻¹) *
        (weylElt .E6 K 2 1)⁻¹ = (weylElt .E6 K 2 1 * weylElt .E6 K 4 1) * pinnedX .E6 K γ c *
          (weylElt .E6 K 2 1 * weylElt .E6 K 4 1)⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem weylElt_two_mul_weylElt_four_mem_yLeviF4 (h c))
      (inv_mem weylElt_two_mul_weylElt_four_mem_yLeviF4)

theorem isRoot_yStep (j : ℕ) {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot .E6 γ) :
    IsRoot .E6 (yStep j γ) := by
  unfold yStep
  split_ifs
  · exact IsRoot.reflect 1 hγ
  · exact IsRoot.reflect 3 hγ
  · exact IsRoot.reflect 2 (IsRoot.reflect 4 hγ)

theorem pinnedX_yWord_mem [CharP K 2] (ω : List ℕ) :
    ∀ {γ : Fin Tag.E6.rank → ℤ}, IsRoot .E6 γ → (∀ c : K, pinnedX .E6 K γ c ∈ yLeviF4 K) →
      ∀ c : K, pinnedX .E6 K (yWord ω γ) c ∈ yLeviF4 K := by
  induction ω with
  | nil => intro γ _ h c; exact h c
  | cons j ω ih =>
    intro γ hγ h c
    exact ih (isRoot_yStep j hγ) (pinnedX_yStep_mem j hγ h) c

theorem pinnedX_mul_pinnedX_yWord_mem [CharP K 2] (ω : List ℕ) :
    ∀ {γ γ' : Fin Tag.E6.rank → ℤ}, IsRoot .E6 γ → IsRoot .E6 γ' →
      (∀ c : K, pinnedX .E6 K γ c * pinnedX .E6 K γ' c ∈ yLeviF4 K) →
      ∀ c : K, pinnedX .E6 K (yWord ω γ) c * pinnedX .E6 K (yWord ω γ') c ∈ yLeviF4 K := by
  induction ω with
  | nil => intro γ γ' _ _ h c; exact h c
  | cons j ω ih =>
    intro γ γ' hγ hγ' h c
    refine ih (isRoot_yStep j hγ) (isRoot_yStep j hγ') (fun c => ?_) c
    have key : ∀ n : ModGL .E6 K, n ∈ yLeviF4 K → ∀ a a' : Fin Tag.E6.rank → ℤ,
        (∀ d : K, n * pinnedX .E6 K γ d * n⁻¹ = pinnedX .E6 K a d) →
        (∀ d : K, n * pinnedX .E6 K γ' d * n⁻¹ = pinnedX .E6 K a' d) →
        pinnedX .E6 K a c * pinnedX .E6 K a' c ∈ yLeviF4 K := by
      intro n hn a a' e e'
      rw [← e c, ← e' c]
      have : n * pinnedX .E6 K γ c * n⁻¹ * (n * pinnedX .E6 K γ' c * n⁻¹) =
          n * (pinnedX .E6 K γ c * pinnedX .E6 K γ' c) * n⁻¹ := by group
      rw [this]
      exact mul_mem (mul_mem hn (h c)) (inv_mem hn)
    unfold yStep
    split_ifs with h1 h3
    · exact key _ (weylElt_mem_yLeviF4 (Or.inl rfl)) _ _ (weylElt_conj_pinnedX_charTwo 1 hγ)
        (weylElt_conj_pinnedX_charTwo 1 hγ')
    · exact key _ (weylElt_mem_yLeviF4 (Or.inr rfl)) _ _ (weylElt_conj_pinnedX_charTwo 3 hγ)
        (weylElt_conj_pinnedX_charTwo 3 hγ')
    · refine key _ weylElt_two_mul_weylElt_four_mem_yLeviF4 _ _ (fun d => ?_) (fun d => ?_)
      · rw [← weylElt_conj_pinnedX_charTwo 2 (IsRoot.reflect 4 hγ) d,
          ← weylElt_conj_pinnedX_charTwo 4 hγ d]
        group
      · rw [← weylElt_conj_pinnedX_charTwo 2 (IsRoot.reflect 4 hγ') d,
          ← weylElt_conj_pinnedX_charTwo 4 hγ' d]
        group

theorem pinnedX_mem_yLeviF4_of_mem_yFixedRootsAS [CharP K 2] {γ : Fin Tag.E6.rank → ℤ}
    (hγ : γ ∈ yFixedRootsAS) (c : K) : pinnedX .E6 K γ c ∈ yLeviF4 K := by
  obtain ⟨p, hp, hpγ⟩ := yWordCheck.1 γ (mem_rootFinset.2 hγ.1) hγ.2.1 hγ.2.2
  rw [← hpγ]
  rcases yWordCheck.2.1 p hp with h | h
  · rw [h]
    exact pinnedX_yWord_mem p.2 (isRoot_single _ _) (fun d => by
      rw [pinnedX_single]; exact (simple_mem_yLeviF4 d).1) c
  · rw [h]
    exact pinnedX_yWord_mem p.2 (isRoot_single _ _) (fun d => by
      rw [pinnedX_single]; exact (simple_mem_yLeviF4 d).2.2.1) c

theorem pinnedX_mul_pinnedX_mem_yLeviF4_of_mem_yPairRootsAS [CharP K 2]
    {δ : Fin Tag.E6.rank → ℤ} (hδ : δ ∈ yPairRootsAS) (c : K) :
    pinnedX .E6 K δ c * pinnedX .E6 K (yPartnerAS δ) c ∈ yLeviF4 K := by
  obtain ⟨ω, -, hω⟩ := yWordCheck.2.2 δ (mem_rootFinset.2 hδ.1) hδ.2.1 hδ.2.2
  have base : ∀ d : K, pinnedX .E6 K (Pi.single 2 1) d * pinnedX .E6 K (Pi.single 4 1) d ∈
      yLeviF4 K := fun d => by
    rw [pinnedX_single, pinnedX_single]; exact (simple_mem_yLeviF4 d).2.2.2.2.1
  have hw := pinnedX_mul_pinnedX_yWord_mem ω (isRoot_single _ _) (isRoot_single _ _) base c
  rcases hω with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rwa [h1, h2] at hw
  · rw [h1, h2] at hw
    have hp : IsRoot .E6 (yPartnerAS δ) := by rw [← h2]; exact isRoot_yWord ω (isRoot_single _ _)
    have h0 : iform (yPartnerAS δ) δ = 0 := by
      have e : yPartnerAS δ = δ - yAlphaAS + yBetaAS := rfl
      rw [e, iform_add_left, iform_sub_left, EPilot.iform_self_eq_two (Or.inl rfl) hδ.1,
        iform_comm yAlphaAS, iform_comm yBetaAS, hδ.2.1, hδ.2.2]
      norm_num
    rwa [(classD4_commute_pinnedX e6_simplyLaced hp hδ.1 h0.ge c c).eq] at hw
where
  isRoot_yWord : ∀ (ω : List ℕ) {γ : Fin Tag.E6.rank → ℤ}, IsRoot .E6 γ → IsRoot .E6 (yWord ω γ)
    | [], _, hγ => hγ
    | j :: ω, _, hγ => isRoot_yWord ω (isRoot_yStep j hγ)

end Words

section Transport


theorem e6RepWeyl_smul_yAlphaAS_yBetaAS :
    e6RepWeyl 1 • yAlphaAS = yA1 ∧ e6RepWeyl 1 • yBetaAS = yA4 := by
  have h := e6RepWeyl_smul_e6ASFrame 1
  rw [yGenCheck.2.2.2.2] at h
  simp only [List.map_cons, List.map_nil] at h
  exact ⟨(List.cons.inj h).1, (List.cons.inj (List.cons.inj h).2).1⟩

theorem iform_e6RepWeyl_smul (γ : Fin Tag.E6.rank → ℤ) :
    iform (e6RepWeyl 1 • γ) yA1 = iform γ yAlphaAS ∧
      iform (e6RepWeyl 1 • γ) yA4 = iform γ yBetaAS := by
  rw [← e6RepWeyl_smul_yAlphaAS_yBetaAS.1, ← e6RepWeyl_smul_yAlphaAS_yBetaAS.2, iform_smul,
    iform_smul]
  exact ⟨rfl, rfl⟩

theorem smul_mem_yFixedRoots_iff {γ : Fin Tag.E6.rank → ℤ} :
    e6RepWeyl 1 • γ ∈ yFixedRoots ↔ γ ∈ yFixedRootsAS := by
  obtain ⟨h1, h4⟩ := iform_e6RepWeyl_smul γ
  simp only [yFixedRoots, yFixedRootsAS, Set.mem_ofPred_eq, h1, h4]
  exact and_congr_left fun _ => ⟨fun h => by simpa using IsRoot.smul h (e6RepWeyl 1)⁻¹,
    fun h => IsRoot.smul h _⟩

theorem smul_mem_yPairRoots_iff {γ : Fin Tag.E6.rank → ℤ} :
    e6RepWeyl 1 • γ ∈ yPairRoots ↔ γ ∈ yPairRootsAS := by
  obtain ⟨h1, h4⟩ := iform_e6RepWeyl_smul γ
  simp only [yPairRoots, yPairRootsAS, Set.mem_ofPred_eq, h1, h4]
  exact and_congr_left fun _ => ⟨fun h => by simpa using IsRoot.smul h (e6RepWeyl 1)⁻¹,
    fun h => IsRoot.smul h _⟩

theorem smul_yPartnerAS (δ : Fin Tag.E6.rank → ℤ) :
    e6RepWeyl 1 • yPartnerAS δ = yPartner (e6RepWeyl 1 • δ) := by
  simp only [yPartnerAS, yPartner, smul_add, smul_sub, e6RepWeyl_smul_yAlphaAS_yBetaAS.1,
    e6RepWeyl_smul_yAlphaAS_yBetaAS.2]

variable {K : Type} [Field K]


theorem conj_e6RepConj_pinnedX [CharP K 2] {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot .E6 γ)
    (c : K) :
    MulAut.conj (e6RepConj K 1 : ModGL .E6 K) (pinnedX .E6 K γ c) =
      pinnedX .E6 K (e6RepWeyl 1 • γ) c := by
  rw [MulAut.conj_apply, coe_e6RepConj]
  exact canonicalRep_mul_pinnedX_mul_inv_of_charTwo _ hγ c

theorem yLeviGL_eq_map_yLeviF4 [CharP K 2] :
    yLeviGL K = (yLeviF4 K).map (MulAut.conj (e6RepConj K 1 : ModGL .E6 K)).toMonoidHom := by
  set w := e6RepWeyl 1 with hw
  refine le_antisymm ((closure_le _).2 ?_) (Subgroup.map_le_iff_le_comap.2 ((closure_le _).2 ?_))
  · rintro _ (⟨γ, hγ, c, rfl⟩ | ⟨δ, hδ, c, rfl⟩)
    · have hγ' : w⁻¹ • γ ∈ yFixedRootsAS := smul_mem_yFixedRoots_iff.1 (by
        rw [hw, smul_inv_smul]; exact hγ)
      refine ⟨pinnedX .E6 K (w⁻¹ • γ) c, pinnedX_mem_yLeviF4_of_mem_yFixedRootsAS hγ' c, ?_⟩
      change MulAut.conj (e6RepConj K 1 : ModGL .E6 K) (pinnedX .E6 K (w⁻¹ • γ) c) = _
      rw [conj_e6RepConj_pinnedX hγ'.1, ← hw, smul_inv_smul]
    · have hδ' : w⁻¹ • δ ∈ yPairRootsAS := smul_mem_yPairRoots_iff.1 (by
        rw [hw, smul_inv_smul]; exact hδ)
      have e : w • yPartnerAS (w⁻¹ • δ) = yPartner δ := by
        rw [hw, smul_yPartnerAS, smul_inv_smul]
      have hp : IsRoot .E6 (yPartnerAS (w⁻¹ • δ)) := by
        have := IsRoot.smul (yPartner_spec hδ).1 w⁻¹
        rwa [← e, inv_smul_smul] at this
      refine ⟨pinnedX .E6 K (w⁻¹ • δ) c * pinnedX .E6 K (yPartnerAS (w⁻¹ • δ)) c,
        pinnedX_mul_pinnedX_mem_yLeviF4_of_mem_yPairRootsAS hδ' c, ?_⟩
      change MulAut.conj (e6RepConj K 1 : ModGL .E6 K)
        (pinnedX .E6 K (w⁻¹ • δ) c * pinnedX .E6 K (yPartnerAS (w⁻¹ • δ)) c) = _
      rw [map_mul, conj_e6RepConj_pinnedX hδ'.1, conj_e6RepConj_pinnedX hp, ← hw,
        smul_yPartnerAS, smul_inv_smul]
  · have hfix : ∀ {γ : Fin Tag.E6.rank → ℤ}, γ ∈ yFixedRootsAS → ∀ c : K,
        pinnedX .E6 K γ c ∈ (yLeviGL K).comap
          (MulAut.conj (e6RepConj K 1 : ModGL .E6 K)).toMonoidHom := fun {γ} hγ c => by
      change MulAut.conj (e6RepConj K 1 : ModGL .E6 K) (pinnedX .E6 K γ c) ∈ yLeviGL K
      rw [conj_e6RepConj_pinnedX hγ.1]
      exact subset_closure (Or.inl ⟨_, smul_mem_yFixedRoots_iff.2 hγ, c, rfl⟩)
    have hpair : ∀ {δ : Fin Tag.E6.rank → ℤ}, δ ∈ yPairRootsAS → IsRoot .E6 (yPartnerAS δ) →
        ∀ c : K, pinnedX .E6 K δ c * pinnedX .E6 K (yPartnerAS δ) c ∈ (yLeviGL K).comap
          (MulAut.conj (e6RepConj K 1 : ModGL .E6 K)).toMonoidHom := fun {δ} hδ hp c => by
      change MulAut.conj (e6RepConj K 1 : ModGL .E6 K)
        (pinnedX .E6 K δ c * pinnedX .E6 K (yPartnerAS δ) c) ∈ yLeviGL K
      rw [map_mul, conj_e6RepConj_pinnedX hδ.1, conj_e6RepConj_pinnedX hp, smul_yPartnerAS]
      exact subset_closure (Or.inr ⟨_, smul_mem_yPairRoots_iff.2 hδ, c, rfl⟩)
    obtain ⟨hlong, ⟨h21, h22, h23⟩, ⟨h41, h42, h43⟩, h24, -⟩ := yGenCheck
    have r1 : IsRoot .E6 (Pi.single 1 1 : Fin Tag.E6.rank → ℤ) := isRoot_single Tag.E6 1
    have r3 : IsRoot .E6 (Pi.single 3 1 : Fin Tag.E6.rank → ℤ) := isRoot_single Tag.E6 3
    have r2 : IsRoot .E6 (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) := isRoot_single Tag.E6 2
    have r4 : IsRoot .E6 (Pi.single 4 1 : Fin Tag.E6.rank → ℤ) := isRoot_single Tag.E6 4
    have f1 : (Pi.single 1 1 : Fin Tag.E6.rank → ℤ) ∈ yFixedRootsAS :=
      ⟨r1, hlong _ (by simp)⟩
    have f1' : (-Pi.single 1 1 : Fin Tag.E6.rank → ℤ) ∈ yFixedRootsAS :=
      ⟨IsRoot.neg r1, hlong _ (by simp)⟩
    have f3 : (Pi.single 3 1 : Fin Tag.E6.rank → ℤ) ∈ yFixedRootsAS :=
      ⟨r3, hlong _ (by simp)⟩
    have f3' : (-Pi.single 3 1 : Fin Tag.E6.rank → ℤ) ∈ yFixedRootsAS :=
      ⟨IsRoot.neg r3, hlong _ (by simp)⟩
    rintro _ ⟨j, hj, c, rfl | rfl⟩
    · obtain rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 := by revert hj; revert j; decide
      · rw [f4OrbitXUnit_zero, ← pinnedX_single]; exact hfix f1 c
      · rw [f4OrbitXUnit_one, ← pinnedX_single]; exact hfix f3 c
      · rw [f4OrbitXUnit_two, ← pinnedX_single, ← pinnedX_single, ← h23]
        exact hpair ⟨r2, h21, h22⟩ (by rw [h23]; exact r4) c
    · obtain rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 := by revert hj; revert j; decide
      · rw [f4OrbitYUnit_zero, ← pinnedX_neg_single]; exact hfix f1' c
      · rw [f4OrbitYUnit_one, ← pinnedX_neg_single]; exact hfix f3' c
      · rw [f4OrbitYUnit_two, ← pinnedX_neg_single, ← pinnedX_neg_single]
        have hc : Commute (pinnedX .E6 K (-Pi.single 2 1) c) (pinnedX .E6 K (-Pi.single 4 1) c) :=
          classD4_commute_pinnedX e6_simplyLaced (IsRoot.neg r2) (IsRoot.neg r4)
            (by rw [iform_neg_left, iform_neg_right, neg_neg, h24]) c c
        rw [hc.eq, ← h43]
        exact hpair ⟨IsRoot.neg r4, h41, h42⟩ (by rw [h43]; exact IsRoot.neg r2) c

end Transport

end CFSG.SeitzReduction.E6Pilot
