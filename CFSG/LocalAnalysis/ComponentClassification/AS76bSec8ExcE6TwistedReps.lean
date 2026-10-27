module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6CascadeFinal
public import CFSG.LieType.Chevalley.E6EvenRootTorusAutFix
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalModel
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoExceptional.TwistedE6Sec8

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley.E6GraphLevi
  CFSG.LieType.Chevalley.E6GraphHighestRoot CFSG.SeitzReduction
open CFSG.ComponentClassification.RankTwoExceptional.Exc

variable {K : Type} [Field K]

abbrev frT : List (Fin TwistTag.E6.tag.rank → ℤ) := [Pi.single (e6Idx 3) 1]

abbrev frU : List (Fin TwistTag.E6.tag.rank → ℤ) :=
  [Pi.single (e6Idx 0) 1, Pi.single (e6Idx 5) 1]

abbrev frV : List (Fin TwistTag.E6.tag.rank → ℤ) :=
  [Pi.single (e6Idx 0) 1, Pi.single (e6Idx 3) 1, Pi.single (e6Idx 5) 1]

abbrev twFrameProd
    (F : List (Fin TwistTag.E6.tag.rank → ℤ)) : ModGL TwistTag.E6.tag K :=
  (F.map fun γ => pinnedX TwistTag.E6.tag K γ 1).prod

theorem commute_four_six :
    Commute (pinnedX TwistTag.E6.tag K (Pi.single (e6Idx 3) 1) 1)
      (pinnedX TwistTag.E6.tag K (Pi.single (e6Idx 5) 1) 1) :=
  commute_pinnedX_of_not_isRoot (isRoot_single _ _) (isRoot_single _ _) (by decide) (by decide)
    (fun h => by
      obtain ⟨n, hn, e⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).1 h
      revert n
      decide +kernel) 1 1

theorem twFrameProd_mem
    [CharP K 2] (σ : K →+* K) (hσσ : ∀ c, σ (σ c) = c) :
    twFrameProd (K := K) frT ∈ graphFixedRootGroup TwistTag.E6 K σ ∧
      twFrameProd (K := K) frU ∈ graphFixedRootGroup TwistTag.E6 K σ ∧
      twFrameProd (K := K) frV ∈ graphFixedRootGroup TwistTag.E6 K σ := by
  have h4 : pinnedX TwistTag.E6.tag K (Pi.single (e6Idx 3) 1) 1 ∈
      graphFixedRootGroup TwistTag.E6 K σ :=
    pinnedX_mem_graphFixedRootGroup_of_fixed σ (isRoot_single _ _) (by decide) (map_one σ)
  have h16 : pinnedX TwistTag.E6.tag K (Pi.single (e6Idx 0) 1) 1 *
      pinnedX TwistTag.E6.tag K (Pi.single (e6Idx 5) 1) 1 ∈
        graphFixedRootGroup TwistTag.E6 K σ := by
    have h := twistedE6PairX_mem_graphFixedRootGroup hσσ (isRoot_single _ (e6Idx 0)) 1
    rwa [twistedE6PairX, show permLattice TwistTag.E6.perm (Pi.single (e6Idx 0) 1) =
      (Pi.single (e6Idx 5) 1 : Fin TwistTag.E6.tag.rank → ℤ) by decide, map_one] at h
  simp only [twFrameProd, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  refine ⟨h4, h16, ?_⟩
  rw [(commute_four_six (K := K)).eq, ← mul_assoc]
  exact mul_mem h16 h4

@[expose] def twReps
    [CharP K 2] (σ : K →+* K) (hσσ : ∀ c, σ (σ c) = c) :
    List (graphFixedRootGroup TwistTag.E6 K σ) :=
  [⟨_, (twFrameProd_mem σ hσσ).1⟩, ⟨_, (twFrameProd_mem σ hσσ).2.1⟩,
    ⟨_, (twFrameProd_mem σ hσσ).2.2⟩]

theorem twistedE6RelWeyl_conj_twFrameProd
    [CharP K 2]
    (ω : List (Fin TwistTag.E6.foldedTag.rank)) {F : List (Fin TwistTag.E6.tag.rank → ℤ)}
    (hF : ∀ β ∈ F, IsRoot TwistTag.E6.tag β) :
    twistedE6RelWeyl K ω * twFrameProd (K := K) F * (twistedE6RelWeyl K ω)⁻¹ =
      twFrameProd (K := K) (F.map (twistedE6RelAct ω)) := by
  rw [twFrameProd, twistedE6RelWeyl_conj_list_prod ω hF fun _ => (1 : K), twFrameProd,
    List.map_map]
  rfl

abbrev wordT : List (Fin TwistTag.E6.foldedTag.rank) := ([3, 2, 1, 2, 3, 0, 1] : List (Fin 4))

abbrev wordU : List (Fin TwistTag.E6.foldedTag.rank) := ([0, 1, 2, 3, 1, 2, 1] : List (Fin 4))

abbrev wordV : List (Fin TwistTag.E6.foldedTag.rank) :=
  ([2, 1, 2, 0, 1, 2, 3, 2, 0, 1] : List (Fin 4))

theorem frT_map : frT.map (twistedE6RelAct wordT) = [e6HighestRoot] := by decide +kernel

theorem frU_map : frU.map (twistedE6RelAct wordU) =
    [twistedE6ClassRootU', twistedE6ClassRootU] := by decide +kernel

theorem frV_map : frV.map (twistedE6RelAct wordV) =
    [twistedE6ClassRootA', twistedE6ClassRootB, twistedE6ClassRootA] := by decide +kernel

theorem commute_of_not_root
    {α β : Fin TwistTag.E6.tag.rank → ℤ}
    (hα : IsRoot TwistTag.E6.tag α) (hβ : IsRoot TwistTag.E6.tag β) (hne : α ≠ β) (hne' : α ≠ -β)
    (h : ∀ n < TwistTag.E6.tag.rootCertificate.roots.length,
      TwistTag.E6.tag.rootCertificate.root n ≠ α + β) :
    Commute (pinnedX TwistTag.E6.tag K α 1) (pinnedX TwistTag.E6.tag K β 1) :=
  commute_pinnedX_of_not_isRoot hα hβ hne hne' (fun hr => by
    obtain ⟨n, hn, e⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).1 hr
    exact h n hn e) 1 1

theorem conj_frT
    [CharP K 2] :
    twistedE6RelWeyl K wordT * twFrameProd (K := K) frT * (twistedE6RelWeyl K wordT)⁻¹ =
      pinnedX TwistTag.E6.tag K e6HighestRoot 1 := by
  rw [twistedE6RelWeyl_conj_twFrameProd wordT (by simpa using isRoot_single _ _), frT_map]
  simp only [twFrameProd, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]

theorem conj_frU
    [CharP K 2] :
    twistedE6RelWeyl K wordU * twFrameProd (K := K) frU * (twistedE6RelWeyl K wordU)⁻¹ =
      twistedE6ClassU K := by
  rw [twistedE6RelWeyl_conj_twFrameProd wordU (by
    intro β hβ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hβ
    rcases hβ with rfl | rfl <;> exact isRoot_single _ _), frU_map]
  simp only [twFrameProd, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    twistedE6ClassU]
  exact (commute_of_not_root isRoot_twistedE6ClassRoots.2.1 isRoot_twistedE6ClassRoots.1
    (by decide) (by decide) (by decide +kernel)).eq

theorem conj_frV
    [CharP K 2] :
    twistedE6RelWeyl K wordV * twFrameProd (K := K) frV * (twistedE6RelWeyl K wordV)⁻¹ =
      twistedE6ClassV K := by
  rw [twistedE6RelWeyl_conj_twFrameProd wordV (by
    intro β hβ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hβ
    rcases hβ with rfl | rfl | rfl <;> exact isRoot_single _ _), frV_map]
  simp only [twFrameProd, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    twistedE6ClassV]
  have hBA := commute_of_not_root (K := K) isRoot_twistedE6ClassRoots.2.2.2.2
    isRoot_twistedE6ClassRoots.2.2.1 (by decide) (by decide) (by decide +kernel)
  have hA'A := commute_of_not_root (K := K) isRoot_twistedE6ClassRoots.2.2.2.1
    isRoot_twistedE6ClassRoots.2.2.1 (by decide) (by decide) (by decide +kernel)
  rw [hBA.eq, ← mul_assoc, hA'A.eq, mul_assoc]

theorem classesCover_twReps
    [Finite K] [CharP K 2] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (hσσ : ∀ c, σ.toRingHom (σ.toRingHom c) = c) :
    ClassesCover (twReps σ.toRingHom hσσ) := by
  intro x hx2 hx1
  obtain ⟨g, hg⟩ := exists_conj_mem_twistedE6ClassReps_of_frameReduction hf hK hσ
    (twistedE6FrameReduction hf hK hσ) (x := x) (by rw [sq]; exact hx2) hx1
  have hW : ∀ ω, twistedE6RelWeyl K ω ∈ graphFixedRootGroup TwistTag.E6 K σ.toRingHom :=
    fun ω => twistedE6RelWeyl_mem _ ω
  have hgx : IsConj (g * x * g⁻¹) x := isConj_iff.2 ⟨g⁻¹, by group⟩
  have key : ∀ {r : graphFixedRootGroup TwistTag.E6 K σ.toRingHom} (ω),
      twistedE6RelWeyl K ω * (r : ModGL TwistTag.E6.tag K) * (twistedE6RelWeyl K ω)⁻¹ =
        ((g * x * g⁻¹ : graphFixedRootGroup TwistTag.E6 K σ.toRingHom) :
          ModGL TwistTag.E6.tag K) → IsConj r x := fun ω h =>
    (isConj_iff.2 ⟨⟨_, hW ω⟩, Subtype.ext h⟩).trans hgx
  rcases hg with h | h | h
  · exact ⟨_, List.mem_cons_self, key wordT (conj_frT.trans h.symm)⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, key wordU (conj_frU.trans h.symm)⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
      key wordV (conj_frV.trans h.symm)⟩

theorem twFrameProd_ne_one
    {F : List (Fin TwistTag.E6.tag.rank → ℤ)} (hnd : F.Nodup)
    (hF : ∀ α ∈ F, IsRoot TwistTag.E6.tag α ∧ 0 < height α) (hne : F ≠ []) :
    twFrameProd (K := K) F ≠ 1 := by
  intro h
  obtain ⟨α, hα⟩ := List.exists_mem_of_ne_nil F hne
  have := pinnedX_list_prod_injective (R := K) F hnd hF (fun _ => 1) (fun _ => 0) (by
    change twFrameProd (K := K) F = _
    rw [h]
    simp only [pinnedX_zero, List.map_const', List.prod_replicate, one_pow]) α hα
  exact one_ne_zero this

theorem mul_self_eq_one_of_conj {G : Type*} [Group G] {r s : G} (W : G) (h : W * r * W⁻¹ = s)
    (hs : s * s = 1) : r * r = 1 := by
  have e : W * (r * r) * W⁻¹ = 1 := by
    rw [show W * (r * r) * W⁻¹ = W * r * W⁻¹ * (W * r * W⁻¹) by group, h, hs]
  calc r * r = W⁻¹ * (W * (r * r) * W⁻¹) * W := by group
    _ = 1 := by rw [e]; group

theorem involution_twReps
    [CharP K 2] (σ : K →+* K) (hσσ : ∀ c, σ (σ c) = c) :
    ∀ x ∈ twReps σ hσσ, x * x = 1 ∧ x ≠ 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hpos : ∀ j : Fin TwistTag.E6.tag.rank,
      IsRoot TwistTag.E6.tag (Pi.single j 1) ∧
        0 < height (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ) := fun j =>
    ⟨isRoot_single _ _, by rw [height_single]; norm_num⟩
  have hT : ∀ α ∈ frT, IsRoot TwistTag.E6.tag α ∧ 0 < height α := by
    intro α hα
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hα
    subst hα
    exact hpos _
  have hU : ∀ α ∈ frU, IsRoot TwistTag.E6.tag α ∧ 0 < height α := by
    intro α hα
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hα
    rcases hα with rfl | rfl <;> exact hpos _
  have hV : ∀ α ∈ frV, IsRoot TwistTag.E6.tag α ∧ 0 < height α := by
    intro α hα
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hα
    rcases hα with rfl | rfl | rfl <;> exact hpos _
  intro x hx
  simp only [twReps, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · refine ⟨Subtype.ext (mul_self_eq_one_of_conj _ conj_frT
      (E6EvenRootTorus.pinnedX_mul_self h2 _ 1)), fun h => twFrameProd_ne_one (K := K)
        (F := frT) (by decide) hT (by simp) (congrArg Subtype.val h)⟩
  · refine ⟨Subtype.ext (mul_self_eq_one_of_conj _ conj_frU
      (by rw [← sq]; exact twistedE6ClassU_sq)), fun h => twFrameProd_ne_one (K := K)
        (F := frU) (by decide) hU (by simp) (congrArg Subtype.val h)⟩
  · refine ⟨Subtype.ext (mul_self_eq_one_of_conj _ conj_frV
      (by rw [← sq]; exact twistedE6ClassV_sq)), fun h => twFrameProd_ne_one (K := K)
        (F := frV) (by decide) hV (by simp) (congrArg Subtype.val h)⟩

theorem charTwo_twReps
    [Finite K] [CharP K 2] {f : ℕ}
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (hσσ : ∀ c, σ.toRingHom (σ.toRingHom c) = c) :
    ∀ x ∈ twReps σ.toRingHom hσσ, CharTwo x := by
  intro x hx
  obtain ⟨hx2, hx1⟩ := involution_twReps σ.toRingHom hσσ x hx
  exact EvenOddRadical.charTwo_of_involution (.fixed .E6 σ (twistedE6_sigma_pow_order hK hσ))
    (x := x) hx2 hx1

end CFSG.ComponentClassification.RankTwoExceptional.TwistedE6Sec8
