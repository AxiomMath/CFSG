module

public import CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3.LayerRoots
public import CFSG.Blueprint.ChevalleyRootArtifact

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Lang.Triality CFSG.HardMathSupport.Lang.E27Lie

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3


private theorem d4_height_four_check : ∀ l ∈ TwistTag.D4.tag.artifactRoots, 4 ≤ l.sum →
    l = [1, 1, 1, 1] ∨ l = [1, 1, 2, 1] := by
  decide

private theorem isRoot_height_ge_four_iff
    {γ : Fin TwistTag.D4.tag.rank → ℤ} :
    (IsRoot TwistTag.D4.tag γ ∧ 0 < height γ ∧ (4 : ℤ) ≤ height γ) ↔ γ = rootC ∨ γ = rootD := by
  constructor
  · rintro ⟨hγ, -, h4⟩
    have hs : (4 : ℤ) ≤ (List.ofFn γ).sum := by
      rw [List.sum_ofFn]
      exact h4
    rcases d4_height_four_check _ (isRoot_iff_mem_artifactRoots.1 hγ) hs with h | h
    · exact Or.inl (List.ofFn_injective (h.trans rfl))
    · exact Or.inr (List.ofFn_injective (h.trans rfl))
  · rintro (rfl | rfl)
    · exact ⟨isRoot_rootC, by norm_num [height_rootC], by norm_num [height_rootC]⟩
    · exact ⟨isRoot_rootD, by norm_num [height_rootD], by norm_num [height_rootD]⟩

variable {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] [CharP K 3]
  (hK : Nat.card K = (3 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (3 ^ f))
include hf hK hσ

theorem exists_long_form_of_mem_layerN_three (x : layerN σ 3) :
    ∃ r r' : K, σ r = r ∧ σ r' = r' ∧
      (((x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL TwistTag.D4.tag K)) =
        pinnedX TwistTag.D4.tag K rootC r * pinnedX TwistTag.D4.tag K rootD r' := by
  obtain ⟨S, hSdef⟩ : ∃ S : Set (Fin TwistTag.D4.tag.rank → ℤ),
      S = {γ | IsRoot TwistTag.D4.tag γ ∧ 0 < height γ ∧ (4 : ℤ) ≤ height γ} := ⟨_, rfl⟩
  have hmemS : ∀ γ, γ ∈ S ↔ IsRoot TwistTag.D4.tag γ ∧ 0 < height γ ∧ (4 : ℤ) ≤ height γ :=
    fun γ => by rw [hSdef]; rfl
  have hrange : Set.range ![rootC, rootD] = S := by
    ext γ
    rw [hmemS, Set.mem_range, isRoot_height_ge_four_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  have hS : ∀ α ∈ S, IsRoot TwistTag.D4.tag α ∧ 0 < height α := fun α hα =>
    ⟨((hmemS α).1 hα).1, ((hmemS α).1 hα).2.1⟩
  have hclosed : ∀ α ∈ S, ∀ β ∈ S, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      IsRoot TwistTag.D4.tag (a • α + b • β) → a • α + b • β ∈ S := by
    intro α hα β hβ a b ha hb hr
    obtain ⟨-, hαp, hα4⟩ := (hmemS α).1 hα
    obtain ⟨-, hβp, -⟩ := (hmemS β).1 hβ
    have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
    have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
    refine (hmemS _).2 ⟨hr, ?_, ?_⟩ <;> rw [height_nsmul_add_nsmul]
    · nlinarith [mul_nonneg (sub_nonneg.2 ha') hαp.le, mul_nonneg (sub_nonneg.2 hb') hβp.le]
    · nlinarith [mul_nonneg (sub_nonneg.2 ha') hαp.le, mul_nonneg (sub_nonneg.2 hb') hβp.le]
  have hinj : Function.Injective ![rootC, rootD] := by
    intro i j h
    fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)
  have hBij := bijOn_prod_pinnedX (τ := TwistTag.D4.tag) K hS hclosed ![rootC, rootD] hinj hrange
  have hx : ((x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL TwistTag.D4.tag K) ∈
      heightSeries TwistTag.D4.tag K 4 := by
    have h : ((x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL TwistTag.D4.tag K) ∈
        heightSeries TwistTag.D4.tag K ((3 + 1 : ℕ) : ℤ) := (mem_layerN σ).1 x.2
    have e : ((3 + 1 : ℕ) : ℤ) = 4 := by norm_num
    rw [e] at h
    exact h
  have hx2 : ((x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL TwistTag.D4.tag K) ∈
      rootSpan TwistTag.D4.tag K S := by
    rw [hSdef]
    exact hx
  obtain ⟨c, -, hc⟩ := hBij.2.2 hx2
  have hc' : pinnedX TwistTag.D4.tag K rootC (c 0) * pinnedX TwistTag.D4.tag K rootD (c 1) =
      ((x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL TwistTag.D4.tag K) := by
    rw [← hc]
    simp [List.ofFn_succ]
  have hF := ((mem_twistedFixedGroup_iff_twistHom TwistTag.D4 K σ.toRingHom).1
    (graphFixedRootGroup_le TwistTag.D4 K σ.toRingHom
      (x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom).2)).2
  have hρC : permLattice TwistTag.D4.perm rootC = rootC := by decide
  have hρD : permLattice TwistTag.D4.perm rootD = rootD := by decide
  rw [← hc', map_mul, twistHom_pinnedX_of_fixedRoot hf hK σ hσ isRoot_rootC hρC,
    twistHom_pinnedX_of_fixedRoot hf hK σ hσ isRoot_rootD hρD] at hF
  have hσc : (fun i => σ (c i)) = c := by
    refine hBij.2.1 (Set.mem_univ _) (Set.mem_univ _) ?_
    simpa [List.ofFn_succ] using hF
  exact ⟨c 0, c 1, congrFun hσc 0, congrFun hσc 1, hc'.symm⟩

end CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3
