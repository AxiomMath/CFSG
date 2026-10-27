module

public import CFSG.LieType.Chevalley.HeightSeries
public import CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3.D4Comm
public import CFSG.Blueprint.ChevalleyRootArtifact
public import CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3.LayerRoots

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431.FieldPart

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3
  (exists_commutator_pinnedX_of_sum)
open scoped commutatorElement

set_option linter.unusedSectionVars false

@[expose] def v4 (a b c d : ℤ) : Fin Tag.D4.rank → ℤ := ![a, b, c, d]

@[expose] def hrD4 : Fin Tag.D4.rank → ℤ := v4 1 1 2 1

theorem isRoot_of_mem_d4 {v : Fin Tag.D4.rank → ℤ} (h : List.ofFn v ∈ d4ArtifactRoots) :
    IsRoot .D4 v :=
  (d4_root_certificate.1 v).2 h

theorem isRoot_hrD4 : IsRoot .D4 hrD4 := isRoot_of_mem_d4 (by decide)

theorem height_hrD4 : height hrD4 = 5 := by decide

theorem height_le_five_d4 {v : Fin Tag.D4.rank → ℤ} (hv : IsRoot .D4 v) : height v ≤ 5 := by
  have hm := (d4_root_certificate.1 v).1 hv
  have key : ∀ l ∈ d4ArtifactRoots, l.sum ≤ 5 := by decide
  have h := key _ hm
  rw [List.sum_ofFn] at h
  rwa [height]

theorem eq_hrD4_of_five_le_height {v : Fin Tag.D4.rank → ℤ} (hv : IsRoot .D4 v)
    (h5 : 5 ≤ height v) : v = hrD4 := by
  have hm := (d4_root_certificate.1 v).1 hv
  have key : ∀ l ∈ d4ArtifactRoots, 5 ≤ l.sum → l = [1, 1, 2, 1] := by decide
  have h : List.ofFn v = [1, 1, 2, 1] := by
    refine key _ hm ?_
    rw [List.sum_ofFn]
    rwa [height] at h5
  exact List.ofFn_injective (h.trans (by decide : [1, 1, 2, 1] = List.ofFn hrD4))

variable (K : Type) [Field K]

theorem heightSeries_five : heightSeries Tag.D4 K 5 = rootSubgroup Tag.D4 K hrD4 := by
  refine le_antisymm (iSup₂_le fun α hα => ?_) (le_iSup₂_of_le hrD4
    ⟨isRoot_hrD4, by rw [height_hrD4]; norm_num, by rw [height_hrD4]⟩ le_rfl)
  rw [eq_hrD4_of_five_le_height hα.1 hα.2.2]

theorem heightSeries_six : heightSeries Tag.D4 K 6 = ⊥ := by
  refine iSup₂_eq_bot.2 fun α hα => ?_
  exact absurd (height_le_five_d4 hα.1) (by linarith [hα.2.2])

theorem lcs_four_le :
    (posUnipotent Tag.D4 K).lowerCentralSeries 4 ≤ rootSubgroup Tag.D4 K hrD4 := by
  have h := lowerCentralSeries_le_heightSeries (τ := Tag.D4) K (n := 4)
  rw [show ((4 : ℕ) : ℤ) + 1 = 5 by norm_num, heightSeries_five] at h
  exact h

theorem lcs_five_eq_bot : (posUnipotent Tag.D4 K).lowerCentralSeries 5 = ⊥ := by
  have h := lowerCentralSeries_le_heightSeries (τ := Tag.D4) K (n := 5)
  rw [show ((5 : ℕ) : ℤ) + 1 = 6 by norm_num, heightSeries_six] at h
  exact le_bot_iff.1 h

theorem pinnedX_mem_posUnipotent {β : Fin Tag.D4.rank → ℤ} (hβ : IsRoot .D4 β)
    (hpos : 0 < height β) (c : K) : pinnedX Tag.D4 K β c ∈ posUnipotent Tag.D4 K :=
  (le_iSup₂_of_le (f := fun α (_ : α ∈ {α | IsRoot Tag.D4 α ∧ 0 < height α}) =>
    rootSubgroup Tag.D4 K α) β ⟨hβ, hpos⟩ le_rfl : rootSubgroup Tag.D4 K β ≤ _)
    (Subgroup.subset_closure ⟨c, rfl⟩)

theorem pinnedX_mem_lcs_succ {n : ℕ} {α β γ : Fin Tag.D4.rank → ℤ} (hα : IsRoot .D4 α)
    (hβ : IsRoot .D4 β) (hγ : IsRoot .D4 γ) (hne : α ≠ β) (hne' : α ≠ -β) (hsum : α + β = γ)
    (hβpos : 0 < height β)
    (hA : ∀ c : K, pinnedX Tag.D4 K α c ∈ (posUnipotent Tag.D4 K).lowerCentralSeries n) (c : K) :
    pinnedX Tag.D4 K γ c ∈ (posUnipotent Tag.D4 K).lowerCentralSeries (n + 1) := by
  obtain ⟨ε, hε, hcomm⟩ := exists_commutator_pinnedX_of_sum (K := K) hα hβ hne hne' hsum hγ
  have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> ring
  have h1 := Subgroup.commutator_mem_commutator (hA (ε * c)) (pinnedX_mem_posUnipotent K hβ hβpos 1)
  have h2 : ⁅pinnedX Tag.D4 K α (ε * c), pinnedX Tag.D4 K β 1⁆ =
      pinnedX Tag.D4 K γ (ε * (ε * c) * 1) := hcomm (ε * c) 1
  have e : ε * (ε * c) * 1 = c := by rw [mul_one, ← mul_assoc, hεε, one_mul]
  rw [h2, e] at h1
  exact h1

theorem rootSubgroup_hrD4_le_lcs_four :
    rootSubgroup Tag.D4 K hrD4 ≤ (posUnipotent Tag.D4 K).lowerCentralSeries 4 := by
  have r0 : IsRoot .D4 (v4 0 0 1 0) := isRoot_of_mem_d4 (by decide)
  have r1 : IsRoot .D4 (v4 1 0 1 0) := isRoot_of_mem_d4 (by decide)
  have r2 : IsRoot .D4 (v4 1 1 1 0) := isRoot_of_mem_d4 (by decide)
  have r3 : IsRoot .D4 (v4 1 1 1 1) := isRoot_of_mem_d4 (by decide)
  have s0 : IsRoot .D4 (v4 1 0 0 0) := isRoot_of_mem_d4 (by decide)
  have s1 : IsRoot .D4 (v4 0 1 0 0) := isRoot_of_mem_d4 (by decide)
  have s3 : IsRoot .D4 (v4 0 0 0 1) := isRoot_of_mem_d4 (by decide)
  have s2 : IsRoot .D4 (v4 0 0 1 0) := isRoot_of_mem_d4 (by decide)
  have base : ∀ c : K, pinnedX Tag.D4 K (v4 0 0 1 0) c ∈
      (posUnipotent Tag.D4 K).lowerCentralSeries 0 :=
    fun c => pinnedX_mem_posUnipotent K r0 (by decide) c
  have st1 := pinnedX_mem_lcs_succ K r0 s0 r1 (by decide) (by decide) (by decide)
    (by decide) base
  have st2 := pinnedX_mem_lcs_succ K r1 s1 r2 (by decide) (by decide) (by decide)
    (by decide) st1
  have st3 := pinnedX_mem_lcs_succ K r2 s3 r3 (by decide) (by decide) (by decide)
    (by decide) st2
  have st4 := pinnedX_mem_lcs_succ K r3 s2 isRoot_hrD4 (by decide) (by decide) (by decide)
    (by decide) st3
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨c, rfl⟩
  exact st4 c

theorem lcs_four_eq :
    (posUnipotent Tag.D4 K).lowerCentralSeries 4 = rootSubgroup Tag.D4 K hrD4 :=
  le_antisymm (lcs_four_le K) (rootSubgroup_hrD4_le_lcs_four K)

theorem commute_of_mem_rootSubgroup_hrD4 {z u : (Module.End K (RootModule Tag.D4 K))ˣ}
    (hz : z ∈ rootSubgroup Tag.D4 K hrD4) (hu : u ∈ posUnipotent Tag.D4 K) : z * u = u * z := by
  have hz4 : z ∈ (posUnipotent Tag.D4 K).lowerCentralSeries 4 := (lcs_four_eq K).symm ▸ hz
  have h5 : ⁅z, u⁆ ∈ (posUnipotent Tag.D4 K).lowerCentralSeries 5 :=
    Subgroup.commutator_mem_commutator hz4 hu
  rw [lcs_five_eq_bot] at h5
  have h := Subgroup.mem_bot.1 h5
  rw [commutatorElement_eq_one_iff_mul_comm] at h
  exact h

end CFSG.HardMathSupport.Dickson.Sec6.I1431.FieldPart
