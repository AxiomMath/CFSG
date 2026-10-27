module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrL18Def
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrJSec
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrJAct
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrImg
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrVocC

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma mem_jSub_iff_mem_of_mem_A (s : Setting3 G L) [Group.IsPerfect ↥L]
    (hZ : Odd (Nat.card ↥(center ↥L))) {W : Subgroup G} (hWA : W ≤ s.fr.A) {x : G}
    (hxA : x ∈ s.fr.A) {α : MulAut (L ⧸ center L)} (hxα : ActsAs L x α) :
    α ∈ jSub L W ↔ x ∈ W := by
  have hxS : x ∈ s.fr.S := s3_A_le_S s hxA
  have hWL : W ≤ L := hWA.trans ((s3_A_le_S s).trans (s3_S_le_L s))
  have hW2 : IsPGroup 2 ↥W := s3_isPGroup_of_le s (hWA.trans (s3_A_le_S s))
  exact mem_jSub_iff_mem hZ hWL hW2 (s3_S_le_L s hxS) (s3_isPGroup_zpowers s hxS) hxα

private lemma jSub_normIn_A (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (s : Setting3 G L) :
    jSub L (normIn L s.fr.A) = normIn (innerAut (L ⧸ center L)) s.fr'.A := by
  haveI := isPerfect_of_hrSetting hS
  have hAL : s.fr.A ≤ L := (s3_A_le_S s).trans (s3_S_le_L s)
  have hA2 : IsPGroup 2 ↥s.fr.A := s3_isPGroup_of_le s (s3_A_le_S s)
  rw [jSub_normIn hZ hAL hA2, jSub_self L, s3_jSub_A s]

theorem lf18_2a_of (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (s : Setting3 G L) : LF18_2a s := by
  haveI := isPerfect_of_hrSetting hS
  obtain ⟨-, -, -, -, -, -, -, h18, -, -⟩ := s.facts
  have hAL : s.fr.A ≤ L := (s3_A_le_S s).trans (s3_S_le_L s)
  have hzL : s.fr.z ∈ L := s3_S_le_L s (s3_z_mem_S s)
  have hz2 : IsPGroup 2 ↥(zpowers s.fr.z) := s3_isPGroup_zpowers s (s3_z_mem_S s)
  have hzα : ActsAs L s.fr.z s.fr'.z := (s3_actsAs_gens s).2.2.2.2.2
  show normIn L s.fr.A = centEl L s.fr.z
  refine jSub_inj (show normIn L s.fr.A ≤ L from inf_le_left)
    (show centEl L s.fr.z ≤ L from inf_le_left) (zL_le_normIn hAL) (zL_le_centEl hzL) ?_
  rw [jSub_normIn hZ hAL (s3_isPGroup_of_le s (s3_A_le_S s)),
    jSub_centEl hZ hzL hz2 hzα, jSub_self L, s3_jSub_A s]
  exact h18.2.1.1

theorem lf18_2b_of (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (s : Setting3 G L) : LF18_2b s := by
  haveI := isPerfect_of_hrSetting hS
  obtain ⟨-, -, -, -, -, -, -, h18, -, -⟩ := s.facts
  have hAL : s.fr.A ≤ L := (s3_A_le_S s).trans (s3_S_le_L s)
  have hAN : s.fr.A ≤ normIn L s.fr.A := le_inf hAL Subgroup.le_normalizer
  have hV : normIn L s.fr.A ≤ normalizer (L : Set G) := inf_le_left.trans Subgroup.le_normalizer
  have hNV : zL L ⊔ s.fr.A ≤ normIn L s.fr.A := sup_le (zL_le_normIn hAL) hAN
  have hK : ∀ x ∈ normIn L s.fr.A, x ∈ centralizer (L : Set G) → x ∈ zL L ⊔ s.fr.A := by
    intro x hx hxC
    exact Subgroup.mem_sup_left (mem_zL_iff.mpr ⟨(Subgroup.mem_inf.mp hx).1, hxC⟩)
  change SecProp (normIn L s.fr.A) (zL L ⊔ s.fr.A)
    (fun Y _ _ _ => IsFrobeniusOfOrder 18 Y)
  rw [secProp_jSub hV hNV hK (Q := fun Y _ => IsFrobeniusOfOrder 18 Y)
    (fun Y Y' _ _ e => isFrobeniusOfOrder_equiv e 18)]
  rw [jSub_normIn_A hS hZ s, jSub_sup_zL hAL, s3_jSub_A s]
  exact h18.2.1.2.1

theorem lf18_2c_of (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (s : Setting3 G L) : LF18_2c s := by
  haveI := isPerfect_of_hrSetting hS
  obtain ⟨-, -, -, -, -, -, -, h18, -, -⟩ := s.facts
  have hAL : s.fr.A ≤ L := (s3_A_le_S s).trans (s3_S_le_L s)
  have hA2 : IsPGroup 2 ↥s.fr.A := s3_isPGroup_of_le s (s3_A_le_S s)
  have hV : normIn L s.fr.A ≤ normalizer (L : Set G) := inf_le_left.trans Subgroup.le_normalizer
  intro T hT
  have hT' : IsSylowIn 3 (normIn (innerAut (L ⧸ center L)) s.fr'.A) (jSub L T) := by
    have h := isSylowIn_jSub (p := 3) Nat.prime_three (V := normIn L s.fr.A) (T := T) hV hT
    rwa [jSub_normIn_A hS hZ s] at h
  obtain ⟨hO1, hO2, hO3⟩ := h18.2.1.2.2 (jSub L T) hT'
  refine ⟨?_, ?_, ?_⟩
  · have hOA : ((closure {s.fr.a₁, s.fr.b₁} : Set G) \ (s.fr.Z : Set G)) ⊆ s.fr.A :=
      Set.diff_subset.trans (s3_K1_le_A s)
    refine isOrbitMod_of_jSub hZ (A := s.fr.A) (T := T) (Z := s.fr.Z)
      (O := (closure {s.fr.a₁, s.fr.b₁} : Set G) \ (s.fr.Z : Set G))
      (O' := (closure {s.fr'.a₁, s.fr'.b₁} : Set (MulAut (L ⧸ center L))) \
        (s.fr'.Z : Set (MulAut (L ⧸ center L))))
      hAL hA2 hT.1 (s3_Z_le_A s) hOA ?_ ?_ ?_
    · intro α hα
      rw [Set.mem_diff] at hα
      have hα1 : α ∈ closure {s.fr'.a₁, s.fr'.b₁} := hα.1
      rw [← s3_jSub_K1 hS hZ s] at hα1
      exact jSub_mono L (s3_K1_le_A s) hα1
    · intro w hwA α hwα
      have hK1 : (α ∈ (closure {s.fr'.a₁, s.fr'.b₁} : Set (MulAut (L ⧸ center L)))) ↔
          (w ∈ (closure {s.fr.a₁, s.fr.b₁} : Set G)) := by
        rw [← s3_jSub_K1 hS hZ s]
        exact mem_jSub_iff_mem_of_mem_A s hZ (s3_K1_le_A s) hwA hwα
      have hZ' : (α ∈ (s.fr'.Z : Set (MulAut (L ⧸ center L)))) ↔ (w ∈ (s.fr.Z : Set G)) := by
        rw [← s3_jSub_Z s]
        exact mem_jSub_iff_mem_of_mem_A s hZ (s3_Z_le_A s) hwA hwα
      rw [Set.mem_diff, Set.mem_diff, hK1, hZ']
    · rwa [s3_jSub_Z s]
  · have hOA : ((closure {s.fr.a₂, s.fr.b₂} : Set G) \ (s.fr.Z : Set G)) ⊆ s.fr.A :=
      Set.diff_subset.trans (s3_K2_le_A s)
    refine isOrbitMod_of_jSub hZ (A := s.fr.A) (T := T) (Z := s.fr.Z)
      (O := (closure {s.fr.a₂, s.fr.b₂} : Set G) \ (s.fr.Z : Set G))
      (O' := (closure {s.fr'.a₂, s.fr'.b₂} : Set (MulAut (L ⧸ center L))) \
        (s.fr'.Z : Set (MulAut (L ⧸ center L))))
      hAL hA2 hT.1 (s3_Z_le_A s) hOA ?_ ?_ ?_
    · intro α hα
      rw [Set.mem_diff] at hα
      have hα1 : α ∈ closure {s.fr'.a₂, s.fr'.b₂} := hα.1
      rw [← s3_jSub_K2 hS hZ s] at hα1
      exact jSub_mono L (s3_K2_le_A s) hα1
    · intro w hwA α hwα
      have hK2 : (α ∈ (closure {s.fr'.a₂, s.fr'.b₂} : Set (MulAut (L ⧸ center L)))) ↔
          (w ∈ (closure {s.fr.a₂, s.fr.b₂} : Set G)) := by
        rw [← s3_jSub_K2 hS hZ s]
        exact mem_jSub_iff_mem_of_mem_A s hZ (s3_K2_le_A s) hwA hwα
      have hZ' : (α ∈ (s.fr'.Z : Set (MulAut (L ⧸ center L)))) ↔ (w ∈ (s.fr.Z : Set G)) := by
        rw [← s3_jSub_Z s]
        exact mem_jSub_iff_mem_of_mem_A s hZ (s3_Z_le_A s) hwA hwα
      rw [Set.mem_diff, Set.mem_diff, hK2, hZ']
    · rwa [s3_jSub_Z s]
  · have hOA : ((s.fr.A : Set G) \ ((closure {s.fr.a₁, s.fr.b₁} : Set G) ∪
        (closure {s.fr.a₂, s.fr.b₂} : Set G))) ⊆ s.fr.A := Set.diff_subset
    refine isOrbitMod_of_jSub hZ (A := s.fr.A) (T := T) (Z := s.fr.Z)
      (O := (s.fr.A : Set G) \ ((closure {s.fr.a₁, s.fr.b₁} : Set G) ∪
        (closure {s.fr.a₂, s.fr.b₂} : Set G)))
      (O' := (s.fr'.A : Set (MulAut (L ⧸ center L))) \
        ((closure {s.fr'.a₁, s.fr'.b₁} : Set (MulAut (L ⧸ center L))) ∪
         (closure {s.fr'.a₂, s.fr'.b₂} : Set (MulAut (L ⧸ center L)))))
      hAL hA2 hT.1 (s3_Z_le_A s) hOA ?_ ?_ ?_
    · intro α hα
      rw [Set.mem_diff] at hα
      have hα1 : α ∈ s.fr'.A := hα.1
      rwa [← s3_jSub_A s] at hα1
    · intro w hwA α hwα
      have hA' : (α ∈ (s.fr'.A : Set (MulAut (L ⧸ center L)))) ↔ (w ∈ (s.fr.A : Set G)) := by
        rw [← s3_jSub_A s]
        exact mem_jSub_iff_mem_of_mem_A s hZ le_rfl hwA hwα
      have hK1 : (α ∈ (closure {s.fr'.a₁, s.fr'.b₁} : Set (MulAut (L ⧸ center L)))) ↔
          (w ∈ (closure {s.fr.a₁, s.fr.b₁} : Set G)) := by
        rw [← s3_jSub_K1 hS hZ s]
        exact mem_jSub_iff_mem_of_mem_A s hZ (s3_K1_le_A s) hwA hwα
      have hK2 : (α ∈ (closure {s.fr'.a₂, s.fr'.b₂} : Set (MulAut (L ⧸ center L)))) ↔
          (w ∈ (closure {s.fr.a₂, s.fr.b₂} : Set G)) := by
        rw [← s3_jSub_K2 hS hZ s]
        exact mem_jSub_iff_mem_of_mem_A s hZ (s3_K2_le_A s) hwA hwα
      rw [Set.mem_diff, Set.mem_diff, Set.mem_union, Set.mem_union, hA', hK1, hK2]
    · rwa [s3_jSub_Z s]

end CFSG.OddStandard.HigherRank.YamadaG23
