module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInnerLine
public import CFSG.LieType.Chevalley.CLSOddE7RationalEightGroup

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

set_option linter.unusedSectionVars false

local instance e6CompTorusNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

theorem commutator_mem_of_mem_closure_normalizer {G : Type*} [Group G] {L : Subgroup G} {n : G}
    {s : Set G} (hs : Subgroup.closure s ≤ Subgroup.normalizer (L : Set G))
    (hgen : ∀ x ∈ s, n * x * n⁻¹ * x⁻¹ ∈ L) {d : G} (hd : d ∈ Subgroup.closure s) :
    n * d * n⁻¹ * d⁻¹ ∈ L := by
  induction hd using Subgroup.closure_induction with
  | mem x hx => exact hgen x hx
  | one =>
    have e : n * 1 * n⁻¹ * (1 : G)⁻¹ = 1 := by group
    rw [e]
    exact one_mem L
  | mul x y hx hy ihx ihy =>
    have e : n * (x * y) * n⁻¹ * (x * y)⁻¹ =
        n * x * n⁻¹ * x⁻¹ * (x * (n * y * n⁻¹ * y⁻¹) * x⁻¹) := by group
    rw [e]
    exact mul_mem ihx ((Subgroup.mem_normalizer_iff.1 (hs hx) _).1 ihy)
  | inv x hx ihx =>
    have e : n * x⁻¹ * n⁻¹ * x⁻¹⁻¹ = x⁻¹ * (n * x * n⁻¹ * x⁻¹)⁻¹ * x⁻¹⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.1 (inv_mem (hs hx)) _).1 (inv_mem ihx)

theorem single_mem_e6LineRoots_of_ne : ∀ k : Fin Tag.E6.rank, k ≠ 3 →
    ∃ i, (Pi.single k 1 : Fin Tag.E6.rank → ℤ) ∈ e6LineRoots i ∧
      (-Pi.single k 1 : Fin Tag.E6.rank → ℤ) ∈ e6LineRoots i := by
  decide +kernel

theorem rootChar_zpow_fun {K : Type} [Field K] (t : Kˣ) (m v : Fin Tag.E6.rank → ℤ) :
    rootChar (fun k => t ^ m k) v = t ^ ∑ k, m k * v k := by
  simp only [rootChar, ← zpow_mul, CFSG.LieType.Chevalley.prod_zpow_eq_zpow_sum]

section Torus

variable {K : Type} [Field K]

theorem torusElt_mem_rootSpan_e6 {S : Set (Fin Tag.E6.rank → ℤ)} {k : Fin Tag.E6.rank}
    (h1 : (Pi.single k 1 : Fin Tag.E6.rank → ℤ) ∈ S)
    (h2 : (-Pi.single k 1 : Fin Tag.E6.rank → ℤ) ∈ S) (t : Kˣ) :
    torusElt .E6 K k t ∈ rootSpan .E6 K S := by
  have hx : ∀ c, xUnit .E6 K k c ∈ rootSpan .E6 K S := fun c => by
    rw [← pinnedX_single]
    exact pinnedX_mem_rootSpan h1 c
  have hy : ∀ c, yUnit .E6 K k c ∈ rootSpan .E6 K S := fun c => by
    rw [← pinnedX_neg_single]
    exact pinnedX_mem_rootSpan h2 c
  have hw : ∀ s : Kˣ, weylElt .E6 K k s ∈ rootSpan .E6 K S := fun s => by
    rw [weylElt_eq_xUnit_mul]
    exact mul_mem (mul_mem (hx _) (hy _)) (hx _)
  exact mul_mem (hw t) (hw (-1))

theorem torusElt_mul_torusElt_e6 (a b : Fin Tag.E6.rank) (t : Kˣ) :
    torusElt .E6 K a t * torusElt .E6 K b t =
      rootDiagUnit .E6 (fun j => t ^ (Tag.E6.cartan a j + Tag.E6.cartan b j)) := by
  rw [torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit, ← rootDiagUnit_mul]
  congr 1
  funext j
  simp only [Pi.mul_apply, zpow_add]

theorem canonicalRep_e6LineWeyl_conj_torusElt (t : Kˣ) :
    canonicalRep (coxeterSystem .E6) K e6LineWeyl * (torusElt .E6 K 3 t * torusElt .E6 K 4 t) *
        (canonicalRep (coxeterSystem .E6) K e6LineWeyl)⁻¹ =
      torusElt .E6 K 2 t * torusElt .E6 K 3 t := by
  have key : ∀ j : Fin Tag.E6.rank, ∑ k, (Tag.E6.cartan 3 k + Tag.E6.cartan 4 k) *
      e6WordAct e6LineWord (e6WordAct e6LineWord (Pi.single j 1)) k =
        Tag.E6.cartan 2 j + Tag.E6.cartan 3 j := by
    decide +kernel
  have hinv : e6LineWeyl⁻¹ = e6LineWeyl * e6LineWeyl :=
    inv_eq_iff_mul_eq_one.2 (by rw [← pow_three]; exact e6LineWeyl_pow_three)
  rw [torusElt_mul_torusElt_e6, torusElt_mul_torusElt_e6, canonicalRep_conj_rootDiagUnit]
  congr 1
  funext j
  show rootChar (fun k => t ^ (Tag.E6.cartan 3 k + Tag.E6.cartan 4 k))
      (e6LineWeyl⁻¹ • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) =
    t ^ (Tag.E6.cartan 2 j + Tag.E6.cartan 3 j)
  rw [hinv, mul_smul, e6LineWeyl_smul, e6LineWeyl_smul, rootChar_zpow_fun, key j]

end Torus

section Comm

variable
  {K : Type} [Field K]

theorem canonicalRep_e6LineWeyl_commutator_torusElt_mem (k : Fin Tag.E6.rank) (t : Kˣ) :
    canonicalRep (coxeterSystem .E6) K e6LineWeyl * torusElt .E6 K k t *
        (canonicalRep (coxeterSystem .E6) K e6LineWeyl)⁻¹ * (torusElt .E6 K k t)⁻¹ ∈
      rootSpan .E6 K (⋃ i, (e6LineRoots i : Set (Fin Tag.E6.rank → ℤ))) := by
  have hS : ∀ α ∈ ⋃ i, (e6LineRoots i : Set (Fin Tag.E6.rank → ℤ)), IsRoot .E6 α := by
    intro α hα
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hα
    exact isRoot_of_mem_e6LineRoots (Finset.mem_coe.1 hi)
  have hHL := torusGroup_le_normalizer_rootSpan_e6 (K := K) hS
  have hnL := canonicalRep_e6LineWeyl_mem_normalizer (K := K)
  have hL : ∀ k : Fin Tag.E6.rank, k ≠ 3 → ∀ t : Kˣ, torusElt .E6 K k t ∈
      rootSpan .E6 K (⋃ i, (e6LineRoots i : Set (Fin Tag.E6.rank → ℤ))) := by
    intro k hk t
    obtain ⟨i, h1, h2⟩ := single_mem_e6LineRoots_of_ne k hk
    exact torusElt_mem_rootSpan_e6 (Set.mem_iUnion.2 ⟨i, Finset.mem_coe.2 h1⟩)
      (Set.mem_iUnion.2 ⟨i, Finset.mem_coe.2 h2⟩) t
  by_cases hk : k = 3
  · subst hk
    have h4L := hL 4 (by decide) t
    have e : canonicalRep (coxeterSystem .E6) K e6LineWeyl * torusElt .E6 K 3 t *
          (canonicalRep (coxeterSystem .E6) K e6LineWeyl)⁻¹ * (torusElt .E6 K 3 t)⁻¹ =
        torusElt .E6 K 2 t * (torusElt .E6 K 3 t *
          (canonicalRep (coxeterSystem .E6) K e6LineWeyl * torusElt .E6 K 4 t *
            (canonicalRep (coxeterSystem .E6) K e6LineWeyl)⁻¹)⁻¹ * (torusElt .E6 K 3 t)⁻¹) := by
      calc canonicalRep (coxeterSystem .E6) K e6LineWeyl * torusElt .E6 K 3 t *
            (canonicalRep (coxeterSystem .E6) K e6LineWeyl)⁻¹ * (torusElt .E6 K 3 t)⁻¹ =
          canonicalRep (coxeterSystem .E6) K e6LineWeyl *
              (torusElt .E6 K 3 t * torusElt .E6 K 4 t) *
              (canonicalRep (coxeterSystem .E6) K e6LineWeyl)⁻¹ *
            (canonicalRep (coxeterSystem .E6) K e6LineWeyl * torusElt .E6 K 4 t *
              (canonicalRep (coxeterSystem .E6) K e6LineWeyl)⁻¹)⁻¹ *
            (torusElt .E6 K 3 t)⁻¹ := by group
        _ = torusElt .E6 K 2 t * torusElt .E6 K 3 t *
            (canonicalRep (coxeterSystem .E6) K e6LineWeyl * torusElt .E6 K 4 t *
              (canonicalRep (coxeterSystem .E6) K e6LineWeyl)⁻¹)⁻¹ *
            (torusElt .E6 K 3 t)⁻¹ := by rw [canonicalRep_e6LineWeyl_conj_torusElt]
        _ = _ := by group
    rw [e]
    refine mul_mem (hL 2 (by decide) t) ((Subgroup.mem_normalizer_iff.1
      (hHL (torusElt_mem_torusGroup 3 t)) _).1 (inv_mem ?_))
    exact (Subgroup.mem_normalizer_iff.1 hnL _).1 h4L
  · have hx := hL k hk t
    exact mul_mem ((Subgroup.mem_normalizer_iff.1 hnL _).1 hx) (inv_mem hx)

theorem canonicalRep_e6LineWeyl_commutator_mem {d : ModGL Tag.E6 K}
    (hd : d ∈ torusGroup .E6 K) :
    canonicalRep (coxeterSystem .E6) K e6LineWeyl * d *
        (canonicalRep (coxeterSystem .E6) K e6LineWeyl)⁻¹ * d⁻¹ ∈
      rootSpan .E6 K (⋃ i, (e6LineRoots i : Set (Fin Tag.E6.rank → ℤ))) := by
  have hS : ∀ α ∈ ⋃ i, (e6LineRoots i : Set (Fin Tag.E6.rank → ℤ)), IsRoot .E6 α := by
    intro α hα
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hα
    exact isRoot_of_mem_e6LineRoots (Finset.mem_coe.1 hi)
  refine commutator_mem_of_mem_closure_normalizer
    (torusGroup_le_normalizer_rootSpan_e6 (K := K) hS) ?_ hd
  rintro _ ⟨⟨k, t⟩, rfl⟩
  exact canonicalRep_e6LineWeyl_commutator_torusElt_mem k t

end Comm

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
