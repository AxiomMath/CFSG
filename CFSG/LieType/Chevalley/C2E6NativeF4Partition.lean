module

public import CFSG.LieType.Chevalley.C2E6NativeF4Coxeter
public import CFSG.LieType.Chevalley.C2E6StandardLevi
public import CFSG.LieType.Chevalley.GraphFixedSimpleBruhat

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Std

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.C2E6Overlap
open scoped Pointwise

section Preimage

variable {G : Type*} [Group G] {H : Subgroup G}

theorem preimage_val_mul {S T : Set G} (hS : S ⊆ H) (hT : T ⊆ H) :
    (Subtype.val ⁻¹' (S * T) : Set H) = Subtype.val ⁻¹' S * Subtype.val ⁻¹' T := by
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs, t, ht, hst⟩ := Set.mem_mul.mp hx
    exact Set.mem_mul.mpr ⟨⟨s, hS hs⟩, hs, ⟨t, hT ht⟩, ht, Subtype.ext hst⟩
  · intro hx
    obtain ⟨s, hs, t, ht, rfl⟩ := Set.mem_mul.mp hx
    exact Set.mem_mul.mpr ⟨s, hs, t, ht, rfl⟩

theorem preimage_val_inv (S : Set G) : (Subtype.val ⁻¹' S⁻¹ : Set H) = (Subtype.val ⁻¹' S)⁻¹ :=
  rfl

theorem preimage_val_singleton (g : H) : (Subtype.val ⁻¹' {(g : G)} : Set H) = {g} :=
  Set.ext fun _ => Subtype.ext_iff.symm

end Preimage

@[expose] def stdRepM
    (w : relWeylTwist TwistTag.E6) : ModGL Tag.E6 K :=
  canonicalRep (coxeterSystem TwistTag.E6.tag) K w

@[expose] def stdBruhatCell
    (w : relWeylTwist TwistTag.E6) : Set (ModGL Tag.E6 K) :=
  graphFixedRootBruhatCell TwistTag.E6 K barHom w

theorem stdBruhatCell_eq
    (w : relWeylTwist TwistTag.E6) :
    stdBruhatCell w = (stdBorel : Set (ModGL Tag.E6 K)) * {stdRepM w} * stdBorel :=
  rfl

theorem stdBorel_le_stdGroup
    : stdBorel ≤ stdGroup :=
  graphFixedRootBorel_le TwistTag.E6 K barHom

theorem stdBruhatCell_subset
    (w : relWeylTwist TwistTag.E6) :
    stdBruhatCell w ⊆ (stdGroup : Set (ModGL Tag.E6 K)) := by
  have h := (fixed_simple_Bruhat_multiplication TwistTag.E6 K barEquiv).2.2.2.2.2 w w.2
  rw [barEquiv_toRingHom] at h
  exact h

theorem stdRepM_mem_stdBruhatCell
    (w : relWeylTwist TwistTag.E6) :
    stdRepM w ∈ stdBruhatCell w := by
  rw [stdBruhatCell_eq]
  have h := Set.mul_mem_mul (Set.mul_mem_mul (one_mem stdBorel) (Set.mem_singleton (stdRepM w)))
    (one_mem stdBorel)
  rwa [one_mul, mul_one] at h

theorem stdRepM_mem_stdGroup
    (w : relWeylTwist TwistTag.E6) : stdRepM w ∈ stdGroup :=
  stdBruhatCell_subset w (stdRepM_mem_stdBruhatCell w)

theorem inv_stdBruhatCell
    (w : relWeylTwist TwistTag.E6) :
    (stdBruhatCell w)⁻¹ = stdBruhatCell w⁻¹ := by
  have h := (fixed_simple_Bruhat_multiplication TwistTag.E6 K barEquiv).1 w w.2
  rw [barEquiv_toRingHom] at h
  exact h

theorem stdRepM_one :
    stdRepM 1 = 1 :=
  canonicalRep_one _ _

theorem stdBruhatCell_one :
    stdBruhatCell 1 = stdBorel := by
  rw [stdBruhatCell_eq, stdRepM_one, Set.singleton_one, mul_one, coe_mul_coe]

theorem coe_mul_nativeSimple
    (w : relWeylTwist TwistTag.E6) (i : Fin 4) :
    ((w * nativeSimple i : relWeylTwist TwistTag.E6) : WeylGroup TwistTag.E6.tag) =
      w * TwistTag.E6.orbitReflection (foldedIndex i) :=
  rfl

theorem stdBruhatCell_mul_of_add
    (w : relWeylTwist TwistTag.E6) (i : Fin 4)
    (h : TwistTag.E6.orbitLength (w * TwistTag.E6.orbitReflection (foldedIndex i)) =
      TwistTag.E6.orbitLength w + 1) :
    stdBruhatCell w * stdBruhatCell (nativeSimple i) = stdBruhatCell (w * nativeSimple i) := by
  have hm := (fixed_simple_Bruhat_multiplication TwistTag.E6 K barEquiv).2.2.2.1 w w.2
    (foldedIndex i) h
  rw [barEquiv_toRingHom] at hm
  exact hm

theorem stdBruhatCell_mul_of_sub
    (w : relWeylTwist TwistTag.E6) (i : Fin 4)
    (h : TwistTag.E6.orbitLength (w * TwistTag.E6.orbitReflection (foldedIndex i)) + 1 =
      TwistTag.E6.orbitLength w) :
    stdBruhatCell w * stdBruhatCell (nativeSimple i) =
      stdBruhatCell (w * nativeSimple i) ∪ stdBruhatCell w := by
  have hm := (fixed_simple_Bruhat_multiplication TwistTag.E6 K barEquiv).2.2.2.2.1 w w.2
    (foldedIndex i) h
  rw [barEquiv_toRingHom] at hm
  exact hm

theorem existsUnique_mem_stdBruhatCell
    {g : ModGL Tag.E6 K} (hg : g ∈ stdGroup) :
    ∃! w, g ∈ stdBruhatCell w := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hC, hdisj, -, -, -⟩ :=
    fixed_root_Bruhat_decomposition TwistTag.E6 K barEquiv
  rw [barEquiv_toRingHom] at hC hdisj
  have hg' : g ∈ ⋃ w : relWeylTwist TwistTag.E6, stdBruhatCell w := by
    have e : (stdGroup : Set (ModGL Tag.E6 K)) =
        ⋃ w : relWeylTwist TwistTag.E6, stdBruhatCell w := hC
    rw [← e]
    exact hg
  obtain ⟨w, hw⟩ := Set.mem_iUnion.mp hg'
  refine ⟨w, hw, fun w' hw' => Subtype.ext ?_⟩
  by_contra h
  exact Set.disjoint_left.mp (hdisj _ _ h) hw' hw

abbrev stdBorelG
    : Subgroup stdGroup := stdBorel.subgroupOf stdGroup

@[expose] def stdCell
    (w : relWeylTwist TwistTag.E6) : Set stdGroup :=
  Subtype.val ⁻¹' stdBruhatCell w

theorem mem_stdCell
    {w : relWeylTwist TwistTag.E6} {g : stdGroup} :
    g ∈ stdCell w ↔ (g : ModGL Tag.E6 K) ∈ stdBruhatCell w :=
  Iff.rfl

@[expose] def stdRep
    (w : relWeylTwist TwistTag.E6) : stdGroup :=
  ⟨stdRepM w, stdRepM_mem_stdGroup w⟩

theorem stdCell_eq
    (w : relWeylTwist TwistTag.E6) :
    stdCell w = (stdBorelG : Set stdGroup) * {stdRep w} * stdBorelG := by
  have hB : (stdBorel : Set (ModGL Tag.E6 K)) ⊆ stdGroup := stdBorel_le_stdGroup
  have hn : ({stdRepM w} : Set (ModGL Tag.E6 K)) ⊆ stdGroup :=
    Set.singleton_subset_iff.mpr (stdRepM_mem_stdGroup w)
  have hBn : (stdBorel : Set (ModGL Tag.E6 K)) * {stdRepM w} ⊆ stdGroup := fun x hx => by
    obtain ⟨b, hb, n, hn', rfl⟩ := Set.mem_mul.mp hx
    exact mul_mem (hB hb) (hn hn')
  rw [stdCell, stdBruhatCell_eq, preimage_val_mul hBn hB, preimage_val_mul hB hn,
    Subgroup.coe_subgroupOf]
  exact congrArg (fun S => _ * S * _) (preimage_val_singleton (stdRep w))

theorem existsUnique_mem_stdCell
    (g : stdGroup) : ∃! w, g ∈ stdCell w :=
  existsUnique_mem_stdBruhatCell g.2

theorem stdCell_one :
    stdCell 1 = stdBorelG := by
  rw [stdCell, stdBruhatCell_one]
  rfl

theorem inv_stdCell
    (w : relWeylTwist TwistTag.E6) : (stdCell w)⁻¹ = stdCell w⁻¹ := by
  rw [stdCell, stdCell, ← preimage_val_inv, inv_stdBruhatCell]

theorem stdCell_mul_eq
    (w v : relWeylTwist TwistTag.E6) :
    stdCell w * stdCell v = Subtype.val ⁻¹' (stdBruhatCell w * stdBruhatCell v) :=
  (preimage_val_mul (stdBruhatCell_subset w) (stdBruhatCell_subset v)).symm

theorem stdCell_mul_of_length_add
    (w : relWeylTwist TwistTag.E6) (i : Fin 4)
    (h : nativeCoxeterSystem.length (w * nativeCoxeterSystem.simple i) =
      nativeCoxeterSystem.length w + 1) :
    stdCell w * stdCell (nativeCoxeterSystem.simple i) =
      stdCell (w * nativeCoxeterSystem.simple i) := by
  rw [nativeCoxeterSystem_simple, nativeCoxeterSystem_length, nativeCoxeterSystem_length,
    coe_mul_nativeSimple] at h
  rw [nativeCoxeterSystem_simple, stdCell_mul_eq, stdBruhatCell_mul_of_add w i h, stdCell]

theorem stdCell_mul_of_length_sub
    (w : relWeylTwist TwistTag.E6) (i : Fin 4)
    (h : nativeCoxeterSystem.length (w * nativeCoxeterSystem.simple i) + 1 =
      nativeCoxeterSystem.length w) :
    stdCell w * stdCell (nativeCoxeterSystem.simple i) =
      stdCell (w * nativeCoxeterSystem.simple i) ∪ stdCell w := by
  rw [nativeCoxeterSystem_simple, nativeCoxeterSystem_length, nativeCoxeterSystem_length,
    coe_mul_nativeSimple] at h
  rw [nativeCoxeterSystem_simple, stdCell_mul_eq, stdBruhatCell_mul_of_sub w i h,
    Set.preimage_union, stdCell, stdCell]

end CFSG.LieType.Chevalley.C2E6Std
