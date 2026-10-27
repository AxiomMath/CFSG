module

public import CFSG.LieType.Ree.FixedWeylStructureData

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace ReeTag

@[expose] def largeReeBlockImage (k : Fin F4.fixedWeylOrder) (j : Fin F4.fixedOrbitCount) :
    List (Fin F4.tag.rank → ℤ) :=
  (F4.fixedOrbitRootList j).map fun α =>
    ((F4.fixedRelWord k).flatMap F4.fixedOrbitWord).foldr (reflect F4.tag) α

@[expose] def largeReeBlockTable (i : Fin 16) : List (Fin F4.tag.rank → ℤ) :=
  ([[![0, 0, 0, 1], ![1, 0, 0, 0]],
    [![0, 0, 1, 0], ![0, 1, 0, 0], ![0, 1, 1, 0], ![0, 1, 2, 0]],
    [![0, 0, 0, -1], ![-1, 0, 0, 0]],
    [![0, 0, 1, 1], ![1, 1, 0, 0], ![1, 1, 1, 1], ![1, 1, 2, 2]],
    [![0, 1, 2, 1], ![1, 2, 2, 0]],
    [![0, 0, -1, 0], ![0, -1, 0, 0], ![0, -1, -1, 0], ![0, -1, -2, 0]],
    [![1, 1, 2, 1], ![1, 2, 2, 2]],
    [![0, 0, -1, -1], ![-1, -1, 0, 0], ![-1, -1, -1, -1], ![-1, -1, -2, -2]],
    [![0, -1, -2, -1], ![-1, -2, -2, 0]],
    [![0, 1, 1, 1], ![1, 1, 2, 0], ![1, 2, 3, 1], ![1, 3, 4, 2]],
    [![-1, -1, -2, -1], ![-1, -2, -2, -2]],
    [![1, 1, 1, 0], ![0, 1, 2, 2], ![1, 2, 3, 2], ![2, 3, 4, 2]],
    [![1, 2, 2, 1], ![1, 2, 4, 2]],
    [![0, -1, -1, -1], ![-1, -1, -2, 0], ![-1, -2, -3, -1], ![-1, -3, -4, -2]],
    [![-1, -1, -1, 0], ![0, -1, -2, -2], ![-1, -2, -3, -2], ![-2, -3, -4, -2]],
    [![-1, -2, -2, -1], ![-1, -2, -4, -2]]] : List (List (Fin 4 → ℤ))).getD i []

theorem largeReeBlockImage_check : ∀ k : Fin F4.fixedWeylOrder, ∀ j : Fin F4.fixedOrbitCount,
    ∃ i : Fin 16, largeReeBlockImage k j ⊆ largeReeBlockTable i ∧
      largeReeBlockTable i ⊆ largeReeBlockImage k j := by
  decide +kernel

theorem largeReeBlockTable_check : ∀ i : Fin 16, ∃ k : Fin F4.fixedWeylOrder,
    ∃ j : Fin F4.fixedOrbitCount, largeReeBlockTable i ⊆ largeReeBlockImage k j ∧
      largeReeBlockImage k j ⊆ largeReeBlockTable i := by
  decide +kernel

theorem largeReeBlockTable_disjoint : ∀ i i' : Fin 16, i ≠ i' →
    ∀ x ∈ largeReeBlockTable i, x ∉ largeReeBlockTable i' := by
  decide +kernel

theorem largeReeBlockTable_ne_nil_nodup : ∀ i : Fin 16,
    largeReeBlockTable i ≠ [] ∧ (largeReeBlockTable i).Nodup := by
  decide +kernel

theorem largeReeBlockTable_cover : ∀ m < F4.tag.rootCertificate.roots.length,
    ∃ i : Fin 16, F4.tag.rootCertificate.root m ∈ largeReeBlockTable i := by
  decide +kernel

theorem largeReeBlockTable_card :
    (Finset.univ.filter fun i : Fin 16 => (largeReeBlockTable i).length = 2).card = 8 ∧
    (Finset.univ.filter fun i : Fin 16 => (largeReeBlockTable i).length = 4).card = 8 ∧
    (Finset.univ.filter fun i : Fin 16 =>
      (∀ x ∈ largeReeBlockTable i, 0 < height x) ∧ (largeReeBlockTable i).length = 2).card = 4 ∧
    (Finset.univ.filter fun i : Fin 16 =>
      (∀ x ∈ largeReeBlockTable i, 0 < height x) ∧ (largeReeBlockTable i).length = 4).card = 4 := by
  decide +kernel

theorem dualRoot_mem_fixedOrbitRootList_F4 : ∀ j : Fin F4.fixedOrbitCount,
    ∀ α ∈ F4.fixedOrbitRootList j, F4.dualRoot α ∈ F4.fixedOrbitRootList j := by
  decide +kernel

end ReeTag

end CFSG.LieType.Ree
