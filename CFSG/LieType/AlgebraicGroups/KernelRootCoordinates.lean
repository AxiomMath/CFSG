module

public import CFSG.LieType.Chevalley.CoordinateFieldBaseChange
public import CFSG.LieType.Chevalley.PositiveRootCollection
import CFSG.LieType.Chevalley.BruhatCellFactorization

public section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Coordinates


theorem mem_rootSpan_of_baseChangeGL_mem {τ : Tag} {K L : Type} [Field K] [Field L] (ι : K →+* L)
    {P S : Set (Fin τ.rank → ℤ)} (hP : P.Finite) (hSP : S ⊆ P)
    (hPpos : ∀ α ∈ P, IsRoot τ α ∧ 0 < height α)
    (hPcl : ∀ α ∈ P, ∀ β ∈ P, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot τ (a • α + b • β) →
      a • α + b • β ∈ P)
    (hScl : ∀ α ∈ S, ∀ β ∈ S, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot τ (a • α + b • β) →
      a • α + b • β ∈ S)
    {u : ModGL τ K} (hu : u ∈ rootSpan τ K P) (huL : baseChangeGL ι u ∈ rootSpan τ L S) :
    u ∈ rootSpan τ K S := by
  obtain ⟨αS, hSinj, hSrange⟩ := exists_rootEnum (hP.subset hSP)
  obtain ⟨αR, hRinj, hRrange⟩ := exists_rootEnum (hP.subset (Set.diff_subset : P \ S ⊆ P))
  have hSmem : ∀ k, αS k ∈ S := fun k => hSrange ▸ Set.mem_range_self k
  have hRmem : ∀ k, αR k ∈ P \ S := fun k => hRrange ▸ Set.mem_range_self k
  have hdisj : ∀ k l, αS k ≠ αR l := fun k l h => (hRmem l).2 (h ▸ hSmem k)
  set α := Fin.append αS αR
  have hinj : Function.Injective α := by
    intro k l h
    induction k using Fin.addCases with
    | left k =>
      induction l using Fin.addCases with
      | left l => simp only [α, Fin.append_left] at h; rw [hSinj h]
      | right l =>
        simp only [α, Fin.append_left, Fin.append_right] at h
        exact absurd h (hdisj k l)
    | right k =>
      induction l using Fin.addCases with
      | left l =>
        simp only [α, Fin.append_left, Fin.append_right] at h
        exact absurd h.symm (hdisj l k)
      | right l => simp only [α, Fin.append_right] at h; rw [hRinj h]
  have hrange : Set.range α = P := by
    ext β
    constructor
    · rintro ⟨k, rfl⟩
      induction k using Fin.addCases with
      | left k => simpa [α] using hSP (hSmem k)
      | right k => simpa [α] using (hRmem k).1
    · intro hβ
      by_cases hβS : β ∈ S
      · obtain ⟨k, hk⟩ : β ∈ Set.range αS := by rw [hSrange]; exact hβS
        exact ⟨Fin.castAdd _ k, by simp [α, hk]⟩
      · obtain ⟨k, hk⟩ : β ∈ Set.range αR := by rw [hRrange]; exact ⟨hβ, hβS⟩
        exact ⟨Fin.natAdd _ k, by simp [α, hk]⟩
  have hPK := (positive_root_collection τ K).1 P hPpos hPcl α hinj hrange
  have hPL := (positive_root_collection τ L).1 P hPpos hPcl α hinj hrange
  have hSL := (positive_root_collection τ L).1 S (fun β hβ => hPpos β (hSP hβ)) hScl αS hSinj
    hSrange
  obtain ⟨c, -, hc⟩ := hPK.surjOn hu
  obtain ⟨d, -, hd⟩ := hSL.surjOn huL
  have hc' : (List.ofFn fun i => pinnedX τ K (α i) (c i)).prod = u := hc
  have hd' : (List.ofFn fun j => pinnedX τ L (αS j) (d j)).prod = baseChangeGL ι u := hd
  have hmap : baseChangeGL ι (List.ofFn fun i => pinnedX τ K (α i) (c i)).prod =
      (List.ofFn fun i => pinnedX τ L (α i) (ι (c i))).prod := by
    rw [map_list_prod, List.map_ofFn]
    congr 1
    exact List.ofFn_inj.2 (funext fun i => baseChangeGL_pinnedX ι (α i) (c i))
  have happ : (List.ofFn fun i =>
      pinnedX τ L (α i) (Fin.append d (0 : Fin (P \ S).ncard → L) i)).prod =
      (List.ofFn fun j => pinnedX τ L (αS j) (d j)).prod := by
    have h1 : (fun i => pinnedX τ L (α i) (Fin.append d (0 : Fin (P \ S).ncard → L) i)) =
        Fin.append (fun j => pinnedX τ L (αS j) (d j))
          (fun j => pinnedX τ L (αR j) (0 : L)) := by
      funext i
      induction i using Fin.addCases with
      | left k => simp [α]
      | right k => simp [α]
    rw [h1, List.ofFn_fin_append, List.prod_append]
    simp [pinnedX_zero]
  have hEq : (fun i => ι (c i)) = Fin.append d (0 : Fin (P \ S).ncard → L) := by
    refine hPL.injOn (Set.mem_univ _) (Set.mem_univ _) ?_
    show (List.ofFn fun i => pinnedX τ L (α i) (ι (c i))).prod =
      (List.ofFn fun i => pinnedX τ L (α i) (Fin.append d (0 : Fin (P \ S).ncard → L) i)).prod
    rw [← hmap, hc', ← hd', happ]
  have hzero : ∀ j, c (Fin.natAdd S.ncard j) = 0 := fun j => by
    have h := congrFun hEq (Fin.natAdd S.ncard j)
    simp only [Fin.append_right, Pi.zero_apply] at h
    exact ι.injective (by rw [h, map_zero])
  rw [← hc']
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
  induction i using Fin.addCases with
  | left k => simpa [α] using pinnedX_mem_rootSpan (hSmem k) (c (Fin.castAdd _ k))
  | right k =>
    simp [α, hzero k, pinnedX_zero]

end Coordinates

end CFSG.LieType.AlgebraicGroups
