module

import CFSG.LieType.Chevalley.ParabolicRadicalLevi
public import CFSG.LieType.Chevalley.ToralCentralizerQuotient
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ModelGenA
public import CFSG.LocalAnalysis.SeitzReduction.EPilotRoots

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction CFSG.SeitzReduction.EPilot
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen (ModelAGen)

variable {τ : Tag} {K : Type} [Field K]

section Two

theorem mem_rootSpan_inter_inter_of_conj_eq (a b : Fin τ.rank → Kˣ) {S : Set (Fin τ.rank → ℤ)}
    (hS : S.Finite) (hSroot : ∀ α ∈ S, IsRoot τ α)
    (hcoll : ∀ {m : ℕ} (α : Fin m → Fin τ.rank → ℤ), Function.Injective α → Set.range α = S →
      Set.BijOn (fun c : Fin m → K => (List.ofFn fun k => pinnedX τ K (α k) (c k)).prod)
        Set.univ (rootSpan τ K S))
    {u : ModGL τ K} (hu : u ∈ rootSpan τ K S)
    (hfa : rootDiagUnit τ a * u * (rootDiagUnit τ a)⁻¹ = u)
    (hfb : rootDiagUnit τ b * u * (rootDiagUnit τ b)⁻¹ = u) :
    u ∈ rootSpan τ K (rootCharKernel a ∩ rootCharKernel b ∩ S) := by
  have : Finite S := hS.to_subtype
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin S
  set α : Fin n → Fin τ.rank → ℤ := fun k => (e.symm k : Fin τ.rank → ℤ)
  have hα : Function.Injective α := fun k k' h => e.symm.injective (Subtype.ext h)
  have hrange : Set.range α = S := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      exact (e.symm k).2
    · intro hx
      exact ⟨e ⟨x, hx⟩, by simp [α]⟩
  have hαS : ∀ k, α k ∈ S := fun k => (e.symm k).2
  have hbij := hcoll α hα hrange
  obtain ⟨c, -, rfl⟩ := hbij.2.2 hu
  have hmap : ∀ d : Fin τ.rank → Kˣ, rootDiagUnit τ d *
      (List.ofFn fun k => pinnedX τ K (α k) (c k)).prod * (rootDiagUnit τ d)⁻¹ =
        (List.ofFn fun k => pinnedX τ K (α k) ((rootChar d (α k) : K) * c k)).prod := by
    intro d
    have h := map_list_prod (MulAut.conj (rootDiagUnit τ d)).toMonoidHom
      (List.ofFn fun k => pinnedX τ K (α k) (c k))
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, List.map_ofFn] at h
    rw [h]
    refine congrArg List.prod (congrArg List.ofFn (funext fun k => ?_))
    exact rootDiagUnit_conj_pinnedX d (hSroot _ (hαS k)) (c k)
  rw [hmap] at hfa hfb
  have hca : (fun k => (rootChar a (α k) : K) * c k) = c :=
    hbij.2.1 (Set.mem_univ _) (Set.mem_univ _) hfa
  have hcb : (fun k => (rootChar b (α k) : K) * c k) = c :=
    hbij.2.1 (Set.mem_univ _) (Set.mem_univ _) hfb
  have hzero : ∀ (d : Fin τ.rank → Kˣ) (k : Fin n), (rootChar d (α k) : K) * c k = c k →
      rootChar d (α k) ≠ 1 → c k = 0 := fun d k h1 hk => by
    have h2 : ((rootChar d (α k) : K) - 1) * c k = 0 := by linear_combination h1
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact absurd (Units.ext (sub_eq_zero.1 h3)) hk
    · exact h3
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨k, rfl⟩ := (List.mem_ofFn' _ _).1 hx
  by_cases hk : rootChar a (α k) = 1 ∧ rootChar b (α k) = 1
  · exact le_iSup₂_of_le (f := fun β (_ : β ∈ rootCharKernel a ∩ rootCharKernel b ∩ S) =>
      rootSubgroup τ K β) (α k) ⟨⟨⟨hSroot _ (hαS k), hk.1⟩, ⟨hSroot _ (hαS k), hk.2⟩⟩, hαS k⟩
      le_rfl (Subgroup.subset_closure ⟨c k, rfl⟩)
  · have hck : c k = 0 := by
      rcases not_and_or.1 hk with hk | hk
      · exact hzero a k (congrFun hca k) hk
      · exact hzero b k (congrFun hcb k) hk
    simp only [hck, pinnedX_zero]
    exact one_mem _

theorem toralCentralizer_inf_le (a b : Fin τ.rank → Kˣ) :
    toralCentralizer τ K a ⊓ toralCentralizer τ K b ≤
      torusGroup τ K ⊔ rootSpan τ K (rootCharKernel a ∩ rootCharKernel b) ⊔
        Subgroup.closure ((fun w => canonicalRep (coxeterSystem τ) K w) ''
          (rootCharStabilizer a ∩ rootCharStabilizer b)) := by
  rintro g ⟨hga, hgb⟩
  obtain ⟨hXa, huniq, -, -⟩ := Chevalley_toral_centralizer_Bruhat_factors τ K a
  obtain ⟨hXb, -, -, -⟩ := Chevalley_toral_centralizer_Bruhat_factors τ K b
  obtain ⟨w, hw, h, hh, u, hu, v, hv, rfl⟩ := hXa _ hga
  obtain ⟨w', hw', h', hh', u', hu', v', hv', heq⟩ := hXb _ hgb
  have huU : u ∈ posUnipotent τ K := rootSpan_mono Set.inter_subset_right hu
  have hu'U : u' ∈ posUnipotent τ K := rootSpan_mono Set.inter_subset_right hu'
  have hvI : v ∈ rootSpan τ K (inversionSet w) := rootSpan_mono Set.inter_subset_right hv
  have hv'I : v' ∈ rootSpan τ K (inversionSet w') := rootSpan_mono Set.inter_subset_right hv'
  obtain ⟨rfl, rfl, rfl, rfl⟩ := huniq w w' h h' u u' v v' hh hh' huU hu'U hvI hv'I heq
  have hposfin : {β : Fin τ.rank → ℤ | IsRoot τ β ∧ 0 < height β}.Finite :=
    (finite_setOf_isRoot τ).subset fun β hβ => hβ.1
  have hfix : ∀ (d : Fin τ.rank → Kˣ) {S : Set (Fin τ.rank → ℤ)} {x : ModGL τ K},
      S ⊆ rootCharKernel d → x ∈ rootSpan τ K S →
        rootDiagUnit τ d * x * (rootDiagUnit τ d)⁻¹ = x := fun d S x hS hx =>
    conj_eq_iff_mem_centralizer.2 (rootSpan_le_centralizer d hS hx)
  have hu₂ : u ∈ rootSpan τ K (rootCharKernel a ∩ rootCharKernel b ∩
      {β | IsRoot τ β ∧ 0 < height β}) :=
    mem_rootSpan_inter_inter_of_conj_eq a b hposfin (fun β hβ => hβ.1)
      (fun α hα hr => (positive_root_collection τ K).2 α hα hr) huU
      (hfix a Set.inter_subset_left hu) (hfix b Set.inter_subset_left hu')
  have hv₂ : v ∈ rootSpan τ K (rootCharKernel a ∩ rootCharKernel b ∩ inversionSet w) :=
    mem_rootSpan_inter_inter_of_conj_eq a b (inversionSet_finite w) (fun β hβ => hβ.1)
      (fun α hα hr => (bruhat_cell_factorization τ K).2.1 w α hα hr) hvI
      (hfix a Set.inter_subset_left hv) (hfix b Set.inter_subset_left hv')
  have hKS : ∀ {S : Set (Fin τ.rank → ℤ)}, S ⊆ rootCharKernel a ∩ rootCharKernel b →
      rootSpan τ K S ≤ torusGroup τ K ⊔ rootSpan τ K (rootCharKernel a ∩ rootCharKernel b) ⊔
        Subgroup.closure ((fun w => canonicalRep (coxeterSystem τ) K w) ''
          (rootCharStabilizer a ∩ rootCharStabilizer b)) := fun hS =>
    (rootSpan_mono hS).trans (le_sup_right.trans le_sup_left)
  refine mul_mem (mul_mem (mul_mem ?_ (hKS Set.inter_subset_left hu₂)) ?_)
    (hKS Set.inter_subset_left hv₂)
  · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left hh)
  · exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨w, ⟨hw, hw'⟩, rfl⟩)

theorem toralCentralizer_inf_le_normalizer (a b : Fin τ.rank → Kˣ) :
    toralCentralizer τ K a ⊓ toralCentralizer τ K b ≤
      Subgroup.normalizer (rootSpan τ K (rootCharKernel a ∩ rootCharKernel b) : Set (ModGL τ K)) := by
  refine (toralCentralizer_inf_le a b).trans (sup_le (sup_le
    (torusGroup_le_normalizer_rootSpan fun _ hα => hα.1.1) Subgroup.le_normalizer) ?_)
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨w, ⟨hwa, hwb⟩, rfl⟩
  refine mem_normalizer_of_map_eq ?_
  rw [(canonical_weyl_root_transport τ K).1 w _ fun _ hα => hα.1.1,
    Set.image_inter (MulAction.injective w), image_rootCharKernel hwa, image_rootCharKernel hwb]

end Two

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

end
