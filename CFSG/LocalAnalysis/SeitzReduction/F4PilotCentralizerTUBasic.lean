module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotRoots
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneF4Inner

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootOps
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit rootChar)

local instance f4CentralizerTUNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

section General

variable {τ : Tag} {K : Type} [Field K]


theorem rootSubgroup_smul_le_of_canonicalRep_mem {M : Subgroup (ModGL τ K)} {w : WeylGroup τ}
    (hw : canonicalRep (coxeterSystem τ) K w ∈ M) {δ : Fin τ.rank → ℤ} (hδ : IsRoot τ δ)
    (hδM : rootSubgroup τ K δ ≤ M) : rootSubgroup τ K (w • δ) ≤ M := by
  rw [← (canonical_weyl_root_transport τ K).2.1 w δ hδ]
  rintro _ ⟨x, hx, rfl⟩
  exact mul_mem (mul_mem hw (hδM hx)) (inv_mem hw)

theorem rootSubgroup_single_le_parabolicLevi' {J : Set (Fin τ.rank)} {j : Fin τ.rank}
    (hj : j ∈ J) : rootSubgroup τ K (Pi.single j 1) ≤ parabolicLevi τ K J :=
  (Subgroup.closure_le _).2 (by
    rintro _ ⟨c, rfl⟩
    rw [pinnedX_single]
    exact xUnit_mem_parabolicLevi hj c)

theorem rootSubgroup_neg_single_le_parabolicLevi' {J : Set (Fin τ.rank)} {j : Fin τ.rank}
    (hj : j ∈ J) : rootSubgroup τ K (-Pi.single j 1) ≤ parabolicLevi τ K J :=
  (Subgroup.closure_le _).2 (by
    rintro _ ⟨c, rfl⟩
    rw [pinnedX_neg_single]
    exact yUnit_mem_parabolicLevi hj c)

theorem rootSubgroup_le_parabolicLevi {J : Set (Fin τ.rank)} {γ : Fin τ.rank → ℤ}
    (hγ : γ ∈ parabolicRoots τ J) : rootSubgroup τ K γ ≤ parabolicLevi τ K J := by
  rcases IsRoot.height_pos_or_neg hγ.1 with hpos | hneg
  · obtain ⟨w, hw, j, hj, hwj⟩ := exists_mem_parabolicWeylGroup_smul _ γ rfl ⟨hγ, hγ.1, hpos⟩
    rw [← hwj]
    exact rootSubgroup_smul_le_of_canonicalRep_mem (canonicalRep_mem_parabolicLevi hw)
      (isRoot_single τ j) (rootSubgroup_single_le_parabolicLevi' hj)
  · have hneg' : -γ ∈ parabolicPosRoots τ J :=
      ⟨⟨IsRoot.neg hγ.1, fun i hi => by rw [Pi.neg_apply, hγ.2 i hi, neg_zero]⟩,
        IsRoot.neg hγ.1, by rw [height_neg]; omega⟩
    obtain ⟨w, hw, j, hj, hwj⟩ := exists_mem_parabolicWeylGroup_smul _ (-γ) rfl hneg'
    have e : γ = w • (-Pi.single j 1 : Fin τ.rank → ℤ) := by rw [smul_neg, hwj, neg_neg]
    rw [e]
    exact rootSubgroup_smul_le_of_canonicalRep_mem (canonicalRep_mem_parabolicLevi hw)
      (isRoot_neg_single τ j) (rootSubgroup_neg_single_le_parabolicLevi' hj)

theorem rootSpan_parabolicRoots_le_parabolicLevi (J : Set (Fin τ.rank)) :
    rootSpan τ K (parabolicRoots τ J) ≤ parabolicLevi τ K J :=
  iSup₂_le fun _ hγ => rootSubgroup_le_parabolicLevi hγ

theorem parabolicRadical_inf_rootSpan (J : Set (Fin τ.rank)) :
    parabolicRadical τ K J ⊓ rootSpan τ K (parabolicRoots τ J) = ⊥ :=
  eq_bot_iff.2 ((inf_le_inf_left _ (rootSpan_parabolicRoots_le_parabolicLevi J)).trans
    (parabolicRadical_inf_parabolicLevi J).le)

theorem rootSpan_parabolicRoots_le_normalizer (J : Set (Fin τ.rank)) :
    rootSpan τ K (parabolicRoots τ J) ≤
      normalizer (parabolicRadical τ K J : Set (ModGL τ K)) :=
  ((rootSpan_parabolicRoots_le_parabolicLevi J).trans (parabolicLevi_le_parabolicSubgroup J)).trans
    (parabolicSubgroup_le_normalizer_parabolicRadical J)

theorem parabolicLevi_le_torusGroup_sup (J : Set (Fin τ.rank)) :
    parabolicLevi τ K J ≤ torusGroup τ K ⊔ rootSpan τ K (parabolicRoots τ J) := by
  refine sup_le le_sup_left (le_sup_of_le_right ((Subgroup.closure_le _).2 ?_))
  rintro _ ⟨j, hj, c, rfl | rfl⟩
  · have hmem : (Pi.single j 1 : Fin τ.rank → ℤ) ∈ parabolicRoots τ J :=
      ⟨isRoot_single τ j, fun i hi =>
        Pi.single_eq_of_ne (show i ≠ j from fun h => hi (h ▸ hj)) _⟩
    exact le_iSup₂_of_le (f := fun δ (_ : δ ∈ parabolicRoots τ J) => rootSubgroup τ K δ) _ hmem
      le_rfl (xUnit_mem_rootSubgroup j c)
  · have hmem : (-Pi.single j 1 : Fin τ.rank → ℤ) ∈ parabolicRoots τ J :=
      ⟨isRoot_neg_single τ j, fun i hi => by
        rw [Pi.neg_apply, Pi.single_eq_of_ne (show i ≠ j from fun h => hi (h ▸ hj)), neg_zero]⟩
    exact le_iSup₂_of_le (f := fun δ (_ : δ ∈ parabolicRoots τ J) => rootSubgroup τ K δ) _ hmem
      le_rfl (yUnit_mem_rootSubgroup j c)

theorem eq_of_pinnedX_eq_pinnedX {β γ : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (hγ : IsRoot τ γ ∧ 0 < height γ) {d e : K} (hd : d ≠ 0)
    (h : pinnedX τ K β d = pinnedX τ K γ e) : β = γ := by
  by_contra hne
  rcases IsRoot.height_pos_or_neg hβ with hpos | hneg
  · have hL := pinnedX_list_prod_injective (R := K) [β, γ] (by simpa using hne)
      (by
        intro α hα
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hα
        rcases hα with rfl | rfl
        · exact ⟨hβ, hpos⟩
        · exact hγ)
      (fun α => if α = β then d else 0) (fun α => if α = γ then e else 0)
      (by
        simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
          hne, Ne.symm hne, ↓reduceIte, pinnedX_zero, one_mul]
        exact h)
      β (by simp)
    simp only [hne, ↓reduceIte] at hL
    exact hd hL
  · have hmem : pinnedX τ K β d ∈ borelGroup τ K ⊓ negUnipotent τ K := by
      refine Subgroup.mem_inf.2 ⟨?_, pinnedX_mem_rootSpan
        (S := {α | IsRoot τ α ∧ height α < 0}) ⟨hβ, hneg⟩ d⟩
      rw [h]
      exact Subgroup.mem_sup_right (pinnedX_mem_rootSpan
        (S := {α | IsRoot τ α ∧ 0 < height α}) hγ e)
    rw [borelGroup_inf_negUnipotent, Subgroup.mem_bot] at hmem
    exact hd (pinnedX_injective τ K β (hmem.trans (pinnedX_zero τ K β).symm))

theorem eq_and_eq_of_pinnedX_mul_eq {α β γ δ : Fin τ.rank → ℤ}
    (hα : IsRoot τ α ∧ 0 < height α) (hβ : IsRoot τ β ∧ 0 < height β)
    (hγ : IsRoot τ γ ∧ 0 < height γ) (hδ : IsRoot τ δ ∧ 0 < height δ)
    (hαβ : α ≠ β) (hγδ : γ ≠ δ) (hαδ : α ≠ δ) (hβγ : β ≠ γ) {c c' d d' : K} (hc : c ≠ 0)
    (hc' : c' ≠ 0)
    (h : pinnedX τ K α c * pinnedX τ K β c' = pinnedX τ K γ d * pinnedX τ K δ d') :
    α = γ ∧ β = δ := by
  by_cases hαγ : α = γ
  · subst hαγ
    by_cases hβδ : β = δ
    · exact ⟨rfl, hβδ⟩
    exfalso
    have hL := pinnedX_list_prod_injective (R := K) [α, β, δ]
      (by simp [hαβ, hαδ, hβδ])
      (by
        intro ρ hρ
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hρ
        rcases hρ with rfl | rfl | rfl
        · exact hα
        · exact hβ
        · exact hδ)
      (fun ρ => if ρ = α then c else if ρ = β then c' else 0)
      (fun ρ => if ρ = α then d else if ρ = δ then d' else 0)
      (by
        simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
          hβδ, Ne.symm hαβ, Ne.symm hαδ, Ne.symm hβδ, ↓reduceIte, pinnedX_zero, one_mul]
        rw [h])
      β (by simp)
    simp only [Ne.symm hαβ, hβδ, ↓reduceIte] at hL
    exact hc' hL
  · exfalso
    by_cases hβδ : β = δ
    · subst hβδ
      have hL := pinnedX_list_prod_injective (R := K) [α, γ, β]
        (by simp [hαγ, hαβ, Ne.symm hβγ])
        (by
          intro ρ hρ
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hρ
          rcases hρ with rfl | rfl | rfl
          · exact hα
          · exact hγ
          · exact hβ)
        (fun ρ => if ρ = α then c else if ρ = β then c' else 0)
        (fun ρ => if ρ = γ then d else if ρ = β then d' else 0)
        (by
          simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
            hαγ, hαβ, hβγ, Ne.symm hαγ, Ne.symm hαβ, Ne.symm hβγ, ↓reduceIte, pinnedX_zero,
            one_mul]
          rw [h])
        α (by simp)
      simp only [hαγ, hαβ, ↓reduceIte] at hL
      exact hc hL
    · have hL := pinnedX_list_prod_injective (R := K) [α, β, γ, δ]
        (by simp [hαβ, hαγ, hαδ, hβγ, hβδ, hγδ])
        (by
          intro ρ hρ
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hρ
          rcases hρ with rfl | rfl | rfl | rfl
          · exact hα
          · exact hβ
          · exact hγ
          · exact hδ)
        (fun ρ => if ρ = α then c else if ρ = β then c' else 0)
        (fun ρ => if ρ = γ then d else if ρ = δ then d' else 0)
        (by
          simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
            hαγ, hαδ, hβγ, hβδ, Ne.symm hαβ, Ne.symm hαγ, Ne.symm hαδ, Ne.symm hβγ,
            Ne.symm hβδ, Ne.symm hγδ, ↓reduceIte, pinnedX_zero, one_mul]
          rw [h])
        α (by simp)
      simp only [hαγ, hαδ, ↓reduceIte] at hL
      exact hc hL

theorem torusElt_mem_rootSpan {S : Set (Fin τ.rank → ℤ)} {j : Fin τ.rank}
    (h1 : (Pi.single j 1 : Fin τ.rank → ℤ) ∈ S) (h2 : (-Pi.single j 1 : Fin τ.rank → ℤ) ∈ S)
    (u : Kˣ) : torusElt τ K j u ∈ rootSpan τ K S := by
  have hx : ∀ c : K, xUnit τ K j c ∈ rootSpan τ K S := fun c =>
    le_iSup₂_of_le (f := fun δ (_ : δ ∈ S) => rootSubgroup τ K δ) _ h1 le_rfl
      (xUnit_mem_rootSubgroup j c)
  have hy : ∀ c : K, yUnit τ K j c ∈ rootSpan τ K S := fun c =>
    le_iSup₂_of_le (f := fun δ (_ : δ ∈ S) => rootSubgroup τ K δ) _ h2 le_rfl
      (yUnit_mem_rootSubgroup j c)
  have hw : ∀ t : Kˣ, weylElt τ K j t ∈ rootSpan τ K S := fun t => by
    rw [CFSG.LieType.Chevalley.weylElt_eq_xUnit_mul]
    exact mul_mem (mul_mem (hx _) (hy _)) (hx _)
  have e : torusElt τ K j u = weylElt τ K j u * (weylElt τ K j 1)⁻¹ :=
    eq_mul_inv_of_mul_eq (weylElt_eq_torusElt_mul_weylElt_one j u).symm
  rw [e]
  exact mul_mem (hw u) (inv_mem (hw 1))

end General

section Torus

variable {K : Type} [Field K]

@[expose] def f4FundWeight : Fin (Tag.rank .F4) → Fin (Tag.rank .F4) → ℤ :=
  ![![2, 3, 4, 2], ![3, 6, 8, 4], ![2, 4, 6, 3], ![1, 2, 3, 2]]

theorem f4FundWeight_cartan : ∀ k l : Fin (Tag.rank .F4),
    ∑ j, f4FundWeight j k * Tag.cartan .F4 j l = if k = l then 1 else 0 := by
  decide +kernel

theorem f4FundWeight_zero_three : f4FundWeight 0 = rootR ∧ f4FundWeight 3 = rootS :=
  ⟨rfl, rfl⟩

theorem cartanChar_rootChar_f4FundWeight (a : Fin (Tag.rank .F4) → Kˣ) :
    cartanChar (fun j => rootChar a (f4FundWeight j)) = a := by
  funext l
  simp only [cartanChar, rootChar]
  calc ∏ j, (∏ i, a i ^ f4FundWeight j i) ^ Tag.cartan .F4 j l
      = ∏ j, ∏ i, a i ^ (f4FundWeight j i * Tag.cartan .F4 j l) := by
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [← Finset.prod_zpow]
        exact Finset.prod_congr rfl fun i _ => (zpow_mul _ _ _).symm
    _ = ∏ i, ∏ j, a i ^ (f4FundWeight j i * Tag.cartan .F4 j l) := Finset.prod_comm
    _ = ∏ i, a i ^ (∑ j, f4FundWeight j i * Tag.cartan .F4 j l) :=
        Finset.prod_congr rfl fun i _ => prod_zpow_eq_zpow_sum _ _ _
    _ = ∏ i, a i ^ (if i = l then (1 : ℤ) else 0) :=
        Finset.prod_congr rfl fun i _ => by rw [f4FundWeight_cartan]
    _ = a l := by
        rw [Finset.prod_eq_single l (fun i _ hi => by rw [ite_eq_right_iff.2 (fun h => absurd h hi), zpow_zero])
          (fun h => absurd (Finset.mem_univ l) h)]
        simp


theorem f4RootDiagUnit_eq_list_prod_torusElt (a : Fin (Tag.rank .F4) → Kˣ) :
    rootDiagUnit .F4 a = ((List.finRange (Tag.rank .F4)).map fun j =>
      torusElt .F4 K j (rootChar a (f4FundWeight j))).prod := by
  rw [list_prod_torusElt_eq_rootDiagUnit, cartanChar_rootChar_f4FundWeight]

theorem torusElt_one' (j : Fin (Tag.rank .F4)) : torusElt .F4 K j 1 = 1 := by
  rw [torusElt_eq_rootDiagUnit]
  simp only [one_zpow]
  exact rootDiagUnit_one

theorem rootDiagUnit_mem_rootSpan_of_rootChar {S : Set (Fin (Tag.rank .F4) → ℤ)}
    {a : Fin (Tag.rank .F4) → Kˣ}
    (h : ∀ j, rootChar a (f4FundWeight j) = 1 ∨
      ((Pi.single j 1 : Fin (Tag.rank .F4) → ℤ) ∈ S ∧ (-Pi.single j 1 : Fin _ → ℤ) ∈ S)) :
    rootDiagUnit .F4 a ∈ rootSpan .F4 K S := by
  rw [f4RootDiagUnit_eq_list_prod_torusElt]
  refine list_prod_mem fun x hx => ?_
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
  rcases h j with h1 | ⟨h1, h2⟩
  · rw [h1, torusElt_one']
    exact one_mem _
  · exact torusElt_mem_rootSpan h1 h2 _

end Torus

end CFSG.SeitzReduction.F4Pilot
