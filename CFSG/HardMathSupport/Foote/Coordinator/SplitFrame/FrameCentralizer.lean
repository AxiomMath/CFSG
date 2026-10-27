module

public import CFSG.RankThree.PartOne.KE8F.FamBruhat

public section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE8F

set_option linter.unusedSectionVars false


variable {τ : Tag} {K : Type} [Field K]

theorem torusElt_mem_rootSpan {S : Set (Fin τ.rank → ℤ)} {k : Fin τ.rank}
    (h1 : (Pi.single k 1 : Fin τ.rank → ℤ) ∈ S) (h2 : (-Pi.single k 1 : Fin τ.rank → ℤ) ∈ S)
    (t : Kˣ) : torusElt τ K k t ∈ rootSpan τ K S := by
  have hx : ∀ c, xUnit τ K k c ∈ rootSpan τ K S := fun c => by
    rw [← pinnedX_single]
    exact pinnedX_mem_rootSpan h1 c
  have hy : ∀ c, yUnit τ K k c ∈ rootSpan τ K S := fun c => by
    rw [← pinnedX_neg_single]
    exact pinnedX_mem_rootSpan h2 c
  have hw : ∀ s : Kˣ, weylElt τ K k s ∈ rootSpan τ K S := fun s => by
    rw [weylElt_eq_xUnit_mul]
    exact mul_mem (mul_mem (hx _) (hy _)) (hx _)
  exact mul_mem (hw t) (hw (-1))

theorem rootChar_cartan_zpow (t : Kˣ) (k : Fin τ.rank) (α : Fin τ.rank → ℤ) :
    rootChar (fun j => t ^ τ.cartan k j) α = t ^ (∑ j, τ.cartan k j * α j) := by
  simp only [rootChar, ← zpow_mul, Finset.prod_zpow_eq_zpow_sum]

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

theorem mem_torusGroup_of_mem_centralizer_rootSpan {S : Set (Fin τ.rank → ℤ)}
    (J : Set (Fin τ.rank))
    (hJ : ∀ k ∈ J, (Pi.single k 1 : Fin τ.rank → ℤ) ∈ S ∧ (-Pi.single k 1 : Fin τ.rank → ℤ) ∈ S)
    (hker : ∀ α, IsRoot τ α → ∃ k ∈ J, ∃ t : Kˣ, t ^ (∑ j, τ.cartan k j * α j) ≠ 1)
    (R : Set (Fin τ.rank → ℤ)) (hRS : R ⊆ S) (hRpos : ∀ α ∈ R, IsRoot τ α ∧ 0 < height α)
    (hRw : ∀ w : WeylGroup τ, (∀ α ∈ R, w • α = α) → w = 1)
    {g : ModGL τ K} (hg : g ∈ adjointGroup τ K)
    (hc : g ∈ Subgroup.centralizer (rootSpan τ K S : Set (ModGL τ K))) :
    g ∈ torusGroup τ K := by
  classical
  set F : Set (Fin τ.rank → Kˣ) := {a | ∃ k ∈ J, ∃ t : Kˣ, a = fun j => t ^ τ.cartan k j}
    with hF
  have hcomm : ∀ a ∈ F, rootDiagUnit τ a * g * (rootDiagUnit τ a)⁻¹ = g := by
    rintro _ ⟨k, hk, t, rfl⟩
    have hmem : rootDiagUnit τ (fun j => t ^ τ.cartan k j) ∈ rootSpan τ K S := by
      rw [← torusElt_eq_rootDiagUnit]
      exact torusElt_mem_rootSpan (hJ k hk).1 (hJ k hk).2 t
    have h := Subgroup.mem_centralizer_iff.1 hc _ hmem
    rw [h]
    group
  obtain ⟨w, -, h, hh, u, hu, v, hv, hgeq⟩ := fam_factor F hg hcomm
  have hker0 : famKernel F = ∅ := by
    ext α
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨hα, hall⟩
    obtain ⟨k, hk, t, ht⟩ := hker α hα
    apply ht
    have := hall _ ⟨k, hk, t, rfl⟩
    rwa [rootChar_cartan_zpow] at this
  have hbot : ∀ T : Set (Fin τ.rank → ℤ), rootSpan τ K (∅ ∩ T) = ⊥ := by
    intro T
    rw [Set.empty_inter]
    exact le_bot_iff.1 (iSup₂_le fun α hα => absurd hα (Set.notMem_empty α))
  rw [hker0, hbot, Subgroup.mem_bot] at hu hv
  subst hu hv
  have hgw : g = h * canonicalRep (coxeterSystem τ) K w := by
    rw [hgeq, mul_one, mul_one]
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  have hwR : ∀ α ∈ R, w • α = α := by
    intro α hα
    obtain ⟨hαr, hαp⟩ := hRpos α hα
    obtain ⟨ε, hε, hconj⟩ := exists_canonicalRep_mul_pinnedX_mul_inv K w hαr
    have hcα : g * pinnedX τ K α 1 * g⁻¹ = pinnedX τ K α 1 := by
      have := Subgroup.mem_centralizer_iff.1 hc (pinnedX τ K α 1) (pinnedX_mem_rootSpan (hRS hα) 1)
      rw [← this]
      group
    have e1 : g * pinnedX τ K α 1 * g⁻¹ =
        pinnedX τ K (w • α) ((rootChar b (w • α) : K) * (ε * 1)) := by
      rw [hgw, ← rootDiagUnit_conj_pinnedX b (CFSG.LieType.Chevalley.IsRoot.smul hαr w), ← hconj]
      group
    have hne : ((rootChar b (w • α) : K) * (ε * 1)) ≠ 0 := by
      refine mul_ne_zero (Units.ne_zero _) ?_
      rw [mul_one]
      intro h0
      rw [h0, mul_zero] at hε
      exact zero_ne_one hε
    exact eq_of_pinnedX_eq_pinnedX (CFSG.LieType.Chevalley.IsRoot.smul hαr w) ⟨hαr, hαp⟩ hne (e1.symm.trans hcα)
  have hw1 : w = 1 := hRw w hwR
  rw [hgw, hw1, canonicalRep_one, mul_one]
  exact hh

theorem eq_one_of_smul_single_of_smul {w : WeylGroup τ} {i₀ : Fin τ.rank}
    (hw : ∀ k, k ≠ i₀ → w • (Pi.single k 1 : Fin τ.rank → ℤ) = Pi.single k 1)
    {θ : Fin τ.rank → ℤ} (hθ : w • θ = θ) (hθ0 : θ i₀ ≠ 0) : w = 1 := by
  classical
  have hdec : ∀ v : Fin τ.rank → ℤ, v = ∑ k, v k • (Pi.single k 1 : Fin τ.rank → ℤ) := by
    intro v
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hlin : ∀ v : Fin τ.rank → ℤ, w • v = ∑ k, v k • (w • (Pi.single k 1 : Fin τ.rank → ℤ)) := by
    intro v
    conv_lhs => rw [hdec v]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_comm]
  have hi₀ : w • (Pi.single i₀ 1 : Fin τ.rank → ℤ) = Pi.single i₀ 1 := by
    have h1 := hlin θ
    rw [hθ] at h1
    have h2 : ∑ k, θ k • (w • (Pi.single k 1 : Fin τ.rank → ℤ)) =
        θ i₀ • (w • (Pi.single i₀ 1 : Fin τ.rank → ℤ)) +
          ∑ k ∈ Finset.univ.erase i₀, θ k • (Pi.single k 1 : Fin τ.rank → ℤ) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
      congr 1
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [hw k (Finset.ne_of_mem_erase hk)]
    have h3 : θ = θ i₀ • (Pi.single i₀ 1 : Fin τ.rank → ℤ) +
        ∑ k ∈ Finset.univ.erase i₀, θ k • (Pi.single k 1 : Fin τ.rank → ℤ) := by
      conv_lhs => rw [hdec θ]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
    have h4 : θ i₀ • (w • (Pi.single i₀ 1 : Fin τ.rank → ℤ)) =
        θ i₀ • (Pi.single i₀ 1 : Fin τ.rank → ℤ) := by
      have := (h1.trans h2).symm.trans h3
      exact add_right_cancel this
    exact smul_right_injective _ hθ0 h4
  have hall : ∀ k, w • (Pi.single k 1 : Fin τ.rank → ℤ) = Pi.single k 1 := fun k => by
    by_cases hk : k = i₀
    · rw [hk]
      exact hi₀
    · exact hw k hk
  apply FaithfulSMul.eq_of_smul_eq_smul (α := Fin τ.rank → ℤ)
  intro v
  rw [one_smul, hlin v]
  conv_rhs => rw [hdec v]
  exact Finset.sum_congr rfl fun k _ => by rw [hall k]

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
