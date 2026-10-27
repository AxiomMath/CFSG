module

public import CFSG.LieType.Chevalley.LangWeylInvolutionReflections

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.RootSystem RootSpace CFSG.LieType.Steinberg.Adjoint

variable {τ : Tag}

theorem exceptional_Lang_Weyl_involution_strongly_orthogonal_reflections
    (τ : Tag)
    (w : WeylGroup τ) (hw : w ^ 2 = 1) :
    ∃ βs : List (Fin τ.rank → ℤ), βs.length ≤ τ.rank ∧ (∀ β ∈ βs, IsRoot τ β) ∧
      w = (βs.map rootReflection).prod ∧
      βs.Pairwise (fun β γ => iform β γ = 0 ∧ ¬ IsRoot τ (β + γ) ∧ ¬ IsRoot τ (β - γ)) := by
  classical
  obtain ⟨c0, hc0, hinner⟩ := exists_inner_ofLattice_eq_iform τ
  have hnormsum : ∀ β γ : Fin τ.rank → ℤ, iform β γ = 0 →
      iform (β + γ) (β + γ) = iform β β + iform γ γ ∧
        iform (β - γ) (β - γ) = iform β β + iform γ γ := by
    intro β γ h0
    have h0' : iform γ β = 0 := by rw [iform_comm]; exact h0
    refine ⟨?_, ?_⟩
    · rw [iform_add_left, iform_add_right, iform_add_right, h0, h0']
      ring
    · rw [iform_sub_left, iform_sub_right, iform_sub_right, h0, h0']
      ring
  have claim : ∀ (n : ℕ) (w : WeylGroup τ), w * w = 1 → (invertedRootsOf w).ncard = n →
      ∃ βs : List (Fin τ.rank → ℤ), (∀ β ∈ βs, IsRoot τ β ∧ w • β = -β) ∧
        w = (βs.map rootReflection).prod ∧
        βs.Pairwise (fun β γ => iform β γ = 0 ∧ ¬ IsRoot τ (β + γ) ∧ ¬ IsRoot τ (β - γ)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro w hw2 hn
      by_cases hw1 : w = 1
      · subst hw1
        exact ⟨[], by simp, by simp, List.Pairwise.nil⟩
      obtain ⟨β₀, hβ₀, hwβ₀⟩ := exists_isRoot_smul_eq_neg_of_involution hw2 hw1
      have hfin := invertedRootsOf_finite w
      obtain ⟨β, hβmem, hβmax⟩ := Finset.exists_max_image hfin.toFinset (fun β => iform β β)
        ⟨β₀, hfin.mem_toFinset.2 ⟨hβ₀, hwβ₀⟩⟩
      obtain ⟨hβ, hwβ⟩ := hfin.mem_toFinset.1 hβmem
      have hmax : ∀ γ ∈ invertedRootsOf w, iform γ γ ≤ iform β β := fun γ hγ =>
        hβmax γ (hfin.mem_toFinset.2 hγ)
      have hww : ∀ v : Fin τ.rank → ℤ, w • (w • v) = v := fun v => by
        rw [← mul_smul, hw2, one_smul]
      have hcomm : rootReflection β * w = w * rootReflection β := by
        have e := rootReflection_smul_root w hβ
        rw [hwβ, rootReflection_neg hβ] at e
        calc rootReflection β * w = w * rootReflection β * w⁻¹ * w := by rw [← e]
          _ = w * rootReflection β := by group
      obtain ⟨w₁, hw₁⟩ : ∃ w₁, w₁ = rootReflection β * w := ⟨_, rfl⟩
      have hw₁2 : w₁ * w₁ = 1 := by
        calc w₁ * w₁ = rootReflection β * (w * rootReflection β) * w := by rw [hw₁]; group
          _ = rootReflection β * (rootReflection β * w) * w := by rw [hcomm]
          _ = (rootReflection β * rootReflection β) * (w * w) := by group
          _ = 1 := by rw [rootReflection_mul_self hβ, hw2, one_mul]
      have hsub : ∀ γ ∈ invertedRootsOf w₁, γ ∈ invertedRootsOf w ∧ iform γ β = 0 ∧ γ ≠ β :=
        fun γ hγ => by
          obtain ⟨h1, h2, h3⟩ := invertedRoots_reflection_subset_general hww hβ hwβ
            (by rw [← hw₁]; exact hγ.2)
          exact ⟨⟨hγ.1, h1⟩, h2, h3⟩
      have hlt : (invertedRootsOf w₁).ncard < n := by
        rw [← hn]
        refine Set.ncard_lt_ncard ⟨fun γ hγ => (hsub γ hγ).1, fun h => ?_⟩ hfin
        exact (hsub β (h ⟨hβ, hwβ⟩)).2.2 rfl
      obtain ⟨γs, hγs, hprod, hpair⟩ := ih _ hlt w₁ hw₁2 rfl
      have hγw : ∀ γ ∈ γs, IsRoot τ γ ∧ w • γ = -γ ∧ iform γ β = 0 := fun γ hγ => by
        obtain ⟨⟨h1, h2⟩, h3, -⟩ := hsub γ (hγs γ hγ)
        exact ⟨h1, h2, h3⟩
      refine ⟨β :: γs, ?_, ?_, ?_⟩
      · intro γ hγ
        rcases List.mem_cons.1 hγ with rfl | hγ
        · exact ⟨hβ, hwβ⟩
        · exact ⟨(hγw γ hγ).1, (hγw γ hγ).2.1⟩
      · rw [List.map_cons, List.prod_cons, ← hprod, hw₁, ← mul_assoc,
          rootReflection_mul_self hβ, one_mul]
      · refine List.Pairwise.cons (fun γ hγ => ?_) hpair
        obtain ⟨hγr, hwγ, h0⟩ := hγw γ hγ
        have h0' : iform β γ = 0 := by rw [iform_comm]; exact h0
        obtain ⟨hn1, hn2⟩ := hnormsum β γ h0'
        have hγpos := iform_self_pos_of_isRoot hγr
        refine ⟨h0', fun hr => ?_, fun hr => ?_⟩
        · have hinv : β + γ ∈ invertedRootsOf w := ⟨hr, by rw [smul_add, hwβ, hwγ, neg_add]⟩
          have := hmax _ hinv
          omega
        · have hinv : β - γ ∈ invertedRootsOf w :=
            ⟨hr, by rw [smul_sub, hwβ, hwγ, neg_sub_neg, neg_sub]⟩
          have := hmax _ hinv
          omega
  obtain ⟨βs, hβs, hprod, hpair⟩ := claim _ w (by rw [← sq]; exact hw) rfl
  have hroots : ∀ β ∈ βs, IsRoot τ β := fun β hβ => (hβs β hβ).1
  refine ⟨βs, ?_, hroots, hprod, hpair⟩
  set v : Fin βs.length → RootSpace τ := fun j => ofLattice (βs.get j) with hv
  have hli : LinearIndependent ℝ v := by
    refine linearIndependent_of_ne_zero_of_inner_eq_zero (fun j => ?_) fun i j hij => ?_
    · rw [hv]
      intro h0
      exact (hroots _ (List.get_mem _ _)).ne_zero (ofLattice_injective (h0.trans
        ofLattice_zero.symm))
    · rw [hv]
      simp only
      rw [hinner]
      have hp := List.pairwise_iff_get.1 hpair
      rcases lt_or_gt_of_ne hij with h | h
      · rw [(hp i j h).1, Int.cast_zero, mul_zero]
      · rw [iform_comm, (hp j i h).1, Int.cast_zero, mul_zero]
  have := hli.fintype_card_le_finrank
  rwa [Fintype.card_fin, Module.finrank_eq_card_basis (basis τ), Fintype.card_fin] at this

end CFSG.LieType.Chevalley
