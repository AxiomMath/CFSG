module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToral

public noncomputable section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

variable {τ : Tag}

theorem exists_strOrth_kernelRoots_of_sq_eq_one
    {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {w : WeylGroup τ}
    (hw : w ∈ kernelWeylGroup χ) (h2 : w ^ 2 = 1) :
    ∃ βs : List (Fin τ.rank → ℤ), (∀ β ∈ βs, β ∈ kernelRoots χ) ∧
      βs.Pairwise (fun β γ => iform β γ = 0 ∧ ¬ IsRoot τ (β + γ) ∧ ¬ IsRoot τ (β - γ)) ∧
      w = (βs.map rootReflection).prod := by
  classical
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
  have claim : ∀ (n : ℕ) (w : WeylGroup τ), w ∈ kernelWeylGroup χ → w * w = 1 →
      (invertedRootsOf w ∩ kernelRoots χ).ncard = n →
      ∃ βs : List (Fin τ.rank → ℤ),
        (∀ β ∈ βs, β ∈ kernelRoots χ ∧ w • β = -β) ∧
        w = (βs.map rootReflection).prod ∧
        βs.Pairwise (fun β γ => iform β γ = 0 ∧ ¬ IsRoot τ (β + γ) ∧
          ¬ IsRoot τ (β - γ)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro w hwmem hw2 hn
      by_cases hw1 : w = 1
      · subst hw1
        exact ⟨[], by simp, by simp, List.Pairwise.nil⟩
      obtain ⟨α, hαk, hαperp⟩ := exists_kernelRoot_perp (χ := χ) hwmem hw1
      have hα : IsRoot τ α := hαk.1
      have hww : ∀ v : Fin τ.rank → ℤ, w • (w • v) = v := fun v => by
        rw [← mul_smul, hw2, one_smul]
      have hneg : w • α = -α := by
        by_contra hne
        have hwv : w • (α + w • α) = α + w • α := by
          rw [smul_add, hww α]
          abel
        have h1 : iform α (α + w • α) = 0 := hαperp _ hwv
        have h2 : iform (w • α) (α + w • α) = 0 := by
          calc iform (w • α) (α + w • α)
              = iform (w • α) (w • (α + w • α)) := by rw [hwv]
            _ = iform α (α + w • α) := iform_smul w α (α + w • α)
            _ = 0 := h1
        have hvv : iform (α + w • α) (α + w • α) = 0 := by
          rw [iform_add_left, h1, h2, add_zero]
        have hvne : α + w • α ≠ 0 := fun hv0 => hne (add_eq_zero_iff_eq_neg'.1 hv0)
        have hpos := iform_self_pos hvne
        rw [hvv] at hpos
        exact lt_irrefl 0 hpos
      have hfin : (invertedRootsOf w ∩ kernelRoots χ).Finite :=
        (invertedRootsOf_finite w).subset Set.inter_subset_left
      obtain ⟨β, hβmem, hβmax⟩ := Finset.exists_max_image hfin.toFinset
        (fun β => iform β β) ⟨α, hfin.mem_toFinset.2 ⟨⟨hα, hneg⟩, hαk⟩⟩
      obtain ⟨hβinv, hβk⟩ := hfin.mem_toFinset.1 hβmem
      have hβ : IsRoot τ β := hβinv.1
      have hwβ : w • β = -β := hβinv.2
      have hmax : ∀ γ ∈ invertedRootsOf w ∩ kernelRoots χ, iform γ γ ≤ iform β β :=
        fun γ hγ => hβmax γ (hfin.mem_toFinset.2 hγ)
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
      have hw₁mem : w₁ ∈ kernelWeylGroup χ := by
        rw [hw₁]
        exact mul_mem (rootReflection_mem_kernelWeylGroup hβk) hwmem
      have hsub : ∀ γ ∈ invertedRootsOf w₁,
          γ ∈ invertedRootsOf w ∧ iform γ β = 0 ∧ γ ≠ β :=
        fun γ hγ => by
          obtain ⟨h1, h2, h3⟩ := invertedRoots_reflection_subset_general hww hβ hwβ
            (by rw [← hw₁]; exact hγ.2)
          exact ⟨⟨hγ.1, h1⟩, h2, h3⟩
      have hlt : (invertedRootsOf w₁ ∩ kernelRoots χ).ncard < n := by
        rw [← hn]
        refine Set.ncard_lt_ncard
          ⟨fun γ hγ => ⟨(hsub γ hγ.1).1, hγ.2⟩, fun h => ?_⟩ hfin
        exact (hsub β (h ⟨hβinv, hβk⟩).1).2.2 rfl
      obtain ⟨γs, hγs, hprod, hpair⟩ := ih _ hlt w₁ hw₁mem hw₁2 rfl
      have hγw : ∀ γ ∈ γs, γ ∈ invertedRootsOf w ∧ iform γ β = 0 ∧ γ ≠ β := by
        intro γ hγ
        exact hsub γ ⟨(hγs γ hγ).1.1, (hγs γ hγ).2⟩
      refine ⟨β :: γs, ?_, ?_, ?_⟩
      · intro γ hγ
        rcases List.mem_cons.1 hγ with rfl | hγ
        · exact ⟨hβk, hwβ⟩
        · exact ⟨(hγs γ hγ).1, (hγw γ hγ).1.2⟩
      · rw [List.map_cons, List.prod_cons, ← hprod, hw₁, ← mul_assoc,
          rootReflection_mul_self hβ, one_mul]
      · refine List.Pairwise.cons (fun γ hγ => ?_) hpair
        obtain ⟨hγinv, h0, -⟩ := hγw γ hγ
        have hγk : γ ∈ kernelRoots χ := (hγs γ hγ).1
        have hγr : IsRoot τ γ := hγk.1
        have hwγ : w • γ = -γ := hγinv.2
        have h0' : iform β γ = 0 := by rw [iform_comm]; exact h0
        obtain ⟨hn1, hn2⟩ := hnormsum β γ h0'
        have hγpos := iform_self_pos_of_isRoot hγr
        refine ⟨h0', fun hr => ?_, fun hr => ?_⟩
        · have hk : β + γ ∈ kernelRoots χ :=
            ⟨hr, by rw [ofAdd_add, map_mul, hβk.2, hγk.2, mul_one]⟩
          have hinv : β + γ ∈ invertedRootsOf w :=
            ⟨hr, by rw [smul_add, hwβ, hwγ, neg_add]⟩
          have hle := hmax _ ⟨hinv, hk⟩
          rw [hn1] at hle
          omega
        · have hk : β - γ ∈ kernelRoots χ :=
            ⟨hr, by rw [ofAdd_sub, map_div, hβk.2, hγk.2, div_one]⟩
          have hinv : β - γ ∈ invertedRootsOf w :=
            ⟨hr, by rw [smul_sub, hwβ, hwγ, neg_sub_neg, neg_sub]⟩
          have hle := hmax _ ⟨hinv, hk⟩
          rw [hn2] at hle
          omega
  obtain ⟨βs, hβs, hprod, hpair⟩ := claim _ w hw (by rw [← sq]; exact h2) rfl
  exact ⟨βs, fun β hβ => (hβs β hβ).1, hpair, hprod⟩


variable (τ) in
theorem monomialToralAt_two : MonomialToralAt τ 2 := by
  intro L _ _ hL M _ χ n hn hw h2
  obtain ⟨βs, hβs, hpair, hprod⟩ :=
    exists_strOrth_kernelRoots_of_sq_eq_one (M := M) (χ := χ)
      (w := weylQuotientHom τ L ⟨n, hn⟩) hw h2
  obtain ⟨g, hg, hgn⟩ := exists_conj_mem_torusGroup_of_pairwise (K := L) hL βs
    (fun β hβ => (hβs β hβ).1) hpair n hn hprod
  refine ⟨g, ?_, hgn⟩
  refine (Subgroup.closure_le _).2 ?_ hg
  rintro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨β, hβ, hx⟩ := hx
  have hβk : β ∈ kernelRoots χ := hβs β hβ
  have hnegk : -β ∈ kernelRoots χ :=
    ⟨IsRoot.neg hβk.1, by rw [ofAdd_neg, map_inv, hβk.2, inv_one]⟩
  have hle : rootRankOneGroup τ L β ≤ rootSpan τ L (kernelRoots χ) := by
    rw [(exceptional_Lang_root_rank_one_torus_transport τ L hβk.1).1]
    exact sup_le (le_iSup₂_of_le β hβk le_rfl) (le_iSup₂_of_le (-β) hnegk le_rfl)
  exact hle hx

end CFSG.HardMathSupport.Timmesfeld.CrossChar
