module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwConjFinCheck
public import CFSG.LieType.SeitzGeneration.ExcWideThree.ConjFin

public section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.SeitzGeneration.ExcWideThree

section Soundness


theorem exists_lift_of_trWit (w : WeylGroup Tag.E6) {κs : List (List ℕ)}
    (hκs : ∀ κ ∈ κs, κ.length = Tag.E6.rank)
    (h : trWit κs ((rfCols w).map (·.map rfRes3)) = true) :
    ∃ κ ∈ κs, ∃ m : Fin Tag.E6.rank → ℤ,
      (∀ j : Fin Tag.E6.rank, (3 : ℤ) ∣ (∑ l, Tag.E6.cartan l j * m l) - (κ.getD j 0 : ℤ)) ∧
      ¬ ∀ i, (3 : ℤ) ∣ (w • m) i - m i := by
  unfold trWit at h
  rw [List.any_eq_true] at h
  obtain ⟨κ, hκ, hκh⟩ := h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hκh
  obtain ⟨hA, hne⟩ := hκh
  set mL := rfMOf κ with hmL
  have hmlen : mL.length = Tag.E6.rank := rfMOf_length κ
  have hmcast := rf_map_cast_eq_ofFn mL hmlen
  refine ⟨κ, hκ, fun l => ((mL.getD l 0 : ℕ) : ℤ), ?_, ?_⟩
  · intro j
    have hlen : (rfCartanMod3.map fun row => rfDotN row mL).length = κ.length := by
      rw [hκs κ hκ]; simp [rfCartanMod3]; rfl
    have h1 := (rfModEq3_iff _ _ hlen).1 hA j
    have hrow : (rfCartanMod3.map fun row => rfDotN row mL).getD j 0 =
        rfDotN ((List.ofFn (fun l : Fin Tag.E6.rank => Tag.E6.cartan j l)).map rfRes3) mL := by
      rw [rfCartanMod3_eq, rfCartanL_eq, List.map_ofFn, List.map_ofFn, List.getD_eq_getElem?_getD]
      simp [List.getElem?_ofFn]
    rw [hrow] at h1
    rw [rfDotN_comm (List.map rfRes3 _) mL] at h1
    have h2 := rfDotN_res3 mL (List.ofFn fun l : Fin Tag.E6.rank => Tag.E6.cartan j l)
    rw [hmcast, rfDotL_ofFn] at h2
    have h3 : ∑ l : Fin Tag.E6.rank, ((mL.getD (l : ℕ) 0 : ℕ) : ℤ) * Tag.E6.cartan j l =
        ∑ l : Fin Tag.E6.rank, Tag.E6.cartan l j * ((mL.getD (l : ℕ) 0 : ℕ) : ℤ) :=
      Finset.sum_congr rfl fun l _ => by rw [mul_comm (Tag.E6.cartan l j), rf_cartan_symm l j]
    rw [h3] at h2
    show (3 : ℤ) ∣ ∑ l : Fin Tag.E6.rank, Tag.E6.cartan l j * ((mL.getD (l : ℕ) 0 : ℕ) : ℤ) -
      ((κ.getD (j : ℕ) 0 : ℕ) : ℤ)
    omega
  · intro hall'
    have hmod : rfModEq3 (rfLincomb3 mL ((rfCols w).map (·.map rfRes3))) mL = true := by
      rw [rfModEq3_iff _ _ (by
        rw [hmlen]; simp [rfLincomb3]; rfl)]
      intro i
      by_cases hi : i < 6
      · have h2 := rfLincomb3_getD_cast mL (rfCols w) i hi
        have hrow := rf_cols_row w ⟨i, hi⟩
        rw [hmcast, hrow, rfDotL_ofFn] at h2
        have h3 : ∑ j : Fin Tag.E6.rank, ((mL.getD (j : ℕ) 0 : ℕ) : ℤ) *
            (w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) ⟨i, hi⟩ =
            (w • fun l : Fin Tag.E6.rank => ((mL.getD (l : ℕ) 0 : ℕ) : ℤ)) ⟨i, hi⟩ :=
          (rf_smul_apply w _ ⟨i, hi⟩).symm
        rw [h3] at h2
        have h4 := hall' ⟨i, hi⟩
        change (3 : ℤ) ∣ (w • fun l : Fin Tag.E6.rank => ((mL.getD (l : ℕ) 0 : ℕ) : ℤ)) ⟨i, hi⟩ -
          ((mL.getD i 0 : ℕ) : ℤ) at h4
        omega
      · have h6 : ¬ i < mL.length := by rw [hmlen]; exact hi
        have hr : ¬ i < (rfLincomb3 mL ((rfCols w).map (·.map rfRes3))).length := by
          simp [rfLincomb3]; omega
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.1 h6),
          List.getElem?_eq_none (not_lt.1 hr)]
    rw [hmod] at hne
    exact Bool.noConfusion hne

theorem tw_regular_elliptic_conj (w : WeylGroup Tag.E6) (k₁ k₂ : Fin Tag.E6.rank → ℕ)
    (hreg : ∀ α : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 α →
      ¬ ((3 : ℤ) ∣ ∑ i, α i * (k₁ i : ℤ) ∧ (3 : ℤ) ∣ ∑ i, α i * (k₂ i : ℤ)))
    (hfix₁ : ∀ t : Fin Tag.E6.rank, (3 : ℤ) ∣
      (∑ i, (k₁ i : ℤ) * (w • (Pi.single t 1 : Fin Tag.E6.rank → ℤ)) i) - (k₁ t : ℤ))
    (hfix₂ : ∀ t : Fin Tag.E6.rank, (3 : ℤ) ∣
      (∑ i, (k₂ i : ℤ) * (w • (Pi.single t 1 : Fin Tag.E6.rank → ℤ)) i) - (k₂ t : ℤ)) :
    ∃ ω : List (Fin Tag.E6.rank),
      InvFixedZ ((coxeterSystem Tag.E6).wordProd ω) (fun j => (k₁ j : ℤ)) ∧
      InvFixedZ ((coxeterSystem Tag.E6).wordProd ω) (fun j => (k₂ j : ℤ)) ∧
      (weylTwist TwistTag.E6 ((coxeterSystem Tag.E6).wordProd ω * w *
            ((coxeterSystem Tag.E6).wordProd ω)⁻¹) =
          (coxeterSystem Tag.E6).wordProd ω * w * ((coxeterSystem Tag.E6).wordProd ω)⁻¹ ∨
        ∃ (a b : ℕ) (m : Fin Tag.E6.rank → ℤ),
          (∀ j : Fin Tag.E6.rank, (3 : ℤ) ∣ (∑ l, Tag.E6.cartan l j * m l) -
            ((a : ℤ) * (k₁ j : ℤ) + (b : ℤ) * (k₂ j : ℤ))) ∧
          ¬ ∀ i, (3 : ℤ) ∣ (w • m) i - m i) := by
  classical
  set K₁ : List ℕ := List.ofFn fun i : Fin Tag.E6.rank => k₁ i % 3 with hK₁
  set K₂ : List ℕ := List.ofFn fun i : Fin Tag.E6.rank => k₂ i % 3 with hK₂
  have hK₁len : K₁.length = Tag.E6.rank := by simp [hK₁]
  have hK₂len : K₂.length = Tag.E6.rank := by simp [hK₂]
  have hK₁3 : ∀ x ∈ K₁, x < 3 := by
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
    exact Nat.mod_lt _ (by norm_num)
  have hK₂3 : ∀ x ∈ K₂, x < 3 := by
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
    exact Nat.mod_lt _ (by norm_num)
  have hf₁ : RfFixes w K₁ := rfFixes_of_fin w k₁ hfix₁
  have hf₂ : RfFixes w K₂ := rfFixes_of_fin w k₂ hfix₂
  have hregpos : ∀ a ∈ posRoots e6ArtifactRoots,
      ¬ (rootDot a K₁ % 3 = 0 ∧ rootDot a K₂ % 3 = 0) := by
    rintro a ha ⟨h1, h2⟩
    have haA : a ∈ e6ArtifactRoots := (List.mem_filter.1 ha).1
    have hal : a.length = Tag.E6.rank := length_of_mem_artifactRoots (τ := Tag.E6) haA
    have hα : List.ofFn (fun i : Fin Tag.E6.rank => a.getD (i : ℕ) 0) = a := rf_ofFn_getD a hal
    have hroot : IsRoot Tag.E6 (fun i : Fin Tag.E6.rank => a.getD (i : ℕ) 0) :=
      isRoot_iff_mem_artifactRoots.2 (by rw [hα]; exact haA)
    rw [← hα, hK₁, rootDot_ofFn] at h1
    rw [← hα, hK₂, rootDot_ofFn] at h2
    exact hreg _ hroot ⟨three_dvd_sum_of_mod _ k₁ h1, three_dvd_sum_of_mod _ k₂ h2⟩
  obtain ⟨p, hp, hpe⟩ := rfCover_sound hK₁len hK₂len hK₁3 hK₂3 hregpos
  obtain ⟨hp1, hp2, hp13, hp23⟩ := rfPlaneBases_wf p hp
  have hr6 : Tag.E6.rank = 6 := rfl
  have hl₁₂ : K₁.length = K₂.length := by rw [hK₁len, hK₂len]
  have hlp : p.1.length = p.2.length := by rw [hp1, hp2]
  have hp1' : p.1.length = Tag.E6.rank := hp1.trans hr6.symm
  have hp2' : p.2.length = Tag.E6.rank := hp2.trans hr6.symm
  have hbitK : ∀ (v : List ℕ) (a b : ℕ), a < 3 → b < 3 → comb a b K₁ K₂ = v →
      Nat.testBit (planeBits K₁ K₂) (vecIdx v) = true := by
    intro v a b ha hb hv
    exact (planeBits_spec hl₁₂ (by rw [← hv, length_comb hl₁₂]) (by rw [← hv]; exact comb_lt)).2
      ⟨a, b, ha, hb, hv⟩
  have hbitP : ∀ (v : List ℕ) (a b : ℕ), a < 3 → b < 3 → comb a b p.1 p.2 = v →
      Nat.testBit (planeBits p.1 p.2) (vecIdx v) = true := by
    intro v a b ha hb hv
    exact (planeBits_spec hlp (by rw [← hv, length_comb hlp]) (by rw [← hv]; exact comb_lt)).2
      ⟨a, b, ha, hb, hv⟩
  have hK₁ab : ∃ a b, a < 3 ∧ b < 3 ∧ comb a b p.1 p.2 = K₁ := by
    have h := hbitK K₁ 1 0 (by norm_num) (by norm_num) (rf_comb_one_zero K₁ K₂ hl₁₂ hK₁3)
    rw [← hpe] at h
    exact (planeBits_spec hlp (hK₁len.trans (hr6.trans hp1.symm)) hK₁3).1 h
  have hK₂ab : ∃ a b, a < 3 ∧ b < 3 ∧ comb a b p.1 p.2 = K₂ := by
    have h := hbitK K₂ 0 1 (by norm_num) (by norm_num) (rf_comb_zero_one K₁ K₂ hl₁₂ hK₂3)
    rw [← hpe] at h
    exact (planeBits_spec hlp (hK₂len.trans (hr6.trans hp1.symm)) hK₂3).1 h
  have hp1K : ∃ a b, a < 3 ∧ b < 3 ∧ comb a b K₁ K₂ = p.1 := by
    have h := hbitP p.1 1 0 (by norm_num) (by norm_num) (rf_comb_one_zero p.1 p.2 hlp hp13)
    rw [hpe] at h
    exact (planeBits_spec hl₁₂ (hp1.trans (hr6.trans hK₁len.symm)) hp13).1 h
  have hp2K : ∃ a b, a < 3 ∧ b < 3 ∧ comb a b K₁ K₂ = p.2 := by
    have h := hbitP p.2 0 1 (by norm_num) (by norm_num) (rf_comb_zero_one p.1 p.2 hlp hp23)
    rw [hpe] at h
    exact (planeBits_spec hl₁₂ (hp2.trans (hr6.trans hK₁len.symm)) hp23).1 h
  have hfp1 : RfFixes w p.1 := by
    obtain ⟨a, b, -, -, hab⟩ := hp1K
    rw [← hab]
    exact rfFixes_comb w hK₁len hK₂len a b hf₁ hf₂
  have hfp2 : RfFixes w p.2 := by
    obtain ⟨a, b, -, -, hab⟩ := hp2K
    rw [← hab]
    exact rfFixes_comb w hK₁len hK₂len a b hf₁ hf₂

  obtain ⟨t, ht, hte⟩ : ∃ t ∈ rfHTable, (t.1, t.2.1) = p := by
    have hmem : p ∈ rfHTable.map (fun t => (t.1, t.2.1)) := by
      rw [rfHTable_planes]
      exact hp
    obtain ⟨t, ht, hte⟩ := List.mem_map.1 hmem
    exact ⟨t, ht, hte⟩
  have hchk := List.all_eq_true.1 rfHPlanes_true t ht
  have hchk2 := List.all_eq_true.1 trHPlanes_true t ht
  have ht1 : t.1 = p.1 := congrArg Prod.fst hte
  have ht2 : t.2.1 = p.2 := congrArg Prod.snd hte
  rw [ht1, ht2] at hchk hchk2
  obtain ⟨ω, hω⟩ := exists_fin_word t.2.2 (rfHTable_words_lt t ht)
  unfold rfHPlaneCheck at hchk
  simp only [Bool.and_eq_true] at hchk
  obtain ⟨⟨hinv1, hinv2⟩, -⟩ := hchk
  unfold trHPlaneCheck at hchk2
  have hmem := mem_rfLeaves ((List.range 6).map (rfCands p.1 p.2)) (rfCols w) []
    (rfCols_validFrom w hp1' hp2' hfp1 hfp2)
  have hcl : (rfCols w).length = 6 := by
    unfold rfCols; rw [List.length_ofFn]; rfl
  rw [List.nil_append, hcl] at hmem
  have hok := List.all_eq_true.1 hchk2 _ hmem
  unfold trLeafOK at hok
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hok
  rw [← hω] at hinv1 hinv2 hok
  have hI1 := invFixedZ_of_rfInvFix ω hp1' hinv1
  have hI2 := invFixedZ_of_rfInvFix ω hp2' hinv2
  have hmodK : ∀ (k : Fin Tag.E6.rank → ℕ) (a b : ℕ),
      (comb a b p.1 p.2 = List.ofFn fun i : Fin Tag.E6.rank => k i % 3) →
      InvFixedZ ((coxeterSystem Tag.E6).wordProd ω) (fun j => (k j : ℤ)) := by
    intro k a b hab
    refine (InvFixedZ.lin (v := (coxeterSystem Tag.E6).wordProd ω) (a : ℤ) (b : ℤ) hI1 hI2).congr
      (fun j => ?_)
    have h1 := rfFx_getD_comb a b p.1 p.2 hlp (j : ℕ)
    rw [hab, rfFx_getD_ofFn k j] at h1
    show (3 : ℤ) ∣ ((a : ℤ) * ((p.1.getD (j : ℕ) 0 : ℕ) : ℤ) +
      (b : ℤ) * ((p.2.getD (j : ℕ) 0 : ℕ) : ℤ)) - (k j : ℤ)
    omega
  refine ⟨ω, ?_, ?_, ?_⟩
  · obtain ⟨a, b, -, -, hab⟩ := hK₁ab
    exact hmodK k₁ a b hab
  · obtain ⟨a, b, -, -, hab⟩ := hK₂ab
    exact hmodK k₂ a b hab
  · rcases hok with (hc | hcomm) | hwit
    · exact absurd (rfCCond_rfCols w) (by simp [hc])
    · left
      exact weylTwist_eq_of_rfRhoComm _ (by rw [← rfConjCols_eq ω w]; exact hcomm)
    · right
      have hκs : ∀ κ ∈ rfPlaneVecs p.1 p.2, κ.length = Tag.E6.rank := by
        intro κ hκ
        unfold rfPlaneVecs at hκ
        simp only [List.mem_flatMap, List.mem_map, List.mem_range] at hκ
        obtain ⟨a, -, b, -, rfl⟩ := hκ
        rw [length_comb hlp, hp1']
      obtain ⟨κ, hκ, m, hm1, hm2⟩ := exists_lift_of_trWit w hκs hwit
      unfold rfPlaneVecs at hκ
      simp only [List.mem_flatMap, List.mem_map, List.mem_range] at hκ
      obtain ⟨a, ha, b, hb, hκab⟩ := hκ
      have hbit : Nat.testBit (planeBits p.1 p.2) (vecIdx κ) = true := by
        rw [← hκab]
        exact hbitP _ a b ha hb rfl
      rw [hpe] at hbit
      have hκlen : κ.length = K₁.length := by rw [hκs κ (by
        unfold rfPlaneVecs
        simp only [List.mem_flatMap, List.mem_map, List.mem_range]
        exact ⟨a, ha, b, hb, hκab⟩), hK₁len]
      have hκ3 : ∀ x ∈ κ, x < 3 := by
        rw [← hκab]
        exact comb_lt
      obtain ⟨a', b', ha', hb', hκ'⟩ := (planeBits_spec hl₁₂ hκlen hκ3).1 hbit
      refine ⟨a', b', m, fun j => ?_, hm2⟩
      have h1 := hm1 j
      have h2 := rfFx_getD_comb a' b' K₁ K₂ hl₁₂ (j : ℕ)
      rw [hκ'] at h2
      have h3 := rfFx_getD_ofFn k₁ j
      have h4 := rfFx_getD_ofFn k₂ j
      simp only [hK₁, hK₂] at h2
      rw [h3, h4] at h2
      interval_cases a' <;> interval_cases b' <;> omega

end Soundness

end CFSG.LieType.SeitzGeneration.ExcHighThree
