module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.DiagFinFixes
public import CFSG.LieType.SeitzGeneration.ExcWideThree.DiagFinCover

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.SeitzGeneration.ExcHighThree

section Main


theorem rfPlaneBases_wf : ∀ p ∈ rfPlaneBases, p.1.length = 6 ∧ p.2.length = 6 ∧
    (∀ x ∈ p.1, x < 3) ∧ (∀ x ∈ p.2, x < 3) := by
  decide +kernel

theorem rf_comb_one_zero : ∀ (x y : List ℕ), x.length = y.length → (∀ a ∈ x, a < 3) →
    comb 1 0 x y = x
  | [], [], _, _ => rfl
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl
  | a :: x, b :: y, hl, h3 => by
    have ha : a < 3 := h3 a (by simp)
    have hx : ∀ c ∈ x, c < 3 := fun c hc => h3 c (by simp [hc])
    have hl' : x.length = y.length := by simpa using hl
    have ih := rf_comb_one_zero x y hl' hx
    simp only [comb] at ih ⊢
    rw [List.zipWith_cons_cons, ih]
    congr 1
    omega

theorem rf_comb_zero_one : ∀ (x y : List ℕ), x.length = y.length → (∀ a ∈ y, a < 3) →
    comb 0 1 x y = y
  | [], [], _, _ => rfl
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl
  | a :: x, b :: y, hl, h3 => by
    have hb : b < 3 := h3 b (by simp)
    have hy : ∀ c ∈ y, c < 3 := fun c hc => h3 c (by simp [hc])
    have hl' : x.length = y.length := by simpa using hl
    have ih := rf_comb_zero_one x y hl' hy
    simp only [comb] at ih ⊢
    rw [List.zipWith_cons_cons, ih]
    congr 1
    omega

theorem mem_rfPlaneVecs_of_comb {k₁ k₂ v : List ℕ} {a b : ℕ} (ha : a < 3) (hb : b < 3)
    (h : comb a b k₁ k₂ = v) : v ∈ rfPlaneVecs k₁ k₂ := by
  unfold rfPlaneVecs
  rw [List.mem_flatMap]
  exact ⟨a, List.mem_range.2 ha, List.mem_map.2 ⟨b, List.mem_range.2 hb, h⟩⟩

theorem e6_regular_dichotomy (w : WeylGroup Tag.E6) (k₁ k₂ : Fin Tag.E6.rank → ℕ)
    (hreg : ∀ α : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 α →
      ¬ ((3 : ℤ) ∣ ∑ i, α i * (k₁ i : ℤ) ∧ (3 : ℤ) ∣ ∑ i, α i * (k₂ i : ℤ)))
    (hfix₁ : ∀ t : Fin Tag.E6.rank, (3 : ℤ) ∣
      (∑ i, (k₁ i : ℤ) * (w • (Pi.single t 1 : Fin Tag.E6.rank → ℤ)) i) - (k₁ t : ℤ))
    (hfix₂ : ∀ t : Fin Tag.E6.rank, (3 : ℤ) ∣
      (∑ i, (k₂ i : ℤ) * (w • (Pi.single t 1 : Fin Tag.E6.rank → ℤ)) i) - (k₂ t : ℤ)) :
    (∃ l : Fin Tag.E6.rank → ℤ, l ≠ 0 ∧
        ∀ v : Fin Tag.E6.rank → ℤ, ∑ i, l i * (w • v) i = ∑ i, l i * v i) ∨
      ∃ m₁ m₂ : Fin Tag.E6.rank → ℤ,
        (∀ j, (3 : ℤ) ∣ (∑ l, Tag.E6.cartan l j * m₁ l) - (k₁ j : ℤ)) ∧
        (∀ j, (3 : ℤ) ∣ (∑ l, Tag.E6.cartan l j * m₂ l) - (k₂ j : ℤ)) ∧
        (∀ i, (3 : ℤ) ∣ (w • m₁) i - m₁ i) ∧ (∀ i, (3 : ℤ) ∣ (w • m₂) i - m₂ i) := by
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
  have hK₁P : K₁ ∈ rfPlaneVecs p.1 p.2 := by
    have h := hbitK K₁ 1 0 (by norm_num) (by norm_num) (rf_comb_one_zero K₁ K₂ hl₁₂ hK₁3)
    rw [← hpe] at h
    obtain ⟨a, b, ha, hb, hab⟩ := (planeBits_spec hlp (hK₁len.trans (hr6.trans hp1.symm)) hK₁3).1 h
    exact mem_rfPlaneVecs_of_comb ha hb hab
  have hK₂P : K₂ ∈ rfPlaneVecs p.1 p.2 := by
    have h := hbitK K₂ 0 1 (by norm_num) (by norm_num) (rf_comb_zero_one K₁ K₂ hl₁₂ hK₂3)
    rw [← hpe] at h
    obtain ⟨a, b, ha, hb, hab⟩ := (planeBits_spec hlp (hK₂len.trans (hr6.trans hp1.symm)) hK₂3).1 h
    exact mem_rfPlaneVecs_of_comb ha hb hab
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
  have hchk : rfPlaneCheck p.1 p.2 = true := List.all_eq_true.1 rfPlanes_true p hp
  rcases rfPlaneCheck_sound w hp1 hp2 hfp1 hfp2 hchk with hfixed | hcls
  · exact Or.inl hfixed
  · right
    have hvecs : ∀ κ ∈ rfPlaneVecs p.1 p.2, κ.length = Tag.E6.rank := by
      intro κ hκ
      unfold rfPlaneVecs at hκ
      obtain ⟨a, -, hκ⟩ := List.mem_flatMap.1 hκ
      obtain ⟨b, -, rfl⟩ := List.mem_map.1 hκ
      rw [length_comb hlp, hp1]
      rfl
    have hlift := exists_lift_of_rfCls0 w hvecs hcls
    obtain ⟨m₁, hm₁, hw₁⟩ := hlift K₁ hK₁P
    obtain ⟨m₂, hm₂, hw₂⟩ := hlift K₂ hK₂P
    have hget : ∀ (k : Fin Tag.E6.rank → ℕ) (j : Fin Tag.E6.rank),
        (List.ofFn fun i : Fin Tag.E6.rank => k i % 3).getD (j : ℕ) 0 = k j % 3 := by
      intro k j
      simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    refine ⟨m₁, m₂, fun j => ?_, fun j => ?_, hw₁, hw₂⟩
    · have h := hm₁ j
      rw [hK₁, hget] at h
      omega
    · have h := hm₂ j
      rw [hK₂, hget] at h
      omega

end Main

end CFSG.LieType.SeitzGeneration.ExcWideThree
