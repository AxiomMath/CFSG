module

public import CFSG.CGT.Timmesfeld75.Sec5Four

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

variable {G : Type} [Group G] [Finite G] {T T₁ : Subgroup G}

theorem exists_mem_hSub_conj_mul (hP : MaxPair T T₁) (hS : Sec3Global T) {g : G}
    (hg : g ∈ Subgroup.normalizer (T : Set G)) {z u : G} (hz : z ∈ T)
    (hzg : z ∉ conjSubgroup g (normIn T T₁)) (hu : u ∈ conjSubgroup g (normIn T T₁)) :
    ∃ l ∈ hSub T (normIn T₁ T), l * z * l⁻¹ = z * u := by
  have hs := hP.sec3_conj hS hg
  have hzM := not_mem_cfgM_of_not_mem_conj hP hS hg hz hzg
  have hu' : u ∈ normIn T (conjSubgroup g T₁) := by
    rwa [normIn_conjSubgroup_of_mem_normalizer hg]
  obtain ⟨l, hl, hlz⟩ := hs.exists_mem_normIn₁_conj_eq hz hzM hu'
  refine ⟨l, ?_, hlz⟩
  have hTg : conjSubgroup g T = T := mem_normalizer_iff_conjSubgroup_eq.1 hg
  have h1 := normIn_conj g T₁ T
  rw [hTg] at h1
  rw [h1] at hl
  exact Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem g (Subgroup.mem_iSup_of_mem hg hl))

theorem exists_mem_conj_not_mem {h g : G} {x : G} (hxg : x ∈ conjSubgroup g (normIn T T₁))
    (hxh : x ∉ conjSubgroup h (normIn T T₁)) :
    ∃ u ∈ conjSubgroup h (normIn T T₁), u ∉ conjSubgroup g (normIn T T₁) := by
  by_contra hcon
  push Not at hcon
  have hle : conjSubgroup h (normIn T T₁) ≤ conjSubgroup g (normIn T T₁) := fun u hu => hcon u hu
  have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSubgroup, card_conjSubgroup])
  exact hxh (heq ▸ hxg)

theorem secA_transitive_hSub (hTO : CFSG.Timmesfeld.Bridge.Asc72.TheoremOne)
    (hBW : BenderWCInput) [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hP : MaxPair T T₁) (hS : Sec3Global T) {x y : G} (hx : x ∈ T) (hxA : x ∉ secA T T₁)
    (hy : y ∈ T) (hyA : y ∉ secA T T₁) :
    ∃ h ∈ hSub T (normIn T₁ T), h * x * h⁻¹ = y := by
  set N := Subgroup.normalizer (T : Set G) with hN
  set L := normIn T T₁ with hL
  set H := hSub T (normIn T₁ T) with hH
  have symm : ∀ {a b : G}, (∃ h ∈ H, h * a * h⁻¹ = b) → ∃ h ∈ H, h * b * h⁻¹ = a := by
    rintro a b ⟨h, hh, rfl⟩
    exact ⟨h⁻¹, H.inv_mem hh, by group⟩
  have trans : ∀ {a b c : G}, (∃ h ∈ H, h * a * h⁻¹ = b) → (∃ h ∈ H, h * b * h⁻¹ = c) →
      ∃ h ∈ H, h * a * h⁻¹ = c := by
    rintro a b c ⟨h₁, hh₁, rfl⟩ ⟨h₂, hh₂, rfl⟩
    exact ⟨h₂ * h₁, H.mul_mem hh₂ hh₁, by group⟩
  have hAne : secA T T₁ ≠ L := secA_ne_normIn hTO hBW hnab hP hS
  have hex : ∀ z ∈ T, z ∉ secA T T₁ → ∃ g ∈ N, z ∈ conjSubgroup g L := by
    intro z hz hzA
    obtain ⟨y₀, hy₀L, hy₀A⟩ : ∃ y₀ ∈ L, y₀ ∉ secA T T₁ := by
      by_contra hcon
      push Not at hcon
      exact hAne (le_antisymm secA_le_normIn hcon)
    obtain ⟨k, hk, hky⟩ := secA_transitive hP hS (normIn_le _ _ hy₀L) hy₀A hz hzA
    exact ⟨k, hk, hky ▸ ⟨y₀, hy₀L, rfl⟩⟩
  have key : ∀ a b : G, a ∈ T → a ∉ secA T T₁ → b ∈ T → b ∉ secA T T₁ →
      (∀ h ∈ N, b ∈ conjSubgroup h L → a ∈ conjSubgroup h L) → ∃ h ∈ H, h * a * h⁻¹ = b := by
    intro a b ha haA hb hbA hcase
    obtain ⟨g, hg, hbg⟩ := hex b hb hbA
    have hag : a ∈ conjSubgroup g L := hcase g hg hbg
    obtain ⟨h, hh, hah⟩ : ∃ h ∈ N, a ∉ conjSubgroup h L := by
      by_contra hcon
      push Not at hcon
      exact haA (mem_secA.2 hcon)
    have hbh : b ∉ conjSubgroup h L := fun hb' => hah (hcase h hh hb')
    obtain ⟨u, huh, hug⟩ := exists_mem_conj_not_mem hag hah
    have huT : u ∈ T := by
      have h1 : conjSubgroup h L ≤ conjSubgroup h T := conjSubgroup_mono (normIn_le T T₁)
      rw [mem_normalizer_iff_conjSubgroup_eq.1 hh] at h1
      exact h1 huh
    have haa : a * a = 1 := elemAbelian_mul_self hP.wc.1 ha
    have hbb : b * b = 1 := elemAbelian_mul_self hP.wc.1 hb
    have hau : a * u ∉ conjSubgroup g L := by
      intro h'
      apply hug
      have := (conjSubgroup g L).mul_mem ((conjSubgroup g L).inv_mem hag) h'
      simpa using this
    have hbu : b * u ∉ conjSubgroup g L := by
      intro h'
      apply hug
      have := (conjSubgroup g L).mul_mem ((conjSubgroup g L).inv_mem hbg) h'
      simpa using this
    obtain ⟨l₁, hl₁, hl₁a⟩ := exists_mem_hSub_conj_mul hP hS hh ha hah huh
    obtain ⟨l₂, hl₂, hl₂b⟩ := exists_mem_hSub_conj_mul hP hS hh hb hbh huh
    obtain ⟨l₃, hl₃, hl₃a⟩ := exists_mem_hSub_conj_mul hP hS hg (T.mul_mem ha huT) hau hag
    obtain ⟨l₄, hl₄, hl₄b⟩ := exists_mem_hSub_conj_mul hP hS hg (T.mul_mem hb huT) hbu hbg
    have hua : (a * u) * a = u := by
      rw [elemAbelian_mul_comm hP.wc.1 ha huT, mul_assoc, haa, mul_one]
    have hub : (b * u) * b = u := by
      rw [elemAbelian_mul_comm hP.wc.1 hb huT, mul_assoc, hbb, mul_one]
    have hau' : ∃ h ∈ H, h * a * h⁻¹ = u :=
      trans ⟨l₁, hl₁, hl₁a⟩ ⟨l₃, hl₃, by rw [hl₃a, hua]⟩
    have hbu' : ∃ h ∈ H, h * b * h⁻¹ = u :=
      trans ⟨l₂, hl₂, hl₂b⟩ ⟨l₄, hl₄, by rw [hl₄b, hub]⟩
    exact trans hau' (symm hbu')
  by_cases hA : (∃ h ∈ N, x ∉ conjSubgroup h L ∧ y ∈ conjSubgroup h L) ∧
      (∃ h ∈ N, y ∉ conjSubgroup h L ∧ x ∈ conjSubgroup h L)
  · obtain ⟨⟨h, hh, hxh, hyh⟩, ⟨h', hh', hyh', hxh'⟩⟩ := hA
    obtain ⟨l₁, hl₁, hl₁x⟩ := exists_mem_hSub_conj_mul hP hS hh hx hxh hyh
    obtain ⟨l₂, hl₂, hl₂y⟩ := exists_mem_hSub_conj_mul hP hS hh' hy hyh' hxh'
    have hcomm : y * x = x * y := elemAbelian_mul_comm hP.wc.1 hy hx
    rw [hcomm] at hl₂y
    exact trans ⟨l₁, hl₁, hl₁x⟩ (symm ⟨l₂, hl₂, hl₂y⟩)
  · rw [not_and_or] at hA
    rcases hA with hA | hA
    · refine key x y hx hxA hy hyA fun h hh hyh => ?_
      by_contra hxh
      exact hA ⟨h, hh, hxh, hyh⟩
    · have := key y x hy hyA hx hxA fun h hh hxh => by
        by_contra hyh
        exact hA ⟨h, hh, hyh, hxh⟩
      exact symm this

end CFSG.CGT.Timmesfeld75
