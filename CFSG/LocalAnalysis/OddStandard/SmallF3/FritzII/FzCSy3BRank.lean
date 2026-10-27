module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCSy3BRankM
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCSy3BRankP

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {x₁ x₂ t a b c : G} {Wp F P M₂ M₃ U : Subgroup G}

private lemma fzc_sy3_mul_bc (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U)
    {f₁ f₂ : G} (hf₁ : f₁ ∈ F) (hf₂ : f₂ ∈ F) :
    ∃ f ∈ F, (f₁ * b) * (f₂ * c) = f * (b * c) := by
  have hbP : b ∈ P := by
    rw [hs.P_eq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
  have hbU : b ∈ U := hs.chain.2.2.1 hbP
  refine ⟨f₁ * (b * f₂ * b⁻¹), F.mul_mem hf₁ (hs.U_elem.2.2 b hbU f₂ hf₂), ?_⟩
  group

private lemma fzc_sy3_mul_bc_c (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U)
    {f₁ f₂ : G} (hf₁ : f₁ ∈ F) (hf₂ : f₂ ∈ F) :
    ∃ f ∈ F, (f₁ * (b * c)) * (f₂ * c) = f * b := by
  have hbP : b ∈ P := by
    rw [hs.P_eq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
  have hbU : b ∈ U := hs.chain.2.2.1 hbP
  have hcU : c ∈ U := by
    rw [hs.U_eq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
  have hbcU : b * c ∈ U := U.mul_mem hbU hcU
  have htF : t ∈ F := hs.chain.1 (by
    rw [hs.Wp_eq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
  refine ⟨f₁ * ((b * c) * f₂ * (b * c)⁻¹) * (b * t * b⁻¹),
    F.mul_mem (F.mul_mem hf₁ (hs.U_elem.2.2 (b * c) hbcU f₂ hf₂))
      (hs.U_elem.2.2 b hbU t htF), ?_⟩
  have hc2 : c * c = t := by simpa [pow_two] using hs.c_sq
  calc (f₁ * (b * c)) * (f₂ * c)
      = (f₁ * ((b * c) * f₂ * (b * c)⁻¹) * (b * (c * c) * b⁻¹)) * b := by group
    _ = (f₁ * ((b * c) * f₂ * (b * c)⁻¹) * (b * t * b⁻¹)) * b := by rw [hc2]

private lemma fzc_sy3_coset_U (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) {g : G}
    (hg : g ∈ U) : g ∈ F ∨ (∃ f ∈ F, g = f * b) ∨ (∃ f ∈ F, g = f * c) ∨
      (∃ f ∈ F, g = f * (b * c)) := by
  obtain ⟨p, hpP, hg | hg⟩ := (hs.U_mem).1 hg
  · obtain ⟨f, hfF, hp | hp⟩ := (hs.P_mem).1 hpP
    · exact Or.inl (by rw [hg, hp]; exact hfF)
    · exact Or.inr (Or.inl ⟨f, hfF, by rw [hg, hp]⟩)
  · obtain ⟨f, hfF, hp | hp⟩ := (hs.P_mem).1 hpP
    · exact Or.inr (Or.inr (Or.inl ⟨f, hfF, by rw [hg, hp]⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨f, hfF, by rw [hg, hp]; group⟩))

private lemma fzc_sy3_coset_notP (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) {g : G}
    (hgU : g ∈ U) (hgP : g ∉ P) :
    (∃ f ∈ F, g = f * c) ∨ (∃ f ∈ F, g = f * (b * c)) := by
  have hFP : F ≤ P := hs.chain.2.1
  have hbP : b ∈ P := by
    rw [hs.P_eq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
  rcases fzc_sy3_coset_U hs hgU with hgF | ⟨f, hfF, hgb⟩ | ⟨f, hfF, hgc⟩ | ⟨f, hfF, hgbc⟩
  · exact absurd (hFP hgF) hgP
  · exact absurd (by rw [hgb]; exact P.mul_mem (hFP hfF) hbP) hgP
  · exact Or.inl ⟨f, hfF, hgc⟩
  · exact Or.inr ⟨f, hfF, hgbc⟩

private lemma fzc_sy3_coset_notM₂ (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) {g : G}
    (hgU : g ∈ U) (hgM₂ : g ∉ M₂) :
    (∃ f ∈ F, g = f * b) ∨ (∃ f ∈ F, g = f * (b * c)) := by
  have hFM₂ : F ≤ M₂ := hs.chain.2.2.2.1
  have hcM₂ : c ∈ M₂ := by
    rw [hs.M₂_eq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
  rcases fzc_sy3_coset_U hs hgU with hgF | ⟨f, hfF, hgb⟩ | ⟨f, hfF, hgc⟩ | ⟨f, hfF, hgbc⟩
  · exact absurd (hFM₂ hgF) hgM₂
  · exact Or.inl ⟨f, hfF, hgb⟩
  · exact absurd (by rw [hgc]; exact M₂.mul_mem (hFM₂ hfF) hcM₂) hgM₂
  · exact Or.inr ⟨f, hfF, hgbc⟩

private lemma fzc_sy3_coset_notM₃ (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) {g : G}
    (hgU : g ∈ U) (hgM₃ : g ∉ M₃) :
    (∃ f ∈ F, g = f * b) ∨ (∃ f ∈ F, g = f * c) := by
  have hFM₃ : F ≤ M₃ := hs.chain.2.2.2.2.2.1
  have hbcM₃ : b * c ∈ M₃ := by
    rw [hs.M₃_eq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers (b * c))
  rcases fzc_sy3_coset_U hs hgU with hgF | ⟨f, hfF, hgb⟩ | ⟨f, hfF, hgc⟩ | ⟨f, hfF, hgbc⟩
  · exact absurd (hFM₃ hgF) hgM₃
  · exact Or.inl ⟨f, hfF, hgb⟩
  · exact Or.inr ⟨f, hfF, hgc⟩
  · exact absurd (by rw [hgbc]; exact M₃.mul_mem (hFM₃ hfF) hbcM₃) hgM₃

theorem fzc_sy3_rank (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) : S4A.RankLE U 3 := by
  classical
  intro X hX
  obtain ⟨hWpF, hFP, hPU, hFM₂, hM₂U, hFM₃, hM₃U⟩ := hs.chain
  by_cases hXP : X ≤ P
  · exact fzc_sy3_rank_P hs X hXP
  by_cases hXM₂ : X ≤ M₂
  · exact fzc_sy3_rank_M₂ hs X hXM₂
  by_cases hXM₃ : X ≤ M₃
  · exact fzc_sy3_rank_M₃ hs X hXM₃
  obtain ⟨g₁, hg₁X, hg₁P⟩ := SetLike.not_le_iff_exists.mp hXP
  obtain ⟨g₂, hg₂X, hg₂M₂⟩ := SetLike.not_le_iff_exists.mp hXM₂
  obtain ⟨g₃, hg₃X, hg₃M₃⟩ := SetLike.not_le_iff_exists.mp hXM₃
  have hg₁U : g₁ ∈ U := hX hg₁X
  have hg₂U : g₂ ∈ U := hX hg₂X
  have hg₃U : g₃ ∈ U := hX hg₃X
  have hv : ∃ v ∈ X, ∃ f ∈ F, v = f * (b * c) := by
    rcases fzc_sy3_coset_notM₂ hs hg₂U hg₂M₂ with ⟨f₂, hf₂F, hg₂b⟩ | ⟨f₂, hf₂F, hg₂bc⟩
    · rcases fzc_sy3_coset_notP hs hg₁U hg₁P with ⟨f₁, hf₁F, hg₁c⟩ | ⟨f₁, hf₁F, hg₁bc⟩
      · obtain ⟨f, hfF, heq⟩ := fzc_sy3_mul_bc hs hf₂F hf₁F
        exact ⟨g₂ * g₁, X.mul_mem hg₂X hg₁X, f, hfF, by rw [hg₂b, hg₁c]; exact heq⟩
      · exact ⟨g₁, hg₁X, f₁, hf₁F, hg₁bc⟩
    · exact ⟨g₂, hg₂X, f₂, hf₂F, hg₂bc⟩
  obtain ⟨v, hvX, f_v, hf_vF, hv_eq⟩ := hv
  have hy : ∃ y ∈ X, ∃ f ∈ F, y = f * b := by
    rcases fzc_sy3_coset_notM₂ hs hg₂U hg₂M₂ with ⟨f₂, hf₂F, hg₂b⟩ | ⟨f₂, hf₂F, hg₂bc⟩
    · exact ⟨g₂, hg₂X, f₂, hf₂F, hg₂b⟩
    · rcases fzc_sy3_coset_notM₃ hs hg₃U hg₃M₃ with ⟨f₃, hf₃F, hg₃b⟩ | ⟨f₃, hf₃F, hg₃c⟩
      · exact ⟨g₃, hg₃X, f₃, hf₃F, hg₃b⟩
      · obtain ⟨f, hfF, heq⟩ := fzc_sy3_mul_bc_c hs hf₂F hf₃F
        exact ⟨g₂ * g₃, X.mul_mem hg₂X hg₃X, f, hfF, by rw [hg₂bc, hg₃c]; exact heq⟩
  obtain ⟨y, hyX, f_y, hf_yF, hy_eq⟩ := hy
  have hbP : b ∈ P := by
    rw [hs.P_eq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
  have hbU : b ∈ U := hPU hbP
  have htF : t ∈ F := hWpF (by
    rw [hs.Wp_eq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
  have hb2F : b ^ 2 ∈ F := by
    have h := hWpF (hs.E_le_Wp hs.b_sq)
    have h2 : b ^ 2 = (b ^ 2 * t) * t⁻¹ := by group
    rw [h2]
    exact F.mul_mem h (F.inv_mem htF)
  have hbcF : b * c ∉ F := by
    intro hbcF
    have hbF_bc : b * (b * c) * b⁻¹ ∈ F := hs.U_elem.2.2 b hbU (b * c) hbcF
    have hcFb : ∃ f ∈ F, c = f * b :=
      ⟨(b ^ 2)⁻¹ * (b * (b * c) * b⁻¹),
        F.mul_mem (F.inv_mem hb2F) hbF_bc, by group⟩
    obtain ⟨f, hfF, hfeq⟩ := hcFb
    exact hs.c_notin (hs.P_mem.mpr ⟨f, hfF, Or.inr hfeq⟩)
  have hvF : v ∉ F := by
    intro hvF
    apply hbcF
    have : b * c = f_v⁻¹ * v := by rw [hv_eq]; group
    rw [this]
    exact F.mul_mem (F.inv_mem hf_vF) hvF
  have hvM₃ : v ∈ M₃ := hs.M₃_mem.mpr ⟨f_v, hf_vF, Or.inr hv_eq⟩
  have hv2 := hs.M₃_sq v hvM₃ hvF
  have hyP : y ∈ P := hs.P_mem.mpr ⟨f_y, hf_yF, Or.inr hy_eq⟩
  have hyWp : y ∉ Wp := by
    intro hyWp
    apply hs.b_notin
    have : b = f_y⁻¹ * y := by rw [hy_eq]; group
    rw [this]
    exact F.mul_mem (F.inv_mem hf_yF) (hWpF hyWp)
  have hv2y : v ^ 2 * y⁻¹ ∉ Wp := by
    intro h
    apply hs.b_notin
    have hyF : y ∈ F := by
      have : y = (v ^ 2 * y⁻¹)⁻¹ * v ^ 2 := by group
      rw [this]
      exact F.mul_mem (F.inv_mem (hWpF h)) hv2.1
    have : b = f_y⁻¹ * y := by rw [hy_eq]; group
    rw [this]
    exact F.mul_mem (F.inv_mem hf_yF) hyF
  have hvP : v ∉ P := fun h => hv2.2 (hs.P_elem.1 v h)
  have hv2X : v ^ 2 ∈ X := X.pow_mem hvX 2
  have hv2P : v ^ 2 ∈ P := hFP hv2.1
  obtain ⟨u, hu⟩ := fzc_sy3_klein_P hs (Y := X ⊓ P) inf_le_right
    (x := v ^ 2) (y := y) ⟨hv2X, hv2P⟩ ⟨hyX, hyP⟩ hv2.2 hyWp hv2y
  refine ⟨{v, y, u}, Finset.card_le_three, ?_⟩
  have hcoe : ((({v, y, u} : Finset G)) : Set G) = {v, y, u} := by simp
  rw [hcoe]
  have hsub : closure ({v ^ 2, y, u} : Set G) ≤ closure ({v, y, u} : Set G) := by
    rw [Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact pow_mem (subset_closure (by simp)) 2
    · exact subset_closure (by simp)
    · exact subset_closure (by simp)
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact hvX
    · exact hyX
    · exact (inf_le_left : X ⊓ P ≤ X) (hu ▸ subset_closure (by simp))
  · intro g hgX
    have hgU : g ∈ U := hX hgX
    by_cases hgP : g ∈ P
    · exact hsub (hu ▸ (⟨hgX, hgP⟩ : g ∈ X ⊓ P))
    · have hg_uc : ∃ p ∈ P, g = p * c := by
        rcases (hs.U_mem.mp hgU) with ⟨p, hpP, hgp | hgp⟩
        · exact absurd (hgp ▸ hpP) hgP
        · exact ⟨p, hpP, hgp⟩
      obtain ⟨p_g, hp_gP, hg_eq⟩ := hg_uc
      have hv_uc : ∃ p ∈ P, v = p * c := by
        rcases (hs.U_mem.mp (hX hvX)) with ⟨p, hpP, hvp | hvp⟩
        · exact absurd (hvp ▸ hpP) hvP
        · exact ⟨p, hpP, hvp⟩
      obtain ⟨p_v, hp_vP, hv_eq'⟩ := hv_uc
      have hgvP : g * v⁻¹ ∈ P := by
        rw [hg_eq, hv_eq']
        have : (p_g * c) * (p_v * c)⁻¹ = p_g * p_v⁻¹ := by group
        rw [this]
        exact P.mul_mem hp_gP (P.inv_mem hp_vP)
      have hgvXP : g * v⁻¹ ∈ X ⊓ P := ⟨X.mul_mem hgX (X.inv_mem hvX), hgvP⟩
      have hmem : g * v⁻¹ ∈ closure ({v, y, u} : Set G) := hsub (hu ▸ hgvXP)
      have : g = (g * v⁻¹) * v := by group
      rw [this]
      exact mul_mem hmem (subset_closure (by simp))

end CFSG.OddStandard.SmallF3.FritzII
