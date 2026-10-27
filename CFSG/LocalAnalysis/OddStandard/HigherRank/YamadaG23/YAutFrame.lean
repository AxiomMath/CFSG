module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FactsL
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Monster.B.TwoA.Base.ElemAut
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {Q : Type} [Group Q] [Finite Q] (fr : Frame (MulAut Q))

private lemma conj_mem_of_rel {G : Type*} [Group G] {S : Subgroup G} {x w σ : G}
    (hx : x ∈ S) (hw : w ∈ S) (hrel : ⁅x, σ⁆ * w⁻¹ = 1) : σ * x * σ⁻¹ ∈ S := by
  have hcomm : ⁅x, σ⁆ = w := mul_inv_eq_one.mp hrel
  have h2 : σ * x⁻¹ * σ⁻¹ = x⁻¹ * w := by
    rw [← hcomm, commutatorElement_def]
    group
  rw [show σ * x * σ⁻¹ = (σ * x⁻¹ * σ⁻¹)⁻¹ by group, h2]
  exact inv_mem (mul_mem (inv_mem hx) hw)

private lemma sigma_conj_inv_of_sq {G : Type*} [Group G] {σ y : G} (hσ : σ ^ 2 = 1) :
    σ * (σ * y * σ⁻¹) * σ⁻¹ = y := by
  have h1 : σ * σ = 1 := by simpa only [pow_two] using hσ
  rw [show σ * (σ * y * σ⁻¹) * σ⁻¹ = (σ * σ) * y * (σ⁻¹ * σ⁻¹) by group]
  rw [h1, ← mul_inv_rev, h1, inv_one, one_mul, mul_one]

private lemma gens11_0 : fr.gens11 0 = fr.a₁ := by simp [Frame.gens11]

private lemma gens11_1 : fr.gens11 1 = fr.b₁ := by simp [Frame.gens11]

private lemma gens11_2 : fr.gens11 2 = fr.a₂ := by simp [Frame.gens11]

private lemma gens11_3 : fr.gens11 3 = fr.b₂ := by simp [Frame.gens11]

private lemma gens11_4 : fr.gens11 4 = fr.h₀ := by simp [Frame.gens11]

private lemma gens11_5 : fr.gens11 5 = fr.σ := by simp [Frame.gens11]

private lemma S_mem_a₁ {fr' : Frame (MulAut Q)} : fr'.a₁ ∈ fr'.S := by
  change fr'.a₁ ∈ Subgroup.closure ({fr'.a₁, fr'.b₁, fr'.a₂, fr'.b₂, fr'.h₀} : Set (MulAut Q))
  exact Subgroup.subset_closure (by simp)

private lemma S_mem_b₁ {fr' : Frame (MulAut Q)} : fr'.b₁ ∈ fr'.S := by
  change fr'.b₁ ∈ Subgroup.closure ({fr'.a₁, fr'.b₁, fr'.a₂, fr'.b₂, fr'.h₀} : Set (MulAut Q))
  exact Subgroup.subset_closure (by simp)

private lemma S_mem_a₂ {fr' : Frame (MulAut Q)} : fr'.a₂ ∈ fr'.S := by
  change fr'.a₂ ∈ Subgroup.closure ({fr'.a₁, fr'.b₁, fr'.a₂, fr'.b₂, fr'.h₀} : Set (MulAut Q))
  exact Subgroup.subset_closure (by simp)

private lemma S_mem_b₂ {fr' : Frame (MulAut Q)} : fr'.b₂ ∈ fr'.S := by
  change fr'.b₂ ∈ Subgroup.closure ({fr'.a₁, fr'.b₁, fr'.a₂, fr'.b₂, fr'.h₀} : Set (MulAut Q))
  exact Subgroup.subset_closure (by simp)

private lemma S_mem_h₀ {fr' : Frame (MulAut Q)} : fr'.h₀ ∈ fr'.S := by
  change fr'.h₀ ∈ Subgroup.closure ({fr'.a₁, fr'.b₁, fr'.a₂, fr'.b₂, fr'.h₀} : Set (MulAut Q))
  exact Subgroup.subset_closure (by simp)

private lemma S_mem_z {fr' : Frame (MulAut Q)} : fr'.z ∈ fr'.S := by
  change fr'.b₁ ^ 2 ∈ fr'.S
  exact pow_mem S_mem_b₁ 2

private lemma sigma_conj_relator (h : fr.Fact11 (innerAut Q)) (x w : FreeGroup (Fin 6))
    (hr : ⁅x, FreeGroup.of 5⁆ * w⁻¹ ∈ Frame.rels11)
    (hx : FreeGroup.lift fr.gens11 x ∈ fr.S)
    (hw : FreeGroup.lift fr.gens11 w ∈ fr.S) :
    fr.σ * FreeGroup.lift fr.gens11 x * fr.σ⁻¹ ∈ fr.S := by
  obtain ⟨hh, -⟩ := h.1
  have hk : ⁅FreeGroup.lift fr.gens11 x, fr.σ⁆ * (FreeGroup.lift fr.gens11 w)⁻¹ = 1 := by
    simpa only [map_mul, map_inv, map_commutatorElement, FreeGroup.lift_apply_of, gens11_5]
      using hh _ hr
  exact conj_mem_of_rel hx hw hk

theorem frame_S_le_inner (h : fr.Fact11 (innerAut Q)) : fr.S ≤ innerAut Q :=
  h.2.1.1

theorem frame_sigma_sq (h : fr.Fact11 (innerAut Q)) : fr.σ ^ 2 = 1 := by
  obtain ⟨hh, -⟩ := h.1
  have hr : FreeGroup.of 5 ^ 2 ∈ Frame.rels11 := by simp [Frame.rels11]
  have hk := hh _ hr
  simpa only [map_pow, FreeGroup.lift_apply_of, gens11_5] using hk

theorem frame_sigma_normalizes (h : fr.Fact11 (innerAut Q)) :
    fr.σ ∈ normalizer (fr.S : Set (MulAut Q)) := by
  have hσ2 : fr.σ ^ 2 = 1 := frame_sigma_sq fr h
  have hconj : ∀ y ∈ fr.S, fr.σ * y * fr.σ⁻¹ ∈ fr.S := by
    have hgen : ∀ x ∈ ({fr.a₁, fr.b₁, fr.a₂, fr.b₂, fr.h₀} : Set (MulAut Q)),
        fr.σ * x * fr.σ⁻¹ ∈ fr.S := by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · have hkey := sigma_conj_relator fr h (FreeGroup.of 0)
            (FreeGroup.of 0 * FreeGroup.of 2 * (FreeGroup.of 1) ^ 2)
            (by simp [Frame.rels11])
            (by simpa only [FreeGroup.lift_apply_of, gens11_0] using S_mem_a₁)
            (by
              simp only [map_mul, map_pow, FreeGroup.lift_apply_of, gens11_0, gens11_1, gens11_2]
              exact mul_mem (mul_mem S_mem_a₁ S_mem_a₂) S_mem_z)
        simpa only [FreeGroup.lift_apply_of, gens11_0] using hkey
      · have hkey := sigma_conj_relator fr h (FreeGroup.of 1)
            (FreeGroup.of 1 * FreeGroup.of 3 * (FreeGroup.of 1) ^ 2)
            (by simp [Frame.rels11])
            (by simpa only [FreeGroup.lift_apply_of, gens11_1] using S_mem_b₁)
            (by
              simp only [map_mul, map_pow, FreeGroup.lift_apply_of, gens11_1, gens11_3]
              exact mul_mem (mul_mem S_mem_b₁ S_mem_b₂) S_mem_z)
        simpa only [FreeGroup.lift_apply_of, gens11_1] using hkey
      · have hkey := sigma_conj_relator fr h (FreeGroup.of 2)
            (FreeGroup.of 0 * FreeGroup.of 2 * (FreeGroup.of 1) ^ 2)
            (by simp [Frame.rels11])
            (by simpa only [FreeGroup.lift_apply_of, gens11_2] using S_mem_a₂)
            (by
              simp only [map_mul, map_pow, FreeGroup.lift_apply_of, gens11_0, gens11_1, gens11_2]
              exact mul_mem (mul_mem S_mem_a₁ S_mem_a₂) S_mem_z)
        simpa only [FreeGroup.lift_apply_of, gens11_2] using hkey
      · have hkey := sigma_conj_relator fr h (FreeGroup.of 3)
            (FreeGroup.of 1 * FreeGroup.of 3 * (FreeGroup.of 1) ^ 2)
            (by simp [Frame.rels11])
            (by simpa only [FreeGroup.lift_apply_of, gens11_3] using S_mem_b₂)
            (by
              simp only [map_mul, map_pow, FreeGroup.lift_apply_of, gens11_1, gens11_3]
              exact mul_mem (mul_mem S_mem_b₁ S_mem_b₂) S_mem_z)
        simpa only [FreeGroup.lift_apply_of, gens11_3] using hkey
      · have hkey := sigma_conj_relator fr h (FreeGroup.of 4) ((FreeGroup.of 1) ^ 2)
            (by simp [Frame.rels11])
            (by simpa only [FreeGroup.lift_apply_of, gens11_4] using S_mem_h₀)
            (by
              simp only [map_pow, FreeGroup.lift_apply_of, gens11_1]
              exact S_mem_z)
        simpa only [FreeGroup.lift_apply_of, gens11_4] using hkey
    intro y hy
    have hy' : y ∈ Subgroup.closure
        ({fr.a₁, fr.b₁, fr.a₂, fr.b₂, fr.h₀} : Set (MulAut Q)) := hy
    exact Subgroup.closure_induction (p := fun z _ => fr.σ * z * fr.σ⁻¹ ∈ fr.S)
      (fun x hx => hgen x hx) (by simpa using Subgroup.one_mem fr.S)
      (fun x y _ _ ihx ihy => by
        rw [show fr.σ * (x * y) * fr.σ⁻¹
            = (fr.σ * x * fr.σ⁻¹) * (fr.σ * y * fr.σ⁻¹) by group]
        exact mul_mem ihx ihy)
      (fun x _ ihx => by
        rw [show fr.σ * x⁻¹ * fr.σ⁻¹ = (fr.σ * x * fr.σ⁻¹)⁻¹ by group]
        exact inv_mem ihx)
      hy'
  rw [Subgroup.mem_set_normalizer_iff]
  intro y
  constructor
  · exact hconj y
  · intro hy
    have hzz : fr.σ * (fr.σ * y * fr.σ⁻¹) * fr.σ⁻¹ ∈ fr.S := hconj _ hy
    rwa [sigma_conj_inv_of_sq hσ2] at hzz

theorem frame_Sσ_isPGroup (h : fr.Fact11 (innerAut Q)) : IsPGroup 2 fr.Sσ :=
  h.2.2.2.1

theorem frame_S_le_Sσ : fr.S ≤ fr.Sσ := by
  change Subgroup.closure ({fr.a₁, fr.b₁, fr.a₂, fr.b₂, fr.h₀} : Set (MulAut Q)) ≤
    Subgroup.closure ({fr.a₁, fr.b₁, fr.a₂, fr.b₂, fr.h₀, fr.σ} : Set (MulAut Q))
  apply Subgroup.closure_mono
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
  tauto

theorem frame_sigma_mem_Sσ : fr.σ ∈ fr.Sσ := by
  change fr.σ ∈ Subgroup.closure
    ({fr.a₁, fr.b₁, fr.a₂, fr.b₂, fr.h₀, fr.σ} : Set (MulAut Q))
  exact Subgroup.subset_closure (by simp)

theorem frame_sigma_not_mem_inner (h : fr.Fact11 (innerAut Q))
    (hOut : (innerAut Q).index = 2) : fr.σ ∉ innerAut Q := by
  intro hσ
  have hS : fr.S ≤ innerAut Q := frame_S_le_inner fr h
  have hSσ : fr.Sσ ≤ innerAut Q := by
    change Subgroup.closure ({fr.a₁, fr.b₁, fr.a₂, fr.b₂, fr.h₀, fr.σ} : Set (MulAut Q)) ≤
      innerAut Q
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hS S_mem_a₁
    · exact hS S_mem_b₁
    · exact hS S_mem_a₂
    · exact hS S_mem_b₂
    · exact hS S_mem_h₀
    · exact hσ
  have hdvd : (innerAut Q).index ∣ fr.Sσ.index := Subgroup.index_dvd_of_le hSσ
  rw [hOut] at hdvd
  have hEven : 2 ∣ fr.Sσ.relIndex ⊤ := by rwa [Subgroup.relIndex_top_right]
  exact h.2.2.2.2 hEven

theorem frame_inner_sup_sigma (h : fr.Fact11 (innerAut Q)) (hOut : (innerAut Q).index = 2) :
    innerAut Q ⊔ closure {fr.σ} = ⊤ := by
  have hσnot : fr.σ ∉ innerAut Q := frame_sigma_not_mem_inner fr h hOut
  rw [eq_top_iff]
  intro g _
  by_cases hg : g ∈ innerAut Q
  · exact Subgroup.mem_sup_left hg
  · have hmul : g * fr.σ ∈ innerAut Q := by
      rw [Subgroup.mul_mem_iff_of_index_two hOut]
      exact ⟨fun hc => absurd hc hg, fun hc => absurd hc hσnot⟩
    have hσinv : fr.σ⁻¹ ∈ closure ({fr.σ} : Set (MulAut Q)) :=
      inv_mem (Subgroup.subset_closure (by simp))
    have heq : g = (g * fr.σ) * fr.σ⁻¹ := by group
    rw [heq]
    exact mul_mem (Subgroup.mem_sup_left hmul) (Subgroup.mem_sup_right hσinv)

theorem frame_normalizer_S_le (h : fr.Facts (innerAut Q)) (hOut : (innerAut Q).index = 2) :
    normalizer (fr.S : Set (MulAut Q)) ≤ fr.Sσ := by
  intro n hn
  have hNS : normIn (innerAut Q) fr.S = fr.S := h.2.2.2.2.2.2.2.1.1.2
  have hσnorm : fr.σ ∈ normalizer (fr.S : Set (MulAut Q)) := frame_sigma_normalizes fr h.1
  have hσnot : fr.σ ∉ innerAut Q := frame_sigma_not_mem_inner fr h.1 hOut
  by_cases hn' : n ∈ innerAut Q
  · have hmem : n ∈ fr.S := by
      have hni : n ∈ normIn (innerAut Q) fr.S := ⟨hn', hn⟩
      simpa only [hNS] using hni
    exact frame_S_le_Sσ fr hmem
  · have hmul : n * fr.σ ∈ innerAut Q := by
      rw [Subgroup.mul_mem_iff_of_index_two hOut]
      exact ⟨fun hc => absurd hc hn', fun hc => absurd hc hσnot⟩
    have hmem : n * fr.σ ∈ fr.S := by
      have hni : n * fr.σ ∈ normIn (innerAut Q) fr.S := ⟨hmul, mul_mem hn hσnorm⟩
      simpa only [hNS] using hni
    have h1 : n * fr.σ ∈ fr.Sσ := frame_S_le_Sσ fr hmem
    have h2 : fr.σ⁻¹ ∈ fr.Sσ := inv_mem (frame_sigma_mem_Sσ fr)
    have heq : n = (n * fr.σ) * fr.σ⁻¹ := by group
    rw [heq]
    exact mul_mem h1 h2

theorem frame_centralizer_A (h : fr.Facts (innerAut Q)) (hOut : (innerAut Q).index = 2)
    {g : MulAut Q} (hg : ∀ a ∈ fr.A, ⁅a, g⁆ ∈ fr.Z) : g ∈ fr.A := by
  have hset : {x : MulAut Q |
        x ∈ innerAut Q ⊔ closure {fr.σ} ∧ ∀ a ∈ fr.A, ⁅a, x⁆ ∈ fr.Z}
      = (fr.A : Set (MulAut Q)) := h.2.2.2.2.2.2.2.2.2.1.2.1
  change g ∈ (fr.A : Set (MulAut Q))
  rw [← hset]
  exact ⟨by rw [frame_inner_sup_sigma fr h.1 hOut]; exact Subgroup.mem_top g, hg⟩

end CFSG.OddStandard.HigherRank.YamadaG23
