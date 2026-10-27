module

public import CFSG.LargeExtraspecial.AS35ZMLin

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35ZM

open Module CFSG.RankThree.OrthogonalInvolutions QuadraticMap

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {J g y σ : V ≃ₗ[ZMod 2] V} (hJ : ∀ v, J (J v) + J v + v = 0)
  (hgJ : ∀ v, g (J v) = J (g v)) (hg3 : ∀ v, g (g (g v)) = v)
  (hyJ : ∀ v, y (J v) = J (y v)) (hyg : ∀ v, y (g v) = g (y v))
  (hσJ : ∀ v, σ (J v) = J (J (σ v))) (hσg : ∀ v, σ (g v) = g (σ v))
  (hσy : ∀ v, σ (y v) = y (σ v)) (hyfin : finrank (ZMod 2) (commSpace y) ≤ 4)
include hJ hgJ hg3 hyJ hyg hσJ hσg hσy hyfin

theorem semilinear_dichotomy :
    commSpace y ≤ fixSpace g ∨ commSpace y ≤ commSpace g := by
  set B := commSpace y ⊓ commSpace g with hB
  have hBg : ∀ c ∈ B, g c ∈ B := fun c hc => Submodule.mem_inf.2
    ⟨commSpace_mem_of_commute (fun v => (hyg v).symm) (Submodule.mem_inf.1 hc).1,
      commSpace_apply_mem (Submodule.mem_inf.1 hc).2⟩
  have hBJ : ∀ c ∈ B, J c ∈ B := fun c hc => Submodule.mem_inf.2
    ⟨commSpace_mem_of_commute (fun v => (hyJ v).symm) (Submodule.mem_inf.1 hc).1,
      J_mem_commSpace hgJ (Submodule.mem_inf.1 hc).2⟩
  have hBσ : ∀ c ∈ B, σ c ∈ B := fun c hc => Submodule.mem_inf.2
    ⟨commSpace_mem_of_commute hσy (Submodule.mem_inf.1 hc).1,
      commSpace_mem_of_commute hσg (Submodule.mem_inf.1 hc).2⟩
  by_cases hB0 : ∀ c ∈ B, c = 0
  · left
    intro w hw
    rw [mem_fixSpace]
    have h1 : g (g w) + g w ∈ B := by
      refine Submodule.mem_inf.2 ⟨?_, ?_⟩
      · have hgw := commSpace_mem_of_commute (fun v => (hyg v).symm) hw
        exact Submodule.add_mem _ (commSpace_mem_of_commute (fun v => (hyg v).symm) hgw) hgw
      · rw [← sub_eq_add_V]
        exact sub_mem_commSpace g _
    exact g.injective (eq_of_add_eq_zero_V (hB0 _ h1))
  · right
    push Not at hB0
    obtain ⟨c, hc, hc0⟩ := hB0
    set B₁ := B ⊓ eigOne J g with hB₁
    set B₂ := B ⊓ eigTwo J g with hB₂
    have hcW := (Submodule.mem_inf.1 hc).2
    have hc₁ : g c + J (J c) ∈ B₁ := Submodule.mem_inf.2
      ⟨Submodule.add_mem _ (hBg c hc) (hBJ _ (hBJ c hc)), decomp_one_mem hgJ hJ hg3 hcW⟩
    have hc₂ : g c + J c ∈ B₂ := Submodule.mem_inf.2
      ⟨Submodule.add_mem _ (hBg c hc) (hBJ c hc), decomp_two_mem hgJ hJ hg3 hcW⟩
    have hσ12 : ∀ x ∈ B₁, σ x ∈ B₂ := by
      intro x hx
      obtain ⟨hxB, hx1⟩ := Submodule.mem_inf.1 hx
      rw [mem_eigOne] at hx1
      refine Submodule.mem_inf.2 ⟨hBσ x hxB, mem_eigTwo.2 ⟨(Submodule.mem_inf.1
        (hBσ x hxB)).2, ?_⟩⟩
      rw [← hσg, hx1.2, hσJ]
    have hσ21 : ∀ x ∈ B₂, σ x ∈ B₁ := by
      intro x hx
      obtain ⟨hxB, hx2⟩ := Submodule.mem_inf.1 hx
      rw [mem_eigTwo] at hx2
      refine Submodule.mem_inf.2 ⟨hBσ x hxB, mem_eigOne.2 ⟨(Submodule.mem_inf.1
        (hBσ x hxB)).2, ?_⟩⟩
      rw [← hσg, hx2.2, hσJ, hσJ, J_J_J hJ]
    have hJ₁ : ∀ x ∈ B₁, J x ∈ B₁ := fun x hx => Submodule.mem_inf.2
      ⟨hBJ x (Submodule.mem_inf.1 hx).1, eigOne_J_mem hgJ (Submodule.mem_inf.1 hx).2⟩
    have hJ₂ : ∀ x ∈ B₂, J x ∈ B₂ := fun x hx => Submodule.mem_inf.2
      ⟨hBJ x (Submodule.mem_inf.1 hx).1, eigTwo_J_mem hgJ (Submodule.mem_inf.1 hx).2⟩
    have hne : B₁ ≠ ⊥ ∧ B₂ ≠ ⊥ := by
      have hσ0 : ∀ x, σ x = 0 → x = 0 := fun x h => σ.injective (by rw [h, map_zero])
      by_cases h1 : g c + J (J c) = 0
      · have h2 : g c + J c ≠ 0 := by
          intro h2
          apply hc0
          rw [← decomp_sum (g := g) hJ c, h1, h2, add_zero]
        refine ⟨fun hb => h2 (hσ0 _ ?_), fun hb => h2 ?_⟩
        · have := hσ21 _ hc₂
          rw [hb, Submodule.mem_bot] at this
          exact this
        · have := hc₂
          rw [hb, Submodule.mem_bot] at this
          exact this
      · refine ⟨fun hb => h1 ?_, fun hb => h1 (hσ0 _ ?_)⟩
        · have := hc₁
          rw [hb, Submodule.mem_bot] at this
          exact this
        · have := hσ12 _ hc₁
          rw [hb, Submodule.mem_bot] at this
          exact this
    have hf₁ := two_le_finrank_of_J hJ hJ₁ hne.1
    have hf₂ := two_le_finrank_of_J hJ hJ₂ hne.2
    have hinf : B₁ ⊓ B₂ = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hx
      have e1 := (mem_eigOne.1 (Submodule.mem_inf.1 h1).2).2
      have e2 := (mem_eigTwo.1 (Submodule.mem_inf.1 h2).2).2
      rw [Submodule.mem_bot]
      exact eq_zero_of_J_eq hJ x (J.injective (e1.symm.trans e2)).symm
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq B₁ B₂
    rw [hinf, finrank_bot, add_zero] at hsum
    have hle : B₁ ⊔ B₂ ≤ commSpace y := sup_le (inf_le_left.trans inf_le_left)
      (inf_le_left.trans inf_le_left)
    have heq := Submodule.eq_of_le_of_finrank_le hle (by omega)
    rw [← heq]
    exact sup_le (inf_le_left.trans inf_le_right) (inf_le_left.trans inf_le_right)

end CFSG.LargeExtraspecial.AS35ZM
