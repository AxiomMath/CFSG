module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888LSP

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z r : G}
  {B A K₁ K₂ : Subgroup G} {h : G}

theorem l515S_mixed2 (h36 : Asc82Lemma36) (h37 : Asc82Lemma37) (h514 : Asc82Lemma514)
    (h52a : Asc82Lemma52a) (hM1 : Asc82FactRhoStar) (h38 : Asc82Lemma38)
    (h311 : Asc82Lemma311) (h7 : AschOmega7)
    (hOne : CFSG.GH74.GLS.Stage2.Final.ModelOneClass)
    (c : Sec5HCtx G t L S z r B A K₁ K₂ h) {d : G} (hd2 : orderOf d = 2) (hdz : d ≠ z)
    {i i' j j' : Fin 4} (hi : (i = 0 ∧ i' = 1) ∨ (i = 1 ∧ i' = 0))
    (hj : (j = 2 ∧ j' = 3) ∨ (j = 3 ∧ j' = 2))
    (hd : d ∈ Kfam5 K₁ K₂ h i ⊔ Kfam5 K₁ K₂ h j) :
    ∃ I : Subgroup G, Sec5Setting G d I ∧
      ∃ P : Subgroup G, IsKOf (Gamma5 K₁ K₂ h) d P ∧ P ≤ I := by
  have hq : Sec5B517Quad (Kfam5 K₁ K₂ h) z := sec5b517_quad h514 c
  obtain ⟨hij, hij', hi'j, hi'j', hii', hjj'⟩ := l515S_idx hi hj
  obtain ⟨α, hα, β, hβ, hdab, hα2, hβ2⟩ := sec5b513_decomp (Classical.choice (hq.iso i))
    (Classical.choice (hq.iso j)) (hq.comm i j hij) (hq.z_mem i) (hq.z_mem j) hq.z_sq hq.z_ne
    hd (l515S_sq_of_orderOf_two hd2) (l515S_ne_one_of_orderOf_two hd2) hdz
  subst hdab
  obtain ⟨g, hgt, hgs, hgz, hgK, hβt, hαs⟩ := l515S_adapt h37 h514 c hi hj hα hβ hα2 hβ2
  obtain ⟨c₁, hcj1, hcj2⟩ := l515S_ctx_fix c hgz hgK
  have hKeq : Kfam5 K₁ K₂ (g⁻¹ * h * g) = Kfam5 K₁ K₂ h := l515S_kfam_eq hcj1 hcj2
  have hα₁ : α ∈ Kfam5 K₁ K₂ (g⁻¹ * h * g) i := by rw [hKeq]; exact hα
  have hβ₁ : β ∈ Kfam5 K₁ K₂ (g⁻¹ * h * g) j := by rw [hKeq]; exact hβ
  have hs₁ : (g⁻¹ * h * g)⁻¹ * (g⁻¹ * t * g) * (g⁻¹ * h * g) = g⁻¹ * (h⁻¹ * t * h) * g := by
    group
  have hds₁ : (α * β) * ((g⁻¹ * h * g)⁻¹ * (g⁻¹ * t * g) * (g⁻¹ * h * g)) =
      ((g⁻¹ * h * g)⁻¹ * (g⁻¹ * t * g) * (g⁻¹ * h * g)) * (α * β) := by
    rw [hs₁]
    exact hgs.symm
  have hαs₁ : α * ((g⁻¹ * h * g)⁻¹ * (g⁻¹ * t * g) * (g⁻¹ * h * g)) =
      ((g⁻¹ * h * g)⁻¹ * (g⁻¹ * t * g) * (g⁻¹ * h * g)) * α := by
    rw [hs₁]
    exact hαs
  obtain ⟨I, hI, hInF, hTwo, hi'I, hj'I⟩ :=
    l515S_core h36 h37 h514 h52a hM1 h38 h311 h7 hOne c₁ hi hj hα₁ hβ₁ hα2 hβ2 hgt.symm hds₁
      hβt hαs₁
  have hSet : Sec5Setting G (α * β) I :=
    ⟨⟨⟨c.simple, c.a1, c.a2, c.notChev3, hd2, hI, hInF⟩, c.lBalance, c.kProper, c.notCat⟩, hTwo⟩
  have hP : Kfam5 K₁ K₂ h i' ⊔ Kfam5 K₁ K₂ h j' ≤ centralizer ({α * β} : Set G) := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact ((show Commute x α from hq.comm i' i hii'.symm x hx α hα).mul_right
        (show Commute x β from hq.comm i' j hi'j x hx β hβ)).eq
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact ((show Commute x α from hq.comm j' i hij'.symm x hx α hα).mul_right
        (show Commute x β from hq.comm j' j hjj'.symm x hx β hβ)).eq
  refine ⟨I, hSet, Kfam5 K₁ K₂ h i' ⊔ Kfam5 K₁ K₂ h j',
    ⟨Kfam5 K₁ K₂ h i', l515S_kfam_mem_gamma _ _ _ _, Kfam5 K₁ K₂ h j',
      l515S_kfam_mem_gamma _ _ _ _, hq.ne hi'j', rfl, hP⟩, ?_⟩
  refine sup_le ?_ ?_
  · rw [← hKeq]
    exact hi'I
  · rw [← hKeq]
    exact hj'I

theorem l515S_mixed2' (h36 : Asc82Lemma36) (h37 : Asc82Lemma37) (h514 : Asc82Lemma514)
    (h52a : Asc82Lemma52a) (hM1 : Asc82FactRhoStar) (h38 : Asc82Lemma38)
    (h311 : Asc82Lemma311) (h7 : AschOmega7)
    (hOne : CFSG.GH74.GLS.Stage2.Final.ModelOneClass)
    (c : Sec5HCtx G t L S z r B A K₁ K₂ h) {d : G} (hd2 : orderOf d = 2) (hdz : d ≠ z)
    {i j : Fin 4} (hi : i = 0 ∨ i = 1) (hj : j = 2 ∨ j = 3)
    (hd : d ∈ Kfam5 K₁ K₂ h i ⊔ Kfam5 K₁ K₂ h j) :
    ∃ I : Subgroup G, Sec5Setting G d I ∧
      ∃ P : Subgroup G, IsKOf (Gamma5 K₁ K₂ h) d P ∧ P ≤ I := by
  obtain ⟨i', hi'⟩ : ∃ i' : Fin 4, (i = 0 ∧ i' = 1) ∨ (i = 1 ∧ i' = 0) := by
    rcases hi with rfl | rfl
    · exact ⟨1, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨0, Or.inr ⟨rfl, rfl⟩⟩
  obtain ⟨j', hj'⟩ : ∃ j' : Fin 4, (j = 2 ∧ j' = 3) ∨ (j = 3 ∧ j' = 2) := by
    rcases hj with rfl | rfl
    · exact ⟨3, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨2, Or.inr ⟨rfl, rfl⟩⟩
  exact l515S_mixed2 h36 h37 h514 h52a hM1 h38 h311 h7 hOne c hd2 hdz hi' hj' hd

private theorem l515S_index_cases2 : ∀ a b : Fin 4, a ≠ b →
    ((a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0)) ∨ ((a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2)) ∨
      ((a = 0 ∨ a = 1) ∧ (b = 2 ∨ b = 3)) ∨ ((a = 2 ∨ a = 3) ∧ (b = 0 ∨ b = 1)) := by
  decide

theorem asc82Lemma515Setting_of_m1 (h36 : Asc82Lemma36) (h37 : Asc82Lemma37)
    (h514 : Asc82Lemma514) (h52a : Asc82Lemma52a) (hM1 : Asc82FactRhoStar)
    (h38 : Asc82Lemma38) (h311 : Asc82Lemma311) (h7 : AschOmega7)
    (hOne : CFSG.GH74.GLS.Stage2.Final.ModelOneClass) : Asc82Lemma515Setting := by
  intro G _ _ t L S z r B A K₁ K₂ h c d hd
  obtain ⟨hd2, hdz, P, hP, P', hP', hne, hdP⟩ := hd
  obtain ⟨a, rfl⟩ := l515S_gamma_mem hP
  obtain ⟨b, rfl⟩ := l515S_gamma_mem hP'
  have hab : a ≠ b := fun hh => hne (by rw [hh])
  have hK0 : Kfam5 K₁ K₂ h 0 = K₁ := by simp [Kfam5]
  have hK1 : Kfam5 K₁ K₂ h 1 = K₂ := by simp [Kfam5]
  have hK2 : Kfam5 K₁ K₂ h 2 = CFSG.conjugate K₁ h := by simp [Kfam5]
  have hK3 : Kfam5 K₁ K₂ h 3 = CFSG.conjugate K₂ h := by simp [Kfam5]
  rcases l515S_index_cases2 a b hab with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) |
      ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [hK0, hK1] at hdP
    exact l515S_tclass h37 h514 c hd2 hdz (Or.inl hdP)
  · rw [sup_comm, hK0, hK1] at hdP
    exact l515S_tclass h37 h514 c hd2 hdz (Or.inl hdP)
  · rw [hK2, hK3] at hdP
    exact l515S_tclass h37 h514 c hd2 hdz (Or.inr hdP)
  · rw [sup_comm, hK2, hK3] at hdP
    exact l515S_tclass h37 h514 c hd2 hdz (Or.inr hdP)
  · exact l515S_mixed2' h36 h37 h514 h52a hM1 h38 h311 h7 hOne c hd2 hdz ha hb hdP
  · rw [sup_comm] at hdP
    exact l515S_mixed2' h36 h37 h514 h52a hM1 h38 h311 h7 hOne c hd2 hdz hb ha hdP

end CFSG.OddStandard.SmallF3.Omega
