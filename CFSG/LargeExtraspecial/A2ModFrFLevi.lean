module

public import CFSG.LargeExtraspecial.A2ModFrFFrame
public import CFSG.LargeExtraspecial.A2ModCfg

public section

namespace CFSG.LargeExtraspecial.A2Mod.FrF

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.ExclNS Matrix
open CFSG.Timmesfeld (sroot)
open scoped commutatorElement

section Invol

variable {G : Type} [Group G]

theorem commutator_zpowers_eq {a b : G} (ha : a * a = 1) (hb : b * b = 1) :
    ⁅Subgroup.zpowers a, Subgroup.zpowers b⁆ = Subgroup.zpowers ⁅a, b⁆ := by
  refine le_antisymm ((Subgroup.commutator_le).mpr fun x hx y hy => ?_)
    ((Subgroup.zpowers_le).mpr (Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers a)
      (Subgroup.mem_zpowers b)))
  by_cases hx1 : x = 1
  · rw [hx1, commutatorElement_one_left]
    exact one_mem _
  by_cases hy1 : y = 1
  · rw [hy1, commutatorElement_one_right]
    exact one_mem _
  rw [eq_of_mem_zpowers ha hx hx1, eq_of_mem_zpowers hb hy hy1]
  exact Subgroup.mem_zpowers _

theorem commuting_zpowers {a b : G} (h : Commute a b) :
    Commuting (Subgroup.zpowers a) (Subgroup.zpowers b) := by
  intro x hx y hy
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact h.zpow_zpow m n

end Invol

abbrev r0 : Fin 4 → ℤ := ![0, 1, 2, 2]
abbrev r1 : Fin 4 → ℤ := ![1, 0, 0, 0]
abbrev r2 : Fin 4 → ℤ := ![0, 1, 0, 0]
abbrev r3 : Fin 4 → ℤ := ![0, 1, 2, 0]

abbrev chain : Fin 3 → Fin 4 → ℤ := ![r0, r1, r2]

namespace F4Frame

variable {G : Type} [Group G] {R : Set (Subgroup G)} {F : F4Frame G R}

theorem isLong_r1 : F.IsLong r1 := by
  have h := F.isLong_single_zero
  rwa [show (Pi.single 0 1 : Fin 4 → ℤ) = r1 by decide] at h

theorem isLong_r2 : F.IsLong r2 := by
  have h := F.isLong_single_one
  rwa [show (Pi.single 1 1 : Fin 4 → ℤ) = r2 by decide] at h

theorem isLong_r3 : F.IsLong r3 :=
  isLong_r2.reflF 2 (by decide)

theorem isLong_r0 : F.IsLong r0 :=
  isLong_r3.reflF 3 (by decide)

theorem isLong_chain (j : Fin 3) : F.IsLong (chain j) := by
  fin_cases j
  · exact isLong_r0
  · exact isLong_r1
  · exact isLong_r2

theorem isLong_r1_add_r2 : F.IsLong (r1 + r2) := by
  rw [show r1 + r2 = ![1, 1, 0, 0] by decide]
  exact isLong_r1.reflF 1 (by decide)

theorem isLong_r1_add_r3 : F.IsLong (r1 + r3) := by
  rw [show r1 + r3 = ![1, 1, 2, 0] by decide]
  exact isLong_r1_add_r2.reflF 2 (by decide)

theorem isLong_r0_add_r1 : F.IsLong (r0 + r1) := by
  rw [show r0 + r1 = ![1, 1, 2, 2] by decide]
  exact isLong_r1_add_r3.reflF 3 (by decide)

theorem isLong_chain_add (j : Fin 2) : F.IsLong (chain j.castSucc + chain j.succ) := by
  fin_cases j
  · exact isLong_r0_add_r1
  · exact isLong_r1_add_r2

variable {D : Set G} (hR : IsRootClass R) (hRD : ∀ E ∈ R, ∃ d ∈ D, E = Subgroup.zpowers d)
include hR hRD

theorem commutator_map_rootGroup {γ δ : Fin 4 → ℤ} (hγ : F.IsLong γ) (hδ : F.IsLong δ)
    (hγδ : F.IsLong (γ + δ)) (hc : (form F.hA).Q γ δ = -2) :
    ⁅(F.X γ).map F.Ψ, (F.X δ).map F.Ψ⁆ = (F.X (γ + δ)).map F.Ψ := by
  rw [map_rootGroup_eq_lr hR hRD hγ, map_rootGroup_eq_lr hR hRD hδ,
    map_rootGroup_eq_lr hR hRD hγδ, commutator_zpowers_eq (lr_mul_self hR hRD hγ)
      (lr_mul_self hR hRD hδ), commutator_lr hR hRD hγ hδ hγδ hc]

theorem commuting_map_rootGroup {γ δ : Fin 4 → ℤ} (hγ : F.IsLong γ) (hδ : F.IsLong δ)
    (hc : 0 ≤ (form F.hA).Q γ δ) (hne : δ ≠ γ) :
    Commuting ((F.X γ).map F.Ψ) ((F.X δ).map F.Ψ) := by
  rw [map_rootGroup_eq_lr hR hRD hγ, map_rootGroup_eq_lr hR hRD hδ]
  exact commuting_zpowers (commute_lr hγ hδ hc hne)

theorem edge_of_long {γ δ : Fin 4 → ℤ} (hγ : F.IsLong γ) (hδ : F.IsLong δ)
    (hγδ : F.IsLong (γ + δ)) (hc : (form F.hA).Q γ δ = -2) :
    Special R ((F.X γ).map F.Ψ) ((F.X δ).map F.Ψ) ∧
      Commuting ((F.X (-γ)).map F.Ψ) ((F.X δ).map F.Ψ) ∧
      ⁅(F.X (-γ)).map F.Ψ, ⁅(F.X γ).map F.Ψ, (F.X δ).map F.Ψ⁆⁆ = (F.X δ).map F.Ψ ∧
      Commuting ((F.X γ).map F.Ψ) ((F.X (-δ)).map F.Ψ) ∧
      ⁅⁅(F.X γ).map F.Ψ, (F.X δ).map F.Ψ⁆, (F.X (-δ)).map F.Ψ⁆ = (F.X γ).map F.Ψ ∧
      Special R ((F.X (-γ)).map F.Ψ) ((F.X (-δ)).map F.Ψ) := by
  have hg := hγ.form
  have hd := hδ.form
  have hdg : (form F.hA).Q δ γ = -2 := by rw [(form F.hA).symm, hc]
  have hδ0 : δ ≠ 0 := fun h => by rw [h] at hd; simp at hd
  have hγ0 : γ ≠ 0 := fun h => by rw [h] at hg; simp at hg
  have hcm := commutator_map_rootGroup hR hRD hγ hδ hγδ hc
  have hnn : F.IsLong (-γ + -δ) := by rw [← neg_add]; exact hγδ.neg
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩⟩
  · rw [hcm]
    exact map_rootGroup_mem hR hγδ
  · rw [hcm]
    refine commuting_map_rootGroup hR hRD hγδ hγ ?_ ?_
    · rw [form_add_left F.hA, hg, hdg]; norm_num
    · intro h
      exact hδ0 (by simpa using h.symm)
  · rw [hcm]
    refine commuting_map_rootGroup hR hRD hγδ hδ ?_ ?_
    · rw [form_add_left F.hA, hd, hc]; norm_num
    · intro h
      exact hγ0 (by simpa using h.symm)
  · refine commuting_map_rootGroup hR hRD hγ.neg hδ ?_ ?_
    · rw [form_neg_left F.hA, hc]; norm_num
    · intro h
      rw [h, form_neg_right F.hA, hg] at hc
      norm_num at hc
  · rw [hcm]
    have h1 : -γ + (γ + δ) = δ := by abel
    have := commutator_map_rootGroup hR hRD hγ.neg hγδ (by rw [h1]; exact hδ)
      (by rw [form_neg_left F.hA, (form F.hA).symm, form_add_left F.hA, hg, hdg]; norm_num)
    rwa [h1] at this
  · refine commuting_map_rootGroup hR hRD hγ hδ.neg ?_ ?_
    · rw [form_neg_right F.hA, hc]; norm_num
    · intro h
      rw [← h, form_neg_left F.hA, hd] at hc
      norm_num at hc
  · rw [hcm]
    have h1 : γ + δ + -δ = γ := by abel
    have := commutator_map_rootGroup hR hRD hγδ hδ.neg (by rw [h1]; exact hγ)
      (by rw [form_neg_right F.hA, form_add_left F.hA, hd, hc]; norm_num)
    rwa [h1] at this
  · rw [commutator_map_rootGroup hR hRD hγ.neg hδ.neg hnn
      (by rw [form_neg_left F.hA, form_neg_right F.hA, hc]; norm_num)]
    exact map_rootGroup_mem hR hnn
  · rw [commutator_map_rootGroup hR hRD hγ.neg hδ.neg hnn
      (by rw [form_neg_left F.hA, form_neg_right F.hA, hc]; norm_num)]
    refine commuting_map_rootGroup hR hRD hnn hγ.neg ?_ ?_
    · rw [form_add_left F.hA, form_neg_left F.hA, form_neg_right F.hA, form_neg_left F.hA,
        form_neg_right F.hA, hg, hdg]
      norm_num
    · intro h
      exact hδ0 (by simpa using h.symm)
  · rw [commutator_map_rootGroup hR hRD hγ.neg hδ.neg hnn
      (by rw [form_neg_left F.hA, form_neg_right F.hA, hc]; norm_num)]
    refine commuting_map_rootGroup hR hRD hnn hδ.neg ?_ ?_
    · rw [form_add_left F.hA, form_neg_left F.hA, form_neg_right F.hA, form_neg_left F.hA,
        form_neg_right F.hA, hd, hc]
      norm_num
    · intro h
      exact hγ0 (by simpa using h.symm)

theorem nonadj_of_long {γ δ : Fin 4 → ℤ} (hγ : F.IsLong γ) (hδ : F.IsLong δ)
    (hc : (form F.hA).Q γ δ = 0) (hne : δ ≠ γ) (hne' : δ ≠ -γ) :
    Commuting ((F.X γ).map F.Ψ) ((F.X δ).map F.Ψ) ∧
      Commuting ((F.X γ).map F.Ψ) ((F.X (-δ)).map F.Ψ) ∧
      Commuting ((F.X (-γ)).map F.Ψ) ((F.X δ).map F.Ψ) ∧
      Commuting ((F.X (-γ)).map F.Ψ) ((F.X (-δ)).map F.Ψ) := by
  refine ⟨commuting_map_rootGroup hR hRD hγ hδ hc.ge hne,
    commuting_map_rootGroup hR hRD hγ hδ.neg (by rw [form_neg_right F.hA, hc]; norm_num)
      (fun h => hne' (by rw [← h, neg_neg])),
    commuting_map_rootGroup hR hRD hγ.neg hδ (by rw [form_neg_left F.hA, hc]; norm_num) hne',
    commuting_map_rootGroup hR hRD hγ.neg hδ.neg
      (by rw [form_neg_left F.hA, form_neg_right F.hA, hc]; norm_num)
      (fun h => hne (neg_inj.mp h))⟩

theorem isConfig_chain :
    IsConfig R (edgeA 3) (fun j => (F.X (chain j)).map F.Ψ)
      (fun j => (F.X (-chain j)).map F.Ψ) where
  memA j := map_rootGroup_mem hR (isLong_chain j)
  memB j := map_rootGroup_mem hR (isLong_chain j).neg
  opp j := opposite_map (isLong_chain j)
  edge i j hij := by
    obtain ⟨i', rfl, rfl⟩ : ∃ i' : Fin 2, i'.castSucc = i ∧ i'.succ = j :=
      ⟨⟨i.val, by have := j.2; simp only [edgeA] at hij; omega⟩, Fin.ext rfl,
        Fin.ext (by simp only [edgeA] at hij; simp [hij])⟩
    exact edge_of_long hR hRD (isLong_chain _) (isLong_chain _) (isLong_chain_add i')
      (by fin_cases i' <;> rw [form_apply] <;> decide)
  nonadj i j hij h1 h2 := by
    fin_cases i <;> fin_cases j
    all_goals first
      | exact absurd rfl hij
      | exact absurd (by decide) h1
      | exact absurd (by decide) h2
      | exact nonadj_of_long hR hRD isLong_r0 isLong_r2 (by rw [form_apply]; decide)
          (by decide) (by decide)
      | exact nonadj_of_long hR hRD isLong_r2 isLong_r0 (by rw [form_apply]; decide)
          (by decide) (by decide)

theorem exists_isLeviNode [Finite G] (hiso : NoIsolated R)
    (hDc : ∀ g, ∀ d ∈ D, g * d * g⁻¹ ∈ D) :
    ∃ Ψ : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) →* G,
      IsLeviNode D Ψ (F.lr r3) (F.lr (-r3)) ∧
        ∀ j : Fin 3, (F.X (chain j)).map F.Ψ ≤ Ψ.range ∧ (F.X (-chain j)).map F.Ψ ≤ Ψ.range := by
  obtain ⟨Ψ, hΨA, hΨB⟩ := exists_levi_zmodTwo hR hiso (card_eq_two_of_forall_eq_zpowers hR hRD)
    (le_refl 3) (isConfig_chain hR hRD)
  have hvA : ∀ j : Fin 3, Ψ (elemTv j.castSucc j.succ) = F.lr (chain j) := fun j =>
    map_elemTv_castSucc_succ Ψ j (lr_ne_one (isLong_chain j))
      ((hΨA j).trans (map_rootGroup_eq_lr hR hRD (isLong_chain j)))
  have hvB : ∀ j : Fin 3, Ψ (elemTv j.succ j.castSucc) = F.lr (-chain j) := fun j =>
    map_elemTv_succ_castSucc Ψ j (lr_ne_one (isLong_chain j).neg)
      ((hΨB j).trans (map_rootGroup_eq_lr hR hRD (isLong_chain j).neg))
  refine ⟨Ψ, ⟨?_, lr_mem hR hRD isLong_r3, lr_mem hR hRD isLong_r3.neg, ?_, ?_, ?_, ?_⟩,
    fun j => ⟨(hΨA j) ▸ Subgroup.map_le_range Ψ _, (hΨB j) ▸ Subgroup.map_le_range Ψ _⟩⟩
  · have h01 : (0 : Fin 3).castSucc ≠ (0 : Fin 3).succ := Fin.castSucc_lt_succ.ne
    exact map_mem_of_elemTv_mem hDc Ψ h01 (by rw [hvA]; exact lr_mem hR hRD (isLong_chain 0))
  · intro i j hij
    obtain ⟨j', rfl, rfl⟩ : ∃ j' : Fin 3, j'.succ = i ∧ j'.castSucc = j :=
      ⟨⟨j.val, by omega⟩, Fin.ext (by simp; omega), Fin.ext rfl⟩
    rw [hvB]
    exact commute_lr isLong_r3 (isLong_chain j').neg
      (by fin_cases j' <;> rw [form_apply] <;> decide) (by fin_cases j' <;> decide)
  · intro i j hij
    obtain ⟨j', rfl, rfl⟩ : ∃ j' : Fin 3, j'.castSucc = i ∧ j'.succ = j :=
      ⟨⟨i.val, by omega⟩, Fin.ext rfl, Fin.ext (by simp; omega)⟩
    rw [hvA]
    exact commute_lr isLong_r3.neg (isLong_chain j')
      (by fin_cases j' <;> rw [form_apply] <;> decide) (by fin_cases j' <;> decide)
  · intro i j hi hj
    obtain rfl : i = (1 : Fin 3).succ := Fin.ext (by simp; omega)
    obtain rfl : j = (1 : Fin 3).castSucc := Fin.ext (by simp; omega)
    rw [hvB]
    have e : r1 + r3 + -r1 = r3 := by decide
    have := mul_lr_mem (F := F) hR hRD hDc isLong_r1_add_r3 isLong_r1.neg
      (by rw [e]; exact isLong_r3)
      (by rw [form_apply]; decide)
    rwa [e] at this
  · intro i j hi hj
    obtain rfl : i = (1 : Fin 3).castSucc := Fin.ext (by simp; omega)
    obtain rfl : j = (1 : Fin 3).succ := Fin.ext (by simp; omega)
    rw [hvA]
    have e : -(r1 + r3) + r1 = -r3 := by decide
    have := mul_lr_mem (F := F) hR hRD hDc isLong_r1_add_r3.neg isLong_r1
      (by rw [e]; exact isLong_r3.neg) (by rw [form_apply]; decide)
    rwa [e] at this

theorem exists_finrank_commSpaceOf_le_nine [Finite G] (hiso : NoIsolated R)
    (hDc : ∀ g, ∀ d ∈ D, g * d * g⁻¹ ∈ D) {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V} {ρ : G →* (V ≃ₗ[ZMod 2] V)}
    (hA : A2Action D Q ρ) :
    ∃ H₀ : Subgroup G, Module.finrank (ZMod 2) (commSpaceOf ρ H₀) ≤ 9 ∧
      ∀ γ : Fin 4 → ℤ, (γ = r0 ∨ γ = r1 ∨ γ = r2 ∨ γ = r3) →
        (F.X γ).map F.Ψ ≤ H₀ ∧ (F.X (-γ)).map F.Ψ ≤ H₀ := by
  obtain ⟨Ψ, hL, hle⟩ := exists_isLeviNode hR hRD hiso hDc
  refine ⟨Ψ.range ⊔ Subgroup.zpowers (F.lr r3) ⊔ Subgroup.zpowers (F.lr (-r3)),
    hL.finrank_commSpaceOf_le hA rfl, fun γ hγ => ?_⟩
  have h3 : (F.X r3).map F.Ψ ≤ Ψ.range ⊔ Subgroup.zpowers (F.lr r3) ⊔
      Subgroup.zpowers (F.lr (-r3)) := by
    rw [map_rootGroup_eq_lr hR hRD isLong_r3]
    exact le_sup_right.trans le_sup_left
  have h3' : (F.X (-r3)).map F.Ψ ≤ Ψ.range ⊔ Subgroup.zpowers (F.lr r3) ⊔
      Subgroup.zpowers (F.lr (-r3)) := by
    rw [map_rootGroup_eq_lr hR hRD isLong_r3.neg]
    exact le_sup_right
  have hR' : Ψ.range ≤ Ψ.range ⊔ Subgroup.zpowers (F.lr r3) ⊔ Subgroup.zpowers (F.lr (-r3)) :=
    le_sup_left.trans le_sup_left
  rcases hγ with rfl | rfl | rfl | rfl
  · exact ⟨(hle 0).1.trans hR', (hle 0).2.trans hR'⟩
  · exact ⟨(hle 1).1.trans hR', (hle 1).2.trans hR'⟩
  · exact ⟨(hle 2).1.trans hR', (hle 2).2.trans hR'⟩
  · exact ⟨h3, h3'⟩

end F4Frame

end CFSG.LargeExtraspecial.A2Mod.FrF
