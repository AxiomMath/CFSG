module

public import CFSG.CGT.Timmesfeld75.NormalClosure
public import CFSG.CGT.T75N.UnitaryTwoGen
public import CFSG.CGT.Timmesfeld75.CentralQuotient
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.FinalTheorem

public noncomputable section

namespace CFSG.CGT.T75E

open CFSG.CGT.Timmesfeld75 CFSG.BenderSuzuki CFSG.Open

section Defs

variable {K : Type} [Group K]

@[expose] def T3 (Tb : Subgroup K) (c₁ c₂ : K) : Fin 3 → Subgroup K :=
  ![Tb, conjSubgroup c₁ Tb, conjSubgroup c₂ Tb]

@[expose] def Y3 (Tb : Subgroup K) (c₁ c₂ : K) : Subgroup K :=
  Tb ⊔ conjSubgroup c₁ Tb ⊔ conjSubgroup c₂ Tb

theorem T3_zero (Tb : Subgroup K) (c₁ c₂ : K) : T3 Tb c₁ c₂ 0 = Tb := rfl

theorem T3_one (Tb : Subgroup K) (c₁ c₂ : K) : T3 Tb c₁ c₂ 1 = conjSubgroup c₁ Tb := rfl

theorem Y3_eq (Tb : Subgroup K) (c₁ c₂ : K) :
    Y3 Tb c₁ c₂ = T3 Tb c₁ c₂ 0 ⊔ T3 Tb c₁ c₂ 1 ⊔ T3 Tb c₁ c₂ 2 := rfl

theorem T3_le_Y3 (Tb : Subgroup K) (c₁ c₂ : K) (i : Fin 3) : T3 Tb c₁ c₂ i ≤ Y3 Tb c₁ c₂ := by
  fin_cases i
  · exact le_sup_of_le_left le_sup_left
  · exact le_sup_of_le_left le_sup_right
  · exact le_sup_right

theorem exists_conj_T3 [Finite K] {Tb : Subgroup K} (hT : IsWC Tb) (c₁ c₂ : K) (i : Fin 3) :
    ∃ y : ↥(Y3 Tb c₁ c₂), T3 Tb c₁ c₂ i = conjSubgroup (y : K) Tb := by
  have hTY : Tb ≤ Y3 Tb c₁ c₂ := T3_le_Y3 Tb c₁ c₂ 0
  fin_cases i
  · exact ⟨1, by simp [T3_zero, conjSubgroup_one]⟩
  · obtain ⟨x, hx, hxe⟩ := exists_mem_conj_eq_of_le hT hTY (T3_le_Y3 Tb c₁ c₂ 1)
    exact ⟨⟨x, hx⟩, hxe⟩
  · obtain ⟨x, hx, hxe⟩ := exists_mem_conj_eq_of_le hT hTY (T3_le_Y3 Tb c₁ c₂ 2)
    exact ⟨⟨x, hx⟩, hxe⟩

end Defs

section QSide

variable {K : Type} [Group K] {Tb : Subgroup K} {c₁ c₂ : K} {f : ℕ}

instance finite_psu3Model (n : ℕ) : Finite (PSU3Model n) := by
  have : Finite (Matrix.ProjGenLinGroup (Fin 3) (GaloisField 2 (2 * n))) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  exact Subtype.finite

@[expose] def imgA (ρ : ↥(Y3 Tb c₁ c₂) →* PSU3Model f) (T : Subgroup K) :
    Subgroup (PSU3Model f) :=
  (T.subgroupOf (Y3 Tb c₁ c₂)).map ρ

theorem isElemAbelian_T3 [Finite K] (hT : IsWC Tb) (c₁ c₂ : K) (i : Fin 3) :
    IsElemAbelian 2 (T3 Tb c₁ c₂ i) := by
  fin_cases i
  · exact hT.1
  · exact isElemAbelian_conjSubgroup hT.1 c₁
  · exact isElemAbelian_conjSubgroup hT.1 c₂

theorem imgA_sq [Finite K] (ρ : ↥(Y3 Tb c₁ c₂) →* PSU3Model f) (hT : IsWC Tb) (i : Fin 3) :
    ∀ a ∈ imgA ρ (T3 Tb c₁ c₂ i), a * a = 1 := by
  rintro _ ⟨t, ht, rfl⟩
  have h1 : (t : K) ∈ T3 Tb c₁ c₂ i := Subgroup.mem_subgroupOf.1 ht
  have h2 : (t : K) * t = 1 := by
    simpa [pow_two] using (isElemAbelian_T3 hT c₁ c₂ i).2 _ h1
  rw [← map_mul]
  have : t * t = 1 := Subtype.ext (by simpa using h2)
  rw [this, map_one]

theorem imgA_conj [Finite K] (ρ : ↥(Y3 Tb c₁ c₂) →* PSU3Model f) (hT : IsWC Tb) (i : Fin 3) :
    ∃ g : PSU3Model f, imgA ρ (T3 Tb c₁ c₂ i) = conjSubgroup g (imgA ρ Tb) := by
  obtain ⟨y, hy⟩ := exists_conj_T3 hT c₁ c₂ i
  refine ⟨ρ y, ?_⟩
  unfold imgA
  rw [hy, ← conjSubgroup_subgroupOf, map_conjSubgroup]

theorem iSup_imgA (ρ : ↥(Y3 Tb c₁ c₂) →* PSU3Model f) (hρ : Function.Surjective ρ) :
    imgA ρ (T3 Tb c₁ c₂ 0) ⊔ imgA ρ (T3 Tb c₁ c₂ 1) ⊔ imgA ρ (T3 Tb c₁ c₂ 2) = ⊤ := by
  unfold imgA
  rw [← Subgroup.map_sup, ← Subgroup.map_sup, ← Subgroup.subgroupOf_sup (T3_le_Y3 _ _ _ 0)
    (T3_le_Y3 _ _ _ 1), ← Subgroup.subgroupOf_sup
      (sup_le (T3_le_Y3 _ _ _ 0) (T3_le_Y3 _ _ _ 1)) (T3_le_Y3 _ _ _ 2),
    ← Y3_eq, Subgroup.subgroupOf_self, Subgroup.map_top_of_surjective _ hρ]

theorem nontrivial_psu3Model (hf : 2 ≤ f) : Nontrivial (PSU3Model f) := by
  have hQ : IsBenderGroup (PSU3Model f) := .isPSU3 f hf (MulEquiv.refl _)
  obtain ⟨a, b, hab⟩ := CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.exists_not_commute hQ
  exact ⟨⟨a, b, fun h => hab (by subst h; exact Commute.refl a)⟩⟩

theorem imgA_ne_bot [Finite K] (ρ : ↥(Y3 Tb c₁ c₂) →* PSU3Model f) (hρ : Function.Surjective ρ)
    (hT : IsWC Tb) (hf : 2 ≤ f) : imgA ρ Tb ≠ ⊥ := by
  intro h
  have : Nontrivial (PSU3Model f) := nontrivial_psu3Model hf
  have h0 : imgA ρ (T3 Tb c₁ c₂ 0) = ⊥ := h
  have hi : ∀ i, imgA ρ (T3 Tb c₁ c₂ i) = ⊥ := by
    intro i
    obtain ⟨g, hg⟩ := imgA_conj ρ hT i
    rw [hg]
    have h' : imgA ρ Tb = ⊥ := h
    rw [h']
    ext x
    simp [conjSubgroup, Subgroup.mem_bot]
  have := iSup_imgA ρ hρ
  rw [hi 0, hi 1, hi 2] at this
  simp only [bot_sup_eq] at this
  exact bot_ne_top this

theorem imgA_sup_ne_top [Finite K] (ρ : ↥(Y3 Tb c₁ c₂) →* PSU3Model f) (hT : IsWC Tb)
    (hf : 2 ≤ f) (i j : Fin 3) : imgA ρ (T3 Tb c₁ c₂ i) ⊔ imgA ρ (T3 Tb c₁ c₂ j) ≠ ⊤ := by
  obtain ⟨gi, hgi⟩ := imgA_conj ρ hT i
  obtain ⟨gj, hgj⟩ := imgA_conj ρ hT j
  have hj : imgA ρ (T3 Tb c₁ c₂ j) = conjSubgroup (gj * gi⁻¹) (imgA ρ (T3 Tb c₁ c₂ i)) := by
    rw [hgi, hgj, conjSubgroup_conjSubgroup]
    simp
  rw [hj]
  exact CFSG.CGT.T75N.sup_conj_ne_top_of_psu3 hf (MulEquiv.refl _) _ (imgA_sq ρ hT i)
    (gj * gi⁻¹)

theorem Y3_ne_sup [Finite K] (ρ : ↥(Y3 Tb c₁ c₂) →* PSU3Model f) (hρ : Function.Surjective ρ)
    (hT : IsWC Tb) (hf : 2 ≤ f) (i j : Fin 3) : Y3 Tb c₁ c₂ ≠ T3 Tb c₁ c₂ i ⊔ T3 Tb c₁ c₂ j := by
  intro h
  refine imgA_sup_ne_top ρ hT hf i j ?_
  unfold imgA
  rw [← Subgroup.map_sup, ← Subgroup.subgroupOf_sup (T3_le_Y3 _ _ _ i) (T3_le_Y3 _ _ _ j),
    ← h, Subgroup.subgroupOf_self, Subgroup.map_top_of_surjective _ hρ]

end QSide

end CFSG.CGT.T75E
