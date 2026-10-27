module

public import CFSG.Fischer.Classification.PartIII.R3.Admissible

public section

namespace CFSG.Fischer.Classification.LocalR3

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Fischer.Classification F3

variable {m n : ℕ} {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)}

theorem muPt_subset_localClass (hf : IsF3Form f) (hm : 4 ≤ m) {v : Fin m → ZMod 3}
    (hv : f v v = 1) (z : Fin m → ZMod 3) : muPt f v z ⊆ LocalClass (D3 f) (reflBar f v) := by
  rintro _ ⟨w, hw, hwv, -, rfl⟩
  exact reflBar_mem_localClass hf hm hv hw hwv

section Star

variable (hf : IsF3Form f) (hm : 4 ≤ m) {v : Fin m → ZMod 3} (hv : f v v = 1)
  (e : perpOne f v ≃ₗ[ZMod 3] (Fin n → ZMod 3))
  {f' : LinearMap.BilinForm (ZMod 3) (Fin n → ZMod 3)}
  (hf' : ∀ a b : perpOne f v, f' (e a) (e b) = f a b)

@[expose] noncomputable def starChart : R3 f → R3 f' :=
  localQuotientEquivR3 hf hm hv e hf' ∘ lqMap (D3 f) (reflBar f v)

theorem isChart_starChart (hm5 : 5 ≤ m) :
    IsChart (starChart hf hm hv e hf') (LocalClass (D3 f) (reflBar f v)) (D3 f') := by
  have hP := pair_R3 hf hm
  have hi := Pair.starImage_injective hP (exists_not_commute_localClass hf hm5 hv)
  have h2 := isChart_mulEquiv (localQuotientEquivR3 hf hm hv e hf')
    (LocalImages (D3 f) (reflBar f v))
  rw [localQuotientEquivR3_image] at h2
  exact (Pair.isChart_lqMap hP hi).comp h2

theorem starChart_image_muPt {z : Fin m → ZMod 3} (hzv : f z v = 0) :
    starChart hf hm hv e hf' '' muPt f v z = sPt f' (e ⟨z, mem_perpOne.2 hzv⟩) := by
  rw [starChart, Set.image_comp, lqMap_image (muPt_subset_localClass hf hm hv z),
    localQuotientEquivR3_image_muPt hf hm hv e hf' hzv]
  rfl

end Star

theorem exists_starChart (hf : IsF3Form f) (hm : 5 ≤ m) {v : Fin m → ZMod 3} (hv : f v v = 1) :
    ∃ (f' : LinearMap.BilinForm (ZMod 3) (Fin (m - 1) → ZMod 3)) (Ψ : R3 f → R3 f'),
      IsF3Form f' ∧ IsChart Ψ (LocalClass (D3 f) (reflBar f v)) (D3 f') ∧
      (∀ z, IsIsoPt f v z → ∃ z', z' ≠ 0 ∧ f' z' z' = 0 ∧ Ψ '' muPt f v z = sPt f' z') ∧
      ∀ z', z' ≠ 0 → f' z' z' = 0 → ∃ z, IsIsoPt f v z ∧ Ψ '' muPt f v z = sPt f' z' := by
  let e : perpOne f v ≃ₗ[ZMod 3] (Fin (m - 1) → ZMod 3) :=
    LinearEquiv.ofFinrankEq _ _ (by rw [finrank_perpOne hv, Module.finrank_fin_fun])
  have happ := restrictForm_apply (f := f) e
  refine ⟨restrictForm f e, starChart hf (by omega) hv e happ, isF3Form_restrictForm hf hv e,
    isChart_starChart hf (by omega) hv e happ hm, fun z hz => ?_, fun z' hz'0 hz' => ?_⟩
  · refine ⟨e ⟨z, mem_perpOne.2 hz.2.2⟩, fun h => hz.1 ?_, by rw [happ]; exact hz.2.1,
      starChart_image_muPt hf (by omega) hv e happ hz.2.2⟩
    exact congrArg Subtype.val ((LinearEquiv.map_eq_zero_iff e).1 h)
  · set Z := e.symm z'
    have hZ : e Z = z' := e.apply_symm_apply z'
    refine ⟨Z, ⟨fun h => hz'0 ?_, ?_, mem_perpOne.1 Z.2⟩, ?_⟩
    · rw [← hZ, show Z = 0 from Subtype.ext h, map_zero]
    · rw [← happ, hZ]; exact hz'
    · rw [starChart_image_muPt hf (by omega) hv e happ (mem_perpOne.1 Z.2), Subtype.coe_eta, hZ]

theorem eq_sPt_of_isChart {X : Type} [Group X] {n₁ n₂ : ℕ}
    {f₁ : LinearMap.BilinForm (ZMod 3) (Fin n₁ → ZMod 3)}
    {f₂ : LinearMap.BilinForm (ZMod 3) (Fin n₂ → ZMod 3)} (hf₁ : IsF3Form f₁)
    (hf₂ : IsF3Form f₂) (hn₁ : 6 ≤ n₁) (hn₂ : 6 ≤ n₂) {A B : Set X} (hBA : B ⊆ A)
    {α₁ : X → R3 f₁} {α₂ : X → R3 f₂} (h₁ : IsChart α₁ A (D3 f₁)) (h₂ : IsChart α₂ A (D3 f₂))
    {z₂ : Fin n₂ → ZMod 3} (hz₂0 : z₂ ≠ 0) (hz₂ : f₂ z₂ z₂ = 0) (hB₂ : α₂ '' B = sPt f₂ z₂)
    (hne : (sPt f₂ z₂).Nonempty) :
    ∃ z₁, z₁ ≠ 0 ∧ f₁ z₁ z₁ = 0 ∧ α₁ '' B = sPt f₁ z₁ := by
  have hadmB : IsAdm A B := (h₂.isAdm_image_iff hBA).1 (hB₂ ▸ isAdm_sPt hf₂ (by omega) hz₂0 hz₂)
  have hadm₁ : IsAdm (D3 f₁) (α₁ '' B) := (h₁.isAdm_image_iff hBA).2 hadmB
  obtain ⟨_, ⟨b, hb, rfl⟩⟩ : (α₁ '' B).Nonempty := by
    obtain ⟨_, ⟨b, hb, rfl⟩⟩ := hB₂ ▸ hne
    exact ⟨_, b, hb, rfl⟩
  obtain ⟨w₁, hw₁, hwb⟩ := mem_D3_iff.1 (h₁.mem (hBA hb))
  have hg₁ : reflBar f₁ w₁ ∈ α₁ '' B := hwb ▸ ⟨b, hb, rfl⟩
  obtain ⟨z₁, hz₁, hS₁⟩ := exists_isIsoPt_of_isAdm hf₁ (by omega) hadm₁ hw₁ hg₁
  have hsub := subset_sPt_of_isAdm hf₁ hn₁ hadm₁ hw₁ hg₁ hz₁ hS₁
  set R := A ∩ α₁ ⁻¹' sPt f₁ z₁ with hR
  have hRA : R ⊆ A := Set.inter_subset_left
  have hR₁ : α₁ '' R = sPt f₁ z₁ := by
    rw [hR, Set.image_inter_preimage, h₁.image_eq]
    exact Set.inter_eq_right.2 (sPt_subset_D3 z₁)
  have hadmR : IsAdm A R :=
    (h₁.isAdm_image_iff hRA).1 (hR₁ ▸ isAdm_sPt hf₁ (by omega) hz₁.1 hz₁.2.1)
  have hBR : B ⊆ R := fun b hb => ⟨hBA hb, hsub ⟨b, hb, rfl⟩⟩
  have hR₂ : α₂ '' R = sPt f₂ z₂ := eq_sPt_of_subset_of_isAdm hf₂ hn₂
    ((h₂.isAdm_image_iff hRA).2 hadmR) hz₂0 hz₂ (hB₂ ▸ Set.image_mono hBR) hne
  have hRB : R = B := (h₂.image_eq_image_iff hRA hBA).1 (hR₂.trans hB₂.symm)
  exact ⟨z₁, hz₁.1, hz₁.2.1, hRB ▸ hR₁⟩

end CFSG.Fischer.Classification.LocalR3
