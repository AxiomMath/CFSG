module

public import CFSG.Fischer.Classification.PartIII.U.SixForms

public section

namespace CFSG.Fischer.Classification.LocalU

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Fischer.Classification LocalR3 F3

variable {f : LinearMap.BilinForm (ZMod 3) (Fin 6 → ZMod 3)}

theorem exists_starChart_six (hf : IsF3Form f) {v : Fin 6 → ZMod 3} (hv : f v v = 1) :
    ∃ (f' : LinearMap.BilinForm (ZMod 3) (Fin 5 → ZMod 3)) (Ψ : R3 f → R3 f')
      (e : perpOne f v ≃ₗ[ZMod 3] (Fin 5 → ZMod 3)),
      IsF3Form f' ∧ (∀ a b : perpOne f v, f' (e a) (e b) = f a b) ∧
      IsChart Ψ (LocalClass (D3 f) (reflBar f v)) (D3 f') ∧
      (∀ a ∈ LocalClass (D3 f) (reflBar f v), ∀ b ∈ LocalClass (D3 f) (reflBar f v),
        Ψ (a * b * a) = Ψ a * Ψ b * Ψ a) ∧
      (∀ z, IsIsoPt f v z → ∃ z', z' ≠ 0 ∧ f' z' z' = 0 ∧ Ψ '' muPt f v z = sPt f' z') ∧
      ∀ z', z' ≠ 0 → f' z' z' = 0 → ∃ z, IsIsoPt f v z ∧ Ψ '' muPt f v z = sPt f' z' := by
  let e : perpOne f v ≃ₗ[ZMod 3] (Fin 5 → ZMod 3) :=
    LinearEquiv.ofFinrankEq _ _ (by rw [finrank_perpOne hv, Module.finrank_fin_fun])
  have happ := restrictForm_apply (f := f) e
  refine ⟨restrictForm f e, starChart hf (by norm_num) hv e happ, e,
    isF3Form_restrictForm hf hv e, happ, isChart_starChart hf (by norm_num) hv e happ
    (by norm_num), fun a ha b hb => ?_, fun z hz => ?_, fun z' hz'0 hz' => ?_⟩
  · simp only [starChart, Function.comp_apply, lqMap_mul_mul ha hb, map_mul]
  · refine ⟨e ⟨z, mem_perpOne.2 hz.2.2⟩, fun h => hz.1 ?_, by rw [happ]; exact hz.2.1,
      starChart_image_muPt hf (by norm_num) hv e happ hz.2.2⟩
    exact congrArg Subtype.val ((LinearEquiv.map_eq_zero_iff e).1 h)
  · set Z := e.symm z'
    have hZ : e Z = z' := e.apply_symm_apply z'
    refine ⟨Z, ⟨fun h => hz'0 ?_, ?_, mem_perpOne.1 Z.2⟩, ?_⟩
    · rw [← hZ, show Z = 0 from Subtype.ext h, map_zero]
    · rw [← happ, hZ]; exact hz'
    · rw [starChart_image_muPt hf (by norm_num) hv e happ (mem_perpOne.1 Z.2), Subtype.coe_eta,
        hZ]

@[expose] def Comparison (Good : LinearMap.BilinForm (ZMod 3) (Fin 5 → ZMod 3) → Prop) : Prop :=
  ∀ {X : Type} [Group X] {f₁ f₂ : LinearMap.BilinForm (ZMod 3) (Fin 5 → ZMod 3)},
    IsF3Form f₁ → IsF3Form f₂ → Good f₁ → Good f₂ → ∀ {A B : Set X}, B ⊆ A →
    (∀ a ∈ A, ∀ b ∈ A, a * b * a ∈ A) → ∀ {α₁ : X → R3 f₁} {α₂ : X → R3 f₂},
    IsChart α₁ A (D3 f₁) → IsChart α₂ A (D3 f₂) →
    (∀ a ∈ A, ∀ b ∈ A, α₁ (a * b * a) = α₁ a * α₁ b * α₁ a) →
    (∀ a ∈ A, ∀ b ∈ A, α₂ (a * b * a) = α₂ a * α₂ b * α₂ a) → ∀ {z₂ : Fin 5 → ZMod 3},
    z₂ ≠ 0 → f₂ z₂ z₂ = 0 → α₂ '' B = sPt f₂ z₂ →
    ∃ z₁, z₁ ≠ 0 ∧ f₁ z₁ z₁ = 0 ∧ α₁ '' B = sPt f₁ z₁

section Local

variable {G : Type} [Group G] {D : Set G}

theorem isAdm_image_muSet_six (hP : Pair G D) (hZ : Subgroup.center G = ⊥)
    (hS : IsSimpleGroup (commutator G)) {d : G} (hd : d ∈ D) (hf : IsF3Form f)
    {Good : LinearMap.BilinForm (ZMod 3) (Fin 5 → ZMod 3) → Prop}
    (hgood : ∀ v, f v v = 1 → ∀ f' : LinearMap.BilinForm (ZMod 3) (Fin 5 → ZMod 3),
      IsF3Form f' → ∀ e : perpOne f v ≃ₗ[ZMod 3] (Fin 5 → ZMod 3),
        (∀ a b : perpOne f v, f' (e a) (e b) = f a b) → Good f')
    (hIC : Comparison Good) (φ : LocalQuotient D d ≃* R3 f)
    (hφ : φ '' LocalImages D d = D3 f) {x : G} (hx : x ∈ D) (hxd : x * d ≠ d * x) :
    IsAdm (D3 f) ((φ ∘ lqMap D d) '' muSet D d x) := by
  have hm4 : 4 ≤ 6 := by norm_num
  set ι : G → R3 f := φ ∘ lqMap D d with hιdef
  have hι : IsChart ι (LocalClass D d) (D3 f) :=
    isChart_of_localQuotientEquiv hP (Pair.starImage_injective_of_simple hP hZ hS hd) φ hφ
  refine ⟨hι.image_subset (muSet_subset_localClass d x), ?_⟩
  rintro _ ⟨f₀, hf₀, rfl⟩
  have hf₀d : f₀ ∈ LocalClass D d := hf₀.1
  have hf₀D : f₀ ∈ D := hf₀d.1
  have hdf₀ : d ∈ LocalClass D f₀ := mem_localClass_symm hd hf₀d
  have hxf₀ : x ∈ LocalClass D f₀ := mem_localClass_symm hx hf₀.2
  obtain ⟨w, hw, hwg⟩ := mem_D3_iff.1 (hι.mem hf₀d)
  obtain ⟨fw, Ψw, ew, hfw, hew, hΨw, hΨwτ, -, hΨw2⟩ := exists_starChart_six hf hw
  obtain ⟨φ₀, hφ₀⟩ := exists_localQuotientEquiv_of_mem hP hd hf₀D φ hφ
  set ι₀ : G → R3 f := φ₀ ∘ lqMap D f₀ with hι₀def
  have hι₀ : IsChart ι₀ (LocalClass D f₀) (D3 f) :=
    isChart_of_localQuotientEquiv hP (Pair.starImage_injective_of_simple hP hZ hS hf₀D) φ₀ hφ₀
  obtain ⟨a, ha, hag⟩ := mem_D3_iff.1 (hι₀.mem hdf₀)
  obtain ⟨b, hb, hbg⟩ := mem_D3_iff.1 (hι₀.mem hxf₀)
  obtain ⟨fa, Ψa, ea, hfa, hea, hΨa, hΨaτ, hΨa1, -⟩ := exists_starChart_six hf ha
  have hA := localClass_localClass_eq_inter (D := D) d f₀
  have hAd : LocalClass (LocalClass D d) f₀ ⊆ LocalClass D d := hA ▸ Set.inter_subset_left
  have hAf : LocalClass (LocalClass D d) f₀ ⊆ LocalClass D f₀ := hA ▸ Set.inter_subset_right
  have hAτ : ∀ a ∈ LocalClass (LocalClass D d) f₀, ∀ b ∈ LocalClass (LocalClass D d) f₀,
      a * b * a ∈ LocalClass (LocalClass D d) f₀ := fun a ha b hb =>
    hA ▸ ⟨Pair.mul_mul_mem_localClass_of_mem hP (hAd ha) (hAd hb),
      Pair.mul_mul_mem_localClass_of_mem hP (hAf ha) (hAf hb)⟩
  have hιA : ∀ s ∈ LocalClass (LocalClass D d) f₀, ι s ∈ LocalClass (D3 f) (reflBar f w) :=
    fun s hs => by rw [hwg, ← hι.image_localClass hf₀d]; exact ⟨s, hs, rfl⟩
  have hι₀A : ∀ s ∈ LocalClass (LocalClass D d) f₀, ι₀ s ∈ LocalClass (D3 f) (reflBar f a) :=
    fun s hs => by
      rw [hag, ← hι₀.image_localClass hdf₀, ← localClass_localClass_comm]
      exact ⟨s, hs, rfl⟩
  have hα : IsChart (Ψw ∘ ι) (LocalClass (LocalClass D d) f₀) (D3 fw) := by
    have h := hι.localClass hf₀d
    rw [← hwg] at h
    exact h.comp hΨw
  have hα' : IsChart (Ψa ∘ ι₀) (LocalClass (LocalClass D d) f₀) (D3 fa) := by
    have h := hι₀.localClass hdf₀
    rw [← hag, ← localClass_localClass_comm] at h
    exact h.comp hΨa
  have hατ : ∀ a ∈ LocalClass (LocalClass D d) f₀, ∀ b ∈ LocalClass (LocalClass D d) f₀,
      (Ψw ∘ ι) (a * b * a) = (Ψw ∘ ι) a * (Ψw ∘ ι) b * (Ψw ∘ ι) a := fun a ha b hb => by
    have h1 : ι (a * b * a) = ι a * ι b * ι a := by
      simp only [hιdef, Function.comp_apply, lqMap_mul_mul (hAd ha) (hAd hb), map_mul]
    simp only [Function.comp_apply, h1, hΨwτ _ (hιA a ha) _ (hιA b hb)]
  have hα'τ : ∀ a ∈ LocalClass (LocalClass D d) f₀, ∀ b ∈ LocalClass (LocalClass D d) f₀,
      (Ψa ∘ ι₀) (a * b * a) = (Ψa ∘ ι₀) a * (Ψa ∘ ι₀) b * (Ψa ∘ ι₀) a := fun a' ha' b' hb' => by
    have h1 : ι₀ (a' * b' * a') = ι₀ a' * ι₀ b' * ι₀ a' := by
      simp only [hι₀def, Function.comp_apply, lqMap_mul_mul (hAf ha') (hAf hb'), map_mul]
    simp only [Function.comp_apply, h1, hΨaτ _ (hι₀A a' ha') _ (hι₀A b' hb')]
  set B := LocalClass (LocalClass D d) f₀ ∩ LocalClass D x with hBdef
  have hBA : B ⊆ LocalClass (LocalClass D d) f₀ := Set.inter_subset_left
  have hB : B = muSet (LocalClass D f₀) d x := by
    ext s
    simp only [hBdef, muSet, mem_localClass, Set.mem_inter_iff]
    tauto
  have hba : reflBar f b * reflBar f a ≠ reflBar f a * reflBar f b := by
    rw [hag, hbg]
    exact fun h => hxd ((hι₀.comm_iff x hxf₀ d hdf₀).2 h)
  obtain ⟨z', hz', hz'μ⟩ : ∃ z', IsIsoPt f a z' ∧
      muPt f a z' = muSet (D3 f) (reflBar f a) (reflBar f b) := by
    have hfam : muSet (D3 f) (reflBar f a) (reflBar f b) ∈ muFamily (D3 f) (reflBar f a) :=
      ⟨_, reflBar_mem_D3 hb, hba, rfl⟩
    rw [muFamily_D3 hf hm4 ha] at hfam
    exact hfam
  obtain ⟨z'', hz''0, hz'', hΨz''⟩ := hΨa1 z' hz'
  have hα'B : (Ψa ∘ ι₀) '' B = sPt fa z'' := by
    rw [Set.image_comp, hB, hι₀.image_muSet hdf₀ hxf₀, ← hag, ← hbg, ← hz'μ, hΨz'']
  obtain ⟨z₁, hz₁0, hz₁, hαB⟩ := hIC hfw hfa (hgood w hw fw hfw ew hew)
    (hgood a ha fa hfa ea hea) hBA hAτ hα hα' hατ hα'τ hz''0 hz'' hα'B
  obtain ⟨ζ, hζ, hΨζ⟩ := hΨw2 z₁ hz₁0 hz₁
  have hιB : ι '' B = muPt f w ζ := by
    have hsub1 : ι '' B ⊆ LocalClass (D3 f) (reflBar f w) := by
      rintro _ ⟨s, hs, rfl⟩
      exact hιA s (hBA hs)
    refine (hΨw.image_eq_image_iff hsub1 (muPt_subset_localClass hf hm4 hw ζ)).1 ?_
    rw [← Set.image_comp, hαB, hΨζ]
  have hwζ : f w ζ = 0 := by rw [hf.symm]; exact hζ.2.2
  have hu : f (w + ζ) (w + ζ) = 1 := by rw [norm_add hf, hw, hwζ, hζ.2.1]; ring
  refine ⟨reflBar f (w + ζ), reflBar_mem_D3 hu, ?_, ?_⟩
  · rw [← hwg]
    exact reflBar_add_not_commute hf hm4 hw hζ
  · rw [← hwg, muSet_eq_muPt hf hm4 hw hu, add_sub_cancel_left, ← hιB, hwg,
      ← hι.image_localClass hf₀d,
      ← hι.image_inter (muSet_subset_localClass d x) (localClass_subset _ _)]
    congr 1
    ext s
    simp only [hBdef, muSet, mem_localClass, Set.mem_inter_iff]
    tauto

end Local

theorem comparison_normOneCompl : Comparison NormOneCompl := by
  intro X _ f₁ f₂ hf₁ hf₂ hN₁ _ A B hBA _ α₁ α₂ h₁ h₂ _ _ z₂ hz₂0 hz₂ hB₂
  have hadmB : IsAdm A B :=
    (h₂.isAdm_image_iff hBA).1 (hB₂ ▸ isAdm_sPt hf₂ (by norm_num) hz₂0 hz₂)
  have hadm₁ : IsAdm (D3 f₁) (α₁ '' B) := (h₁.isAdm_image_iff hBA).2 hadmB
  obtain ⟨z₂', hz₂'z₂', hz₂z₂', -⟩ := exists_hyp_partner_of_dual hf₂ (k := 0) (b := Fin.elim0)
    (b' := Fin.elim0) (fun i => i.elim0) (fun _ _ i => i.elim0) hz₂0 hz₂ (fun i => i.elim0)
  have hz₂'z₂ : f₂ z₂' z₂ = 1 := by rw [hf₂.symm]; exact hz₂z₂'
  obtain ⟨t, htt, htb⟩ := exists_norm_perp_of_dual hf₂ (k := 2) (by norm_num)
    (b := ![z₂, z₂']) (b' := ![z₂', z₂])
    (fun i j => by fin_cases i <;> fin_cases j <;> simp [hz₂, hz₂'z₂', hz₂z₂', hz₂'z₂])
    (fun y hy i => by
      have h0 := hy 0
      have h1 := hy 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
      fin_cases i <;> simp [h0, h1]) one_ne_zero
  have htz : f₂ t z₂ = 0 := htb 1
  obtain ⟨s, hs, -⟩ : reflBar f₂ t ∈ α₂ '' B := hB₂ ▸ ⟨t, htt, htz, rfl⟩
  obtain ⟨w₁, hw₁, hwg⟩ := mem_D3_iff.1 (h₁.mem (hBA hs))
  exact eq_sPt_of_isAdm_five hf₁ hN₁ hadm₁ hw₁ (by rw [hwg]; exact ⟨s, hs, rfl⟩)

end CFSG.Fischer.Classification.LocalU
