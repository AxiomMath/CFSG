module

public import CFSG.Fischer.Classification.PartIII.U4.Link

public section

namespace CFSG.Fischer.Classification.LocalU4

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Fischer.Classification
  CFSG.Fischer.Classification.Unitary CFSG.Fischer.Classification.Beta
  CFSG.Fischer.Classification.LocalU CFSG.Fischer.Classification.LocalR3 F3

variable {m : ℕ} {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)}

theorem mul_mul_mem_sPt (hf : IsF3Form f) {z : Fin m → ZMod 3} {a b : R3 f}
    (ha : a ∈ sPt f z) (hb : b ∈ sPt f z) : a * b * a ∈ sPt f z := by
  obtain ⟨v, hv, hvz, rfl⟩ := ha
  obtain ⟨w, hw, hwz, rfl⟩ := hb
  refine ⟨act (F3.refl f v) w, by rw [(isIsom_refl hf v).norm, hw], ?_,
    (reflBar_conj hf v w).symm⟩
  rw [act_refl hv, LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hwz, hvz,
    mul_zero, add_zero]

theorem exists_conj_image_sPt (hf : IsF3Form f) (h : R3 f) {z : Fin m → ZMod 3} (hz0 : z ≠ 0)
    (hzz : f z z = 0) :
    ∃ z', z' ≠ 0 ∧ f z' z' = 0 ∧ (fun s => h * s * h⁻¹) '' sPt f z = sPt f z' := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective h
  have hG : IsIsom f (g : GL (Fin m) (ZMod 3)) := isIsom_of_mem hf g.2
  refine ⟨act (g : GL (Fin m) (ZMod 3)) z, fun h0 => hz0 (act_injective _ (h0.trans
    (act_zero _).symm)), by rw [hG.norm, hzz], Set.ext fun q => ⟨?_, ?_⟩⟩
  · rintro ⟨_, ⟨w, hw, hwz, rfl⟩, rfl⟩
    exact ⟨act (g : GL (Fin m) (ZMod 3)) w, by rw [hG.norm, hw], by rw [hG, hwz],
      (mk_conj_reflBar hf g w).symm⟩
  · rintro ⟨u, hu, huz, rfl⟩
    refine ⟨reflBar f (act (g : GL (Fin m) (ZMod 3))⁻¹ u), ⟨_, by rw [hG.inv.norm, hu],
      by rw [hG.inv_left, huz], rfl⟩, ?_⟩
    dsimp only
    rw [mk_conj_reflBar hf g, act_act_inv]

theorem flagInv_sPt (hf : IsF3Form f) (hm : 5 ≤ m) {w z : Fin m → ZMod 3} (hw : f w w = 1)
    (hwz : f w z = 0) (hz0 : z ≠ 0) (hzz : f z z = 0) :
    FlagInv (reflBar f w) (sPt f z ∩ LocalClass (D3 f) (reflBar f w)) (sPt f z) := by
  have hm4 : 4 ≤ m := by omega
  intro h hhw hhS
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective h
  obtain ⟨G, hGeq⟩ : ∃ G : GL (Fin m) (ZMod 3), (g : GL (Fin m) (ZMod 3)) = G := ⟨_, rfl⟩
  have hG : IsIsom f G := hGeq ▸ isIsom_of_mem hf g.2
  rw [sPt_inter_localClass hf hm4 hw] at hhS
  have hGw : f z (act G w) = 0 := by
    rw [mk_conj_reflBar hf g, hGeq] at hhw
    rcases (reflBar_eq_reflBar_iff hf hm4 hw (by rw [hG.norm, hw])).1 hhw.symm with h1 | h1 <;>
      rw [h1]
    · rw [hf.symm]; exact hwz
    · rw [LinearMap.BilinForm.neg_right, hf.symm, hwz, neg_zero]
  have hGy : ∀ y, f y y = 1 → f y w = 0 → f y z = 0 → f (act G y) z = 0 := by
    intro y hy hyw hyz
    have hmem : (QuotientGroup.mk g : R3 f) * reflBar f y * (QuotientGroup.mk g)⁻¹ ∈
        muPt f w z := by
      rw [← hhS]
      exact ⟨reflBar f y, ⟨y, hy, hyw, hyz, rfl⟩, rfl⟩
    rw [mk_conj_reflBar hf g, hGeq, reflBar_mem_muPt_iff hf hm4 (by rw [hG.norm, hy])] at hmem
    exact hmem.2
  obtain ⟨γ, hγ⟩ := exists_smul_eq_of_perp hf hm hw hz0 hzz (by rw [hf.symm]; exact hwz)
    (s := act G⁻¹ z) (by rw [hG.inv_left]; exact hGw)
    (fun y hy hyw hyz => by rw [hG.inv_left, hf.symm]; exact hGy y hy hyw hyz)
    (Or.inl (by rw [hG.inv.norm, hzz]))
  have hγ0 : γ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hγ
    exact hz0 (act_injective G⁻¹ (hγ.trans (act_zero _).symm))
  have hGz : act G z = γ⁻¹ • z := by
    have h1 : z = act G (γ • z) := by rw [← hγ, act_act_inv]
    rw [act_smul] at h1
    conv_rhs => rw [h1]
    rw [smul_smul, inv_mul_cancel₀ hγ0, one_smul]
  ext q
  constructor
  · rintro ⟨_, ⟨u, hu, huz, rfl⟩, rfl⟩
    refine ⟨act G u, by rw [hG.norm, hu], ?_, by rw [← hGeq]; exact (mk_conj_reflBar hf g u).symm⟩
    rw [← act_act_inv G z, hG, hγ, LinearMap.BilinForm.smul_right, huz, mul_zero]
  · rintro ⟨u, hu, huz, rfl⟩
    refine ⟨reflBar f (act G⁻¹ u), ⟨_, by rw [hG.inv.norm, hu], ?_, rfl⟩, ?_⟩
    · rw [hG.inv_left, hGz, LinearMap.BilinForm.smul_right, huz, mul_zero]
    · dsimp only
      rw [mk_conj_reflBar hf g, hGeq, act_act_inv]

theorem image_R3Congr_sPt {f' : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)}
    {e : (Fin m → ZMod 3) ≃ₗ[ZMod 3] (Fin m → ZMod 3)} (he : ∀ x y, f x y = f' (e x) (e y))
    (z : Fin m → ZMod 3) : R3Congr e he '' sPt f z = sPt f' (e z) := by
  ext q
  constructor
  · rintro ⟨_, ⟨w, hw, hwz, rfl⟩, rfl⟩
    exact ⟨e w, by rw [← he, hw], by rw [← he, hwz], (R3Congr_reflBar he w).symm⟩
  · rintro ⟨u, hu, huz, rfl⟩
    refine ⟨reflBar f (e.symm u), ⟨e.symm u, by rw [he, e.apply_symm_apply, hu],
      by rw [he, e.apply_symm_apply, huz], rfl⟩, ?_⟩
    rw [R3Congr_reflBar, e.apply_symm_apply]

theorem exists_isometry_I5Form {f : LinearMap.BilinForm (ZMod 3) (Fin 5 → ZMod 3)}
    (hf : IsF3Form f) (h45 : (D3 f).ncard = 45) :
    ∃ e : (Fin 5 → ZMod 3) ≃ₗ[ZMod 3] (Fin 5 → ZMod 3), ∀ x y, f x y = I5Form (e x) (e y) := by
  obtain ⟨δ, e, hδ, he⟩ := exists_linearEquiv_diagF3 (by norm_num) hf
  rcases hδ with rfl | rfl
  · rw [diagF3_five_one] at he
    exact ⟨e, he⟩
  · have := (ncard_D3_of_isometry e he).trans ncard_D3_diagF3_five_two
    omega

theorem exists_conj_image_sPt_eq_M18 {f : LinearMap.BilinForm (ZMod 3) (Fin 5 → ZMod 3)}
    (hf : IsF3Form f) (Φ : R3 f ≃* PG 4) (hΦ : Φ '' D3 f = DG 4) {z : Fin 5 → ZMod 3}
    (hz0 : z ≠ 0) (hzz : f z z = 0) (h18 : (sPt f z).ncard = 18) :
    ∃ c : PG 4, (fun s => c * s * c⁻¹) '' (Φ '' sPt f z) = M18 := by
  have hPG : Pair (PG 4) (DG 4) := pair_DG le_rfl
  have hF : MuSections (DG 4) := muSections_DG (n := 2) le_rfl
  have hc : IsChart Φ (D3 f) (DG 4) := hΦ ▸ isChart_mulEquiv Φ (D3 f)
  set N := Φ '' sPt f z with hNdef
  have hND : N ⊆ DG 4 := hc.image_subset (sPt_subset_D3 z)
  have hadm : IsAdm (DG 4) N :=
    (hc.isAdm_image_iff (sPt_subset_D3 z)).2 (isAdm_sPt hf (by norm_num) hz0 hzz)
  have hτ : ∀ a ∈ N, ∀ b ∈ N, a * b * a ∈ N := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact ⟨a * b * a, mul_mul_mem_sPt hf ha hb, by rw [map_mul, map_mul]⟩
  have hTF : ∀ g ∈ N, TwinFree (LocalClass (DG 4) g) (N ∩ LocalClass (DG 4) g) := by
    intro g hg
    obtain ⟨q, hq, hqg, hμ⟩ := hadm.2 g hg
    rw [hμ]
    exact hF.twinFree g (hND hg) q hq hqg
  have hMT : ∀ g ∈ N, MeetsTwins (LocalClass (DG 4) g) (N ∩ LocalClass (DG 4) g) := by
    intro g hg
    obtain ⟨q, hq, hqg, hμ⟩ := hadm.2 g hg
    rw [hμ]
    exact hF.meets g (hND hg) q hq hqg
  obtain ⟨_, ⟨w, hw, hwz, rfl⟩⟩ : (sPt f z).Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by rw [h18]; norm_num)
  have hg₀ : Φ (reflBar f w) ∈ N := ⟨_, ⟨w, hw, hwz, rfl⟩, rfl⟩
  obtain ⟨q₀, hq₀, hq₀g₀, hS₀⟩ := hadm.2 _ hg₀
  have hinv : FlagInv (Φ (reflBar f w)) (N ∩ LocalClass (DG 4) (Φ (reflBar f w))) N := by
    have h := (flagInv_sPt hf le_rfl hw hwz hz0 hzz).map Φ
    rwa [Set.image_inter Φ.injective, ← localClass_congr Φ hΦ rfl] at h
  obtain ⟨c, h6 | h18'⟩ := exists_conj_eq_M6_or_M18 hND hτ hTF hMT hg₀ hq₀ hq₀g₀ hS₀ hinv
  · have h1 := congrArg Set.ncard h6
    rw [Set.ncard_image_of_injective _ (conj_injective c), hNdef,
      Set.ncard_image_of_injective _ Φ.injective, h18, ncard_M6] at h1
    norm_num at h1
  · exact ⟨c, h18'⟩

theorem exists_image_sPt_eq_45 {f₁ f₂ : LinearMap.BilinForm (ZMod 3) (Fin 5 → ZMod 3)}
    (hf₁ : IsF3Form f₁) (hf₂ : IsF3Form f₂) (h₁ : (D3 f₁).ncard = 45) (h₂ : (D3 f₂).ncard = 45)
    (Ψ : R3 f₂ ≃* R3 f₁) (hΨ : Ψ '' D3 f₂ = D3 f₁) {z₂ : Fin 5 → ZMod 3} (hz₂0 : z₂ ≠ 0)
    (hz₂ : f₂ z₂ z₂ = 0) : ∃ z₁, z₁ ≠ 0 ∧ f₁ z₁ z₁ = 0 ∧ Ψ '' sPt f₂ z₂ = sPt f₁ z₁ := by
  obtain ⟨e₁, he₁⟩ := exists_isometry_I5Form hf₁ h₁
  obtain ⟨e₂, he₂⟩ := exists_isometry_I5Form hf₂ h₂
  obtain ⟨Ξ, hΞpt, hΞD⟩ := exists_mulEquiv_PG_four_R3_I5
  have h18 : (sPt f₂ z₂).ncard = 18 := by
    rw [← Set.ncard_image_of_injective _ (R3Congr e₂ he₂).injective, image_R3Congr_sPt he₂]
    exact ncard_sPt_I5Form (fun h => hz₂0 (e₂.map_eq_zero_iff.1 h)) (by rw [← he₂, hz₂])
  set Φ : R3 f₂ ≃* PG 4 := (Ψ.trans (R3Congr e₁ he₁)).trans Ξ.symm with hΦdef
  have hΦ : Φ '' D3 f₂ = DG 4 := by
    rw [hΦdef, MulEquiv.coe_trans, MulEquiv.coe_trans, Set.image_comp, Set.image_comp, hΨ,
      image_D3_R3Congr, ← hΞD, image_symm_image]
  obtain ⟨c, hc⟩ := exists_conj_image_sPt_eq_M18 hf₂ Φ hΦ hz₂0 hz₂ h18
  have hΦS : Φ '' sPt f₂ z₂ = (fun s => c⁻¹ * s * c⁻¹⁻¹) '' M18 := by
    rw [← hc, Set.image_image]
    conv_lhs => rw [← Set.image_id (Φ '' sPt f₂ z₂)]
    exact Set.image_congr fun s _ => by rw [id]; group
  have hstd : R3Congr e₁ he₁ '' (Ψ '' sPt f₂ z₂) =
      (fun s => Ξ c⁻¹ * s * (Ξ c⁻¹)⁻¹) '' sPt I5Form zStar := by
    have e1 : R3Congr e₁ he₁ '' (Ψ '' sPt f₂ z₂) = Ξ '' (Φ '' sPt f₂ z₂) := by
      rw [Set.image_image, Set.image_image]
      exact Set.image_congr fun s _ => by
        rw [hΦdef, MulEquiv.trans_apply, MulEquiv.apply_symm_apply, MulEquiv.trans_apply]
    rw [e1, hΦS, image_conj_map, image_M18_eq_sPt hΞpt]
  obtain ⟨z', hz'0, hz', hz'S⟩ := exists_conj_image_sPt isF3Form_I5Form (Ξ c⁻¹) zStar_ne_zero
    I5Form_zStar
  refine ⟨e₁.symm z', fun h => hz'0 (by rw [← e₁.apply_symm_apply z', h, map_zero]),
    by rw [he₁, e₁.apply_symm_apply, hz'], ?_⟩
  apply (Set.image_injective.2 (R3Congr e₁ he₁).injective)
  rw [hstd, hz'S, image_R3Congr_sPt he₁, e₁.apply_symm_apply]

theorem bijOn_of_isChart {X Y : Type} [Group X] [Group Y] {c : X → Y} {A : Set X}
    {F : Set Y} (h : IsChart c A F) : Set.BijOn c A F :=
  ⟨fun _ ha => h.mem ha, h.injOn, fun _ hy => h.exists_eq hy⟩

theorem eq_sPt_of_tauChart_45 {X : Type} [Group X]
    {f₁ f₂ : LinearMap.BilinForm (ZMod 3) (Fin 5 → ZMod 3)}
    (hf₁ : IsF3Form f₁) (hf₂ : IsF3Form f₂) (h₁ : (D3 f₁).ncard = 45) (h₂ : (D3 f₂).ncard = 45)
    {A B : Set X} (hBA : B ⊆ A) (hA : ∀ a ∈ A, ∀ b ∈ A, a * b * a ∈ A)
    {α₁ : X → R3 f₁} {α₂ : X → R3 f₂} (hc₁ : LocalR3.IsChart α₁ A (D3 f₁))
    (hc₂ : LocalR3.IsChart α₂ A (D3 f₂))
    (hτ₁ : ∀ a ∈ A, ∀ b ∈ A, α₁ (a * b * a) = α₁ a * α₁ b * α₁ a)
    (hτ₂ : ∀ a ∈ A, ∀ b ∈ A, α₂ (a * b * a) = α₂ a * α₂ b * α₂ a)
    {z₂ : Fin 5 → ZMod 3} (hz₂0 : z₂ ≠ 0) (hz₂ : f₂ z₂ z₂ = 0)
    (hB₂ : α₂ '' B = LocalR3.sPt f₂ z₂) :
    ∃ z₁, z₁ ≠ 0 ∧ f₁ z₁ z₁ = 0 ∧ α₁ '' B = LocalR3.sPt f₁ z₁ := by
  set E₁ := (bijOn_of_isChart hc₁).equiv α₁ with hE₁
  set E₂ := (bijOn_of_isChart hc₂).equiv α₂ with hE₂
  have hE₁a : ∀ a : A, (E₁ a : R3 f₁) = α₁ a := fun _ => rfl
  have hE₂a : ∀ a : A, (E₂ a : R3 f₂) = α₂ a := fun _ => rfl
  set Θ : D3 f₂ ≃ D3 f₁ := E₂.symm.trans E₁ with hΘdef
  have hΘ : ∀ a : A, Θ (E₂ a) = E₁ a := fun a => by
    rw [hΘdef, Equiv.trans_apply, Equiv.symm_apply_apply]
  have hP₁ := pair_R3 hf₁ (by norm_num)
  have hP₂ := pair_R3 hf₂ (by norm_num)
  have hΘτ : ∀ e e' : D3 f₂, Θ (tauE hP₂ e e') = tauE hP₁ (Θ e) (Θ e') := by
    intro e e'
    obtain ⟨a, rfl⟩ := E₂.surjective e
    obtain ⟨b, rfl⟩ := E₂.surjective e'
    have h1 : tauE hP₂ (E₂ a) (E₂ b) = E₂ ⟨a * b * a, hA a a.2 b b.2⟩ := by
      apply Subtype.ext
      show (E₂ a : R3 f₂) * E₂ b * E₂ a = E₂ ⟨a * b * a, hA a a.2 b b.2⟩
      simp only [hE₂a]
      exact (hτ₂ a a.2 b b.2).symm
    rw [h1, hΘ, hΘ, hΘ]
    apply Subtype.ext
    show (E₁ ⟨a * b * a, hA a a.2 b b.2⟩ : R3 f₁) = E₁ a * E₁ b * E₁ a
    simp only [hE₁a]
    exact hτ₁ a a.2 b b.2
  obtain ⟨Ψ, hΨ⟩ := exists_mulEquiv_of_tau_eq hP₂ hP₁ (center_R3_eq_bot hf₂ (by norm_num))
    (center_R3_eq_bot hf₁ (by norm_num)) Θ hΘτ
  have hΨD : Ψ '' D3 f₂ = D3 f₁ := image_eq_of_forall_eq Θ hΨ
  have hΨα : ∀ a ∈ A, Ψ (α₂ a) = α₁ a := fun a ha => by
    have h := hΨ (E₂ ⟨a, ha⟩)
    rwa [hΘ, hE₂a, hE₁a] at h
  have hB : α₁ '' B = Ψ '' (α₂ '' B) := by
    rw [Set.image_image]
    exact Set.image_congr fun b hb => (hΨα b (hBA hb)).symm
  obtain ⟨z₁, hz₁0, hz₁, hz₁S⟩ := exists_image_sPt_eq_45 hf₁ hf₂ h₁ h₂ Ψ hΨD hz₂0 hz₂
  exact ⟨z₁, hz₁0, hz₁, by rw [hB, hB₂, hz₁S]⟩

end CFSG.Fischer.Classification.LocalU4
