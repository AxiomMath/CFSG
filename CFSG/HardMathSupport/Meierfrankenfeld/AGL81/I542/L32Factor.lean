module

public import CFSG.Quasithin.H13.NQTermTensorEquality

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542

open Module CFSG.QuasithinUnique.Setup.Family CFSG.Quasithin.H13.NQTerm

variable {S : Type*} [AddCommGroup S] [Module (ZMod 2) S]

@[expose] noncomputable def yRep (Y : Subgroup (Module.End (ZMod 2) S)ˣ) (eY : ↥Y ≃* GL32) :
    GL32 →* (S ≃ₗ[ZMod 2] S) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) S).toMonoidHom.comp
    (Y.subtype.comp eY.symm.toMonoidHom)

theorem yRep_apply (Y : Subgroup (Module.End (ZMod 2) S)ˣ) (eY : ↥Y ≃* GL32) (g : GL32) (v : S) :
    yRep Y eY g v = (((eY.symm g : ↥Y) : (Module.End (ZMod 2) S)ˣ) : Module.End (ZMod 2) S) v :=
  rfl

@[expose] def yImg (Y : Subgroup (Module.End (ZMod 2) S)ˣ) (eY : ↥Y ≃* GL32)
    (A : Subgroup (Module.End (ZMod 2) S)ˣ) : Subgroup GL32 :=
  (A.subgroupOf Y).map eY.toMonoidHom

theorem mem_yImg {Y A : Subgroup (Module.End (ZMod 2) S)ˣ} {eY : ↥Y ≃* GL32} {g : GL32} :
    g ∈ yImg Y eY A ↔ ((eY.symm g : ↥Y) : (Module.End (ZMod 2) S)ˣ) ∈ A := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    have : eY.symm (eY y) = y := eY.symm_apply_apply y
    simp only [MulEquiv.coe_toMonoidHom] at this ⊢
    rw [this]
    exact hy
  · intro h
    exact ⟨eY.symm g, h, eY.apply_symm_apply g⟩

theorem natCard_yImg {Y A : Subgroup (Module.End (ZMod 2) S)ˣ} (eY : ↥Y ≃* GL32) (hAY : A ≤ Y) :
    Nat.card (yImg Y eY A) = Nat.card A := by
  rw [yImg, Subgroup.card_map_of_injective eY.injective]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAY).toEquiv

theorem mem_fixedSub_yRep_yImg {Y A : Subgroup (Module.End (ZMod 2) S)ˣ} (eY : ↥Y ≃* GL32)
    (hAY : A ≤ Y) {v : S} :
    v ∈ fixedSub (yRep Y eY) (yImg Y eY A) ↔ v ∈ LocalAnalysis.CommutingFactor.fixedSub A := by
  rw [mem_fixedSub, LocalAnalysis.CommutingFactor.mem_fixedSub]
  constructor
  · intro h a ha
    have h1 := h (eY ⟨a, hAY ha⟩) (mem_yImg.mpr (by rw [MulEquiv.symm_apply_apply]; exact ha))
    rw [yRep_apply, MulEquiv.symm_apply_apply] at h1
    exact h1
  · intro h g hg
    rw [yRep_apply]
    exact h _ (mem_yImg.mp hg)

theorem natCard_fixedSub_yRep_yImg {Y A : Subgroup (Module.End (ZMod 2) S)ˣ} (eY : ↥Y ≃* GL32)
    (hAY : A ≤ Y) :
    Nat.card (fixedSub (yRep Y eY) (yImg Y eY A)) =
      Nat.card (LocalAnalysis.CommutingFactor.fixedSub A) :=
  Nat.card_congr (Equiv.subtypeEquivRight fun _ => mem_fixedSub_yRep_yImg eY hAY)

theorem eq_one_of_commute_of_irreducible_of_center [Finite S] [Nontrivial S] {K : Type*} [Group K]
    (hK : Subgroup.center K = ⊥) {Y A : Subgroup (Module.End (ZMod 2) S)ˣ}
    (hirr : ∀ N : Submodule (ZMod 2) S,
      (∀ d ∈ Y ⊔ A, ∀ v ∈ N, (d : Module.End (ZMod 2) S) v ∈ N) → N = ⊥ ∨ N = ⊤)
    (hAN : A ≤ Subgroup.normalizer (Y : Set (Module.End (ZMod 2) S)ˣ)) (eY : ↥Y ≃* K)
    (hA2 : ∀ a ∈ A, a ^ 2 = 1) :
    ∀ d ∈ Y ⊔ A, (∀ y ∈ Y, d * y = y * d) → d = 1 := by
  classical
  have hDN : Y ⊔ A ≤ Subgroup.normalizer (Y : Set (Module.End (ZMod 2) S)ˣ) :=
    sup_le Subgroup.le_normalizer hAN
  set C : Subgroup (Module.End (ZMod 2) S)ˣ :=
    (Y ⊔ A) ⊓ Subgroup.centralizer (Y : Set (Module.End (ZMod 2) S)ˣ) with hC
  have hsq : ∀ c ∈ C, c * c = 1 := by
    intro c hc
    obtain ⟨hcD, hcY⟩ := Subgroup.mem_inf.mp hc
    have hmem : c ∈ ((Y ⊔ A : Subgroup (Module.End (ZMod 2) S)ˣ) : Set (Module.End (ZMod 2) S)ˣ) :=
      hcD
    rw [Subgroup.coe_mul_of_right_le_normalizer_left Y A hAN] at hmem
    obtain ⟨y, hy, a, ha, rfl⟩ := hmem
    have h1 : a * y * a⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp (hAN ha) y).mp hy
    have h2 : a * a = 1 := by rw [← pow_two]; exact hA2 a ha
    have hz : y * a * (y * a) ∈ Y := by
      have e : y * a * (y * a) = y * (a * y * a⁻¹) * (a * a) := by group
      rw [e, h2, mul_one]
      exact Y.mul_mem hy h1
    have hcomm : ∀ y' ∈ Y, y' * (y * a) = y * a * y' :=
      fun y' hy' => Subgroup.mem_centralizer_iff.mp hcY y' hy'
    have hcen : eY ⟨_, hz⟩ ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨y', rfl⟩ := eY.surjective g
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      show (y' : (Module.End (ZMod 2) S)ˣ) * (y * a * (y * a)) = y * a * (y * a) * y'
      have h3 := hcomm _ y'.2
      calc (y' : (Module.End (ZMod 2) S)ˣ) * (y * a * (y * a))
          = (y' * (y * a)) * (y * a) := by group
        _ = (y * a * y') * (y * a) := by rw [h3]
        _ = (y * a) * (y' * (y * a)) := by group
        _ = (y * a) * (y * a * y') := by rw [h3]
        _ = y * a * (y * a) * y' := by group
    rw [hK, Subgroup.mem_bot] at hcen
    have h4 : (⟨_, hz⟩ : ↥Y) = 1 := eY.injective (by rw [hcen, map_one])
    exact congrArg Subtype.val h4
  have hP : IsPGroup 2 ↥C := fun c => ⟨1, Subtype.ext (by
    rw [pow_one, pow_two]
    exact hsq c c.2)⟩
  have hconj : ∀ d ∈ Y ⊔ A, ∀ c ∈ C, d⁻¹ * c * d ∈ C := by
    intro d hd c hc
    obtain ⟨hcD, hcY⟩ := Subgroup.mem_inf.mp hc
    refine Subgroup.mem_inf.mpr ⟨(Y ⊔ A).mul_mem ((Y ⊔ A).mul_mem ((Y ⊔ A).inv_mem hd) hcD) hd, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y' hy'
    have h1 : d * y' * d⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp (hDN hd) y').mp hy'
    have h2 := Subgroup.mem_centralizer_iff.mp hcY _ h1
    calc y' * (d⁻¹ * c * d) = d⁻¹ * ((d * y' * d⁻¹) * c) * d := by group
      _ = d⁻¹ * (c * (d * y' * d⁻¹)) * d := by rw [h2]
      _ = d⁻¹ * c * d * y' := by group
  set F := LocalAnalysis.CommutingFactor.fixedSub C with hF
  have hFinv : ∀ d ∈ Y ⊔ A, ∀ v ∈ F, (d : Module.End (ZMod 2) S) v ∈ F := by
    intro d hd v hv
    rw [hF, LocalAnalysis.CommutingFactor.mem_fixedSub] at hv ⊢
    intro c hc
    have h1 := hv _ (hconj d hd c hc)
    have e : ((d⁻¹ * c * d : (Module.End (ZMod 2) S)ˣ) : Module.End (ZMod 2) S) v =
        ((d⁻¹ : (Module.End (ZMod 2) S)ˣ) : Module.End (ZMod 2) S)
          ((c : Module.End (ZMod 2) S) ((d : Module.End (ZMod 2) S) v)) :=
      rfl
    rw [e] at h1
    have h2 : (d : Module.End (ZMod 2) S) (((d⁻¹ : (Module.End (ZMod 2) S)ˣ) : Module.End (ZMod 2) S)
        ((c : Module.End (ZMod 2) S) ((d : Module.End (ZMod 2) S) v))) =
        (d : Module.End (ZMod 2) S) v := congrArg _ h1
    rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Module.End.one_apply] at h2
    exact h2
  have hFtop : F = ⊤ := by
    rcases hirr F hFinv with h | h
    · exfalso
      have hmod := hP.card_modEq_card_fixedPoints S
      have hfix : Nat.card (MulAction.fixedPoints ↥C S) = 1 := by
        rw [Nat.card_eq_one_iff_exists]
        refine ⟨⟨0, fun c => ?_⟩, fun x => ?_⟩
        · show ((c : (Module.End (ZMod 2) S)ˣ) : Module.End (ZMod 2) S) 0 = 0
          exact map_zero _
        · apply Subtype.ext
          have hx : (x : S) ∈ F := by
            rw [hF, LocalAnalysis.CommutingFactor.mem_fixedSub]
            intro c hc
            exact x.2 ⟨c, hc⟩
          rw [h, Submodule.mem_bot] at hx
          exact hx
      rw [hfix, card_eq_two_pow_finrank] at hmod
      have hpos : 0 < finrank (ZMod 2) S := Module.finrank_pos
      have h0 : 2 ^ finrank (ZMod 2) S % 2 = 0 := by
        obtain ⟨k, hk⟩ : ∃ k, finrank (ZMod 2) S = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
        rw [hk, pow_succ]
        simp
      have := hmod
      unfold Nat.ModEq at this
      rw [h0] at this
      norm_num at this
    · exact h
  intro d hd hcomm
  have hdC : d ∈ C := Subgroup.mem_inf.mpr ⟨hd, Subgroup.mem_centralizer_iff.mpr fun y hy =>
    (hcomm y hy).symm⟩
  apply Units.ext
  refine LinearMap.ext fun v => ?_
  have hv : v ∈ F := by rw [hFtop]; exact Submodule.mem_top
  rw [hF, LocalAnalysis.CommutingFactor.mem_fixedSub] at hv
  exact hv d hdC

theorem eq_one_of_commute_of_irreducible [Finite S] [Nontrivial S]
    {Y A : Subgroup (Module.End (ZMod 2) S)ˣ}
    (hirr : ∀ N : Submodule (ZMod 2) S,
      (∀ d ∈ Y ⊔ A, ∀ v ∈ N, (d : Module.End (ZMod 2) S) v ∈ N) → N = ⊥ ∨ N = ⊤)
    (hAN : A ≤ Subgroup.normalizer (Y : Set (Module.End (ZMod 2) S)ˣ)) (eY : ↥Y ≃* GL32)
    (hA2 : ∀ a ∈ A, a ^ 2 = 1) :
    ∀ d ∈ Y ⊔ A, (∀ y ∈ Y, d * y = y * d) → d = 1 :=
  eq_one_of_commute_of_irreducible_of_center center_GL32 hirr hAN eY hA2

theorem l32_factor [Finite S] [Nontrivial S] {Y A : Subgroup (Module.End (ZMod 2) S)ˣ}
    (hirr : ∀ N : Submodule (ZMod 2) S,
      (∀ d ∈ Y ⊔ A, ∀ v ∈ N, (d : Module.End (ZMod 2) S) v ∈ N) → N = ⊥ ∨ N = ⊤)
    (hAN : A ≤ Subgroup.normalizer (Y : Set (Module.End (ZMod 2) S)ˣ)) (eY : ↥Y ≃* GL32)
    (hA1 : A ≠ ⊥) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hA2 : ∀ a ∈ A, a ^ 2 = 1)
    {m : ℕ} (hm : Nat.card A = 2 ^ m)
    (hcost : finrank (ZMod 2) S ≤
      m + finrank (ZMod 2) (LocalAnalysis.CommutingFactor.fixedSub A)) :
    A ≤ Y ∧ (ModIso repV (yRep Y eY) ∨ ModIso repDual (yRep Y eY)) := by
  classical
  have : Module.Finite (ZMod 2) S := Module.Finite.of_finite
  have := nontrivial_GL32
  have hDN : Y ⊔ A ≤ Subgroup.normalizer (Y : Set (Module.End (ZMod 2) S)ˣ) :=
    sup_le Subgroup.le_normalizer hAN
  have hYn : ∀ d ∈ Y ⊔ A, ∀ y ∈ Y, d * y * d⁻¹ ∈ Y := fun d hd y hy =>
    (Subgroup.mem_normalizer_iff.mp (hDN hd) y).mp hy
  have hfaith : ∀ d ∈ Y ⊔ A,
      (∀ v ∈ (⊤ : Submodule (ZMod 2) S), (d : Module.End (ZMod 2) S) v = v) → d = 1 :=
    fun d _ h => Units.ext (LinearMap.ext fun v => h v Submodule.mem_top)
  have hCY := eq_one_of_commute_of_irreducible hirr hAN eY hA2
  have hAY : A ≤ Y := by
    by_contra hcon
    obtain ⟨a, ha, haY⟩ := Set.not_subset.mp hcon
    have hlt := lt_finrank_of_not_le (I := ⊤) (fun _ _ _ _ => Submodule.mem_top) hfaith
      le_sup_left hYn eY hCY le_sup_right hA1 hAc hA2 (d₀ := a) (le_sup_right (a := Y) ha) haY hm
    rw [top_inf_eq, finrank_top] at hlt
    omega
  refine ⟨hAY, ?_⟩
  have hYA : Y ⊔ A = Y := sup_eq_left.mpr hAY
  set ρG := yRep Y eY with hρG
  have hirrG : IsIrrRep ρG := by
    refine isIrrRep_of inferInstance fun N hN => hirr N fun d hd v hv => ?_
    rw [hYA] at hd
    have h1 := hN (eY ⟨d, hd⟩) v hv
    rw [hρG, yRep_apply, MulEquiv.symm_apply_apply] at h1
    exact h1
  set Bh := yImg Y eY A with hBh
  have hBcard : Nat.card Bh = 2 ^ m := (natCard_yImg eY hAY).trans hm
  have hB0 : Bh ≠ ⊥ := by
    intro h
    have h1 : Nat.card Bh = 1 := by rw [h]; exact Subgroup.card_bot
    rw [natCard_yImg eY hAY] at h1
    exact hA1 (Subgroup.card_eq_one.mp h1)
  have hBc : ∀ g ∈ Bh, ∀ h ∈ Bh, g * h = h * g := by
    intro g hg h hh
    apply eY.symm.injective
    apply Subtype.ext
    rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul]
    exact hAc _ (mem_yImg.mp hg) _ (mem_yImg.mp hh)
  have hBsq : ∀ g ∈ Bh, g ^ 2 = 1 := by
    intro g hg
    apply eY.symm.injective
    apply Subtype.ext
    rw [map_pow, map_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hA2 _ (mem_yImg.mp hg)
  have hfix := GL3_elementary_abelian_fixed_codimensions hB0 hBc hBsq
  have hfixA : Nat.card (fixedSub ρG Bh) =
      2 ^ finrank (ZMod 2) (LocalAnalysis.CommutingFactor.fixedSub A) := by
    rw [hρG, hBh, natCard_fixedSub_yRep_yImg eY hAY, card_eq_two_pow_finrank]
  rcases irreducible_binary_GL3_classification ρG hirrG with h | h | h | h
  · exfalso
    obtain ⟨e, he⟩ := h
    obtain ⟨g, hg⟩ := exists_ne (1 : GL32)
    apply hg
    have h1 : ((eY.symm g : ↥Y) : (Module.End (ZMod 2) S)ˣ) = 1 := by
      refine hfaith _ (le_sup_left (a := Y) (eY.symm g).2) fun v _ => ?_
      have h2 : e (e.symm v) = ρG g (e (e.symm v)) := he g _
      rw [LinearEquiv.apply_symm_apply] at h2
      rw [hρG, yRep_apply] at h2
      exact h2.symm
    have h3 : eY.symm g = 1 := Subtype.ext h1
    rw [← eY.apply_symm_apply g, h3, map_one]
  · exact .inl h
  · exact .inr h
  · exfalso
    have hA8 : finrank (ZMod 2) S = 8 := by
      have h1 := card_eq_of_modIso h
      rw [natCard_traceZero, card_eq_two_pow_finrank] at h1
      have h2 : 2 ^ finrank (ZMod 2) S = 2 ^ 8 := by rw [← h1]; norm_num
      exact Nat.pow_right_injective le_rfl h2
    have hT := natCard_fixedSub_of_modIso_repA h Bh
    rw [hfixA] at hT
    unfold FixedCodimData at hfix
    rcases hfix with ⟨hB2, -, -, hT16⟩ | ⟨hB4, -, hT4⟩
    · have hm1 : m = 1 := Nat.pow_right_injective le_rfl (hBcard.symm.trans hB2)
      have hf : finrank (ZMod 2) (LocalAnalysis.CommutingFactor.fixedSub A) = 4 :=
        Nat.pow_right_injective le_rfl ((hT.trans hT16).trans (by norm_num))
      omega
    · have hm2 : m = 2 := Nat.pow_right_injective le_rfl (hBcard.symm.trans (hB4.trans (by norm_num)))
      have hf : finrank (ZMod 2) (LocalAnalysis.CommutingFactor.fixedSub A) = 2 :=
        Nat.pow_right_injective le_rfl ((hT.trans hT4).trans (by norm_num))
      omega

end CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
