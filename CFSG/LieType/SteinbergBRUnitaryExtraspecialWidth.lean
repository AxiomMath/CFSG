module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBUFourUnitaryAxisFlagKernel

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LieType.SteinbergBR.UnitaryWidth

open Module CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups Subgroup
  CFSG.LocalAnalysis.GorensteinLyons CFSG.LocalAnalysis.GorensteinLyons.FourUnitary

variable {F : Type*} [Field F] {hF : UnitaryFieldData 2 1 F} {W : Type*} [AddCommGroup W]
  [Module F W] {B : W →ₛₗ[hF.bar] W →ₗ[F] F}

theorem add_self_W (hF : UnitaryFieldData 2 1 F) (w : W) : w + w = 0 := by
  rw [← two_smul F w, two_eq_zero hF, zero_smul]

theorem mem_zpowers_two {G : Type*} [Group G] {t x : G} (ht : orderOf t = 2)
    (hx : x ∈ zpowers t) : x = 1 ∨ x = t := by
  obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hx
  rw [← zpow_mod_orderOf, ht]
  have h : m % ((2 : ℕ) : ℤ) = 0 ∨ m % ((2 : ℕ) : ℤ) = 1 := by omega
  rcases h with h | h <;> rw [h]
  · left; exact zpow_zero t
  · right; exact zpow_one t

theorem zmod_two_cases' (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

theorem val_cast_add (hF : UnitaryFieldData 2 1 F) (a b : ZMod 2) :
    (((a + b).val : ℕ) : F) = (a.val : F) + (b.val : F) := by
  have h2 := two_eq_zero hF
  rcases zmod_two_cases' a with rfl | rfl <;> rcases zmod_two_cases' b with rfl | rfl
  · change ((0 : ℕ) : F) = ((0 : ℕ) : F) + ((0 : ℕ) : F)
    simp
  · change ((1 : ℕ) : F) = ((0 : ℕ) : F) + ((1 : ℕ) : F)
    simp
  · change ((1 : ℕ) : F) = ((1 : ℕ) : F) + ((0 : ℕ) : F)
    simp
  · change ((0 : ℕ) : F) = ((1 : ℕ) : F) + ((1 : ℕ) : F)
    rw [Nat.cast_zero, Nat.cast_one, one_add_one_eq_two, h2]

theorem val_cast_injective {a b : ZMod 2}
    (h : (a.val : F) = (b.val : F)) : a = b := by
  rcases zmod_two_cases' a with rfl | rfl <;> rcases zmod_two_cases' b with rfl | rfl
  · rfl
  · change ((0 : ℕ) : F) = ((1 : ℕ) : F) at h
    simp at h
  · change ((1 : ℕ) : F) = ((0 : ℕ) : F) at h
    simp at h
  · rfl

theorem B_e_apply {e : W} {g : LinearMap.GeneralLinearGroup F W} (hg : g ∈ axisStab B e)
    (z : W) : B e ((g : W →ₗ[F] W) z) = B e z := by
  have h := hg.1 e z
  rw [hg.2] at h
  exact h


theorem transvection_pow_apply {e : W} (he : B e e = 0) (b : ZMod 2) (w : W) :
    ((hermTransvectionGL B he 1 ^ b.val : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) w =
      w + ((b.val : F) * B e w) • e := by
  rcases zmod_two_cases' b with rfl | rfl
  · change ((1 : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) w = w + (((0 : ℕ) : F) * B e w) • e
    simp
  · change ((hermTransvectionGL B he 1 ^ 1 : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) w =
      w + (((1 : ℕ) : F) * B e w) • e
    rw [pow_one, coe_hermTransvectionGL, hermTransvection_apply, Nat.cast_one]

end CFSG.LieType.SteinbergBR.UnitaryWidth

namespace CFSG.LieType

open Module CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups Subgroup
  CFSG.LocalAnalysis.GorensteinLyons CFSG.LocalAnalysis.GorensteinLyons.FourUnitary
  CFSG.LieType.SteinbergBR.UnitaryWidth

theorem unitary_extraspecial_central_transvection_width_and_equality {F : Type*} [Field F]
    (hF : UnitaryFieldData 2 1 F) {W : Type*} [AddCommGroup W] [Module F W]
    [FiniteDimensional F W] {B : W →ₛₗ[hF.bar] W →ₗ[F] F} (hB : B.IsSymm)
    (hBl : B.SeparatingLeft) (hd : 3 ≤ finrank F W)
    (P : Subgroup (LinearMap.GeneralLinearGroup F W)) (hPU : P ≤ sesqUnitaryGroup B) {n : ℕ}
    (_hn : 1 ≤ n) (hP : IsExtraspecialPGroup 2 P) (hPcard : Nat.card P = 2 ^ (1 + 2 * n))
    {e : W} (he0 : e ≠ 0) (he : B e e = 0) (hT : hermTransvectionGL B he 1 ∈ P)
    (hZ : center P = zpowers ⟨_, hT⟩) {f : W} (_hf : B f f = 0) (hef : B e f = 1) :
    (∀ x ∈ P, (x : W →ₗ[F] W) e = e) ∧
    ∃ δ : P ⧸ center P → axisQuot B e,
      (∀ (x : P) (hx : (x : LinearMap.GeneralLinearGroup F W) ∈ axisStab B e),
        δ (x : P ⧸ center P) = displacement B e f ⟨x, hx⟩) ∧
      (∀ u v : P ⧸ center P,
        hF.trace (axisForm hB e (δ u) (δ v)) = ((commVal ⟨_, hT⟩ u v).val : F)) ∧
      n ≤ finrank F W - 2 ∧
      (n = finrank F W - 2 → Function.Bijective δ ∧ (∀ u v, δ (u * v) = δ u + δ v) ∧
        (∀ x ∈ P, ∀ z ∈ axisPerp B e, (x : W →ₗ[F] W) z - z ∈ F ∙ e) ∧
        P = axisKernel B e) := by
  classical
  have : Finite F := hF.finite
  have h2F : (2 : F) = 0 := two_eq_zero hF
  have : Finite W := Module.finite_of_finite F
  have : Finite (W →ₗ[F] W) := Finite.of_injective _ DFunLike.coe_injective
  set t : P := ⟨_, hT⟩ with ht
  have H := commPairHyp_of_extraspecial hP hZ
  have htz : ∀ z, ((t : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) z = z + B e z • e := by
    intro z
    rw [ht, coe_hermTransvectionGL, hermTransvection_apply, one_mul]
  have htc : ∀ x : P, x * t = t * x := fun x =>
    Subgroup.mem_center_iff.1 (hZ ▸ mem_zpowers t) x
  have hfe : B f e = 1 := by rw [← hB.eq, hef, map_one]
  have hfix : ∀ x ∈ P, (x : W →ₗ[F] W) e = e := by
    intro x hx
    have h1 := LinearMap.congr_fun (congrArg Units.val (congrArg Subtype.val (htc ⟨x, hx⟩))) f
    simp only [Subgroup.coe_mul, Units.val_mul, Module.End.mul_apply] at h1
    rw [htz, htz, map_add, map_smul, hef, one_smul] at h1
    have hxe : (x : W →ₗ[F] W) e = B e ((x : W →ₗ[F] W) f) • e := add_left_cancel h1
    set c := B e ((x : W →ₗ[F] W) f) with hc
    have hpow : ∀ k : ℕ,
        ((x ^ k : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) e = c ^ k • e := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ x k, Units.val_mul, Module.End.mul_apply, hxe, map_smul, ih, smul_smul,
          ← pow_succ' c k]
    obtain ⟨k, hk⟩ := hP.1 ⟨x, hx⟩
    have hk' : x ^ (2 ^ k) = 1 := congrArg Subtype.val hk
    have hc2 : c ^ (2 ^ k) = 1 := by
      have h2 := hpow (2 ^ k)
      rw [hk', Units.val_one, Module.End.one_apply] at h2
      have h3 : (c ^ (2 ^ k) - 1) • e = 0 := by rw [sub_smul, one_smul, ← h2, sub_self]
      exact sub_eq_zero.1 ((smul_eq_zero.1 h3).resolve_right he0)
    have hc0 : c ≠ 0 := by
      intro h0
      rw [h0, zero_smul] at hxe
      apply he0
      have h2 : ((x⁻¹ : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W)
          ((x : W →ₗ[F] W) e) = e := by
        rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Module.End.one_apply]
      rw [hxe, map_zero] at h2
      exact h2.symm
    have hc1 : c = 1 := by
      have h := pow_gcd_eq_one.2 ⟨hc2, pow_three_eq_one hF hc0⟩
      rwa [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3)),
        pow_one] at h
    rw [hxe, hc1, one_smul]
  have hstab : ∀ x ∈ P, x ∈ axisStab B e := fun x hx => ⟨hPU hx, hfix x hx⟩
  have htt : (t : LinearMap.GeneralLinearGroup F W) * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [H.orderOf_eq, pow_two] at h
    exact congrArg Subtype.val h
  have hinv : ∀ x ∈ P, ∀ Y ∈ axisPerp B e,
      ((x⁻¹ : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) Y = (x : W →ₗ[F] W) Y := by
    intro x hx Y hY
    have hsq := H.sq_mem_center ⟨x, hx⟩
    rw [hZ] at hsq
    rcases mem_zpowers_two H.orderOf_eq hsq with h1 | h1
    · have h1' : x * x = 1 := by
        have h2 := congrArg Subtype.val h1
        rw [pow_two] at h2
        exact h2
      rw [inv_eq_of_mul_eq_one_right h1']
    · have h1' : x * x = (t : LinearMap.GeneralLinearGroup F W) := by
        have h2 := congrArg Subtype.val h1
        rw [pow_two] at h2
        exact h2
      have hxinv : x⁻¹ = x * (t : LinearMap.GeneralLinearGroup F W) :=
        inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, h1', htt])
      rw [hxinv, Units.val_mul, Module.End.mul_apply, htz, mem_axisPerp.1 hY, zero_smul,
        add_zero]
  have hD : ∀ x : P, ((x : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) f - f ∈ axisPerp B e :=
    fun x => sub_mem_axisPerp (hstab x x.2) f
  have hmul_t : ∀ a : P, (((a * t : P) : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) f =
      ((a : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) f + e := by
    intro a
    rw [Subgroup.coe_mul, Units.val_mul, Module.End.mul_apply, htz, map_add, map_smul, hef,
      one_smul, hfix _ a.2]
  let δ : P ⧸ center P → axisQuot B e :=
    Quotient.lift (fun x : P => displacement B e f ⟨x, hstab x x.2⟩) (by
      intro a b hab
      have hab' : a⁻¹ * b ∈ center P := QuotientGroup.leftRel_apply.1 hab
      rw [hZ] at hab'
      have hb : b = a ∨ b = a * t := by
        rcases mem_zpowers_two H.orderOf_eq hab' with h | h
        · left
          rw [← mul_inv_cancel_left a b, h, mul_one]
        · right
          rw [← mul_inv_cancel_left a b, h]
      rcases hb with rfl | rfl
      · rfl
      · refine (Submodule.Quotient.eq _).2 ?_
        change ((a : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) f - f -
          ((((a * t : P) : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) f - f) ∈ F ∙ e
        rw [hmul_t]
        have : ((a : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) f - f -
            (((a : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) f + e - f) = (-1 : F) • e := by
          rw [neg_one_smul]
          abel
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e))
  have hδ : ∀ x : P, δ (x : P ⧸ center P) = displacement B e f ⟨x, hstab x x.2⟩ := fun x => rfl
  have hpair0 : ∀ x y : P, hF.trace (axisForm hB e (δ x) (δ y)) =
      ((commVal t (x : P ⧸ center P) (y : P ⧸ center P)).val : F) := by
    intro x y
    rw [hδ, hδ, displacement, displacement, axisForm_mk, UnitaryFieldData.trace, hB.eq]
    set a := ((x : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) with ha
    set c := ((y : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) with hc
    set b := commVal t (x : P ⧸ center P) (y : P ⧸ center P) with hbdef
    have hadj : ∀ g : P, ∀ Y ∈ axisPerp B e,
        B (((g : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) f - f) Y =
          B f (((g : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) Y - Y) := by
      intro g Y hY
      have h1 := hPU g.2 f (((g⁻¹ : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) Y)
      rw [generalLinearGroup_apply_inv_apply, hinv _ g.2 Y hY] at h1
      rw [map_sub, LinearMap.sub_apply, h1, map_sub]
    have hYc : c f - f ∈ axisPerp B e := hD y
    have hXa : a f - f ∈ axisPerp B e := hD x
    rw [hadj x _ hYc, hadj y _ hXa, ← ha, ← hc]
    have hcomm := H.commutatorElement_eq_zpow x y
    have hxy : x * y = t ^ b.val * (y * x) := by
      rw [← hcomm, commutatorElement_def]
      group
    have hxyf : a (c f) = c (a f) + (b.val : F) • e := by
      have h1 := LinearMap.congr_fun (congrArg Units.val (congrArg Subtype.val hxy)) f
      simp only [Subgroup.coe_mul, Subgroup.coe_pow, Units.val_mul, Module.End.mul_apply] at h1
      rw [← ha, ← hc] at h1
      rw [h1, ht, transvection_pow_apply he b, B_e_apply (hstab _ y.2),
        B_e_apply (hstab _ x.2), hef, mul_one]
    simp only [map_sub, hxyf, map_add, map_smul, hfe, smul_eq_mul, mul_one]
    linear_combination (B f (c (a f)) - B f (a f) - B f (c f) + B f f) * h2F
  have hpair : ∀ u v : P ⧸ center P, hF.trace (axisForm hB e (δ u) (δ v)) =
      ((commVal t u v).val : F) := by
    intro u v
    induction u using QuotientGroup.induction_on with | H x =>
    induction v using QuotientGroup.induction_on with | H y =>
    exact hpair0 x y
  have hinv_q : ∀ u : P ⧸ center P, u⁻¹ = u := by
    intro u
    induction u using QuotientGroup.induction_on with | H x =>
    rw [← QuotientGroup.mk_inv, QuotientGroup.eq, inv_inv, ← pow_two]
    exact H.sq_mem_center x
  have hδinj : Function.Injective δ := by
    intro u u' huu
    have h1 : ∀ v, commVal t u v = commVal t u' v := fun v =>
      val_cast_injective (by rw [← hpair u v, ← hpair u' v, huu])
    have h2 : ∀ v, commVal t (u * u'⁻¹) v = 0 := by
      intro v
      rw [hinv_q, H.commVal_mul_left, h1 v, ← two_mul]
      exact (show (2 : ZMod 2) = 0 from rfl) ▸ zero_mul _
    have h3 := H.eq_one_of_forall_commVal_eq_zero h2
    exact mul_inv_eq_one.1 h3
  have hcardQ : Nat.card (P ⧸ center P) = 2 ^ (2 * n) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center P)
    rw [hPcard, hP.2.2.2, pow_add, pow_one, mul_comm] at h1
    exact (Nat.eq_of_mul_eq_mul_right (by norm_num) h1).symm
  obtain ⟨⟨-, -, -, hsep, hdimB⟩, -, -, -⟩ :=
    four_element_unitary_axis_flag_kernel_data hF hB hBl he0 he
  have hcardB : Nat.card (axisQuot B e) = 2 ^ (2 * (finrank F W - 2)) := by
    rw [Module.natCard_eq_pow_finrank (K := F), hdimB, hF.card, ← pow_mul, mul_one]
  have : Finite (axisQuot B e) := Module.finite_of_finite F
  have hle : n ≤ finrank F W - 2 := by
    have h1 := Nat.card_le_card_of_injective δ hδinj
    rw [hcardQ, hcardB] at h1
    have h2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h1
    omega
  refine ⟨hfix, δ, fun x hx => rfl, hpair, hle, fun hnd => ?_⟩
  have hbij : Function.Bijective δ :=
    hδinj.bijective_of_nat_card_le (by rw [hcardQ, hcardB, hnd])
  obtain ⟨ν, hν⟩ : ∃ ν : F, hF.trace ν ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h01 : ∀ a : F, a = 0 ∨ a = 1 := fun a => AxisFlag.eq_zero_or_one_of_trace a (hcon a)
    have hinj : Function.Injective (fun a : F => (if a = 0 then 0 else 1 : Fin 2)) := by
      intro a a' h
      rcases h01 a with rfl | rfl <;> rcases h01 a' with rfl | rfl <;> simp_all
    have h1 := Nat.card_le_card_of_injective _ hinj
    rw [hF.card, Nat.card_eq_fintype_card, Fintype.card_fin] at h1
    norm_num at h1
  have hβnd : ∀ w : axisQuot B e, (∀ w', hF.trace (axisForm hB e w w') = 0) → w = 0 := by
    intro w hw
    refine hsep w fun w' => ?_
    by_contra hμ
    have h1 := hw ((ν * (axisForm hB e w w')⁻¹) • w')
    rw [map_smul, smul_eq_mul, inv_mul_cancel_right₀ hμ] at h1
    exact hν h1
  have htr_add : ∀ a b : F, hF.trace (a + b) = hF.trace a + hF.trace b := fun a b => by
    rw [UnitaryFieldData.trace, UnitaryFieldData.trace, UnitaryFieldData.trace, map_add]
    ring
  have htr_sub : ∀ a b : F, hF.trace (a - b) = hF.trace a - hF.trace b := fun a b => by
    rw [UnitaryFieldData.trace, UnitaryFieldData.trace, UnitaryFieldData.trace, map_sub]
    ring
  have hadd : ∀ u v, δ (u * v) = δ u + δ v := by
    intro u v
    rw [← sub_eq_zero]
    refine hβnd _ fun w' => ?_
    obtain ⟨z, rfl⟩ := hbij.2 w'
    rw [map_sub, map_add, LinearMap.sub_apply, LinearMap.add_apply, htr_sub, htr_add, hpair,
      hpair, hpair, H.commVal_mul_left, val_cast_add hF, sub_self]
  have htriv : ∀ x ∈ P, ∀ z ∈ axisPerp B e, (x : W →ₗ[F] W) z - z ∈ F ∙ e := by
    intro x hx z hz
    obtain ⟨v, hv⟩ := hbij.2 (Submodule.Quotient.mk ⟨z, hz⟩)
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective v
    have hyz := (Submodule.Quotient.eq _).1 hv
    change ((y : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) f - f - z ∈ F ∙ e at hyz
    have hxy := hadd (⟨x, hx⟩ : P) y
    rw [← QuotientGroup.mk_mul, hδ, hδ, hδ, displacement, displacement, displacement,
      ← Submodule.Quotient.mk_add, Submodule.Quotient.eq] at hxy
    change (((⟨x, hx⟩ * y : P) : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) f - f -
      ((x : W →ₗ[F] W) f - f + (((y : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) f - f)) ∈
        F ∙ e at hxy
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hyz
    have hz' : z = ((y : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) f - f - c • e := by
      rw [hc]
      abel
    have hval : (x : W →ₗ[F] W) z - z =
        (((⟨x, hx⟩ * y : P) : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) f - f -
          ((x : W →ₗ[F] W) f - f +
            (((y : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) f - f)) := by
      rw [hz', map_sub, map_sub, map_smul, hfix x hx, Subgroup.coe_mul, Units.val_mul,
        Module.End.mul_apply]
      abel
    rw [hval]
    exact hxy
  have hle' : P ≤ axisKernel B e := fun x hx => ⟨hstab x hx, htriv x hx⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, hcard8, -⟩ :=
    four_element_unitary_axis_flag_kernel_and_regular_orbit hF hB hBl hd he0 he
  exact ⟨hbij, hadd, htriv, Subgroup.eq_of_le_of_card_ge hle' (by rw [hcard8, hPcard, hnd])⟩

end CFSG.LieType
