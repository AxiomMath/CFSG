module

public import CFSG.CGT.PushingUpLit.CGT6X.K7aLinearAll
public import CFSG.CGT.PushingUpLit.CGT6X.K7aUnitary
public import CFSG.LocalAnalysis.SteinbergBNUnitaryThreeOuterInvolutionRigidity

public section

namespace CFSG.CGT.PushingUpLit.CGT6X.K7a

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne CFSG.SL2MinimalFaithful CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis

section Quot

variable (L : Type*) [Group L]

@[expose] noncomputable def centerAutHom : MulAut L →* MulAut (L ⧸ Subgroup.center L) where
  toFun τ := QuotientGroup.congr (Subgroup.center L) (Subgroup.center L) τ
    (Subgroup.map_center_eq τ)
  map_one' := MulEquiv.ext fun x => QuotientGroup.induction_on x fun _ => rfl
  map_mul' _ _ := MulEquiv.ext fun x => QuotientGroup.induction_on x fun _ => rfl

variable {L}

theorem centerAutHom_mk (τ : MulAut L) (y : L) :
    centerAutHom L τ (QuotientGroup.mk y) = QuotientGroup.mk (τ y) := rfl

theorem center_sl2_eq_bot' {F : Type} [Field F] [CharP F 2] :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) = ⊥ := by
  ext g
  rw [Subgroup.mem_bot, Matrix.SpecialLinearGroup.mem_center_iff]
  constructor
  · rintro ⟨r, hr, hg⟩
    have hr2 : r ^ 2 = 1 := by simpa using hr
    have h : (r + 1) ^ 2 = 0 := by
      rw [CharTwo.add_sq, hr2, one_pow, CharTwo.add_self_eq_zero]
    have h1 : r + 1 = 0 := pow_eq_zero_iff two_ne_zero |>.mp h
    have hr1 : r = 1 := by
      calc r = -1 := eq_neg_of_add_eq_zero_left h1
        _ = 1 := CharTwo.neg_eq 1
    subst hr1
    apply Subtype.ext
    rw [← hg]
    simp
  · rintro rfl
    exact ⟨1, by simp, by simp⟩

theorem inf_center_eq_bot {F : Type} [Field F] [CharP F 2] (Y : Subgroup L)
    (φ : Y ≃* Matrix.SpecialLinearGroup (Fin 2) F) : Y ⊓ Subgroup.center L = ⊥ := by
  rw [eq_bot_iff]
  rintro y ⟨hyY, hyZ⟩
  have hc : φ ⟨y, hyY⟩ ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨z, rfl⟩ := φ.surjective g
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact Subgroup.mem_center_iff.1 hyZ z
  rw [center_sl2_eq_bot', Subgroup.mem_bot] at hc
  have h1 : (⟨y, hyY⟩ : Y) = 1 := φ.injective (by rw [hc, map_one])
  exact Subgroup.mem_bot.2 (congrArg Subtype.val h1)

theorem card_map_mk_of_inf_eq_bot (Y : Subgroup L) (hYZ : Y ⊓ Subgroup.center L = ⊥) :
    Nat.card (Y.map (QuotientGroup.mk' (Subgroup.center L))) = Nat.card Y := by
  have hinj : Function.Injective
      ((QuotientGroup.mk' (Subgroup.center L)).domRestrict Y) := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have h1 : (y : L) ∈ Subgroup.center L := (QuotientGroup.eq_one_iff _).1 hy
    have hmem : (y : L) ∈ Y ⊓ Subgroup.center L := ⟨y.2, h1⟩
    rw [hYZ] at hmem
    exact Subtype.ext (Subgroup.mem_bot.1 hmem)
  rw [← MonoidHom.domRestrict_range]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

end Quot

section Wrappers

variable {L : Type} [Group L]

theorem K7a_linear {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (e : (L ⧸ Subgroup.center L) ≃* projectiveSL 3 K) (τ : MulAut L) (hτ : τ ^ 2 = 1)
    (hτout : ∀ x : L ⧸ Subgroup.center L, centerAutHom L τ ≠ MulAut.conj x)
    (Y : Subgroup L) {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ f)
    (hY : Nonempty (Y ≃* Matrix.SpecialLinearGroup (Fin 2) F)) (hYτ : ∀ y ∈ Y, τ y = y) :
    ∃ H : GL (Fin 3) K,
      (∀ x, e (centerAutHom L τ x) =
        (conjAut 3 K H * dualAut 3 K * (conjAut 3 K H)⁻¹) (e x)) ∧
      (Y.map (QuotientGroup.mk' (Subgroup.center L))).map e.toMonoidHom =
        (orthProj K).map (conjAut 3 K H : MulAut (projectiveSL 3 K)).toMonoidHom := by
  obtain ⟨φ⟩ := hY
  have hcharF : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two hf hF
  have hYZ := inf_center_eq_bot Y φ
  set t : MulAut (projectiveSL 3 K) := MulAut.congr e (centerAutHom L τ) with ht
  have htx : ∀ x, t (e x) = e (centerAutHom L τ x) := fun x => by
    simp [ht, MulAut.congr_apply]
  have ht2 : t ^ 2 = 1 := by
    rw [ht, ← map_pow, ← map_pow, hτ, map_one, map_one]
  have htout : t ∉ innSL 3 K := by
    rintro ⟨z, hz⟩
    apply hτout (e.symm z)
    apply MulEquiv.ext
    intro x
    have h1 := congrArg (fun a : MulAut (projectiveSL 3 K) => a (e x)) hz
    simp only [MulAut.conj_apply] at h1
    rw [htx] at h1
    apply e.injective
    simp [h1]
  have hcardY : Nat.card Y = Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) := by
    rw [Nat.card_congr φ.toEquiv, card_specialLinearGroup_fin_two,
      card_specialLinearGroup_fin_two, hF, hK]
  set Ybar := Y.map (QuotientGroup.mk' (Subgroup.center L)) with hYbar
  set Y' : Subgroup (projectiveSL 3 K) := Ybar.map e.toMonoidHom with hY'
  have hcard' : Nat.card Y' = Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) := by
    rw [hY', (Nat.card_congr (Subgroup.equivMapOfInjective Ybar e.toMonoidHom
      e.injective).toEquiv).symm, hYbar, card_map_mk_of_inf_eq_bot Y hYZ, hcardY]
  have hYt : ∀ y' ∈ Y', t y' = y' := by
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    show t (e (QuotientGroup.mk y)) = e (QuotientGroup.mk y)
    rw [htx, centerAutHom_mk, hYτ y hy]
  obtain ⟨H, hHt, hHY⟩ := linear_involution_surviving hf hK t ht2 htout Y' hcard' hYt
  refine ⟨H, fun x => ?_, hHY⟩
  rw [← htx, hHt]

@[expose] noncomputable def projEquivStated (K : Type) [Field K] :
    projectiveSL 3 K ≃* StatedProj (StatedSL 3 K) :=
  (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K).symm.trans
    (projectiveSpecialLinearGroupEquivStatedProj 3 K)

theorem K7a_linear_model {f : ℕ} (hf : 1 ≤ f)
    (hmod : StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 3 2 f) (τ : MulAut L)
    (hτ : τ ^ 2 = 1) (hτout : ∀ x : L ⧸ Subgroup.center L, centerAutHom L τ ≠ MulAut.conj x)
    (Y : Subgroup L) {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ f)
    (hY : Nonempty (Y ≃* Matrix.SpecialLinearGroup (Fin 2) F)) (hYτ : ∀ y ∈ Y, τ y = y) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ f ∧
      ∃ (e : (L ⧸ Subgroup.center L) ≃* projectiveSL 3 K) (H : GL (Fin 3) K),
      (∀ x, e (centerAutHom L τ x) =
        (conjAut 3 K H * dualAut 3 K * (conjAut 3 K H)⁻¹) (e x)) ∧
      (Y.map (QuotientGroup.mk' (Subgroup.center L))).map e.toMonoidHom =
        (orthProj K).map (conjAut 3 K H : MulAut (projectiveSL 3 K)).toMonoidHom := by
  obtain ⟨-, K, _, _, hK, ⟨eD⟩⟩ := hmod
  obtain ⟨H, hH1, hH2⟩ := K7a_linear hf hK (eD.trans (projEquivStated K).symm) τ hτ hτout Y hF hY
    hYτ
  exact ⟨K, inferInstance, inferInstance, hK, _, H, hH1, hH2⟩

theorem K7a_unitary {f : ℕ} (hf : 2 ≤ f)
    (hmod : StatedClassicalModel (L ⧸ Subgroup.center L) .PSU 3 2 f) (τ : MulAut L)
    (hτ : τ ^ 2 = 1) (hτout : ∀ x : L ⧸ Subgroup.center L, centerAutHom L τ ≠ MulAut.conj x)
    (Y : Subgroup L) {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ f)
    (hY : Nonempty (Y ≃* Matrix.SpecialLinearGroup (Fin 2) F)) (hYτ : ∀ y ∈ Y, τ y = y) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (h : UnitaryFieldData 2 f K)
      (Φ : (L ⧸ Subgroup.center L) ≃* PI h) (θ : PI h ≃* PI h) (H : GL (Fin 3) K),
      ((H : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ * (H : Matrix (Fin 3) (Fin 3) K) = 1 ∧
      (∀ g g' : gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K),
        (g' : GL (Fin 3) K) = H * g * H⁻¹ → θ (g : PI h) = g') ∧
      (∀ x, Φ (centerAutHom L τ x) = θ (barAut h (θ.symm (Φ x)))) ∧
      (Y.map (QuotientGroup.mk' (Subgroup.center L))).map Φ.toMonoidHom =
        (orthToP h).range.map θ.toMonoidHom := by
  obtain ⟨φ⟩ := hY
  have hcharF : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hF
  have hYZ := inf_center_eq_bot Y φ
  obtain ⟨⟨-, hf1, -⟩, K, _, _, hK, ⟨eD⟩⟩ := hmod
  have h : UnitaryFieldData 2 f K := ⟨Nat.prime_two, hf1, by rw [hK, ← pow_mul, mul_comm]⟩
  let Φ : (L ⧸ Subgroup.center L) ≃* PI h :=
    eD.trans ((unitaryPSUEquiv h (by norm_num : 1 ≤ 3)).symm.trans
      (unitaryPSUEquivPrimeFormOne h 3))
  set t : MulAut (PI h) := MulAut.congr Φ (centerAutHom L τ) with ht
  have htx : ∀ x, t (Φ x) = Φ (centerAutHom L τ x) := fun x => by
    simp [ht, MulAut.congr_apply]
  have ht2 : t ^ 2 = 1 := by
    rw [ht, ← map_pow, ← map_pow, hτ, map_one, map_one]
  have htout : ∀ z, t ≠ MulAut.conj z := by
    intro z hz
    apply hτout (Φ.symm z)
    apply MulEquiv.ext
    intro x
    have h1 := congrArg (fun a : MulAut (PI h) => a (Φ x)) hz
    simp only [MulAut.conj_apply] at h1
    rw [htx] at h1
    apply Φ.injective
    simp [h1]
  have ht1 : t ≠ 1 := fun h1 => htout 1 (by rw [h1, map_one])
  have hord : orderOf t = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime ht2 ht1
  have hcardY : Nat.card Y = Nat.card (Matrix.SpecialLinearGroup (Fin 2) h.fixedField) := by
    have : Finite K := h.finite
    rw [Nat.card_congr φ.toEquiv, card_specialLinearGroup_fin_two,
      card_specialLinearGroup_fin_two, hF, h.card_fixedField]
  set Ybar := Y.map (QuotientGroup.mk' (Subgroup.center L)) with hYbar
  set Y' : Subgroup (PI h) := Ybar.map Φ.toMonoidHom with hY'
  have hcard' : Nat.card Y' = Nat.card (Matrix.SpecialLinearGroup (Fin 2) h.fixedField) := by
    rw [hY', (Nat.card_congr (Subgroup.equivMapOfInjective Ybar Φ.toMonoidHom
      Φ.injective).toEquiv).symm, hYbar, card_map_mk_of_inf_eq_bot Y hYZ, hcardY]
  have hYt : ∀ y' ∈ Y', t y' = y' := by
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    show t (Φ (QuotientGroup.mk y)) = Φ (QuotientGroup.mk y)
    rw [htx, centerAutHom_mk, hYτ y hy]
  obtain ⟨θ, H, hH1, hθH, hθ, hθY⟩ :=
    unitary_involution_surviving h hf t hord htout Y' hcard' hYt
  refine ⟨K, inferInstance, inferInstance, h, Φ, θ, H, hH1, hθH, fun x => ?_, hθY⟩
  have h1 := hθ (θ.symm (Φ x))
  rw [MulEquiv.apply_symm_apply, htx] at h1
  exact h1

end Wrappers

end CFSG.CGT.PushingUpLit.CGT6X.K7a
