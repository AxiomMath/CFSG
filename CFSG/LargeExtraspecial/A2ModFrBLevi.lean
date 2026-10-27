module

public import CFSG.LieType.Universal.SpinOmega.Range
public import CFSG.LieType.Universal.SpinOmega.Kernel
public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.LargeExtraspecial.A2ModCfgSL
public import CFSG.LieType.Universal.Spin.Twisted.Frame

public section

namespace CFSG.LargeExtraspecial.A2Mod.FrB

open Matrix CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted

section Lift

variable {G M N : Type*} [Group G] [Group M] [Group N]

noncomputable def liftHom (f : M →* N) (hf : Function.Injective f) (g : G →* N)
    (hg : g.range ≤ f.range) : G →* M :=
  (MonoidHom.ofInjective hf).symm.toMonoidHom.comp (g.codRestrict f.range fun x => hg ⟨x, rfl⟩)

theorem apply_liftHom (f : M →* N) (hf : Function.Injective f) (g : G →* N)
    (hg : g.range ≤ f.range) (x : G) : f (liftHom f hf g hg x) = g x := by
  change f ((MonoidHom.ofInjective hf).symm ⟨g x, hg ⟨x, rfl⟩⟩) = g x
  rw [← MonoidHom.ofInjective_apply hf, MulEquiv.apply_symm_apply]

end Lift

variable (n : ℕ) (K : Type*) [Field K]

@[expose] def leviFun (g : SpecialLinearGroup (Fin (n - 1)) K) (v : Vm n K) : Vm n K :=
  Sum.elim ((g : Matrix (Fin (n - 1)) (Fin (n - 1)) K) *ᵥ fun i => v (.inl i))
    (Sum.elim (contra g fun i => v (.inr (.inl i))) fun t => v (.inr (.inr t)))

variable {n K}

@[simp] theorem leviFun_inl (g : SpecialLinearGroup (Fin (n - 1)) K) (v : Vm n K)
    (i : Fin (n - 1)) :
    leviFun n K g v (.inl i) = ((g : Matrix (Fin (n - 1)) (Fin (n - 1)) K) *ᵥ
      fun i => v (.inl i)) i := rfl

@[simp] theorem leviFun_inr_inl (g : SpecialLinearGroup (Fin (n - 1)) K) (v : Vm n K)
    (i : Fin (n - 1)) :
    leviFun n K g v (.inr (.inl i)) = contra g (fun i => v (.inr (.inl i))) i := rfl

@[simp] theorem leviFun_inr_inr (g : SpecialLinearGroup (Fin (n - 1)) K) (v : Vm n K)
    (t : Fin 2) : leviFun n K g v (.inr (.inr t)) = v (.inr (.inr t)) := rfl

theorem leviFun_add (g : SpecialLinearGroup (Fin (n - 1)) K) (v w : Vm n K) :
    leviFun n K g (v + w) = leviFun n K g v + leviFun n K g w := by
  funext x
  rcases x with i | i | t
  · change (_ *ᵥ ((fun i => v (.inl i)) + fun i => w (.inl i))) i = _
    rw [mulVec_add]
    rfl
  · change contra g ((fun i => v (.inr (.inl i))) + fun i => w (.inr (.inl i))) i = _
    rw [contra_add]
    rfl
  · rfl

theorem leviFun_smul (g : SpecialLinearGroup (Fin (n - 1)) K) (a : K) (v : Vm n K) :
    leviFun n K g (a • v) = a • leviFun n K g v := by
  funext x
  rcases x with i | i | t
  · change (_ *ᵥ (a • fun i => v (.inl i))) i = _
    rw [mulVec_smul]
    rfl
  · change contra g (a • fun i => v (.inr (.inl i))) i = _
    rw [contra_smul]
    rfl
  · rfl

theorem leviFun_mul (g h : SpecialLinearGroup (Fin (n - 1)) K) (v : Vm n K) :
    leviFun n K (g * h) v = leviFun n K g (leviFun n K h v) := by
  funext x
  rcases x with i | i | t
  · rw [leviFun_inl, leviFun_inl, sl_mulVec_mul]
    rfl
  · change contra (g * h) _ i = _
    rw [contra_mul]
    rfl
  · rfl

theorem leviFun_one (v : Vm n K) : leviFun n K 1 v = v := by
  funext x
  rcases x with i | i | t
  · exact congrFun (one_mulVec (fun i => v (Sum.inl i))) i
  · change contra 1 _ i = _
    rw [contra_one]
  · rfl

@[expose] def leviEquiv (g : SpecialLinearGroup (Fin (n - 1)) K) : Vm n K ≃ₗ[K] Vm n K where
  toFun := leviFun n K g
  invFun := leviFun n K g⁻¹
  map_add' := leviFun_add g
  map_smul' := leviFun_smul g
  left_inv v := by rw [← leviFun_mul, inv_mul_cancel, leviFun_one]
  right_inv v := by rw [← leviFun_mul, mul_inv_cancel, leviFun_one]

variable (n K) in
@[expose] def leviHom : SpecialLinearGroup (Fin (n - 1)) K →* (Vm n K ≃ₗ[K] Vm n K) where
  toFun := leviEquiv
  map_one' := LinearEquiv.ext fun v => leviFun_one v
  map_mul' g h := LinearEquiv.ext fun v => leviFun_mul g h v

theorem leviHom_apply (g : SpecialLinearGroup (Fin (n - 1)) K) (v : Vm n K) :
    leviHom n K g v = leviFun n K g v := rfl

theorem quadMinus_leviFun (b c : K) (g : SpecialLinearGroup (Fin (n - 1)) K) (v : Vm n K) :
    quadMinus n K b c (leviFun n K g v) = quadMinus n K b c v := by
  have h := contra_dotProduct_mulVec g (fun i => v (.inr (.inl i))) fun i => v (.inl i)
  rw [quadMinus_apply, quadMinus_apply]
  simp only [leviFun_inl, leviFun_inr_inl, leviFun_inr_inr]
  congr 3
  rw [dotProduct_comm] at h
  simpa only [dotProduct, mul_comm] using h

section Spin

variable (n) {K : Type} [Field K] [Finite K] {b c : K}

theorem spinAction_injective (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (h2 : (2 : K) = 0) :
    Function.Injective (spinAction (quadMinus n K b c)) := by
  rw [← MonoidHom.ker_eq_bot_iff, ← ker_spinMatrix]
  exact ker_spinMatrix_quadMinus_eq_bot hirr h2

theorem range_leviHom_le (hn : 4 ≤ n) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (leviHom n K).range ≤ (spinAction (quadMinus n K b c)).range := by
  have := CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (K := K)
    (n := n - 1) (by omega)
  rw [range_spinAction_quadMinus_eq_commutator hn hirr, MonoidHom.range_eq_map,
    ← Group.IsPerfect.commutator_eq_top, commutator_def, Subgroup.map_commutator]
  have hO : (⊤ : Subgroup (SpecialLinearGroup (Fin (n - 1)) K)).map (leviHom n K) ≤
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus n K b c) := by
    rintro _ ⟨g, -, rfl⟩
    exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (quadMinus_leviFun b c g)
  exact Subgroup.commutator_mono hO hO

variable (b c) in
noncomputable def leviSpin (hn : 4 ≤ n) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (h2 : (2 : K) = 0) : SpecialLinearGroup (Fin (n - 1)) K →* spinGroup (quadMinus n K b c) :=
  liftHom _ (spinAction_injective n hirr h2) (leviHom n K) (range_leviHom_le n hn hirr)

theorem spinAction_leviSpin (hn : 4 ≤ n) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (h2 : (2 : K) = 0) (g : SpecialLinearGroup (Fin (n - 1)) K) :
    spinAction (quadMinus n K b c) (leviSpin n b c hn hirr h2 g) = leviHom n K g :=
  apply_liftHom _ _ _ _ g

theorem leviSpin_transvection (hn : 4 ≤ n) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (h2 : (2 : K) = 0) {i j : Fin (n - 1)} (hij : i ≠ j) (a : K) :
    leviSpin n b c hn hirr h2 (SpecialLinearGroup.transvection hij a) =
      (minusFrame n b c).longRoot hij true false (.ofAdd a) := by
  apply spinAction_injective n hirr h2
  rw [spinAction_leviSpin]
  refine LinearEquiv.ext fun v => funext fun x => ?_
  rw [leviHom_apply, HypFrame.spinAction_longRoot]
  simp only [minusFrame_vec, minusVec_true, minusVec_false, eVec, fVec,
    polar_quadMinus_single_inl, polar_quadMinus_single_inr_inl]
  have hdot : (Pi.single j (1 : K) : Fin (n - 1) → K) ⬝ᵥ Pi.single i a = 0 := by
    rw [single_dotProduct, one_mul, Pi.single_eq_of_ne hij.symm]
  rw [transvection_eq_tv hij]
  rcases x with l | l | t
  · rw [leviFun_inl, tv_mulVec hdot]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, single_dotProduct,
      one_mul]
    by_cases hl : l = i
    · subst hl
      simp [mul_comm]
    · simp [hl]
  · rw [leviFun_inr_inl, contra_tv hdot]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, dotProduct_single]
    by_cases hl : l = j
    · subst hl
      simp [mul_comm]
    · simp [hl]
  · simp

end Spin

section Two

variable (n) {K : Type} [Field K] [Finite K] {b c : K}

omit [Finite K] in
theorem two_eq_zero_of_card (hK : Nat.card K = 2) : (2 : K) = 0 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have h : (ringEquivZModTwo K hK).symm (2 : ZMod 2) = 2 := map_ofNat _ 2
  rw [← h]
  exact map_eq_zero_iff _ (RingEquiv.injective _) |>.mpr rfl

variable (b c) in
noncomputable def leviZ (hn : 4 ≤ n) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hK : Nat.card K = 2) :
    SpecialLinearGroup (Fin (n - 1)) (ZMod 2) →* spinGroup (quadMinus n K b c) :=
  (leviSpin n b c hn hirr (two_eq_zero_of_card hK)).comp
    (slEquiv (ringEquivZModTwo K hK).symm).toMonoidHom

theorem leviZ_elemTv (hn : 4 ≤ n) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hK : Nat.card K = 2) {i j : Fin (n - 1)} (hij : i ≠ j) :
    leviZ n b c hn hirr hK (elemTv i j) =
      (minusFrame n b c).longRoot hij true false (.ofAdd 1) := by
  rw [leviZ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, elemTv_eq_transvection hij,
    slEquiv_transvection, map_one, leviSpin_transvection]

end Two

end CFSG.LargeExtraspecial.A2Mod.FrB
