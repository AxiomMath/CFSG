module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchExt
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.QuotientGroup.Defs

public section

namespace CFSG.KC.SBExt

open CFSG.EvenSmallLie.OmegaEight.SpBranch Subgroup

universe u

variable {S : Type u} [Group S] {N : ℕ} {mul : ℕ → ℕ → ℕ} (Φ : CodeIso S N mul) (F : ℕ → ℕ) (z : ℕ)

structure ExtHyp : Prop where
  h0 : mul 0 0 = 0
  lt : ∀ s : S, F (Φ.f s) < N
  hmul : ∀ a < N, ∀ c < N, F (mul a c) = mul (F a) (F c)
  hz : z < N
  hFz : F z = z
  hconj : ∀ y < N, mul z y = mul (F (F y)) z

variable {Φ F z}

theorem g_mul {c d : ℕ} (hc : c < N) (hd : d < N) : Φ.g (mul c d) = Φ.g c * Φ.g d := by
  have e : mul c d = Φ.f (Φ.g c * Φ.g d) := by rw [Φ.map_mul, Φ.f_g hc, Φ.f_g hd]
  rw [e, Φ.g_f]

variable (hE : ExtHyp Φ F z)
include hE

@[expose] noncomputable def αh : S →* S where
  toFun s := Φ.g (F (Φ.f s))
  map_one' := by
    have h1 : F 0 < N := by
      have := hE.lt 1
      rwa [Φ.f_one hE.h0] at this
    have e1 := hE.hmul 0 Φ.pos 0 Φ.pos
    rw [hE.h0] at e1
    have e2 : Φ.g (F 0) = Φ.g (F 0) * Φ.g (F 0) := by
      conv_lhs => rw [e1]
      exact g_mul h1 h1
    rw [Φ.f_one hE.h0]
    exact (mul_eq_left.1 e2.symm)
  map_mul' a b := by
    rw [Φ.map_mul, hE.hmul _ (Φ.lt a) _ (Φ.lt b), g_mul (hE.lt a) (hE.lt b)]

theorem f_αh (s : S) : Φ.f (αh hE s) = F (Φ.f s) := Φ.f_g (hE.lt s)

theorem αh_αh (s : S) : αh hE (αh hE s) = Φ.g z * s * (Φ.g z)⁻¹ := by
  have e : Φ.g z * s = αh hE (αh hE s) * Φ.g z := by
    refine Φ.inj ?_
    rw [Φ.map_mul, Φ.map_mul, Φ.f_g hE.hz, f_αh, f_αh, hE.hconj _ (Φ.lt s)]
  rw [e]
  group

theorem αh_inj : Function.Injective (αh hE) := by
  intro a b h
  have := congrArg (αh hE) h
  rw [αh_αh, αh_αh] at this
  simpa using this

@[expose] noncomputable def αe : MulAut S :=
  have := Φ.finite
  MulEquiv.ofBijective (αh hE) ⟨αh_inj hE, Finite.surjective_of_injective (αh_inj hE)⟩

theorem αe_apply (s : S) : αe hE s = αh hE s := rfl

theorem αe_z : αe hE (Φ.g z) = Φ.g z := by
  rw [αe_apply]
  refine Φ.inj ?_
  rw [f_αh, Φ.f_g hE.hz, hE.hFz]

theorem αe_zpow_z (n : ℤ) : (αe hE ^ n) (Φ.g z) = Φ.g z := by
  induction n using Int.induction_on with
  | zero => rfl
  | succ n ih => rw [zpow_add_one, MulAut.mul_apply, αe_z, ih]
  | pred n ih =>
    rw [zpow_sub_one, MulAut.mul_apply, MulAut.inv_apply, (MulEquiv.symm_apply_eq _).2 (αe_z hE).symm,
      ih]

@[expose] noncomputable def φ : Multiplicative ℤ →* MulAut S := zpowersHom (MulAut S) (αe hE)

abbrev P := SemidirectProduct S (Multiplicative ℤ) (φ hE)

@[expose] noncomputable def wE : P hE := ⟨(Φ.g z)⁻¹, Multiplicative.ofAdd 2⟩

theorem φ_z (n : Multiplicative ℤ) : φ hE n (Φ.g z)⁻¹ = (Φ.g z)⁻¹ := by
  rw [map_inv, φ, zpowersHom_apply, αe_zpow_z]

theorem φ_two (s : S) : φ hE (Multiplicative.ofAdd 2) s = Φ.g z * s * (Φ.g z)⁻¹ := by
  rw [φ, zpowersHom_apply, toAdd_ofAdd, zpow_two, MulAut.mul_apply, αe_apply, αe_apply, αh_αh]

theorem wE_comm (p : P hE) : p * wE hE = wE hE * p := by
  refine SemidirectProduct.ext ?_ ?_
  · rw [SemidirectProduct.mul_left, SemidirectProduct.mul_left, wE]
    simp only
    rw [φ_z, φ_two]
    group
  · rw [SemidirectProduct.mul_right, SemidirectProduct.mul_right]
    exact mul_comm _ _

instance wE_normal : (zpowers (wE hE)).Normal where
  conj_mem n hn g := by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hn
    have hc0 : Commute g (wE hE) := wE_comm hE g
    have hc : Commute g (wE hE ^ k) := hc0.zpow_right k
    rw [hc.eq, mul_inv_cancel_right]
    exact zpow_mem (mem_zpowers _) k

abbrev T := P hE ⧸ zpowers (wE hE)

theorem right_zpow (k : ℤ) : (wE hE ^ k).right = Multiplicative.ofAdd (2 * k) := by
  have := map_zpow (SemidirectProduct.rightHom (φ := φ hE)) (wE hE) k
  rw [SemidirectProduct.rightHom_eq_right] at this
  rw [this, wE]
  simp only
  rw [← ofAdd_zsmul, smul_eq_mul, mul_comm]

@[expose] noncomputable def ι : S →* T hE := (QuotientGroup.mk' _).comp SemidirectProduct.inl

theorem ι_inj : Function.Injective (ι hE) := by
  refine (injective_iff_map_eq_one _).2 fun s hs => ?_
  rw [ι, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hs
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hs
  have hr := congrArg SemidirectProduct.right hk
  rw [right_zpow, SemidirectProduct.right_inl] at hr
  have hk0 : k = 0 := by
    have := congrArg Multiplicative.toAdd hr
    simp only [toAdd_ofAdd, toAdd_one] at this
    omega
  rw [hk0, zpow_zero] at hk
  exact SemidirectProduct.inl_injective (hk.symm.trans (map_one _).symm)

noncomputable abbrev K := (ι hE).range

@[expose] noncomputable def ΦK : CodeIso (K hE) N mul := Φ.ofEquiv (MonoidHom.ofInjective (ι_inj hE)).symm

theorem ΦK_f (s : S) (h : ι hE s ∈ K hE) : (ΦK hE).f ⟨ι hE s, h⟩ = Φ.f s := by
  change Φ.f ((MonoidHom.ofInjective (ι_inj hE)).symm _) = _
  congr 1
  rw [MulEquiv.symm_apply_eq]
  exact Subtype.ext (MonoidHom.ofInjective_apply _).symm

@[expose] noncomputable def xE : T hE := QuotientGroup.mk (SemidirectProduct.inr (Multiplicative.ofAdd 1))

theorem xE_conj (s : S) : xE hE * ι hE s * (xE hE)⁻¹ = ι hE (αh hE s) := by
  rw [xE, ι, MonoidHom.comp_apply, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.mk'_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
    ← map_inv, ← SemidirectProduct.inl_aut]
  unfold φ
  rw [zpowersHom_apply, toAdd_ofAdd, zpow_one, αe_apply]
  rfl

theorem xE_mem : xE hE ∈ normalizer ((K hE : Subgroup (T hE)) : Set (T hE)) := by
  refine mem_normalizer_iff.2 fun h => ⟨fun hh => ?_, fun hh => ?_⟩
  · obtain ⟨s, rfl⟩ := hh
    exact ⟨_, (xE_conj hE s).symm⟩
  · obtain ⟨t, ht⟩ := hh
    have := Φ.finite
    obtain ⟨s, rfl⟩ := Finite.surjective_of_injective (αh_inj hE) t
    have e : h = ι hE s := by
      have h2 := xE_conj hE s
      rw [ht] at h2
      exact (mul_left_cancel (mul_right_cancel h2)).symm
    exact ⟨s, e.symm⟩

theorem xE_not_mem : xE hE ∉ K hE := by
  rintro ⟨s, hs⟩
  rw [ι, MonoidHom.comp_apply, QuotientGroup.mk'_apply, xE, QuotientGroup.eq] at hs
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hs
  have hr := congrArg SemidirectProduct.right hk
  rw [right_zpow, SemidirectProduct.mul_right, SemidirectProduct.inv_right,
    SemidirectProduct.right_inl, SemidirectProduct.right_inr, inv_one, one_mul] at hr
  have := congrArg Multiplicative.toAdd hr
  simp only [toAdd_ofAdd] at this
  omega

theorem xE_sq : xE hE * xE hE = ι hE (Φ.g z) := by
  refine Eq.symm ?_
  rw [xE, ι, MonoidHom.comp_apply, QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul,
    QuotientGroup.eq]
  refine mem_zpowers_iff.2 ⟨1, ?_⟩
  rw [zpow_one]
  refine SemidirectProduct.ext ?_ ?_
  · simp [wE, SemidirectProduct.mul_left, SemidirectProduct.inv_left]
  · simp only [wE, SemidirectProduct.mul_right, SemidirectProduct.inv_right,
      SemidirectProduct.right_inl, SemidirectProduct.right_inr, inv_one, one_mul, ← ofAdd_add]
    rfl

theorem xE_sq_mem : xE hE * xE hE ∈ K hE := by
  rw [xE_sq]
  exact MonoidHom.mem_range.2 ⟨_, rfl⟩

theorem hF_E : ∀ k : K hE, (ΦK hE).f ⟨xE hE * k * (xE hE)⁻¹,
    (mem_normalizer_iff.1 (xE_mem hE) k).1 k.2⟩ = F ((ΦK hE).f k) := by
  rintro ⟨k, hk⟩
  obtain ⟨s, rfl⟩ := MonoidHom.mem_range.1 hk
  have e : (⟨xE hE * ι hE s * (xE hE)⁻¹, (mem_normalizer_iff.1 (xE_mem hE) _).1 hk⟩ : K hE) =
      ⟨ι hE (αh hE s), MonoidHom.mem_range.2 ⟨_, rfl⟩⟩ :=
    Subtype.ext (xE_conj hE s)
  rw [e, ΦK_f, ΦK_f, f_αh]

theorem ΦK_sq : (ΦK hE).f ⟨xE hE * xE hE, xE_sq_mem hE⟩ = z := by
  have e : (⟨xE hE * xE hE, xE_sq_mem hE⟩ : K hE) =
      ⟨ι hE (Φ.g z), MonoidHom.mem_range.2 ⟨_, rfl⟩⟩ :=
    Subtype.ext (xE_sq hE)
  rw [e, ΦK_f, Φ.f_g hE.hz]

omit hE in
theorem exists_ext (hE : ExtHyp Φ F z) :
    ∃ (H : Type u) (_ : Group H), Nonempty (CodeIso H (2 * N) (extMul N mul F z)) :=
  ⟨_, inferInstance, ⟨ΦK_sq hE ▸ (ΦK hE).extCodeIso (xE_mem hE) (xE_not_mem hE) (xE_sq_mem hE)
    (hF_E hE)⟩⟩

end CFSG.KC.SBExt

end
