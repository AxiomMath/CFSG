module

public import CFSG.ClassicalGroups.UnitaryFlag.ModelTransport
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.ChainEmbedding

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YU5

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2]

@[expose] noncomputable def act (g : GL (HypIndex 2 1) K) : Module.End K (HypIndex 2 1 → K) :=
  Matrix.toLinAlgEquiv' (g : Matrix (HypIndex 2 1) (HypIndex 2 1) K)

theorem act_apply (g : GL (HypIndex 2 1) K) (v : HypIndex 2 1 → K) :
    act g v = (g : Matrix (HypIndex 2 1) (HypIndex 2 1) K) *ᵥ v := by
  simp [act]

theorem act_one : act (1 : GL (HypIndex 2 1) K) = 1 := by
  simp [act]

theorem act_pow (g : GL (HypIndex 2 1) K) (n : ℕ) : act (g ^ n) = act g ^ n := by
  simp [act, Units.val_pow_eq_pow_val, map_pow]

theorem hyp_isometry (h : UnitaryFieldData 2 1 K) (g : GL (HypIndex 2 1) K)
    (hg : g ∈ hypSU h 2 1) (x y : HypIndex 2 1 → K) :
    hypForm h 2 1 ((g : Matrix (HypIndex 2 1) (HypIndex 2 1) K) *ᵥ x)
      ((g : Matrix (HypIndex 2 1) (HypIndex 2 1) K) *ᵥ y) = hypForm h 2 1 x y := by
  have hg' : ((g : Matrix (HypIndex 2 1) (HypIndex 2 1) K).map h.bar)ᵀ * hypGram 2 1 K *
      (g : Matrix (HypIndex 2 1) (HypIndex 2 1) K) = hypGram 2 1 K :=
    (show _ ∧ _ from hg).1
  exact (gramForm_isometry_iff h (hypGram 2 1 K) _).mpr hg' x y

@[expose] def FixesPt (W : Submodule K (HypIndex 2 1 → K)) (g : GL (HypIndex 2 1) K) : Prop :=
  ∀ w ∈ W, (g : Matrix (HypIndex 2 1) (HypIndex 2 1) K) *ᵥ w = w

theorem fixesPt_mul {W : Submodule K (HypIndex 2 1 → K)} {g g' : GL (HypIndex 2 1) K}
    (hg : FixesPt W g) (hg' : FixesPt W g') : FixesPt W (g * g') := by
  intro w hw
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, hg' w hw, hg w hw]

theorem fixesPt_one (W : Submodule K (HypIndex 2 1 → K)) : FixesPt W (1 : GL (HypIndex 2 1) K) := by
  intro w _
  simp

theorem fixesPt_pow {W : Submodule K (HypIndex 2 1 → K)} {g : GL (HypIndex 2 1) K}
    (hg : FixesPt W g) (n : ℕ) : FixesPt W (g ^ n) := by
  induction n with
  | zero => simpa using fixesPt_one W
  | succ n ih => rw [pow_succ]; exact fixesPt_mul ih hg

noncomputable abbrev perpW (h : UnitaryFieldData 2 1 K) (W : Submodule K (HypIndex 2 1 → K)) :
    Submodule K (HypIndex 2 1 → K) :=
  W.orthogonalBilin (hypForm h 2 1)

theorem mem_perpW {h : UnitaryFieldData 2 1 K} {W : Submodule K (HypIndex 2 1 → K)}
    {y : HypIndex 2 1 → K} : y ∈ perpW h W ↔ ∀ n ∈ W, hypForm h 2 1 n y = 0 :=
  Iff.rfl

theorem finrank_V : Module.finrank K (HypIndex 2 1 → K) = 5 := by
  rw [Module.finrank_fintype_fun_eq_card, card_hypIndex]

theorem finrank_perpW (h : UnitaryFieldData 2 1 K) (W : Submodule K (HypIndex 2 1 → K))
    (hk : Module.finrank K W = 2) : Module.finrank K (perpW h W) = 3 := by
  show Module.finrank K (W.orthogonalBilin (hypForm h 2 1)) = 3
  have hsurj : Function.Surjective h.bar := Finite.surjective_of_injective h.bar.injective
  have := CFSG.HardMathSupport.Curtis.UnitaryLevi.finrank_orthogonalBilin_eq hsurj
    (hypForm_separatingLeft h) W
  rw [finrank_V] at this
  omega

structure Frame (h : UnitaryFieldData 2 1 K) (W : Submodule K (HypIndex 2 1 → K)) where
  m : HypIndex 2 1 → K
  ℓ : Module.Dual K (HypIndex 2 1 → K)
  mem_perp : m ∈ perpW h W
  ell_m : ℓ m = 1
  ell_W : ∀ w ∈ W, ℓ w = 0
  decomp : ∀ y ∈ perpW h W, y - ℓ y • m ∈ W

theorem exists_frame (h : UnitaryFieldData 2 1 K) (W : Submodule K (HypIndex 2 1 → K))
    (hW : ∀ x ∈ W, ∀ y ∈ W, hypForm h 2 1 x y = 0) (hk : Module.finrank K W = 2) :
    Nonempty (Frame h W) := by
  have hle : W ≤ perpW h W := fun x hx y hy => hW y hy x hx
  have hne : W ≠ perpW h W := by
    intro heq
    have h3 := finrank_perpW h W hk
    rw [← heq, hk] at h3
    omega
  obtain ⟨m, hm, hmW⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hle hne)
  have hm0 : m ≠ 0 := fun h0 => hmW (h0 ▸ W.zero_mem)
  have hinf : W ⊓ (K ∙ m) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxW, hxm⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hxm
    by_cases ha : a = 0
    · simp [ha]
    · exfalso
      apply hmW
      have hm' : m = a⁻¹ • (a • m) := by rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
      rw [hm']
      exact W.smul_mem a⁻¹ hxW
  have hsup_le : W ⊔ (K ∙ m) ≤ perpW h W := by
    refine sup_le hle ?_
    rw [Submodule.span_singleton_le_iff_mem]
    exact hm
  have hfin := Submodule.finrank_sup_add_finrank_inf_eq W (K ∙ m)
  rw [hinf, finrank_bot, finrank_span_singleton hm0, hk] at hfin
  have hsup : W ⊔ (K ∙ m) = perpW h W :=
    Submodule.eq_of_le_of_finrank_eq hsup_le (by rw [finrank_perpW h W hk]; omega)
  obtain ⟨ℓ0, hℓ0m, hℓ0W⟩ : ∃ f : Module.Dual K (HypIndex 2 1 → K), f m ≠ 0 ∧ W.map f = ⊥ :=
    Submodule.exists_dual_map_eq_bot_of_notMem hmW inferInstance
  set ℓ : Module.Dual K (HypIndex 2 1 → K) := (ℓ0 m)⁻¹ • ℓ0 with hℓdef
  have hℓm : ℓ m = 1 := by
    rw [hℓdef, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hℓ0m]
  have hℓW : ∀ w ∈ W, ℓ w = 0 := by
    intro w hw
    have hmem : ℓ0 w ∈ W.map ℓ0 := Submodule.mem_map_of_mem hw
    rw [hℓ0W, Submodule.mem_bot] at hmem
    rw [hℓdef, LinearMap.smul_apply, hmem, smul_zero]
  have hdec : ∀ y ∈ perpW h W, y - ℓ y • m ∈ W := by
    intro y hy
    have hy' : y ∈ W ⊔ (K ∙ m) := by rw [hsup]; exact hy
    obtain ⟨w, hw, z, hz, hwz⟩ := Submodule.mem_sup.mp hy'
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
    rw [← hwz]
    have hℓy : ℓ (w + a • m) = a := by
      rw [map_add, map_smul, hℓW w hw, hℓm, smul_eq_mul, mul_one, zero_add]
    rw [hℓy, add_sub_cancel_right]
    exact hw
  exact ⟨⟨m, ℓ, hm, hℓm, hℓW, hdec⟩⟩

@[expose] def cc {h : UnitaryFieldData 2 1 K} {W : Submodule K (HypIndex 2 1 → K)} (F : Frame h W)
    (g : GL (HypIndex 2 1) K) : K :=
  F.ℓ ((g : Matrix (HypIndex 2 1) (HypIndex 2 1) K) *ᵥ F.m)

theorem shift_mem_perp (h : UnitaryFieldData 2 1 K) {W : Submodule K (HypIndex 2 1 → K)}
    {g : GL (HypIndex 2 1) K} (hg : g ∈ hypSU h 2 1) (hfix : FixesPt W g)
    (x : HypIndex 2 1 → K) :
    (g : Matrix (HypIndex 2 1) (HypIndex 2 1) K) *ᵥ x - x ∈ perpW h W := by
  rw [mem_perpW]
  intro n hn
  have hgn := hfix n hn
  rw [map_sub, sub_eq_zero]
  calc hypForm h 2 1 n ((g : Matrix (HypIndex 2 1) (HypIndex 2 1) K) *ᵥ x)
      = hypForm h 2 1 ((g : Matrix (HypIndex 2 1) (HypIndex 2 1) K) *ᵥ n)
          ((g : Matrix (HypIndex 2 1) (HypIndex 2 1) K) *ᵥ x) := by rw [hgn]
    _ = hypForm h 2 1 n x := hyp_isometry h g hg n x

theorem act_m_mem_perp {h : UnitaryFieldData 2 1 K} {W : Submodule K (HypIndex 2 1 → K)}
    (F : Frame h W) {g : GL (HypIndex 2 1) K} (hg : g ∈ hypSU h 2 1) (hfix : FixesPt W g) :
    (g : Matrix (HypIndex 2 1) (HypIndex 2 1) K) *ᵥ F.m ∈ perpW h W := by
  have h1 := shift_mem_perp h hg hfix F.m
  have h2 := (perpW h W).add_mem h1 F.mem_perp
  simpa using h2

theorem cc_mul {h : UnitaryFieldData 2 1 K} {W : Submodule K (HypIndex 2 1 → K)}
    (F : Frame h W) {a b : GL (HypIndex 2 1) K} (ha : a ∈ hypSU h 2 1) (hb : b ∈ hypSU h 2 1)
    (hfa : FixesPt W a) (hfb : FixesPt W b) : cc F (a * b) = cc F a * cc F b := by
  unfold cc
  rw [Units.val_mul, ← Matrix.mulVec_mulVec]
  have hu : (b : Matrix (HypIndex 2 1) (HypIndex 2 1) K) *ᵥ F.m ∈ perpW h W :=
    act_m_mem_perp F hb hfb
  have hw := F.decomp _ hu
  have hsplit : (a : Matrix (HypIndex 2 1) (HypIndex 2 1) K) *ᵥ
      ((b : Matrix (HypIndex 2 1) (HypIndex 2 1) K) *ᵥ F.m) =
      ((b : Matrix (HypIndex 2 1) (HypIndex 2 1) K) *ᵥ F.m -
        F.ℓ ((b : Matrix (HypIndex 2 1) (HypIndex 2 1) K) *ᵥ F.m) • F.m) +
      F.ℓ ((b : Matrix (HypIndex 2 1) (HypIndex 2 1) K) *ᵥ F.m) •
        ((a : Matrix (HypIndex 2 1) (HypIndex 2 1) K) *ᵥ F.m) := by
    conv_lhs => rw [← sub_add_cancel ((b : Matrix (HypIndex 2 1) (HypIndex 2 1) K) *ᵥ F.m)
      (F.ℓ ((b : Matrix (HypIndex 2 1) (HypIndex 2 1) K) *ᵥ F.m) • F.m)]
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, hfa _ hw]
  rw [hsplit, map_add, map_smul, F.ell_W _ hw, zero_add, smul_eq_mul, mul_comm]

theorem pow_four_of_cc_one {h : UnitaryFieldData 2 1 K} {W : Submodule K (HypIndex 2 1 → K)}
    (F : Frame h W) {g : GL (HypIndex 2 1) K} (hg : g ∈ hypSU h 2 1) (hfix : FixesPt W g)
    (hc : cc F g = 1) : g ^ 4 = 1 := by
  set N : Module.End K (HypIndex 2 1 → K) := act g - 1 with hNdef
  have hNv : ∀ v, N v = (g : Matrix (HypIndex 2 1) (HypIndex 2 1) K) *ᵥ v - v := by
    intro v
    simp [hNdef, act_apply]
  have hN_fix : ∀ w ∈ W, N w = 0 := by
    intro w hw
    rw [hNv, hfix w hw, sub_self]
  have hN_perp : ∀ v, N v ∈ perpW h W := by
    intro v
    rw [hNv]
    exact shift_mem_perp h hg hfix v
  have hNm : N F.m ∈ W := by
    have hz := shift_mem_perp h hg hfix F.m
    have hℓz : F.ℓ ((g : Matrix (HypIndex 2 1) (HypIndex 2 1) K) *ᵥ F.m - F.m) = 0 := by
      rw [map_sub, F.ell_m]
      have hc' : F.ℓ ((g : Matrix (HypIndex 2 1) (HypIndex 2 1) K) *ᵥ F.m) = 1 := hc
      rw [hc', sub_self]
    have hdec := F.decomp _ hz
    rw [hℓz, zero_smul, sub_zero] at hdec
    rw [hNv]
    exact hdec
  have hN_W : ∀ y ∈ perpW h W, N y ∈ W := by
    intro y hy
    have hyW := F.decomp y hy
    have key : N y = N (y - F.ℓ y • F.m) + F.ℓ y • N F.m := by
      rw [← map_smul, ← map_add, sub_add_cancel]
    rw [key, hN_fix _ hyW, zero_add]
    exact W.smul_mem _ hNm
  have hN3 : N ^ 3 = 0 := by
    apply LinearMap.ext
    intro v
    have h3 := hN_fix _ (hN_W _ (hN_perp v))
    simpa [pow_succ, Module.End.mul_apply] using h3
  have hN4 : N ^ 4 = 0 := by
    rw [pow_succ', hN3, mul_zero]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP (Module.End K (HypIndex 2 1 → K)) 2 :=
    charP_of_injective_algebraMap (algebraMap K (Module.End K (HypIndex 2 1 → K))).injective 2
  have hact : act g = 1 + N := by
    rw [hNdef]
    abel
  have hpow4 : act g ^ 4 = 1 := by
    rw [hact]
    have h4 := add_pow_char_pow_of_commute (p := 2) (n := 2) (Commute.one_left N)
    norm_num at h4
    rw [h4, hN4, add_zero]
  have hA4 : act (g ^ 4) = act 1 := by
    rw [act_pow, hpow4, act_one]
  have hmat := (Matrix.toLinAlgEquiv' :
    Matrix (HypIndex 2 1) (HypIndex 2 1) K ≃ₐ[K] Module.End K (HypIndex 2 1 → K)).injective hA4
  exact Units.ext hmat

theorem not_order_five {h : UnitaryFieldData 2 1 K} (hK : Nat.card K = 4)
    {W : Submodule K (HypIndex 2 1 → K)} (F : Frame h W) {x : GL (HypIndex 2 1) K}
    (hx : x ∈ hypSU h 2 1) (hfix : FixesPt W x) (hord : orderOf x = 5) : False := by
  have hx5 : x ^ 5 = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one x
  have h1 : cc F 1 = 1 := by
    simp [cc, F.ell_m]
  have hcpow : ∀ n : ℕ, cc F (x ^ n) = cc F x ^ n := by
    intro n
    induction n with
    | zero => simpa using h1
    | succ n ih =>
      rw [pow_succ, cc_mul F (pow_mem hx n) hx (fixesPt_pow hfix n) hfix, ih, pow_succ]
  have h5 : cc F x ^ 5 = 1 := by
    rw [← hcpow 5, hx5, h1]
  have hne : cc F x ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by norm_num)] at h5
    exact zero_ne_one h5
  haveI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 4 := by
    rw [← Nat.card_eq_fintype_card]
    exact hK
  have h3 : cc F x ^ 3 = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one (cc F x) hne
    rw [hcard] at this
    simpa using this
  have hgcd : cc F x ^ Nat.gcd 5 3 = 1 := pow_gcd_eq_one.mpr ⟨h5, h3⟩
  have hc1 : cc F x = 1 := by
    have h53 : Nat.gcd 5 3 = 1 := by norm_num
    rw [h53, pow_one] at hgcd
    exact hgcd
  have h4 := pow_four_of_cc_one F hx hfix hc1
  have hdvd : orderOf x ∣ 4 := orderOf_dvd_of_pow_eq_one h4
  rw [hord] at hdvd
  norm_num at hdvd

theorem not_five_dvd_pointwise {h : UnitaryFieldData 2 1 K} (hK : Nat.card K = 4)
    {W : Submodule K (HypIndex 2 1 → K)} (F : Frame h W) (Y : Subgroup (hypSU h 2 1))
    (hY : ∀ y ∈ Y, FixesPt W ((y : hypSU h 2 1) : GL (HypIndex 2 1) K)) :
    ¬ 5 ∣ Nat.card Y := by
  intro h5
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := Y) 5 h5
  have hord : orderOf ((y : hypSU h 2 1) : GL (HypIndex 2 1) K) = 5 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hy]
  exact not_order_five hK F (y : hypSU h 2 1).2 (hY y y.2) hord

end CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YU5

end
