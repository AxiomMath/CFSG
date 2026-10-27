module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD309LieHeart3

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309L

open CFSG.LocalAnalysis.RankThreeUC.S15.ACore Equiv Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309
open scoped commutatorElement

variable {A : Type} [Group A] {Φ : M5 →* A}

theorem ker_eq_Sc (hΦ : KerSc Φ) : Φ.ker = Sc := by
  ext x
  rw [MonoidHom.mem_ker, hΦ x]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, rfl⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c, rfl⟩

theorem card_map_mul_five (hΦ : KerSc Φ) {K : Subgroup M5} (hK : Sc ≤ K) :
    Nat.card (K.map Φ) * 5 = Nat.card K := by
  have h := Subgroup.card_ker_mul_card_range (Φ.comp K.subtype)
  have hker : Nat.card (Φ.comp K.subtype).ker = 5 := by
    have : (Φ.comp K.subtype).ker = Sc.subgroupOf K := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← ker_eq_Sc hΦ, MonoidHom.mem_ker]
      rfl
    rw [this, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK).toEquiv, card_Sc]
  have hrange : (Φ.comp K.subtype).range = K.map Φ := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, k.2, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, rfl⟩
  rw [hker, hrange] at h
  linarith

theorem mem_normalizer_map (N : Subgroup M5) [N.Normal] (x : M5) :
    Φ x ∈ normalizer ((N.map Φ : Subgroup A) : Set A) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨x * n * x⁻¹, Subgroup.Normal.conj_mem inferInstance n hn x, by simp⟩
  · rintro ⟨n, hn, hny⟩
    refine ⟨x⁻¹ * n * x, ?_, ?_⟩
    · have := Subgroup.Normal.conj_mem inferInstance n hn x⁻¹
      simpa using this
    · rw [map_mul, map_mul, map_inv, hny]
      group

instance : T0.Normal := by
  unfold T0
  haveI : (monDet : M5 →* C5).ker.Normal := MonoidHom.normal_ker _
  infer_instance

@[expose] def ddv : Fin 5 → ZMod 5 := fun i => ((i : ℕ) : ZMod 5)

theorem mT_pow (y : Fin 5 → ZMod 5) (k : ℕ) : (mT y) ^ k = mT (k • y) := by
  induction k with
  | zero => simp [mT_zero]
  | succ k ih => rw [pow_succ, ih, ← mT_add, succ_nsmul]

theorem mT_ddv_mem_T0 : mT ddv ∈ T0 := by
  refine ⟨monT_mem_T5 _, ?_⟩
  change monDet (monT _) = 1
  rw [monDet_monT]
  have : ∏ i : Fin 5, Multiplicative.ofAdd (ddv i) = Multiplicative.ofAdd (∑ i, ddv i) :=
    (ofAdd_sum _ _).symm
  rw [this]
  have h0 : ∑ i, ddv i = 0 := by
    simp [Fin.sum_univ_five, ddv]
    decide
  rw [h0]
  rfl

theorem nsmul_ddv (k : ℕ) (i : Fin 5) : (k • ddv) i = (k : ZMod 5) * ((i : ℕ) : ZMod 5) := by
  simp [ddv, nsmul_eq_mul]

theorem center_eq (hΦ : KerSc Φ) {z : A} (hzP : z ∈ Pt Φ) (hzc : ∀ p ∈ Pt Φ, p * z = z * p) :
    ∃ k : ℕ, z = (Φ (mT ddv)) ^ k := by
  obtain ⟨r, hrP, rfl⟩ := hzP
  have hcomm : ∀ u ∈ Pm, ∃ c : C5, ⁅r, u⁆ = monScalar C5 5 c := by
    intro u hu
    have h1 : Φ ⁅r, u⁆ = 1 := by
      rw [map_commutatorElement]
      exact (commutatorElement_eq_one_iff_mul_comm).mpr (hzc (Φ u) ⟨u, hu, rfl⟩).symm
    exact (hΦ _).mp h1
  have hD : ∀ t : Fin 5 → C5, ∏ i, t i = 1 → monT t ∈ Pm := fun t _ =>
    T5_le_Pm (monT_mem_T5 t)
  have hζ2 : (Multiplicative.ofAdd (1 : ZMod 5)) ^ 2 ≠ 1 := by decide
  have hr : r.right = 1 :=
    CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.RankP.LU.right_eq_one_of_scalar_comm
      (by norm_num) hζ2 hD hcomm
  have hrT : r = monT r.left := eq_monT_of_right_eq_one hr
  set t : Fin 5 → C5 := r.left with ht
  set y : Fin 5 → ZMod 5 := fun i => Multiplicative.toAdd (t i) with hy
  have hσ : monS (C := C5) sig5 ∈ Pm := by
    have := monS_zpow_mem_Pm 1
    rwa [zpow_one] at this
  obtain ⟨c, hc⟩ := hcomm _ hσ
  have hmon : (monS (C := C5) sig5).right = sig5 := rfl
  rw [hrT, comm_monT_left, hmon, monScalar_apply] at hc
  have hc' := monT_injective hc
  set γ : ZMod 5 := Multiplicative.toAdd c with hγ
  have hall : ∀ i : Fin 5, y i - y (i - 1) = γ := by
    intro i
    have h1 := congrFun hc' i
    simp only [Function.comp_apply, Pi.mul_apply, Pi.inv_apply, sig5_symm_apply] at h1
    have h2 := congrArg Multiplicative.toAdd h1
    simp only [toAdd_mul, toAdd_inv] at h2
    rw [hγ, ← h2]
    simp only [hy]
    ring
  have h1 : y 1 - y 0 = γ := hall 1
  have h2 : y 2 - y 1 = γ := hall 2
  have h3 : y 3 - y 2 = γ := hall 3
  have h4 : y 4 - y 3 = γ := hall 4
  have hyform : y = (fun _ => y 0) + (γ.val • ddv) := by
    funext i
    have hv : ((γ.val : ℕ) : ZMod 5) = γ := ZMod.natCast_zmod_val γ
    rw [Pi.add_apply, nsmul_ddv, hv]
    fin_cases i
    · show y 0 = y 0 + γ * ((0 : ℕ) : ZMod 5)
      push_cast
      ring
    · show y 1 = y 0 + γ * ((1 : ℕ) : ZMod 5)
      push_cast
      linear_combination h1
    · show y 2 = y 0 + γ * ((2 : ℕ) : ZMod 5)
      push_cast
      linear_combination h1 + h2
    · show y 3 = y 0 + γ * ((3 : ℕ) : ZMod 5)
      push_cast
      linear_combination h1 + h2 + h3
    · show y 4 = y 0 + γ * ((4 : ℕ) : ZMod 5)
      push_cast
      linear_combination h1 + h2 + h3 + h4
  have hmT : mT y = mT (fun _ => y 0) * mT (γ.val • ddv) := by
    rw [← mT_add, ← hyform]
  refine ⟨γ.val, ?_⟩
  have hΦr : Φ r = Φ (mT y) := by
    rw [hrT]
    exact congrArg Φ (monT_eq_mT t)
  rw [hΦr, hmT, map_mul, mT_const, (hΦ _).mpr ⟨_, rfl⟩, one_mul, ← mT_pow, map_pow]

theorem card_Jt (hΦ : KerSc Φ) : Nat.card (Jt Φ) = 5 ^ 4 := by
  have h := card_map_mul_five hΦ Sc_le_T5
  rw [card_T5] at h
  unfold Jt
  omega

theorem card_Et (hΦ : KerSc Φ) : Nat.card (Et Φ) = 5 ^ 3 := by
  have h := card_map_mul_five hΦ Sc_le_T0
  rw [card_T0] at h
  unfold Et
  omega

theorem isElemAbelian_Jt : CFSG.Open.IsElemAbelian 5 (Jt Φ) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨x, hx, hxa⟩ := a.2
    obtain ⟨y, hy, hyb⟩ := b.2
    obtain ⟨s, rfl⟩ := hx
    obtain ⟨t, rfl⟩ := hy
    refine Subtype.ext ?_
    change (a : A) * b = b * a
    have hc := congrArg Φ (monT_comm s t)
    rw [map_mul, map_mul] at hc
    rw [← hxa, ← hyb]
    exact hc
  · obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨s, rfl⟩ := hy
    rw [← map_pow]
    have : (SemidirectProduct.inl s : M5) ^ 5 = 1 := by
      rw [← map_pow (SemidirectProduct.inl : (Fin 5 → C5) →* M5) s 5]
      have : s ^ 5 = 1 := by
        funext i
        exact c5_pow_five (s i)
      rw [this]
      exact map_one _
    rw [this, map_one]

theorem Jt_le_Pt : Jt Φ ≤ Pt Φ := Subgroup.map_mono T5_le_Pm

theorem monS_not_mem_Jt (hΦ : KerSc Φ) {τ : Perm (Fin 5)} (hτ : τ ≠ 1) :
    Φ (monS (C := C5) τ) ∉ Jt Φ := by
  rintro ⟨x, hx, hxe⟩
  have h1 : Φ (x⁻¹ * monS (C := C5) τ) = 1 := by
    rw [map_mul, map_inv, hxe, inv_mul_cancel]
  obtain ⟨c, hc⟩ := (hΦ _).mp h1
  have h2 : monS (C := C5) τ = x * monScalar C5 5 c := by
    rw [← hc]
    group
  have h3 : monS (C := C5) τ ∈ T5 := by
    rw [h2]
    exact T5.mul_mem hx (Sc_le_T5 ⟨c, rfl⟩)
  rw [T5_eq_ker, MonoidHom.mem_ker] at h3
  exact hτ (by simpa [monPerm_monS] using h3)

theorem monS_zpow' (a : Perm (Fin 5)) (n : ℤ) : monS (C := C5) (a ^ n) = (monS a) ^ n :=
  map_zpow (SemidirectProduct.inr : Perm (Fin 5) →* M5) a n

theorem pow_five_ddv (hΦ : KerSc Φ) : (Φ (mT ddv)) ^ 5 = 1 := by
  rw [← map_pow, mT_pow]
  have : (5 : ℕ) • ddv = 0 := by
    funext i
    rw [nsmul_ddv]
    have : ((5 : ℕ) : ZMod 5) = 0 := ZMod.natCast_self 5
    rw [this, zero_mul]
    rfl
  rw [this, mT_zero, map_one]

theorem mon_cfg (hΦ : KerSc Φ) {z : A} (hzP : z ∈ Pt Φ) (hzc : ∀ p ∈ Pt Φ, p * z = z * p)
    (hz1 : z ≠ 1)
    (hdft : ∃ w : A, w * Φ (monS (C := C5) sig5) * w⁻¹ = (Φ (mT ddv))⁻¹) :
    ∃ g h : A, KD309Cfg (Pt Φ) z (Jt Φ) (nt Φ) g h := by
  classical
  obtain ⟨k0, hk0⟩ := center_eq hΦ hzP hzc
  have hk5 := pow_five_ddv hΦ
  set k := k0 % 5 with hk
  have hzk : z = (Φ (mT ddv)) ^ k := by rw [hk0, pow_eq_pow_mod k0 hk5]
  have hklt : k < 5 := Nat.mod_lt k0 (by norm_num)
  have hk1 : 1 ≤ k := by
    by_contra h0
    have : k = 0 := by omega
    apply hz1
    rw [hzk, this, pow_zero]
  set τ : Perm (Fin 5) := sig5 ^ (-(k : ℤ)) with hτ
  have hτ1 : τ ≠ 1 := by
    intro h1
    have := (orderOf_dvd_iff_zpow_eq_one (G := Perm (Fin 5)) (x := sig5)
      (i := -(k : ℤ))).mpr h1
    rw [orderOf_sig5] at this
    omega
  set g : A := Φ (monS (C := C5) τ) with hg
  have hgP : g ∈ Pt Φ := ⟨monS τ, monS_zpow_mem_Pm _, rfl⟩
  have hgJ : g ∉ Jt Φ := monS_not_mem_Jt hΦ hτ1
  set h : A := nt Φ * g * (nt Φ)⁻¹ with hh
  have hhmem : h ∈ conjSub (nt Φ) (Pt Φ) := mem_conjSub.mpr ⟨g, hgP, rfl⟩
  have hhJ : h ∉ Jt Φ := by
    have : h = Φ (monS (C := C5) (pi5 * τ * pi5⁻¹)) := by
      simp only [hh, hg, nt, monS_mul', monS_inv, map_mul, map_inv]
    rw [this]
    refine monS_not_mem_Jt hΦ ?_
    intro h1
    apply hτ1
    have h2 : τ = pi5⁻¹ * (pi5 * τ * pi5⁻¹) * pi5 := by group
    rw [h2, h1]
    group
  refine ⟨g, h, ?_⟩
  obtain ⟨w, hw⟩ := hdft
  have hgz : g = (Φ (monS (C := C5) sig5)) ^ (-(k : ℤ)) := by
    simp only [hg, hτ, monS_zpow', map_zpow]
  have hσw : Φ (monS (C := C5) sig5) = w⁻¹ * (Φ (mT ddv))⁻¹ * w := by
    rw [← hw]
    group
  have hconj_g : IsConj z g := by
    refine isConj_iff.mpr ⟨w⁻¹, ?_⟩
    rw [hgz, hσw]
    have := conj_zpow (a := w⁻¹) (b := (Φ (mT ddv))⁻¹) (i := -(k : ℤ))
    rw [inv_inv] at this
    rw [this, hzk]
    simp [zpow_neg, inv_zpow]
  refine
    { J_le := Jt_le_Pt
      J_abel := isElemAbelian_Jt
      J_card := card_Jt hΦ
      E_card := by rw [comm_Jt_Pt, card_Et hΦ]
      z_mem := ?_
      n_J := mem_normalizer_map T5 (monS pi5)
      n_E := by
        rw [comm_Jt_Pt]
        exact mem_normalizer_map T0 (monS pi5)
      g_mem := hgP
      g_not := hgJ
      h_mem := hhmem
      h_not := hhJ
      conj_g := hconj_g
      conj_h := hconj_g.trans (isConj_iff.mpr ⟨nt Φ, rfl⟩)
      irr := ?_ }
  · rw [comm_Jt_Pt, hzk]
    exact ⟨(mT ddv) ^ k, T0.pow_mem mT_ddv_mem_T0 k, by rw [map_pow]⟩
  · intro S hS hidx F hF hinv
    rw [comm_Jt_Pt] at hF ⊢
    exact heart_irr hΦ hS hidx hF hinv

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309L
