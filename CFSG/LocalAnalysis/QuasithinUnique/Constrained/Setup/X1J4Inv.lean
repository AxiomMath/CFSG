module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Fix

public section

namespace CFSG.QuasithinUnique.Setup.X1.J4Inv

open CFSG.Quasithin

section Pm

variable {W : Type} [CommGroup W]

@[expose] def pm (φ : MulAut W) : W →* W where
  toFun w := φ w * w
  map_one' := by simp
  map_mul' a b := by
    simp only [map_mul]
    exact mul_mul_mul_comm _ _ _ _

theorem pm_apply (φ : MulAut W) (w : W) : pm φ w = φ w * w := rfl

theorem pm_eq_one_iff (hW : ∀ w : W, w * w = 1) (φ : MulAut W) (w : W) :
    pm φ w = 1 ↔ φ w = w := by
  rw [pm_apply]
  constructor
  · intro h
    rw [eq_inv_of_mul_eq_one_left h]
    exact inv_eq_of_mul_eq_one_right (hW w)
  · intro h
    rw [h]
    exact hW w

theorem pm_comm {φ X : MulAut W} (h : X * φ = φ * X) (w : W) : pm φ (X w) = X (pm φ w) := by
  have h1 : φ (X w) = X (φ w) := by
    have := congrArg (fun f : MulAut W => f w) h
    simpa [MulAut.mul_apply] using this.symm
  rw [pm_apply, pm_apply, h1, map_mul]

@[expose] def zp (φ : MulAut W) (r : ZMod 11) : MulAut W := φ ^ r.val

theorem zp_zero (φ : MulAut W) : zp φ 0 = 1 := by simp [zp]

theorem zp_one (φ : MulAut W) : zp φ 1 = φ := by
  have : (1 : ZMod 11).val = 1 := rfl
  simp [zp, this]

theorem zp_add {φ : MulAut W} (h : φ ^ 11 = 1) (a b : ZMod 11) :
    zp φ (a + b) = zp φ a * zp φ b := by
  unfold zp
  rw [ZMod.val_add, ← pow_add, ← pow_eq_pow_mod _ h]

theorem zp_pow {φ : MulAut W} (h : φ ^ 11 = 1) (r : ZMod 11) (k : ℕ) :
    (zp φ r) ^ k = zp φ (r * k) := by
  unfold zp
  rw [← pow_mul, ZMod.val_mul, ZMod.val_natCast, pow_eq_pow_mod (r.val * k) h,
    pow_eq_pow_mod (r.val * (k % 11) % 11) h]
  congr 1
  rw [Nat.mul_mod, Nat.mul_mod r.val (k % 11), Nat.mod_mod, Nat.mod_mod]

@[expose] def nm (φ : MulAut W) (w : W) : W := ∏ r : ZMod 11, zp φ r w

theorem zp_apply_map {φ : MulAut W} (h : φ ^ 11 = 1) (r : ZMod 11) (w : W) :
    zp φ r (φ w) = zp φ (r + 1) w := by
  rw [zp_add h, zp_one]
  rfl

theorem nm_pm (hW : ∀ w : W, w * w = 1) {φ : MulAut W} (h : φ ^ 11 = 1) (w : W) :
    nm φ (pm φ w) = 1 := by
  unfold nm
  simp only [pm_apply, map_mul, Finset.prod_mul_distrib]
  have e : ∏ r : ZMod 11, zp φ r (φ w) = ∏ r : ZMod 11, zp φ r w := by
    simp only [zp_apply_map h]
    exact Fintype.prod_equiv (Equiv.addRight 1) _ _ (fun _ => rfl)
  rw [e]
  exact hW _

theorem zp_fixed {φ : MulAut W} {u : W} (hu : φ u = u) (r : ZMod 11) : zp φ r u = u := by
  unfold zp
  induction r.val with
  | zero => rfl
  | succ n ih => rw [pow_succ, MulAut.mul_apply, hu, ih]

theorem nm_fixed (hW : ∀ w : W, w * w = 1) {φ : MulAut W} {u : W} (hu : φ u = u) :
    nm φ u = u := by
  unfold nm
  simp only [zp_fixed hu]
  rw [Finset.prod_const, Finset.card_univ, ZMod.card]
  have h11 : u ^ 11 = u := by
    have : u ^ 2 = 1 := by rw [sq]; exact hW u
    calc u ^ 11 = (u ^ 2) ^ 5 * u := by rw [← pow_mul, ← pow_succ]
      _ = u := by rw [this]; simp
  exact h11

theorem apply_zp {φ : MulAut W} (r : ZMod 11) (w : W) : φ (zp φ r w) = zp φ r (φ w) := by
  unfold zp
  rw [← MulAut.mul_apply, ← pow_succ', pow_succ, MulAut.mul_apply]

theorem nm_invariant {φ : MulAut W} (h : φ ^ 11 = 1) (w : W) : φ (nm φ w) = nm φ w := by
  unfold nm
  rw [map_prod]
  simp only [apply_zp, zp_apply_map h]
  exact Fintype.prod_equiv (Equiv.addRight 1) _ _ (fun _ => rfl)

theorem eq_one_of_fixed_pm (hW : ∀ w : W, w * w = 1) {φ : MulAut W} (h : φ ^ 11 = 1) (w : W)
    (hu : φ (pm φ w) = pm φ w) : pm φ w = 1 := by
  rw [← nm_fixed hW hu]
  exact nm_pm hW h w

theorem pow_stable {X : MulAut W} {S : Subgroup W} (hSX : ∀ s ∈ S, X s ∈ S) :
    ∀ (k : ℕ), ∀ s ∈ S, (X ^ k) s ∈ S := by
  intro k
  induction k with
  | zero => intro s hs; simpa using hs
  | succ k ih => intro s hs; rw [pow_succ, MulAut.mul_apply]; exact ih _ (hSX s hs)

theorem inv_pow_eq {X : MulAut W} (h : X ^ 11 = 1) {k : ℕ} (hk : k ≤ 11) :
    (X⁻¹) ^ k = X ^ (11 - k) := by
  rw [inv_pow]
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_add, Nat.add_sub_cancel' hk, h]

theorem conj_pow_apply {X T : MulAut W} (hT : T * T = 1) (hTX : T * X * T = X⁻¹) (k : ℕ)
    (w : W) : T ((X ^ k) (T w)) = ((X⁻¹) ^ k) w := by
  have hTi : T⁻¹ = T := inv_eq_of_mul_eq_one_right hT
  have h1 : (T * X * T⁻¹) ^ k = T * X ^ k * T⁻¹ := conj_pow
  rw [hTi, hTX] at h1
  have := congrArg (fun f : MulAut W => f w) h1
  simpa [MulAut.mul_apply] using this.symm

theorem nm_eq_prod_range (X : MulAut W) (s : W) :
    nm X s = (∏ r ∈ Finset.range 10, (X ^ (r + 1)) s) * s := by
  have h1 : nm X s = ∏ k ∈ Finset.range 11, (X ^ k) s :=
    Fin.prod_univ_eq_prod_range (fun k => (X ^ k) s) 11
  rw [h1, Finset.prod_range_succ']
  simp

theorem card_sq_of_inverted (hW : ∀ w : W, w * w = 1) {X T : MulAut W} (hX : X ^ 11 = 1)
    (hT : T * T = 1) (hTX : T * X * T = X⁻¹) (S : Subgroup W) (hSX : ∀ s ∈ S, X s ∈ S)
    (hST : ∀ s ∈ S, T s ∈ S) (hfpf : ∀ s ∈ S, X s = s → s = 1) :
    Nat.card S = Nat.card (S.map (pm T)) ^ 2 := by
  have hTT : ∀ w, T (T w) = w := fun w => by
    simpa [MulAut.mul_apply] using congrArg (fun f : MulAut W => f w) hT
  have hker : (pm T).ker ⊓ S = S.map (pm T) := by
    ext s
    simp only [Subgroup.mem_inf, MonoidHom.mem_ker, Subgroup.mem_map]
    constructor
    · rintro ⟨hs1, hsS⟩
      have hTs : T s = s := (pm_eq_one_iff hW T s).1 hs1
      refine ⟨∏ r ∈ Finset.range 5, (X ^ (r + 1)) s, ?_, ?_⟩
      · exact Subgroup.prod_mem _ (fun r _ => pow_stable hSX _ s hsS)
      · have hnm : nm X s = 1 := by
          apply hfpf (nm X s) (Subgroup.prod_mem _ (fun r _ => pow_stable hSX _ s hsS))
            (nm_invariant hX s)
        have hP : ∏ r ∈ Finset.range 10, (X ^ (r + 1)) s = s := by
          have h2 := nm_eq_prod_range X s
          rw [hnm] at h2
          rw [eq_inv_of_mul_eq_one_left h2.symm]
          exact inv_eq_of_mul_eq_one_right (hW s)
        have hTv : T (∏ r ∈ Finset.range 5, (X ^ (r + 1)) s) =
            ∏ r ∈ Finset.range 5, ((X⁻¹) ^ (r + 1)) s := by
          rw [map_prod]
          refine Finset.prod_congr rfl (fun r _ => ?_)
          have := conj_pow_apply hT hTX (r + 1) s
          rw [hTs] at this
          exact this
        have e1 : ∏ r ∈ Finset.range 5, ((X⁻¹) ^ (r + 1)) s =
            ∏ r ∈ Finset.range 5, (X ^ (10 - r)) s := by
          refine Finset.prod_congr rfl (fun r hr => ?_)
          have hr5 : r < 5 := Finset.mem_range.1 hr
          rw [inv_pow_eq hX (by omega : r + 1 ≤ 11)]
          congr 2
          omega
        have key : (∏ r ∈ Finset.range 5, (X ^ (10 - r)) s) *
            (∏ r ∈ Finset.range 5, (X ^ (r + 1)) s) =
            ∏ r ∈ Finset.range 10, (X ^ (r + 1)) s := by
          simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
          norm_num
          ac_rfl
        rw [pm_apply, hTv, e1, key, hP]
    · rintro ⟨v, hv, rfl⟩
      refine ⟨?_, S.mul_mem (hST v hv) hv⟩
      show pm T (pm T v) = 1
      rw [pm_apply, pm_apply, map_mul, hTT]
      calc v * T v * (T v * v) = (v * v) * (T v * T v) := by ac_rfl
        _ = 1 := by rw [hW v, hW (T v), one_mul]
  have h1 := Subgroup.relIndex_mul_card (H := (pm T).ker) (K := S)
  rw [Subgroup.relIndex_ker, hker] at h1
  rw [← h1, sq]

end Pm

section F

variable {W : Type} [CommGroup W]

theorem card_modEq_one [Finite W] {φ : MulAut W} (h : φ ^ 11 = 1) (S : Subgroup W)
    (hS : ∀ s ∈ S, φ s ∈ S) (hfpf : ∀ s ∈ S, φ s = s → s = 1) : Nat.card S ≡ 1 [MOD 11] := by
  classical
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have : Fintype W := Fintype.ofFinite W
  let f : Function.End S := fun s => ⟨φ s, hS s s.2⟩
  have hpow : ∀ k : ℕ, ∀ s : S, ((f ^ k) s : W) = (φ ^ k) s := by
    intro k
    induction k with
    | zero => intro s; rfl
    | succ k ih =>
      intro s
      rw [pow_succ, pow_succ, MulAut.mul_apply]
      exact ih (f s)
  have hf : f ^ 11 ^ 1 = 1 := by
    funext s
    apply Subtype.ext
    rw [pow_one, hpow, h]
    rfl
  have h1 := Equiv.Perm.card_fixedPoints_modEq (p := 11) (n := 1) hf
  have h2 : Fintype.card (Function.fixedPoints f) = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨1, ?_⟩, ?_⟩
    · apply Subtype.ext; simp [f]
    · rintro ⟨s, hs⟩
      apply Subtype.ext
      apply Subtype.ext
      apply hfpf s s.2
      have := congrArg Subtype.val hs
      simpa [f] using this
  rw [h2] at h1
  simpa [Nat.card_eq_fintype_card] using h1

end F

section Heis

variable {W : Type} [CommGroup W]

@[expose] def Bz (Zm X : MulAut W) (i : ZMod 11) : MulAut W := zp Zm i * X

theorem commute_zp_left {Zm X : MulAut W} (h : X * Zm = Zm * X) (i : ZMod 11) :
    Commute (zp Zm i) X := by
  have hc : Commute Zm X := h.symm
  exact hc.pow_left _

theorem Bz_apply (Zm X : MulAut W) (i : ZMod 11) (w : W) : Bz Zm X i w = zp Zm i (X w) := rfl

theorem Bz_pow {Zm X : MulAut W} (hZ : Zm ^ 11 = 1) (hXZ : X * Zm = Zm * X) (i : ZMod 11)
    (k : ℕ) : (Bz Zm X i) ^ k = zp Zm (i * k) * X ^ k := by
  rw [Bz, (commute_zp_left hXZ i).mul_pow, zp_pow hZ]

theorem Bz_pow_eleven {Zm X : MulAut W} (hX : X ^ 11 = 1) (hZ : Zm ^ 11 = 1)
    (hXZ : X * Zm = Zm * X) (i : ZMod 11) : (Bz Zm X i) ^ 11 = 1 := by
  rw [Bz_pow hZ hXZ, hX]
  have : ((11 : ℕ) : ZMod 11) = 0 := ZMod.natCast_self 11
  rw [this, mul_zero, zp_zero, one_mul]

theorem apply_zp_comm {Zm X : MulAut W} (h : X * Zm = Zm * X) (r : ZMod 11) (w : W) :
    X (zp Zm r w) = zp Zm r (X w) := by
  have := (commute_zp_left h r).symm
  have h2 := congrArg (fun f : MulAut W => f w) (this : X * zp Zm r = zp Zm r * X)
  simpa [MulAut.mul_apply] using h2

theorem X_pow_apply_of_fixed {Zm X : MulAut W} (hZ : Zm ^ 11 = 1) (hXZ : X * Zm = Zm * X)
    {i : ZMod 11} {u : W} (hu : Bz Zm X i u = u) (k : ℕ) :
    (X ^ k) u = zp Zm (-i * k) u := by
  have hXu : X u = zp Zm (-i) u := by
    have h1 : zp Zm i (X u) = u := hu
    calc X u = (zp Zm (-i) * zp Zm i) (X u) := by
          rw [← zp_add hZ, neg_add_cancel, zp_zero]; rfl
      _ = zp Zm (-i) u := by rw [MulAut.mul_apply, h1]
  induction k with
  | zero => simp [zp_zero]
  | succ k ih =>
    rw [pow_succ', MulAut.mul_apply, ih, apply_zp_comm hXZ, hXu, ← MulAut.mul_apply,
      ← zp_add hZ]
    congr 2
    push_cast
    ring

end Heis

section Heis2

variable {W : Type} [CommGroup W]

local instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩

theorem nm_mul (φ : MulAut W) (a b : W) : nm φ (a * b) = nm φ a * nm φ b := by
  unfold nm
  simp [map_mul, Finset.prod_mul_distrib]

theorem nm_one (φ : MulAut W) : nm φ 1 = 1 := by simp [nm]

theorem nm_Bz_ne {Zm X : MulAut W} (hZ : Zm ^ 11 = 1) (hXZ : X * Zm = Zm * X)
    {i j : ZMod 11} (hij : i ≠ j) {u : W} (hu : Bz Zm X j u = u) (hnm : nm Zm u = 1) :
    nm (Bz Zm X i) u = 1 := by
  unfold nm
  have h1 : ∀ r : ZMod 11, zp (Bz Zm X i) r u = zp Zm ((i - j) * r) u := by
    intro r
    show ((Bz Zm X i) ^ r.val) u = _
    rw [Bz_pow hZ hXZ i r.val, MulAut.mul_apply, X_pow_apply_of_fixed hZ hXZ hu,
      ← MulAut.mul_apply, ← zp_add hZ, ZMod.natCast_zmod_val]
    congr 2
    ring
  simp only [h1]
  have hd : i - j ≠ 0 := sub_ne_zero.2 hij
  calc ∏ r : ZMod 11, zp Zm ((i - j) * r) u = ∏ r : ZMod 11, zp Zm r u :=
        Fintype.prod_equiv (Equiv.mulLeft₀ (i - j) hd) _ _ (fun _ => rfl)
    _ = 1 := hnm

theorem prod_nm_Bz (hW : ∀ w : W, w * w = 1) {Zm X : MulAut W} (hZ : Zm ^ 11 = 1)
    (hXZ : X * Zm = Zm * X) (S : Subgroup W) (hSX : ∀ s ∈ S, X s ∈ S)
    (hnmS : ∀ s ∈ S, nm Zm s = 1) {w : W} (hw : w ∈ S) :
    ∏ i : ZMod 11, nm (Bz Zm X i) w = w := by
  have h1 : ∀ i k : ZMod 11, zp (Bz Zm X i) k w = zp Zm (i * k) ((X ^ k.val) w) := by
    intro i k
    show ((Bz Zm X i) ^ k.val) w = _
    rw [Bz_pow hZ hXZ i k.val, MulAut.mul_apply, ZMod.natCast_zmod_val]
  unfold nm
  simp only [h1]
  rw [Finset.prod_comm]
  rw [Finset.prod_eq_single (0 : ZMod 11)]
  · simp only [mul_zero, zp_zero]
    show ∏ i : ZMod 11, ((1 : MulAut W) ((X ^ (0 : ZMod 11).val) w)) = w
    simp only [ZMod.val_zero, pow_zero]
    rw [Finset.prod_const, Finset.card_univ, ZMod.card]
    have : w ^ 2 = 1 := by rw [sq]; exact hW w
    calc ((1 : MulAut W) w) ^ 11 = w ^ 11 := rfl
      _ = (w ^ 2) ^ 5 * w := by rw [← pow_mul, ← pow_succ]
      _ = w := by rw [this]; simp
  · intro k _ hk
    have hmem : (X ^ k.val) w ∈ S := pow_stable hSX _ w hw
    have hk' := hnmS _ hmem
    calc ∏ i : ZMod 11, zp Zm (i * k) ((X ^ k.val) w) = ∏ i : ZMod 11, zp Zm i ((X ^ k.val) w) :=
          Fintype.prod_equiv (Equiv.mulRight₀ k hk) _ _ (fun _ => rfl)
      _ = 1 := hk'
  · intro h
    exact absurd (Finset.mem_univ _) h

end Heis2

section Heis3

variable {W : Type} [CommGroup W]

local instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩

@[expose] def Cfix (Zm X : MulAut W) (S : Subgroup W) (i : ZMod 11) : Subgroup W where
  carrier := {u | u ∈ S ∧ Bz Zm X i u = u}
  one_mem' := ⟨S.one_mem, map_one _⟩
  mul_mem' := fun ha hb => ⟨S.mul_mem ha.1 hb.1, by rw [map_mul, ha.2, hb.2]⟩
  inv_mem' := fun ha => ⟨S.inv_mem ha.1, by rw [map_inv, ha.2]⟩

theorem mem_Cfix {Zm X : MulAut W} {S : Subgroup W} {i : ZMod 11} {u : W} :
    u ∈ Cfix Zm X S i ↔ u ∈ S ∧ Bz Zm X i u = u := Iff.rfl

@[expose] def nmH (φ : MulAut W) : W →* W where
  toFun := nm φ
  map_one' := nm_one φ
  map_mul' := nm_mul φ

theorem nm_prod (φ : MulAut W) (s : Finset (ZMod 11)) (f : ZMod 11 → W) :
    nm φ (∏ i ∈ s, f i) = ∏ i ∈ s, nm φ (f i) := map_prod (nmH φ) f s

theorem Cfix_indep (hW : ∀ w : W, w * w = 1) {Zm X : MulAut W} (hZ : Zm ^ 11 = 1)
    (hXZ : X * Zm = Zm * X) (S : Subgroup W) (hnmS : ∀ s ∈ S, nm Zm s = 1)
    (f : ZMod 11 → W) (hf : ∀ i, f i ∈ Cfix Zm X S i) (hprod : ∏ i, f i = 1) (i₀ : ZMod 11) :
    f i₀ = 1 := by
  have h1 : nm (Bz Zm X i₀) (∏ i, f i) = ∏ i, nm (Bz Zm X i₀) (f i) := nm_prod _ _ _
  rw [hprod, nm_one] at h1
  rw [Finset.prod_eq_single i₀] at h1
  · rw [nm_fixed hW (hf i₀).2] at h1
    exact h1.symm
  · intro i _ hi
    exact nm_Bz_ne hZ hXZ (Ne.symm hi) (hf i).2 (hnmS _ (hf i).1)
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem prod_card_Cfix_le [Finite W] (hW : ∀ w : W, w * w = 1) {Zm X : MulAut W}
    (hZ : Zm ^ 11 = 1) (hXZ : X * Zm = Zm * X) (S : Subgroup W)
    (hnmS : ∀ s ∈ S, nm Zm s = 1) :
    ∏ i : ZMod 11, Nat.card (Cfix Zm X S i) ≤ Nat.card S := by
  classical
  let Φ : (∀ i : ZMod 11, ↥(Cfix Zm X S i)) →* ↥S :=
    { toFun := fun f => ⟨∏ i, ((f i : Cfix Zm X S i) : W),
        Subgroup.prod_mem _ (fun i _ => (f i).2.1)⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun f g => by
        apply Subtype.ext
        simp [Finset.prod_mul_distrib] }
  have hΦ : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro f hf
    funext i₀
    apply Subtype.ext
    have hprod : ∏ i, ((f i : Cfix Zm X S i) : W) = 1 := congrArg Subtype.val hf
    have h1 := Cfix_indep hW hZ hXZ S hnmS (fun i => ((f i : Cfix Zm X S i) : W))
      (fun i => (f i).2) hprod i₀
    exact h1
  have := Nat.card_le_card_of_injective _ hΦ
  rwa [Nat.card_pi] at this

end Heis3

section Heis4

variable {W : Type} [CommGroup W]

local instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩

theorem Bz_conj_Y {Zm X Y : MulAut W} (hZ : Zm ^ 11 = 1) (hYZ : Y * Zm = Zm * Y)
    (hYX : Y⁻¹ * X * Y = Zm * X) (i : ZMod 11) :
    Y⁻¹ * Bz Zm X i * Y = Bz Zm X (i + 1) := by
  have hc : Commute Y (zp Zm i) := (show Commute Y Zm from hYZ).pow_right _
  have h1 : Y⁻¹ * zp Zm i * Y = zp Zm i := by
    calc Y⁻¹ * zp Zm i * Y = zp Zm i * Y⁻¹ * Y := by rw [hc.inv_left.eq]
      _ = zp Zm i := by group
  calc Y⁻¹ * Bz Zm X i * Y = (Y⁻¹ * zp Zm i * Y) * (Y⁻¹ * X * Y) := by unfold Bz; group
    _ = zp Zm i * (Zm * X) := by rw [h1, hYX]
    _ = Bz Zm X (i + 1) := by rw [Bz, zp_add hZ, zp_one, mul_assoc]

theorem card_Cfix_succ [Finite W] {Zm X Y : MulAut W} (hZ : Zm ^ 11 = 1)
    (hYZ : Y * Zm = Zm * Y) (hYX : Y⁻¹ * X * Y = Zm * X) (S : Subgroup W)
    (hSY : ∀ s ∈ S, Y s ∈ S) (hSYi : ∀ s ∈ S, Y⁻¹ s ∈ S) (i : ZMod 11) :
    Nat.card (Cfix Zm X S (i + 1)) = Nat.card (Cfix Zm X S i) := by
  have hB := Bz_conj_Y hZ hYZ hYX i
  have h1 : Bz Zm X (i + 1) * Y⁻¹ = Y⁻¹ * Bz Zm X i := by rw [← hB]; group
  have h2 : Bz Zm X i * Y = Y * Bz Zm X (i + 1) := by rw [← hB]; group
  apply le_antisymm
  · let f : Cfix Zm X S (i + 1) → Cfix Zm X S i := fun v =>
      ⟨Y v, hSY v v.2.1, by
        have := congrArg (fun a : MulAut W => a v) h2
        simp only [MulAut.mul_apply] at this
        rw [this, v.2.2]⟩
    refine Nat.card_le_card_of_injective f (fun v v' h => ?_)
    apply Subtype.ext
    exact Y.injective (congrArg Subtype.val h)
  · let g : Cfix Zm X S i → Cfix Zm X S (i + 1) := fun u =>
      ⟨Y⁻¹ u, hSYi u u.2.1, by
        have := congrArg (fun a : MulAut W => a u) h1
        simp only [MulAut.mul_apply] at this
        rw [this, u.2.2]⟩
    refine Nat.card_le_card_of_injective g (fun u u' h => ?_)
    apply Subtype.ext
    exact Y⁻¹.injective (congrArg Subtype.val h)

theorem card_Cfix_eq [Finite W] {Zm X Y : MulAut W} (hZ : Zm ^ 11 = 1)
    (hYZ : Y * Zm = Zm * Y) (hYX : Y⁻¹ * X * Y = Zm * X) (S : Subgroup W)
    (hSY : ∀ s ∈ S, Y s ∈ S) (hSYi : ∀ s ∈ S, Y⁻¹ s ∈ S) (i : ZMod 11) :
    Nat.card (Cfix Zm X S i) = Nat.card (Cfix Zm X S 0) := by
  have h : ∀ n : ℕ, Nat.card (Cfix Zm X S (n : ZMod 11)) = Nat.card (Cfix Zm X S 0) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.cast_succ, card_Cfix_succ hZ hYZ hYX S hSY hSYi, ih]
  have := h i.val
  rwa [ZMod.natCast_zmod_val] at this

end Heis4

section Heis5

variable {W : Type} [CommGroup W]

local instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩

theorem X_Zm_apply {Zm X : MulAut W} (h : X * Zm = Zm * X) (u : W) : X (Zm u) = Zm (X u) := by
  have := congrArg (fun a : MulAut W => a u) h
  simpa [MulAut.mul_apply] using this

theorem nm_mem {φ : MulAut W} {S : Subgroup W} (hS : ∀ s ∈ S, φ s ∈ S) {w : W} (hw : w ∈ S) :
    nm φ w ∈ S :=
  Subgroup.prod_mem _ (fun r _ => pow_stable hS r.val w hw)

theorem Cfix_zero_ge [Finite W] (hW : ∀ w : W, w * w = 1) {Zm X Y : MulAut W}
    (hX : X ^ 11 = 1) (hZ : Zm ^ 11 = 1) (hXZ : X * Zm = Zm * X) (hYZ : Y * Zm = Zm * Y)
    (hYX : Y⁻¹ * X * Y = Zm * X) (S : Subgroup W) (hSX : ∀ s ∈ S, X s ∈ S)
    (hSZ : ∀ s ∈ S, Zm s ∈ S) (hSY : ∀ s ∈ S, Y s ∈ S) (hSYi : ∀ s ∈ S, Y⁻¹ s ∈ S)
    (hnmS : ∀ s ∈ S, nm Zm s = 1) (hSne : S ≠ ⊥) :
    2 ^ 10 ≤ Nat.card (Cfix Zm X S 0) := by
  have hpos : 0 < Nat.card (Cfix Zm X S 0) := Nat.card_pos
  have hBz : ∀ (i : ZMod 11), ∀ s ∈ S, Bz Zm X i s ∈ S := fun i s hs =>
    pow_stable hSZ i.val _ (hSX s hs)
  have hne : Nat.card (Cfix Zm X S 0) ≠ 1 := by
    intro h1
    apply hSne
    rw [eq_bot_iff]
    intro w hw
    have hall : ∀ i, Cfix Zm X S i = ⊥ := fun i =>
      Subgroup.eq_bot_of_card_eq _ (by rw [card_Cfix_eq hZ hYZ hYX S hSY hSYi i, h1])
    have hspan := prod_nm_Bz hW hZ hXZ S hSX hnmS hw
    have hone : ∀ i, nm (Bz Zm X i) w = 1 := by
      intro i
      have hmem : nm (Bz Zm X i) w ∈ Cfix Zm X S i :=
        ⟨nm_mem (hBz i) hw, nm_invariant (Bz_pow_eleven hX hZ hXZ i) w⟩
      rw [hall i] at hmem
      exact Subgroup.mem_bot.1 hmem
    rw [← hspan]
    simp [hone]
  have hstable : ∀ u ∈ Cfix Zm X S 0, Zm u ∈ Cfix Zm X S 0 := by
    intro u hu
    refine ⟨hSZ u hu.1, ?_⟩
    have hXu : X u = u := by
      have := hu.2
      rwa [Bz_apply, zp_zero, MulAut.one_apply] at this
    rw [Bz_apply, zp_zero, MulAut.one_apply, X_Zm_apply hXZ, hXu]
  have hfpf : ∀ u ∈ Cfix Zm X S 0, Zm u = u → u = 1 := by
    intro u hu h
    rw [← nm_fixed hW h]
    exact hnmS u hu.1
  have hmod := card_modEq_one hZ (Cfix Zm X S 0) hstable hfpf
  have hp : IsPGroup 2 (Cfix Zm X S 0) := fun x => ⟨1, by
    rw [pow_one, sq]
    exact Subtype.ext (hW x)⟩
  obtain ⟨e, he⟩ := (IsPGroup.iff_card (p := 2)).1 hp
  rw [he] at hmod hne ⊢
  have he1 : e ≠ 0 := fun h => hne (by rw [h]; rfl)
  have h2e : (2 : ZMod 11) ^ e = 1 := by
    have := (ZMod.natCast_eq_natCast_iff _ _ 11).2 hmod
    simpa using this
  have hord : orderOf (2 : ZMod 11) ∣ e := orderOf_dvd_of_pow_eq_one h2e
  rw [orderOf_two_zmod_11] at hord
  exact Nat.pow_le_pow_right (by norm_num) (Nat.le_of_dvd (Nat.pos_of_ne_zero he1) hord)

end Heis5

section Heis6

variable {W : Type} [CommGroup W]

local instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩

theorem card_S_eq_map_mul [Finite W] (hW : ∀ w : W, w * w = 1) (Zm X : MulAut W)
    (S : Subgroup W) :
    Nat.card S = Nat.card (S.map (pm X)) * Nat.card (Cfix Zm X S 0) := by
  have h1 := Subgroup.relIndex_mul_card (H := (pm X).ker) (K := S)
  rw [Subgroup.relIndex_ker] at h1
  have h2 : (pm X).ker ⊓ S = Cfix Zm X S 0 := by
    ext u
    rw [Subgroup.mem_inf, MonoidHom.mem_ker, mem_Cfix, Bz_apply, zp_zero, MulAut.one_apply,
      pm_eq_one_iff hW]
    exact and_comm
  rw [h2] at h1
  exact h1.symm

theorem fixV_zpowers_eq_ker (hW : ∀ w : W, w * w = 1) (T : MulAut W) :
    fixV (Subgroup.zpowers T) = (pm T).ker := by
  ext w
  rw [mem_fixV_zpowers, MonoidHom.mem_ker, pm_eq_one_iff hW]

theorem two_pow_hundred_le_index_sq [Finite W] (hW : ∀ w : W, w * w = 1) {X Y Zm T : MulAut W}
    (hX : X ^ 11 = 1) (hZ : Zm ^ 11 = 1) (hZ1 : Zm ≠ 1) (hXZ : X * Zm = Zm * X)
    (hYZ : Y * Zm = Zm * Y) (hYX : Y⁻¹ * X * Y = Zm * X) (hT : T * T = 1)
    (hTX : T * X * T = X⁻¹) (hTZ : T * Zm = Zm * T) :
    2 ^ 100 ≤ (fixV (Subgroup.zpowers T)).index ^ 2 := by
  let S : Subgroup W := (pm Zm).range
  have hSX : ∀ s ∈ S, X s ∈ S := by
    rintro _ ⟨w, rfl⟩
    exact ⟨X w, pm_comm hXZ w⟩
  have hSZ : ∀ s ∈ S, Zm s ∈ S := by
    rintro _ ⟨w, rfl⟩
    exact ⟨Zm w, pm_comm (show Zm * Zm = Zm * Zm from rfl) w⟩
  have hSY : ∀ s ∈ S, Y s ∈ S := by
    rintro _ ⟨w, rfl⟩
    exact ⟨Y w, pm_comm hYZ w⟩
  have hSYi : ∀ s ∈ S, Y⁻¹ s ∈ S := by
    rintro _ ⟨w, rfl⟩
    exact ⟨Y⁻¹ w, pm_comm (show Commute Y Zm from hYZ).inv_left.eq w⟩
  have hSne : S ≠ ⊥ := by
    intro hbot
    apply hZ1
    ext w
    have : pm Zm w ∈ S := ⟨w, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    simpa using (pm_eq_one_iff hW Zm w).1 this
  have hnmS : ∀ s ∈ S, nm Zm s = 1 := by
    rintro _ ⟨w, rfl⟩
    exact nm_pm hW hZ w
  have hc := Cfix_zero_ge hW hX hZ hXZ hYZ hYX S hSX hSZ hSY hSYi hnmS hSne
  have hS11 : Nat.card (Cfix Zm X S 0) ^ 11 ≤ Nat.card S := by
    have h := prod_card_Cfix_le hW hZ hXZ S hnmS
    have h2 : ∏ i : ZMod 11, Nat.card (Cfix Zm X S i) = Nat.card (Cfix Zm X S 0) ^ 11 := by
      rw [Finset.prod_congr rfl (fun i _ => card_Cfix_eq hZ hYZ hYX S hSY hSYi i),
        Finset.prod_const, Finset.card_univ, ZMod.card]
    rwa [h2] at h
  let M : Subgroup W := S.map (pm X)
  have hSM := card_S_eq_map_mul hW Zm X S
  have hcpos : 0 < Nat.card (Cfix Zm X S 0) := Nat.card_pos
  have hM10 : Nat.card (Cfix Zm X S 0) ^ 10 ≤ Nat.card M := by
    have : Nat.card (Cfix Zm X S 0) ^ 10 * Nat.card (Cfix Zm X S 0) ≤
        Nat.card M * Nat.card (Cfix Zm X S 0) := by
      calc Nat.card (Cfix Zm X S 0) ^ 10 * Nat.card (Cfix Zm X S 0)
          = Nat.card (Cfix Zm X S 0) ^ 11 := (pow_succ _ 10).symm
        _ ≤ Nat.card S := hS11
        _ = Nat.card M * Nat.card (Cfix Zm X S 0) := hSM
    exact Nat.le_of_mul_le_mul_right this hcpos
  have hMX : ∀ m ∈ M, X m ∈ M := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨X w, hSX w hw, pm_comm (show X * X = X * X from rfl) w⟩
  have hXi : X⁻¹ = X ^ 10 := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ', hX]
  have hMT : ∀ m ∈ M, T m ∈ M := by
    rintro _ ⟨w, hw, rfl⟩
    have hTSw : T w ∈ S := by
      obtain ⟨v, rfl⟩ := hw
      exact ⟨T v, pm_comm hTZ v⟩
    have hTT : ∀ v, T (T v) = v := fun v => by
      simpa [MulAut.mul_apply] using congrArg (fun f : MulAut W => f v) hT
    have h1 : T (X w) = X⁻¹ (T w) := by
      have := congrArg (fun f : MulAut W => f (T w)) hTX
      simpa [MulAut.mul_apply, hTT] using this
    have h2 : T (pm X w) = X⁻¹ (pm X (T w)) := by
      rw [pm_apply, pm_apply, map_mul, h1, map_mul, MulAut.inv_apply_self W X (T w)]
      exact mul_comm _ _
    rw [h2, hXi]
    exact pow_stable hMX 10 _ ⟨T w, hTSw, rfl⟩
  have hMfpf : ∀ m ∈ M, X m = m → m = 1 := by
    rintro _ ⟨w, hw, rfl⟩ hfix
    exact eq_one_of_fixed_pm hW hX w hfix
  have hsq := card_sq_of_inverted hW hX hT hTX M hMX hMT hMfpf
  have hle : Nat.card (M.map (pm T)) ≤ (fixV (Subgroup.zpowers T)).index := by
    rw [fixV_zpowers_eq_ker hW, Subgroup.index_ker]
    exact Nat.card_le_card_of_injective (Subgroup.inclusion (fun x hx => by
      obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨y, rfl⟩)) (Subgroup.inclusion_injective _)
  calc 2 ^ 100 = (2 ^ 10) ^ 10 := by norm_num
    _ ≤ Nat.card (Cfix Zm X S 0) ^ 10 := Nat.pow_le_pow_left hc 10
    _ ≤ Nat.card M := hM10
    _ = Nat.card (M.map (pm T)) ^ 2 := hsq
    _ ≤ (fixV (Subgroup.zpowers T)).index ^ 2 := Nat.pow_le_pow_left hle 2

end Heis6


section Cyclic

variable {W : Type} [CommGroup W] [Finite W]

theorem two_pow_le_index_sq_of_dihedral_prime (hW : ∀ w : W, w * w = 1) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {t k : MulAut W} (hord : orderOf (t * (k * t * k⁻¹)) = p) :
    2 ^ orderOf (2 : ZMod p) ≤ (fixV (Subgroup.zpowers t)).index ^ 2 := by
  have h1 := two_pow_orderOf_le_index_fixV hW hp2 hord
  have h2 := index_fixV_mul_le t (k * t * k⁻¹)
  rw [index_fixV_conj k t] at h2
  calc 2 ^ orderOf (2 : ZMod p) ≤ _ := h1
    _ ≤ _ := h2
    _ = _ := (sq _).symm

theorem two_pow_eighteen_le_index_of_dihedral_37 (hW : ∀ w : W, w * w = 1) {t k : MulAut W}
    (hord : orderOf (t * (k * t * k⁻¹)) = 37) :
    2 ^ 18 ≤ (fixV (Subgroup.zpowers t)).index := by
  have : Fact (Nat.Prime 37) := ⟨by norm_num⟩
  have h := two_pow_le_index_sq_of_dihedral_prime hW (by norm_num : (37 : ℕ) ≠ 2) hord
  rw [orderOf_two_zmod_37] at h
  by_contra hlt
  push Not at hlt
  have : (fixV (Subgroup.zpowers t)).index ^ 2 < (2 ^ 18) ^ 2 := Nat.pow_lt_pow_left hlt (by norm_num)
  have h36 : (2 : ℕ) ^ 36 = (2 ^ 18) ^ 2 := by norm_num
  omega

end Cyclic

end CFSG.QuasithinUnique.Setup.X1.J4Inv
