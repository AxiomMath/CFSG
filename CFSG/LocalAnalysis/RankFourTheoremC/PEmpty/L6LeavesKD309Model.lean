module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD309Linear
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309

open Subgroup

abbrev K16 : Type := GaloisField 2 4

theorem card_K16 : Nat.card K16 = 16 := by
  rw [GaloisField.card 2 4 (by norm_num)]
  norm_num

theorem finrank_K16 : Module.finrank (ZMod 2) K16 = 4 :=
  GaloisField.finrank 2 (by norm_num)

theorem exists_zeta : ∃ ζ : K16, orderOf ζ = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h : 5 ∣ Nat.card K16ˣ := by
    rw [Nat.card_units, card_K16]
    norm_num
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 5 h
  exact ⟨(u : K16), by rw [orderOf_units]; exact hu⟩

noncomputable def zeta : K16 := Classical.choose exists_zeta

theorem orderOf_zeta : orderOf zeta = 5 := Classical.choose_spec exists_zeta

theorem zeta_pow_five : zeta ^ 5 = 1 := by
  rw [← orderOf_zeta]
  exact pow_orderOf_eq_one _

@[expose] noncomputable def chi (k : ZMod 5) : K16 := zeta ^ k.val

theorem chi_add (a b : ZMod 5) : chi (a + b) = chi a * chi b := by
  unfold chi
  rw [ZMod.val_add, ← pow_add, ← pow_eq_pow_mod _ zeta_pow_five]

theorem chi_zero : chi 0 = 1 := by
  simp [chi]

theorem chi_ne_one {k : ZMod 5} (hk : k ≠ 0) : chi k ≠ 1 := by
  intro h
  have h1 : 5 ∣ k.val := by
    have := orderOf_dvd_of_pow_eq_one h
    rwa [orderOf_zeta] at this
  have h2 : k.val < 5 := ZMod.val_lt k
  have h3 : k.val = 0 := by omega
  exact hk ((ZMod.val_eq_zero k).mp h3)

theorem chi_eq_one_iff (a : ZMod 5) : chi a = 1 ↔ a = 0 :=
  ⟨fun h => by_contra fun h' => chi_ne_one h' h, fun h => h ▸ chi_zero⟩

theorem chi_ne_zero (a : ZMod 5) : chi a ≠ 0 := by
  unfold chi
  exact pow_ne_zero _ (by
    intro h
    have := zeta_pow_five
    rw [h] at this
    simp at this)

@[ext] structure Wr where
  a : ZMod 5 → ZMod 5
  c : ZMod 5

namespace Wr

instance : Mul Wr := ⟨fun x y => ⟨fun i => x.a i + y.a (i - x.c), x.c + y.c⟩⟩

instance : One Wr := ⟨⟨0, 0⟩⟩

instance : Inv Wr := ⟨fun x => ⟨fun i => - x.a (i + x.c), - x.c⟩⟩

@[simp] theorem mul_a (x y : Wr) (i : ZMod 5) : (x * y).a i = x.a i + y.a (i - x.c) := rfl

@[simp] theorem mul_c (x y : Wr) : (x * y).c = x.c + y.c := rfl

@[simp] theorem one_a (i : ZMod 5) : (1 : Wr).a i = 0 := rfl

@[simp] theorem one_c : (1 : Wr).c = 0 := rfl

@[simp] theorem inv_a (x : Wr) (i : ZMod 5) : (x⁻¹).a i = - x.a (i + x.c) := rfl

@[simp] theorem inv_c (x : Wr) : (x⁻¹).c = - x.c := rfl

instance : Group Wr where
  mul_assoc x y z := by
    ext i
    · simp only [mul_a, mul_c]
      rw [add_assoc]
      congr 2
      · congr 1; ring
    · simp [add_assoc]
  one_mul x := by
    ext i
    · simp
    · simp
  mul_one x := by
    ext i
    · simp
    · simp
  inv_mul_cancel x := by
    ext i
    · simp
    · simp

end Wr

instance : Finite Wr :=
  Finite.of_injective (fun w : Wr => (w.a, w.c)) (fun x y h => Wr.ext (congrArg Prod.fst h)
    (congrArg Prod.snd h))

theorem card_Wr : Nat.card Wr = 5 ^ 6 := by
  have e : Wr ≃ (ZMod 5 → ZMod 5) × ZMod 5 :=
    { toFun := fun x => (x.a, x.c)
      invFun := fun p => ⟨p.1, p.2⟩
      left_inv := fun x => rfl
      right_inv := fun p => rfl }
  rw [Nat.card_congr e, Nat.card_prod]
  simp [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card]

theorem isPGroup_Wr : IsPGroup 5 Wr := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact IsPGroup.of_card card_Wr


abbrev UU : Type := ZMod 5 → K16

theorem finrank_UU : Module.finrank (ZMod 2) UU = 20 := by
  rw [Module.finrank_pi_fintype]
  simp [finrank_K16]

@[expose] noncomputable def Tlin (w : Wr) : UU →ₗ[ZMod 2] UU where
  toFun v := fun i => chi (w.a i) * v (i - w.c)
  map_add' u v := by
    ext i
    simp [mul_add]
  map_smul' r v := by
    ext i
    simp [mul_smul_comm]

theorem Tlin_apply (w : Wr) (v : UU) (i : ZMod 5) :
    Tlin w v i = chi (w.a i) * v (i - w.c) := rfl

theorem Tlin_mul (x y : Wr) : Tlin (x * y) = Tlin x * Tlin y := by
  refine LinearMap.ext fun v => funext fun i => ?_
  simp only [Module.End.mul_apply, Tlin_apply, Wr.mul_a, Wr.mul_c, chi_add]
  rw [mul_assoc, sub_sub]

theorem Tlin_one : Tlin 1 = 1 := by
  refine LinearMap.ext fun v => funext fun i => ?_
  rw [Tlin_apply, Module.End.one_apply]
  simp [chi_zero]

@[expose] noncomputable def T : Representation (ZMod 2) Wr UU where
  toFun := Tlin
  map_one' := Tlin_one
  map_mul' := Tlin_mul

theorem T_apply (w : Wr) (v : UU) (i : ZMod 5) : T w v i = chi (w.a i) * v (i - w.c) := rfl

theorem T_injective : Function.Injective T := by
  rw [injective_iff_map_eq_one]
  intro w hw
  have h : ∀ (v : UU) (i : ZMod 5), chi (w.a i) * v (i - w.c) = v i := fun v i => by
    have := LinearMap.congr_fun hw v
    exact congrFun this i
  have hc : w.c = 0 := by
    by_contra hc
    have h1 := h (Pi.single 0 1) w.c
    rw [sub_self, Pi.single_eq_same, Pi.single_eq_of_ne hc] at h1
    exact chi_ne_zero _ (by simpa using h1)
  refine Wr.ext (funext fun i => ?_) hc
  have h1 := h (Pi.single i 1) i
  rw [hc, sub_zero, Pi.single_eq_same, mul_one] at h1
  exact (chi_eq_one_iff _).mp h1

@[expose] noncomputable def Trep : Wr →* (UU ≃ₗ[ZMod 2] UU) := repEquiv T

theorem Trep_injective : Function.Injective Trep := by
  intro x y h
  apply T_injective
  refine LinearMap.ext fun v => ?_
  exact LinearEquiv.congr_fun h v

theorem finrank_ker_le_four {w : Wr} (hc : w.c ≠ 0) :
    Module.finrank (ZMod 2) (LinearMap.ker (T w - 1)) ≤ 4 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let f : LinearMap.ker (T w - 1) →ₗ[ZMod 2] K16 :=
    (LinearMap.proj (R := ZMod 2) (φ := fun _ : ZMod 5 => K16) 0).comp
      (LinearMap.ker (T w - 1)).subtype
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have hv0 : (v : UU) 0 = 0 := hv
    have hker : ∀ i, (v : UU) i = chi (w.a i) * (v : UU) (i - w.c) := by
      intro i
      have h1 := LinearMap.mem_ker.mp v.2
      have h2 := congrFun h1 i
      simp only [LinearMap.sub_apply, Module.End.one_apply, Pi.sub_apply, Pi.zero_apply,
        T_apply, sub_eq_zero] at h2
      exact h2.symm
    have hk : ∀ k : ℕ, (v : UU) ((k : ZMod 5) * w.c) = 0 := by
      intro k
      induction k with
      | zero => simpa using hv0
      | succ k ih =>
        rw [hker, Nat.cast_succ, add_mul, one_mul, add_sub_cancel_right, ih, mul_zero]
    have hall : ∀ i : ZMod 5, (v : UU) i = 0 := by
      intro i
      have : i = (((i * (w.c)⁻¹).val : ℕ) : ZMod 5) * w.c := by
        rw [ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ hc, mul_one]
      rw [this]
      exact hk _
    exact Subtype.ext (funext hall)
  calc Module.finrank (ZMod 2) (LinearMap.ker (T w - 1))
      ≤ Module.finrank (ZMod 2) K16 := LinearMap.finrank_le_finrank_of_injective hinj
    _ = 4 := finrank_K16

theorem rank_ge_sixteen {w : Wr} (hc : w.c ≠ 0) :
    16 ≤ Module.finrank (ZMod 2) (LinearMap.range (T w - 1)) := by
  have h := LinearMap.finrank_range_add_finrank_ker (T w - 1)
  rw [finrank_UU] at h
  have := finrank_ker_le_four hc
  omega

theorem finrank_ker_le_eight {w : Wr} (hc : w.c = 0)
    (hz : (Finset.univ.filter fun i => w.a i = 0).card ≤ 2) :
    Module.finrank (ZMod 2) (LinearMap.ker (T w - 1)) ≤ 8 := by
  classical
  let s : Finset (ZMod 5) := Finset.univ.filter fun i => w.a i = 0
  let f : LinearMap.ker (T w - 1) →ₗ[ZMod 2] (s → K16) :=
    (LinearMap.funLeft (ZMod 2) K16 (fun j : s => (j : ZMod 5))).comp
      (LinearMap.ker (T w - 1)).subtype
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have hv0 : ∀ j : s, (v : UU) (j : ZMod 5) = 0 := fun j => congrFun hv j
    refine Subtype.ext (funext fun i => ?_)
    by_cases hi : w.a i = 0
    · exact hv0 ⟨i, by simp [s, hi]⟩
    · have h1 := LinearMap.mem_ker.mp v.2
      have h2 := congrFun h1 i
      simp only [LinearMap.sub_apply, Module.End.one_apply, Pi.sub_apply, Pi.zero_apply,
        T_apply, hc, sub_zero] at h2
      have h3 : (chi (w.a i) - 1) * (v : UU) i = 0 := by rw [sub_mul, one_mul]; exact h2
      rcases mul_eq_zero.mp h3 with h4 | h4
      · exact absurd (sub_eq_zero.mp h4) (chi_ne_one hi)
      · exact h4
  calc Module.finrank (ZMod 2) (LinearMap.ker (T w - 1))
      ≤ Module.finrank (ZMod 2) (s → K16) := LinearMap.finrank_le_finrank_of_injective hinj
    _ = s.card * 4 := by
        rw [Module.finrank_pi_fintype]
        simp [finrank_K16]
    _ ≤ 8 := by
        have hz' : s.card ≤ 2 := hz
        omega

theorem rank_ge_twelve {w : Wr} (hc : w.c = 0)
    (hz : (Finset.univ.filter fun i => w.a i = 0).card ≤ 2) :
    12 ≤ Module.finrank (ZMod 2) (LinearMap.range (T w - 1)) := by
  have h := LinearMap.finrank_range_add_finrank_ker (T w - 1)
  rw [finrank_UU] at h
  have := finrank_ker_le_eight hc hz
  omega

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309
