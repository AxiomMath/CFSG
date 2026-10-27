
module

public import Certificates.Data.Kernel.GammaUOrbK
public import CFSG.Certificates.Kernel.GammaUNormSound
public import CFSG.Certificates.Kernel.GammaUSigmaSoundBase
public import CFSG.GF2Type.Smith1979.GammaU.StepAOrbitFacts
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

public section

namespace CFSG.KC.GUO

open CFSG.KC.IF4C CFSG.KC.IF4R CFSG.KC.GUV CFSG.KC.GUS CFSG.GF2Type.Smith1979.GammaU
open CFSG.GF2Type.Smith1979.GammaU.StepA CFSG.GF2Type.Smith1979.GammaU.SigmaP
open CFSG.GF2Type.Smith1979.IdxFour Module

local notation "GL" => V12 ≃ₗ[ZMod 2] V12

local notation "Sub" => Submodule (ZMod 2) V12

theorem land_one_eq (y : Nat) : Nat.land y 1 = if y.testBit 0 then 1 else 0 := by
  rw [Nat.land_eq, Nat.and_one_is_mod, Nat.testBit_zero]
  rcases Nat.mod_two_eq_zero_or_one y with h | h <;> simp [h]

theorem par6_eq (x : Nat) : par6 x =
    Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor 0 (Nat.land x 1))
      (Nat.land (x >>> 1) 1)) (Nat.land (x >>> 1 >>> 1) 1)) (Nat.land (x >>> 1 >>> 1 >>> 1) 1))
      (Nat.land (x >>> 1 >>> 1 >>> 1 >>> 1) 1)) (Nat.land (x >>> 1 >>> 1 >>> 1 >>> 1 >>> 1) 1) :=
  rfl

theorem par6_spec (x : Nat) : par6 x =
    if (List.range 6).foldl (fun acc i => acc ^^ x.testBit i) false then 1 else 0 := by
  rw [par6_eq]
  simp only [land_one_eq, Nat.testBit_shiftRight, List.range_succ, List.range_zero,
    List.nil_append, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.add_zero,
    Nat.reduceAdd]
  generalize x.testBit 0 = b0
  generalize x.testBit 1 = b1
  generalize x.testBit 2 = b2
  generalize x.testBit 3 = b3
  generalize x.testBit 4 = b4
  generalize x.testBit 5 = b5
  revert b0 b1 b2 b3 b4 b5
  decide

theorem testBit_63 : ∀ i < 6, (63 : Nat).testBit i = true := by decide

theorem q0k_eq (n : Nat) : q0k n = if q0b n then 1 else 0 := by
  have h : q0k n = par6 ((n ||| n >>> 6) &&& 63) := rfl
  have hb : (List.range 6).foldl (fun acc i => acc ^^ ((n ||| n >>> 6) &&& 63).testBit i) false =
      q0b n := by
    simp only [q0b, List.range_succ, List.range_zero, List.nil_append, List.foldl_append,
      List.foldl_cons, List.foldl_nil, Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftRight,
      testBit_63 0 (by omega), testBit_63 1 (by omega), testBit_63 2 (by omega),
      testBit_63 3 (by omega), testBit_63 4 (by omega), testBit_63 5 (by omega), Bool.and_true,
      Nat.reduceAdd]
  rw [h, par6_spec, hb]

theorem f0k_eq (m n : Nat) : f0k m n = if f0b m n then 1 else 0 := by
  have h : f0k m n = par6 (((m &&& n >>> 6) ^^^ (m >>> 6 &&& n)) &&& 63) := rfl
  have hb : (List.range 6).foldl
      (fun acc i => acc ^^ (((m &&& n >>> 6) ^^^ (m >>> 6 &&& n)) &&& 63).testBit i) false =
      f0b m n := by
    simp only [f0b, List.range_succ, List.range_zero, List.nil_append, List.foldl_append,
      List.foldl_cons, List.foldl_nil, Nat.testBit_and, Nat.testBit_xor, Nat.testBit_shiftRight,
      testBit_63 0 (by omega), testBit_63 1 (by omega), testBit_63 2 (by omega),
      testBit_63 3 (by omega), testBit_63 4 (by omega), testBit_63 5 (by omega), Bool.and_true,
      Nat.reduceAdd]
  rw [h, par6_spec, hb]

theorem f0_vecOf_k (m n : Nat) : f0 (vecOf m) (vecOf n) = (f0k m n : ZMod 2) := by
  rw [f0_vecOf, f0k_eq]
  by_cases hb : f0b m n <;> simp [hb]

theorem q0k_zero_iff (n : Nat) : q0k n = 0 ↔ q0 (vecOf n) = 0 := by
  rw [q0_vecOf, q0k_eq]
  by_cases hb : q0b n <;> simp [hb]

theorem f0k_zero_iff (m n : Nat) : f0k m n = 0 ↔ f0 (vecOf m) (vecOf n) = 0 := by
  rw [f0_vecOf, f0k_eq]
  by_cases hb : f0b m n <;> simp [hb]

theorem testBit_of_land {m p : Nat} (h : Nat.land (Nat.shiftRight m p) 1 = 1) :
    m.testBit p = true := by
  rw [Nat.shiftRight_eq', Nat.land_eq, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow] at h
  rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_iff]
  exact h

theorem z2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

theorem bits5 (a b c d e : ZMod 2) :
    a.val + 2 * b.val + 4 * c.val + 8 * d.val + 16 * e.val < 32 ∧
      ((Nat.land (Nat.shiftRight (a.val + 2 * b.val + 4 * c.val + 8 * d.val + 16 * e.val) 0) 1 :
        ℕ) : ZMod 2) = a ∧
      ((Nat.land (Nat.shiftRight (a.val + 2 * b.val + 4 * c.val + 8 * d.val + 16 * e.val) 1) 1 :
        ℕ) : ZMod 2) = b ∧
      ((Nat.land (Nat.shiftRight (a.val + 2 * b.val + 4 * c.val + 8 * d.val + 16 * e.val) 2) 1 :
        ℕ) : ZMod 2) = c ∧
      ((Nat.land (Nat.shiftRight (a.val + 2 * b.val + 4 * c.val + 8 * d.val + 16 * e.val) 3) 1 :
        ℕ) : ZMod 2) = d ∧
      ((Nat.land (Nat.shiftRight (a.val + 2 * b.val + 4 * c.val + 8 * d.val + 16 * e.val) 4) 1 :
        ℕ) : ZMod 2) = e := by
  revert a b c d e
  decide

theorem f0_add_left (x y z : V12) : f0 (x + y) z = f0 x z + f0 y z := by
  unfold f0
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by
    simp only [Pi.add_apply]
    ring

theorem f0_add_right (x y z : V12) : f0 x (y + z) = f0 x y + f0 x z := by
  rw [FLCheck.f0_comm, f0_add_left, FLCheck.f0_comm y, FLCheck.f0_comm z]

theorem f0_smul_right (c : ZMod 2) (x y : V12) : f0 x (c • y) = c * f0 x y := by
  rw [FLCheck.f0_comm, FLCheck.f0_smul_left, FLCheck.f0_comm]

theorem f0_self (x : V12) : f0 x x = 0 := by
  unfold f0
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [mul_comm (x (hi i))]
  exact CharTwo.add_self_eq_zero _

theorem f0_zero_right (x : V12) : f0 x 0 = 0 := by simp [f0]

theorem vec_add_self (x : V12) : x + x = 0 := by
  rw [← vec_sub_eq_add, sub_self]

@[expose] noncomputable def B0 : LinearMap.BilinForm (ZMod 2) V12 :=
  LinearMap.mk₂ (ZMod 2) f0 f0_add_left (fun c x y => by rw [FLCheck.f0_smul_left, smul_eq_mul])
    f0_add_right (fun c x y => by rw [f0_smul_right, smul_eq_mul])

theorem B0_nondeg : B0.Nondegenerate :=
  ⟨fun x h => eq_zero_of_f0 h, fun y h => eq_zero_of_f0 fun x => by
    rw [FLCheck.f0_comm]
    exact h x⟩

theorem f0_map {g : GL} (hg : g ∈ gammaU) (x y : V12) : f0 (g x) (g y) = f0 x y := by
  rw [← polar_q0, ← polar_q0]
  simp only [QuadraticMap.polar, ← map_add, hg.1]

theorem finrank_V12 : finrank (ZMod 2) V12 = 12 := Module.finrank_fin_fun (ZMod 2)

theorem finrank_perp (W : Sub) :
    finrank (ZMod 2) (B0.orthogonal W) = 12 - finrank (ZMod 2) W := by
  rw [LinearMap.BilinForm.finrank_orthogonal B0_nondeg, finrank_V12]

theorem mem_perp {W : Sub} {z : V12} : z ∈ B0.orthogonal W ↔ ∀ n ∈ W, f0 n z = 0 :=
  LinearMap.BilinForm.mem_orthogonal_iff

theorem perp_span_of {S : Set V12} {z : V12} (h : ∀ s ∈ S, f0 s z = 0) :
    ∀ n ∈ Submodule.span (ZMod 2) S, f0 n z = 0 := by
  intro n hn
  induction hn using Submodule.span_induction with
  | mem s hs => exact h s hs
  | zero => exact FLCheck.f0_zero_left z
  | add x y _ _ ihx ihy => rw [f0_add_left, ihx, ihy, add_zero]
  | smul c x _ ih => rw [FLCheck.f0_smul_left, ih, mul_zero]

theorem ts_span {S : Set V12} (hq : ∀ s ∈ S, q0 s = 0) (hf : ∀ s ∈ S, ∀ t ∈ S, f0 s t = 0) :
    ∀ x ∈ Submodule.span (ZMod 2) S, q0 x = 0 := by
  have h2 : ∀ x ∈ Submodule.span (ZMod 2) S, ∀ y ∈ Submodule.span (ZMod 2) S, f0 x y = 0 := by
    intro x hx y hy
    rw [FLCheck.f0_comm]
    exact perp_span_of (fun t ht => by
      rw [FLCheck.f0_comm]
      exact perp_span_of (fun s hs => hf s hs t ht) x hx) y hy
  intro x hx
  induction hx using Submodule.span_induction with
  | mem s hs => exact hq s hs
  | zero => simp [q0]
  | add x y hx hy ihx ihy => rw [FLCheck.q0_add, ihx, ihy, h2 x hx y hy, add_zero, add_zero]
  | smul c x _ ih => rw [FLCheck.q0_smul, ih, mul_zero]

theorem le_perp {D : Sub} (hD : ∀ x ∈ D, q0 x = 0) : D ≤ B0.orthogonal D := fun _ hz =>
  mem_perp.2 fun _ hn => f0_eq_zero_of_mem hD hn hz

theorem finrank_le_six {D : Sub} (hD : ∀ x ∈ D, q0 x = 0) : finrank (ZMod 2) D ≤ 6 := by
  have h1 := Submodule.finrank_mono (le_perp hD)
  have h2 := Submodule.finrank_le D
  rw [finrank_perp] at h1
  rw [finrank_V12] at h2
  omega

theorem perp_eq {D : Sub} (hD : ∀ x ∈ D, q0 x = 0) (h6 : finrank (ZMod 2) D = 6) :
    B0.orthogonal D = D :=
  (Submodule.eq_of_le_of_finrank_eq (le_perp hD) (by rw [finrank_perp, h6])).symm

theorem finrank_sup_single {W : Sub} {y : V12} (hy : y ∉ W) :
    finrank (ZMod 2) (W ⊔ (ZMod 2 ∙ y) : Sub) = finrank (ZMod 2) W + 1 := by
  have hy0 : y ≠ 0 := fun h => hy (h ▸ W.zero_mem)
  have hinf : W ⊓ (ZMod 2 ∙ y) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨hz1, hz2⟩ := Submodule.mem_inf.1 hz
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz2
    rcases z2_cases c with rfl | rfl
    · simp
    · rw [one_smul] at hz1
      exact absurd hz1 hy
  have h := Submodule.finrank_sup_add_finrank_inf_eq W (ZMod 2 ∙ y)
  rw [hinf, finrank_bot, add_zero, finrank_span_singleton hy0] at h
  exact h

theorem map_mul_eq (S : Sub) (g h : GL) :
    (S.map (h : V12 →ₗ[ZMod 2] V12)).map (g : V12 →ₗ[ZMod 2] V12) =
      S.map ((g * h : GL) : V12 →ₗ[ZMod 2] V12) := by
  rw [← Submodule.map_comp]
  rfl

theorem map_one_eq (S : Sub) : S.map ((1 : GL) : V12 →ₗ[ZMod 2] V12) = S := by
  ext x
  simp

@[expose] noncomputable def nb (D : Sub) (y : V12) : Sub := D ⊓ LinearMap.ker (B0 y) ⊔ (ZMod 2 ∙ y)

theorem mem_nb {D : Sub} {y x : V12} :
    x ∈ nb D y ↔ ∃ a ∈ D, f0 y a = 0 ∧ ∃ c : ZMod 2, a + c • y = x := by
  unfold nb
  rw [Submodule.mem_sup]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    obtain ⟨ha1, ha2⟩ := Submodule.mem_inf.1 ha
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hb
    exact ⟨a, ha1, LinearMap.mem_ker.1 ha2, c, rfl⟩
  · rintro ⟨a, ha, hfa, c, rfl⟩
    exact ⟨a, Submodule.mem_inf.2 ⟨ha, LinearMap.mem_ker.2 hfa⟩, c • y,
      Submodule.mem_span_singleton.2 ⟨c, rfl⟩, rfl⟩

theorem nb_ts {D : Sub} (hD : ∀ x ∈ D, q0 x = 0) {y : V12} (hy : q0 y = 0) :
    ∀ x ∈ nb D y, q0 x = 0 := by
  intro x hx
  obtain ⟨a, ha, hfa, c, rfl⟩ := mem_nb.1 hx
  rw [FLCheck.q0_add, FLCheck.q0_smul, hD a ha, hy, f0_smul_right, FLCheck.f0_comm, hfa]
  simp

theorem nb_le {D : Sub} (hD : ∀ x ∈ D, q0 x = 0) {y y' : V12} (hy : q0 y = 0) (hy' : q0 y' = 0)
    (hz : y + y' ∈ D) : nb D y ≤ nb D y' := by
  intro x hx
  obtain ⟨a, ha, hfa, c, rfl⟩ := mem_nb.1 hx
  have hyy' : f0 y y' = 0 := by
    have h := FLCheck.q0_add y y'
    rw [hD _ hz, hy, hy', zero_add, zero_add] at h
    exact h.symm
  have hfz : f0 y' (y + y') = 0 := by
    rw [f0_add_right, FLCheck.f0_comm, hyy', f0_self, add_zero]
  have hfa' : f0 y' a = 0 := by
    have h := f0_eq_zero_of_mem hD hz ha
    rw [f0_add_left, hfa, zero_add] at h
    exact h
  refine mem_nb.2 ⟨a + c • (y + y'), D.add_mem ha (D.smul_mem c hz), ?_, c, ?_⟩
  · rw [f0_add_right, f0_smul_right, hfa', hfz, mul_zero, add_zero]
  · rw [smul_add, add_assoc, add_assoc, vec_add_self, add_zero]

theorem nb_congr {D : Sub} (hD : ∀ x ∈ D, q0 x = 0) {y y' : V12} (hy : q0 y = 0)
    (hy' : q0 y' = 0) (hz : y + y' ∈ D) : nb D y = nb D y' :=
  le_antisymm (nb_le hD hy hy' hz) (nb_le hD hy' hy (by rwa [add_comm]))

theorem nb_map {D : Sub} {y : V12} {g : GL} (hg : g ∈ gammaU) :
    (nb D y).map (g : V12 →ₗ[ZMod 2] V12) = nb (D.map (g : V12 →ₗ[ZMod 2] V12)) (g y) := by
  ext x
  rw [Submodule.mem_map, mem_nb]
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨a, ha, hfa, c, rfl⟩ := mem_nb.1 hz
    refine ⟨g a, Submodule.mem_map_of_mem ha, by rw [f0_map hg, hfa], c, ?_⟩
    simp
  · rintro ⟨a, ha, hfa, c, rfl⟩
    obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.1 ha
    refine ⟨b + c • y, mem_nb.2 ⟨b, hb, ?_, c, rfl⟩, ?_⟩
    · rw [← f0_map hg]
      exact hfa
    · simp

theorem xs_cons (b : Nat) (L : List Nat) (m : Nat) :
    xs (b :: L) m =
      Nat.xor (bif Nat.beq (Nat.land m 1) 1 then b else 0) (xs L (Nat.shiftRight m 1)) := rfl

theorem xs_cons_even (b : Nat) (L : List Nat) (m : Nat) : xs (b :: L) (2 * m) = xs L m := by
  have h1 : Nat.land (2 * m) 1 = 0 := by
    rw [Nat.land_eq, Nat.and_one_is_mod]
    omega
  have h2 : Nat.shiftRight (2 * m) 1 = m := by
    rw [Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow]
    omega
  rw [xs_cons, h1, h2]
  simp

theorem xs_cons_odd (b : Nat) (L : List Nat) (m : Nat) :
    xs (b :: L) (2 * m + 1) = b ^^^ xs L m := by
  have h1 : Nat.land (2 * m + 1) 1 = 1 := by
    rw [Nat.land_eq, Nat.and_one_is_mod]
    omega
  have h2 : Nat.shiftRight (2 * m + 1) 1 = m := by
    rw [Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow]
    omega
  rw [xs_cons, h1, h2]
  simp

theorem spanOf_le_cons (b : Nat) (L : List Nat) : spanOf L ≤ spanOf (b :: L) :=
  Submodule.span_mono fun _ ⟨w, hw, hx⟩ => ⟨w, List.mem_cons_of_mem b hw, hx⟩

theorem xs_mem : ∀ (L : List Nat) (m : Nat), vecOf (xs L m) ∈ spanOf L
  | [], _ => by
    change vecOf 0 ∈ _
    rw [vecOf_zero]
    exact Submodule.zero_mem _
  | b :: L, m => by
    rw [xs_cons, Nat.xor_eq, vecOf_xor, vecOf_bif]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (mem_spanOf_of_mem List.mem_cons_self))
      (spanOf_le_cons b L (xs_mem L _))

theorem xs_lt : ∀ {L : List Nat}, (∀ v ∈ L, v < 4096) → ∀ m, xs L m < 4096
  | [], _, _ => by
    change 0 < 4096
    norm_num
  | b :: L, hL, m => by
    rw [xs_cons, Nat.xor_eq]
    refine xor_lt ?_ (xs_lt (fun v hv => hL v (List.mem_cons_of_mem b hv)) _)
    cases Nat.beq (Nat.land m 1) 1
    · change 0 < 4096
      norm_num
    · exact hL b List.mem_cons_self

theorem exists_xs : ∀ (L : List Nat), ∀ x ∈ spanOf L, ∃ m < 2 ^ L.length, vecOf (xs L m) = x
  | [], x, hx => by
    rw [spanOf_nil, Submodule.mem_bot] at hx
    exact ⟨0, by norm_num, by rw [hx]; exact vecOf_zero⟩
  | b :: L, x, hx => by
    rw [spanOf_cons, Submodule.mem_span_insert] at hx
    obtain ⟨a, z, hz, rfl⟩ := hx
    obtain ⟨m, hm, rfl⟩ := exists_xs L z hz
    have hlen : 2 ^ (b :: L).length = 2 * 2 ^ L.length := by
      rw [List.length_cons, pow_succ]
      ring
    rcases z2_cases a with rfl | rfl
    · exact ⟨2 * m, by omega, by rw [xs_cons_even, zero_smul, zero_add]⟩
    · exact ⟨2 * m + 1, by omega, by rw [xs_cons_odd, vecOf_xor, one_smul]⟩

theorem finrank_xs : ∀ (L : List Nat), (∀ v ∈ L, v < 4096) →
    (∀ m, 0 < m → m < 2 ^ L.length → xs L m ≠ 0) → finrank (ZMod 2) (spanOf L) = L.length
  | [], _, _ => by
    rw [spanOf_nil, finrank_bot]
    rfl
  | b :: L, hlt, hm => by
    have hL : ∀ v ∈ L, v < 4096 := fun v hv => hlt v (List.mem_cons_of_mem b hv)
    have hlen : 2 ^ (b :: L).length = 2 * 2 ^ L.length := by
      rw [List.length_cons, pow_succ]
      ring
    have hm' : ∀ m, 0 < m → m < 2 ^ L.length → xs L m ≠ 0 := fun m h1 h2 => by
      have := hm (2 * m) (by omega) (by omega)
      rwa [xs_cons_even] at this
    have hnot : vecOf b ∉ spanOf L := by
      intro hb
      obtain ⟨m', hm'lt, he⟩ := exists_xs L _ hb
      have := hm (2 * m' + 1) (by omega) (by omega)
      rw [xs_cons_odd] at this
      apply this
      apply vecOf_inj (xor_lt (hlt b List.mem_cons_self) (xs_lt hL m')) (by norm_num)
      rw [vecOf_xor, he, vecOf_zero, vec_add_self]
    rw [finrank_spanOf_cons hnot, finrank_xs L hL hm', List.length_cons]

theorem spanOf_append_le (L : List Nat) (y : Nat) :
    spanOf (L ++ [y]) ≤ spanOf L ⊔ (ZMod 2 ∙ vecOf y) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨v, hv, rfl⟩
  rcases List.mem_append.1 hv with hv | hv
  · exact Submodule.mem_sup_left (mem_spanOf_of_mem hv)
  · rw [List.mem_singleton.1 hv]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)

theorem mem_nb_of_xs {B : List Nat} {y m : Nat}
    (hf : f0 (vecOf (xs (B ++ [y]) m)) (vecOf y) = 0) :
    vecOf (xs (B ++ [y]) m) ∈ nb (spanOf B) (vecOf y) := by
  obtain ⟨d, hd, e, he, hde⟩ := Submodule.mem_sup.1 (spanOf_append_le B y (xs_mem (B ++ [y]) m))
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 he
  refine mem_nb.2 ⟨d, hd, ?_, c, hde⟩
  rw [← hde, f0_add_left, FLCheck.f0_smul_left, f0_self, mul_zero, add_zero] at hf
  rw [FLCheck.f0_comm]
  exact hf

structure RepFacts (B : List Nat) : Prop where
  len : B.length = 6
  last : nthD 0 B 5 = 3072
  lt : ∀ i < 6, nthD 0 B i < 4096
  q : ∀ i < 6, q0k (nthD 0 B i) = 0
  f : ∀ i < 6, ∀ j < 6, f0k (nthD 0 B i) (nthD 0 B j) = 0
  ind : ∀ m < 63, xs B (m + 1) ≠ 0

theorem repF_spec {R : List (List Nat)} {ri : Nat} (h : repF R ri = true) :
    RepFacts (nthD [] R ri) := by
  simp only [repF, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq, allBelow_iff, lenN_eq] at h
  obtain ⟨⟨⟨⟨hl, h5⟩, hq⟩, hf⟩, hind⟩ := h
  refine ⟨hl, h5, fun i hi => (hq i hi).1, fun i hi => (hq i hi).2, hf, fun m hm h0 => ?_⟩
  have := hind m hm
  have e : Nat.succ m = m + 1 := rfl
  rw [e, h0] at this
  exact absurd this (by decide)

namespace RepFacts

variable {B : List Nat} (hB : RepFacts B)
include hB

theorem mem {v : Nat} (hv : v ∈ B) : ∃ i < 6, nthD 0 B i = v := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hv
  refine ⟨i, hB.len ▸ hi, ?_⟩
  rw [nthD_eq, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  rfl

theorem ts : ∀ x ∈ spanOf B, q0 x = 0 := by
  refine ts_span ?_ ?_
  · rintro _ ⟨v, hv, rfl⟩
    obtain ⟨i, hi, rfl⟩ := hB.mem hv
    exact (q0k_zero_iff _).1 (hB.q i hi)
  · rintro _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩
    obtain ⟨i, hi, rfl⟩ := hB.mem hv
    obtain ⟨j, hj, rfl⟩ := hB.mem hw
    exact (f0k_zero_iff _ _).1 (hB.f i hi j hj)

theorem finrank : finrank (ZMod 2) (spanOf B) = 6 := by
  have hlt : ∀ v ∈ B, v < 4096 := fun v hv => by
    obtain ⟨i, hi, rfl⟩ := hB.mem hv
    exact hB.lt i hi
  rw [finrank_xs B hlt fun m h1 h2 => ?_, hB.len]
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [hB.len] at h2
  exact hB.ind k (by norm_num at h2; omega)

theorem a0_mem : vecOf 3072 ∈ spanOf B := by
  rw [← hB.last]
  exact mem_spanOf_of_mem (nthD_mem 0 (by rw [hB.len]; norm_num))

theorem mem_of_perp {z : V12} (h : ∀ i < 6, f0 (vecOf (nthD 0 B i)) z = 0) : z ∈ spanOf B := by
  rw [← perp_eq hB.ts hB.finrank]
  refine mem_perp.2 (perp_span_of ?_)
  rintro _ ⟨v, hv, rfl⟩
  obtain ⟨i, hi, rfl⟩ := hB.mem hv
  exact h i hi

end RepFacts

theorem exists_of_guOK {TH A : Nat} (hTH : ∀ v, linP TH v = theta0 v) (h : guOK TH A = true) :
    ∃ U : GL, IsP U A ∧ U ∈ gammaU := by
  have hq : ∀ x, q0 (linP A x) = q0 x := by
    have h' := h
    unfold guOK at h'
    simp only [Bool.and_eq_true, Bool.or_eq_true, allBelow_iff, beq_iff_eq] at h'
    obtain ⟨⟨hq, hf⟩, -⟩ := h'
    intro x
    rw [linP]
    refine FLCheck.q0_linOfRows (fun j => ?_) (fun j k => ?_) x
    · rw [rowsP_get, q0_vecOf, q0_vecOf, hq j j.2]
    · rw [rowsP_get, rowsP_get, f0_vecOf, f0_vecOf, hf j j.2 k k.2]
  have hU : IsP (equivOfPreserves (linP A) hq) A := fun _ => rfl
  exact ⟨_, hU, guOK_spec hTH h hU⟩

theorem rec_all {p : Nat → Bool} : ∀ l : List Nat,
    List.rec (motive := fun _ => Bool) true (fun g _ ih => p g && ih) l = true → ∀ g ∈ l, p g = true
  | [], _, g, hg => absurd hg List.not_mem_nil
  | a :: l, h, g, hg => by
    have h' : (p a && List.rec (motive := fun _ => Bool) true (fun g _ ih => p g && ih) l) = true :=
      h
    rw [Bool.and_eq_true] at h'
    rcases List.mem_cons.1 hg with rfl | hg
    · exact h'.1
    · exact rec_all l h'.2 g hg

theorem gensOK_spec {TH : Nat} {SG GG : List Nat} (h : gensOK TH SG GG = true) :
    lenN SG = 2 ∧ lenN GG = 4 ∧ (∀ g ∈ SG, guOK TH g = true ∧ ap12 g 3072 = 3072) ∧
      ∀ g ∈ GG, guOK TH g = true := by
  unfold gensOK at h
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, fun g hg => ?_, rec_all (p := fun g => guOK TH g) GG h4⟩
  have := rec_all (p := fun g => guOK TH g && Nat.beq (ap12 g 3072) 3072) SG h3 g hg
  simp only [Bool.and_eq_true, Nat.beq_eq] at this
  exact this

theorem word_spec {SG : List Nat}
    (hSA : ∀ g < 2, ∃ U ∈ saSet, IsP U (nthD 0 SG g)) :
    ∀ w : List Nat, (∀ e ∈ w, e < 2) →
      ∃ h ∈ Submonoid.closure saSet, ∀ x, vecOf (wordAp SG w x) = h (vecOf x)
  | [], _ => ⟨1, Submonoid.one_mem _, fun _ => rfl⟩
  | g :: w, hw => by
    obtain ⟨U, hU, hUP⟩ := hSA g (hw g List.mem_cons_self)
    obtain ⟨h, hh, hx⟩ := word_spec hSA w fun e he => hw e (List.mem_cons_of_mem g he)
    refine ⟨h * U, Submonoid.mul_mem _ hh (Submonoid.subset_closure hU), fun x => ?_⟩
    change vecOf (wordAp SG w (ap12 (nthD 0 SG g) x)) = _
    rw [hx, ← hUP.apply_code]
    rfl

theorem closure_spec (hSAg : ∀ U ∈ saSet, U ∈ gammaU ∧ U (vecOf 3072) = vecOf 3072) :
    ∀ h ∈ Submonoid.closure saSet, h ∈ gammaU ∧ h (vecOf 3072) = vecOf 3072 := by
  intro h hh
  induction hh using Submonoid.closure_induction with
  | mem x hx => exact hSAg x hx
  | one => exact ⟨one_mem _, rfl⟩
  | mul x y _ _ hx hy => exact ⟨mul_mem hx.1 hy.1, by rw [LinearEquiv.mul_apply, hy.2, hx.2]⟩

theorem treeW_spec {GG : List Nat} {SM : Nat}
    (hGG : ∀ g < 4, ∃ U : GL, IsP U (nthD 0 GG g) ∧ U ∈ gammaU) :
    ∀ (es : List (List Nat)) (mask : Nat), treeW GG SM es mask = true →
      (∀ n, mask.testBit n = true → ∃ g ∈ gammaU, g (vecOf 3072) = vecOf n) →
      ∀ n, SM.testBit n = true → ∃ g ∈ gammaU, g (vecOf 3072) = vecOf n
  | [], mask, h, hm => by
    have e : mask = SM := Nat.eq_of_beq_eq_true h
    rw [← e]
    exact hm
  | e :: es, mask, h, hm => by
    have h' : (Nat.blt (nthD 0 e 1) 4 &&
        Nat.beq (Nat.land (Nat.shiftRight mask (nthD 0 e 2)) 1) 1 &&
        Nat.beq (ap12 (nthD 0 GG (nthD 0 e 1)) (nthD 0 e 2)) (nthD 0 e 0) &&
        treeW GG SM es (Nat.lor mask (Nat.shiftLeft 1 (nthD 0 e 0)))) = true := h
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h'
    obtain ⟨⟨⟨hg, hp⟩, hap⟩, hrest⟩ := h'
    refine treeW_spec hGG es _ hrest fun n hn => ?_
    simp only [Nat.lor_eq, Nat.shiftLeft_eq', Nat.testBit_or, Nat.shiftLeft_eq, one_mul,
      Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq] at hn
    rcases hn with hn | rfl
    · exact hm n hn
    · obtain ⟨g, hgg, hgx⟩ := hm _ (testBit_of_land hp)
      obtain ⟨U, hUP, hU⟩ := hGG _ hg
      exact ⟨U * g, mul_mem hU hgg, by rw [LinearEquiv.mul_apply, hgx, hUP.apply_code, hap]⟩

@[expose] noncomputable def repRec (SG : List Nat) (R : List (List Nat)) (ri : Nat) (rs : List (List Nat))
    (c : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun r _ ih c => Nat.beq (nthD 0 r 0) ri && Nat.beq (nthD 0 r 1) c && recOK SG R r &&
      ih (Nat.succ c)) rs c

theorem repRec_cons (SG : List Nat) (R : List (List Nat)) (ri : Nat) (r : List Nat)
    (rs : List (List Nat)) (c : Nat) :
    repRec SG R ri (r :: rs) c = (Nat.beq (nthD 0 r 0) ri && Nat.beq (nthD 0 r 1) c &&
      recOK SG R r && repRec SG R ri rs (Nat.succ c)) := rfl

theorem repRec_spec {SG : List Nat} {R : List (List Nat)} {ri : Nat} :
    ∀ (rs : List (List Nat)) (c0 : Nat), repRec SG R ri rs c0 = true →
      ∀ c, c0 ≤ c → c < c0 + rs.length →
        ∃ r ∈ rs, nthD 0 r 0 = ri ∧ nthD 0 r 1 = c ∧ recOK SG R r = true
  | [], c0, _, c, h1, h2 => by
    rw [List.length_nil] at h2
    omega
  | r :: rs, c0, h, c, h1, h2 => by
    rw [repRec_cons] at h
    simp only [Bool.and_eq_true, Nat.beq_eq] at h
    obtain ⟨⟨⟨hr0, hr1⟩, hr⟩, hrest⟩ := h
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · exact ⟨r, List.mem_cons_self, hr0, hr1, hr⟩
    · rw [List.length_cons] at h2
      obtain ⟨r', hr', H⟩ := repRec_spec rs (Nat.succ c0) hrest c hlt (by omega)
      exact ⟨r', List.mem_cons_of_mem r hr', H⟩

theorem repOK_spec {SG : List Nat} {R : List (List Nat)} {ri : Nat} {rs : List (List Nat)}
    (h : repOK SG R ri rs = true) :
    ∀ c, 1 ≤ c → c < 32 → ∃ r ∈ rs, nthD 0 r 0 = ri ∧ nthD 0 r 1 = c ∧ recOK SG R r = true := by
  have h' : (Nat.beq (lenN rs) 31 && repRec SG R ri rs 1) = true := h
  rw [Bool.and_eq_true, Nat.beq_eq, lenN_eq] at h'
  exact fun c h1 h2 => repRec_spec rs 1 h'.2 c h1 (by rw [h'.1]; omega)

theorem recOK_spec {SG : List Nat} {R : List (List Nat)} {r : List Nat} (h : recOK SG R r = true) :
    nthD 0 r 3 < 6 ∧ (∀ e ∈ dropN 10 r, e < 2) ∧ nthD 0 r 2 < 4096 ∧ q0k (nthD 0 r 2) = 0 ∧
      f0k (nthD 0 r 2) (nthD 0 (nthD [] R (nthD 0 r 0)) 5) = 0 ∧
      (∀ i < 5, f0k (nthD 0 r 2) (nthD 0 (nthD [] R (nthD 0 r 0)) i) =
        Nat.land (Nat.shiftRight (nthD 0 r 1) i) 1) ∧
      ∀ j < 6, wordAp SG (dropN 10 r) (nthD 0 (nthD [] R (nthD 0 r 3)) j) =
          xs (nthD [] R (nthD 0 r 0) ++ [nthD 0 r 2]) (nthD 0 r (Nat.add 4 j)) ∧
        f0k (wordAp SG (dropN 10 r) (nthD 0 (nthD [] R (nthD 0 r 3)) j)) (nthD 0 r 2) = 0 := by
  simp only [recOK, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, allBelow_iff, ltAll_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

section Records

variable {SG : List Nat} {R : List (List Nat)}
  (hSA : ∀ g < 2, ∃ U ∈ saSet, IsP U (nthD 0 SG g)) (hrep : ∀ i < 6, RepFacts (nthD [] R i))
include hSA hrep

theorem nb_rec {r : List Nat} (hr : recOK SG R r = true) (hri : nthD 0 r 0 < 6) :
    ∃ h ∈ Submonoid.closure saSet,
      nb (spanOf (nthD [] R (nthD 0 r 0))) (vecOf (nthD 0 r 2)) =
        (spanOf (nthD [] R (nthD 0 r 3))).map (h : V12 →ₗ[ZMod 2] V12) := by
  obtain ⟨hrj, hw, -, hq, -, -, hj⟩ := recOK_spec hr
  obtain ⟨h, hh, hhx⟩ := word_spec hSA _ hw
  have hyq : q0 (vecOf (nthD 0 r 2)) = 0 := (q0k_zero_iff _).1 hq
  refine ⟨h, hh, (Submodule.eq_of_le_of_finrank_le ?_ ?_).symm⟩
  · rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨x, ⟨v, hv, rfl⟩, rfl⟩
    obtain ⟨j, hj6, rfl⟩ := (hrep _ hrj).mem hv
    obtain ⟨heq, hjf⟩ := hj j hj6
    rw [heq] at hjf
    have e : (h : V12 →ₗ[ZMod 2] V12) (vecOf (nthD 0 (nthD [] R (nthD 0 r 3)) j)) =
        vecOf (xs (nthD [] R (nthD 0 r 0) ++ [nthD 0 r 2]) (nthD 0 r (Nat.add 4 j))) := by
      rw [LinearEquiv.coe_coe, ← hhx, heq]
    rw [SetLike.mem_coe, e]
    exact mem_nb_of_xs (by rw [f0_vecOf_k, hjf, Nat.cast_zero])
  · rw [LinearEquiv.finrank_map_eq, (hrep _ hrj).finrank]
    exact finrank_le_six (nb_ts (hrep _ hri).ts hyq)

theorem nb_rep (hrecs : ∀ i < 6, ∃ rs, repOK SG R i rs = true) {ri : Nat} (hri : ri < 6)
    {y : V12} (hy : q0 y = 0) (hya : f0 y (vecOf 3072) = 0)
    (hyD : y ∉ spanOf (nthD [] R ri)) :
    ∃ rj < 6, ∃ h ∈ Submonoid.closure saSet,
      nb (spanOf (nthD [] R ri)) y = (spanOf (nthD [] R rj)).map (h : V12 →ₗ[ZMod 2] V12) := by
  obtain ⟨B, hBe⟩ : ∃ B, nthD [] R ri = B := ⟨_, rfl⟩
  have hB : RepFacts B := hBe ▸ hrep ri hri
  rw [hBe] at hyD ⊢
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ZMod 2, ∀ i, a i = f0 y (vecOf (nthD 0 B i)) := ⟨_, fun _ => rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = (a 0).val + 2 * (a 1).val + 4 * (a 2).val + 8 * (a 3).val +
      16 * (a 4).val := ⟨_, rfl⟩
  obtain ⟨hc32, hb0, hb1, hb2, hb3, hb4⟩ := bits5 (a 0) (a 1) (a 2) (a 3) (a 4)
  rw [← hc] at hc32 hb0 hb1 hb2 hb3 hb4
  have hbit : ∀ i < 5, ((Nat.land (Nat.shiftRight c i) 1 : ℕ) : ZMod 2) = a i := by
    intro i hi
    interval_cases i <;> assumption
  have hc0 : c ≠ 0 := by
    intro h0
    refine hyD (hB.mem_of_perp fun i hi => ?_)
    rw [FLCheck.f0_comm]
    rcases (by omega : i < 5 ∨ i = 5) with hi5 | rfl
    · rw [← ha i, ← hbit i hi5, h0]
      simp
    · rw [hB.last]
      exact hya
  obtain ⟨rs, hrs⟩ := hrecs ri hri
  obtain ⟨r, -, hr0, hr1, hr⟩ := repOK_spec hrs c (by omega) hc32
  obtain ⟨hrj, -, -, hyq, hya', hyb, -⟩ := recOK_spec hr
  rw [hr0, hBe] at hya' hyb
  have hyq' : q0 (vecOf (nthD 0 r 2)) = 0 := (q0k_zero_iff _).1 hyq
  have hz : y + vecOf (nthD 0 r 2) ∈ spanOf B := hB.mem_of_perp fun i hi => by
    rw [f0_add_right]
    rcases (by omega : i < 5 ∨ i = 5) with hi5 | rfl
    · have e1 := hyb i hi5
      rw [hr1] at e1
      have e2 : f0 (vecOf (nthD 0 B i)) (vecOf (nthD 0 r 2)) = f0 (vecOf (nthD 0 B i)) y := by
        rw [FLCheck.f0_comm, f0_vecOf_k, e1, hbit i hi5, ha i, FLCheck.f0_comm]
      rw [e2, CharTwo.add_self_eq_zero]
    · rw [FLCheck.f0_comm, FLCheck.f0_comm _ (vecOf (nthD 0 r 2)), f0_vecOf_k, hya', hB.last,
        hya, Nat.cast_zero, add_zero]
  obtain ⟨h, hh, he⟩ := nb_rec hSA hrep hr (by rw [hr0]; exact hri)
  rw [hr0, hBe] at he
  exact ⟨nthD 0 r 3, hrj, h, hh, (nb_congr hB.ts hy hyq' hz).trans he⟩

end Records

@[expose] def MaxA (D : Sub) : Prop :=
  (∀ x ∈ D, q0 x = 0) ∧ finrank (ZMod 2) D = 6 ∧ vecOf 3072 ∈ D

@[expose] def InS (R : List (List Nat)) (D : Sub) : Prop :=
  ∃ ri < 6, ∃ h ∈ Submonoid.closure saSet, D = (spanOf (nthD [] R ri)).map (h : V12 →ₗ[ZMod 2] V12)

section Reach

variable {R : List (List Nat)}
  (hMg : ∀ h ∈ Submonoid.closure saSet, h ∈ gammaU ∧ h (vecOf 3072) = vecOf 3072)
  (hrep : ∀ i < 6, RepFacts (nthD [] R i))
  (hN2 : ∀ ri < 6, ∀ y : V12, q0 y = 0 → f0 y (vecOf 3072) = 0 → y ∉ spanOf (nthD [] R ri) →
    ∃ rj < 6, ∃ h ∈ Submonoid.closure saSet,
      nb (spanOf (nthD [] R ri)) y = (spanOf (nthD [] R rj)).map (h : V12 →ₗ[ZMod 2] V12))

include hMg hrep in
theorem InS.maxA {D : Sub} (hD : InS R D) : MaxA D := by
  obtain ⟨ri, hri, h, hh, rfl⟩ := hD
  obtain ⟨hg, hfix⟩ := hMg h hh
  refine ⟨fun x hx => ?_, ?_, ?_⟩
  · obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hx
    rw [LinearEquiv.coe_coe, hg.1]
    exact (hrep ri hri).ts z hz
  · rw [LinearEquiv.finrank_map_eq, (hrep ri hri).finrank]
  · rw [← hfix]
    exact Submodule.mem_map_of_mem (hrep ri hri).a0_mem

include hMg hN2 in
theorem nb_S {D : Sub} (hD : InS R D) {y : V12} (hy : q0 y = 0)
    (hya : f0 y (vecOf 3072) = 0) (hyD : y ∉ D) : InS R (nb D y) := by
  obtain ⟨ri, hri, h, hh, rfl⟩ := hD
  obtain ⟨hg, hfix⟩ := hMg h hh
  have hyy : h (h⁻¹ y) = y := apply_inv_apply h y
  have hq' : q0 (h⁻¹ y) = 0 := by
    rw [(inv_mem hg).1]
    exact hy
  have hf' : f0 (h⁻¹ y) (vecOf 3072) = 0 := by
    rw [← f0_map hg, hyy, hfix]
    exact hya
  have hD' : h⁻¹ y ∉ spanOf (nthD [] R ri) := fun hm => hyD (by
    rw [← hyy]
    exact Submodule.mem_map_of_mem hm)
  obtain ⟨rj, hrj, h₂, hh₂, he⟩ := hN2 ri hri _ hq' hf' hD'
  refine ⟨rj, hrj, h * h₂, Submonoid.mul_mem _ hh hh₂, ?_⟩
  rw [← hyy, ← nb_map hg, he, map_mul_eq]

include hMg hrep hN2 in
theorem reach (n : ℕ) : ∀ D D' : Sub, InS R D → MaxA D' →
    6 ≤ finrank (ZMod 2) (D ⊓ D' : Sub) + n → InS R D' := by
  induction n with
  | zero =>
    intro D D' hD hD' hk
    have hDm := hD.maxA hMg hrep
    have h1 : D ⊓ D' = D' := Submodule.eq_of_le_of_finrank_le inf_le_right (by
      rw [hD'.2.1]
      omega)
    have hle : D' ≤ D := by
      rw [← h1]
      exact inf_le_left
    rw [Submodule.eq_of_le_of_finrank_eq hle (by rw [hD'.2.1, hDm.2.1])]
    exact hD
  | succ n ih =>
    intro D D' hD hD' hk
    have hDm := hD.maxA hMg hrep
    by_cases hle : D' ≤ D
    · rw [Submodule.eq_of_le_of_finrank_eq hle (by rw [hD'.2.1, hDm.2.1])]
      exact hD
    obtain ⟨y, hyD', hyD⟩ := SetLike.not_le_iff_exists.1 hle
    have hy : q0 y = 0 := hD'.1 y hyD'
    have hya : f0 y (vecOf 3072) = 0 := f0_eq_zero_of_mem hD'.1 hyD' hD'.2.2
    refine ih (nb D y) D' (nb_S hMg hN2 hD hy hya hyD) hD' ?_
    have hyI : y ∉ D ⊓ D' := fun h => hyD (Submodule.mem_inf.1 h).1
    have hsub : D ⊓ D' ⊔ (ZMod 2 ∙ y) ≤ nb D y ⊓ D' := by
      refine sup_le (fun x hx => ?_) ?_
      · obtain ⟨hxD, hxD'⟩ := Submodule.mem_inf.1 hx
        refine Submodule.mem_inf.2 ⟨mem_nb.2 ⟨x, hxD, f0_eq_zero_of_mem hD'.1 hyD' hxD', 0, ?_⟩,
          hxD'⟩
        rw [zero_smul, add_zero]
      · rw [Submodule.span_singleton_le_iff_mem]
        refine Submodule.mem_inf.2 ⟨mem_nb.2 ⟨0, D.zero_mem, f0_zero_right y, 1, ?_⟩, hyD'⟩
        rw [one_smul, zero_add]
    have h1 := Submodule.finrank_mono hsub
    rw [finrank_sup_single hyI] at h1
    omega

end Reach

theorem orbFacts_of {TH : Nat} {SG GG : List Nat} {R : List (List Nat)} {SM : Nat}
    {TR : List (List Nat)}
    (hpin : TH = packR thetaRows ∧ SG = saGens.map packR ∧ R = dReps ∧
      (saGens.all fun r => rowsOK r.toList) = true)
    (hrecs : ∀ i < 6, ∃ rs, repOK SG R i rs = true) (hreps : ∀ i < 6, repF R i = true)
    (htree : treeOK GG SM TR = true) (hsm : smOK SM = true) (hgens : gensOK TH SG GG = true) :
    (∀ v : V12, v ≠ 0 → q0 v = 0 → ∃ g ∈ gammaU, g (vecOf a0) = v) ∧
      (∀ U ∈ saSet, U ∈ gammaU ∧ U (vecOf a0) = vecOf a0) ∧
      (∀ r ∈ saGens, ∃ U : GL, ∀ y, U y = linOfRows r y) ∧
      ∀ D : Sub, (∀ x ∈ D, q0 x = 0) → finrank (ZMod 2) D = 6 → vecOf a0 ∈ D →
        ∃ rep ∈ dReps, ∃ h ∈ Submonoid.closure saSet,
          D = (spanOf rep).map (h : V12 →ₗ[ZMod 2] V12) := by
  obtain ⟨rfl, rfl, rfl, hrows⟩ := hpin
  have hrows' : ∀ r ∈ saGens, rowsOK r.toList = true := List.all_eq_true.1 hrows
  have hTH : ∀ v, linP (packR thetaRows) v = theta0 v := fun v => by
    rw [linP_eq_of_rowsP (rowsP_packR rowsOK_thetaRows)]
    exact linOfRows_thetaRows v
  obtain ⟨hSGl, hGGl, hSGc, hGGc⟩ := gensOK_spec hgens
  have hSAg : ∀ U ∈ saSet, U ∈ gammaU ∧ U (vecOf 3072) = vecOf 3072 := by
    rintro U ⟨r, hr, hU⟩
    have hP : IsP U (packR r) := (isP_packR (hrows' r hr) U).2 hU
    obtain ⟨hgu, hfix⟩ := hSGc (packR r) (List.mem_map_of_mem hr)
    refine ⟨guOK_spec hTH hgu hP, ?_⟩
    rw [hP.apply_code, hfix]
  have hSA : ∀ g < 2, ∃ U ∈ saSet, IsP U (nthD 0 (saGens.map packR) g) := by
    intro g hg
    have hm := nthD_mem 0 (by rw [← lenN_eq, hSGl]; exact hg : g < (saGens.map packR).length)
    obtain ⟨r, hr, hrg⟩ := List.mem_map.1 hm
    obtain ⟨U, hUP, -⟩ := exists_of_guOK hTH (hSGc _ hm).1
    rw [← hrg] at hUP
    refine ⟨U, ⟨r, hr, (isP_packR (hrows' r hr) U).1 hUP⟩, ?_⟩
    rw [← hrg]
    exact hUP
  have hMg := closure_spec hSAg
  have hrep : ∀ i < 6, RepFacts (nthD [] dReps i) := fun i hi => repF_spec (hreps i hi)
  refine ⟨fun v hv hq => ?_, hSAg, fun r hr => ?_, fun D hD h6 ha => ?_⟩
  ·
    have hGG : ∀ g < 4, ∃ U : GL, IsP U (nthD 0 GG g) ∧ U ∈ gammaU := fun g hg =>
      exists_of_guOK hTH (hGGc _ (nthD_mem 0 (by rw [← lenN_eq, hGGl]; exact hg)))
    have hn := codeOf_lt v
    have hvn := vecOf_codeOf v
    have hn0 : codeOf v ≠ 0 := fun h => hv (by rw [← hvn, h, vecOf_zero])
    have hqk : q0k (codeOf v) = 0 := (q0k_zero_iff _).2 (by rw [hvn]; exact hq)
    have hbit : SM.testBit (codeOf v) = true := by
      have h := (allBelow_iff _ _).1 hsm _ hn
      have e := Nat.eq_of_beq_eq_true h
      cases hb : Nat.beq (codeOf v) 0
      · rw [hb, hqk] at e
        exact testBit_of_land e
      · exact absurd (Nat.eq_of_beq_eq_true hb) hn0
    have hinit : ∀ n, (Nat.shiftLeft 1 3072).testBit n = true →
        ∃ g ∈ gammaU, g (vecOf 3072) = vecOf n := by
      intro n hn
      simp only [Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow,
        decide_eq_true_eq] at hn
      rw [← hn]
      exact ⟨1, one_mem _, rfl⟩
    obtain ⟨g, hg, hgx⟩ := treeW_spec hGG TR (Nat.shiftLeft 1 3072) htree hinit _ hbit
    exact ⟨g, hg, by rw [← hvn]; exact hgx⟩
  ·
    obtain ⟨U, hUP, -⟩ := exists_of_guOK hTH (hSGc (packR r) (List.mem_map_of_mem hr)).1
    exact ⟨U, (isP_packR (hrows' r hr) U).1 hUP⟩
  ·
    have hN2 := fun ri hri y hy hya hyD =>
      nb_rep hSA hrep hrecs (ri := ri) hri (y := y) hy hya hyD
    have h0 : InS dReps (spanOf (nthD [] dReps 0)) :=
      ⟨0, by norm_num, 1, Submonoid.one_mem _, (map_one_eq _).symm⟩
    obtain ⟨ri, hri, h, hh, hD⟩ := reach hMg hrep hN2 6 _ D h0 ⟨hD, h6, ha⟩ (by omega)
    exact ⟨nthD [] dReps ri, nthD_mem [] (by rw [← lenN_eq]; exact hri), h, hh, hD⟩

end CFSG.KC.GUO

end
