module

public import CFSG.ClassicalInvolution.Q3.Sec13End12
import CFSG.ClassicalInvolution.Q3.Sec13End15A
import CFSG.ClassicalInvolution.Q3.Sec13EndDETwin
import CFSG.ClassicalInvolution.Q3.Sec13PerpA3
import CFSG.ClassicalInvolution.Q3.TL3T25
import CFSG.ClassicalInvolution.Q3.TL3T28
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.ClassicalInvolution.Asc77.AscE18FromM
public import CFSG.ClassicalInvolution.Asc77.AscFusionR7
public import CFSG.ClassicalInvolution.Asc77.AscP1SevenTwelve
public import CFSG.ClassicalInvolution.Asc77.AscT7AFinal
public import CFSG.ClassicalInvolution.Asc77.AscT7ASectD
public import CFSG.ClassicalInvolution.Asc77.AscT7CFinal
public import CFSG.ClassicalInvolution.Asc77.AscT7EFinal3
public import CFSG.ClassicalInvolution.Asc77.AscT7FJ
public import CFSG.ClassicalInvolution.Asc77.AscT7HFinal
public import CFSG.ClassicalInvolution.Asc77.AscT7QFinal
public import CFSG.ClassicalInvolution.Asc77.WP2Branch
public import CFSG.ClassicalInvolution.AschTight.S1916F2a
public import CFSG.ClassicalInvolution.Q3.OddCoreCentral
public import CFSG.ClassicalInvolution.Q3.Q3CPOmega
public import CFSG.ClassicalInvolution.Q3.Q3T7E9Comp
public import CFSG.ClassicalInvolution.Q3.Q3T7E9Main
public import CFSG.ClassicalInvolution.Q3.Q3T7LayerQ
public import CFSG.ClassicalInvolution.Q3.Q3T8Std8
public import CFSG.ClassicalInvolution.Q3.Q3TIMain
public import CFSG.ClassicalInvolution.Q3.Q3TIYOAMain
public import CFSG.ClassicalInvolution.Q3.Q3TKMem
public import CFSG.ClassicalInvolution.Q3.Q3WAEDict
public import CFSG.ClassicalInvolution.Q3.Q3WMain
public import CFSG.ClassicalInvolution.Q3.Q3ZFraStd
public import CFSG.ClassicalInvolution.Q3.RankThreeBootstrap
public import CFSG.ClassicalInvolution.Q3.Sec13StarBasic
public import CFSG.ClassicalInvolution.SmallCases.NobqFinal
public import CFSG.ClassicalInvolution.Uniform.U3IH8
public import CFSG.ClassicalInvolution.Uniform.U4Basic
public import CFSG.Sporadic.J4.QT2LocProof
import CFSG.ClassicalInvolution.Q3.Sec13PerpD
import CFSG.ClassicalInvolution.Q3.TL4D1Facts
import CFSG.ClassicalInvolution.Q3.TL4D1ML32B

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G]

namespace End18

private theorem e18a_sq {K : Subgroup G} {z i j : G} (hQ : Q8Data K z i j) {x : G}
    (hx : x ∈ K) : x * x ∈ Subgroup.zpowers z := by
  rcases det_tw_sq_mem hQ hx with h | h
  · rw [h]
    exact Subgroup.one_mem _
  · rw [h]
    exact Subgroup.mem_zpowers z

private theorem e18a_comm {K : Subgroup G} {z i j : G} (hQ : Q8Data K z i j) {a b : G}
    (ha : a ∈ K) (hb : b ∈ K) : a * b * a⁻¹ * b⁻¹ ∈ Subgroup.zpowers z := by
  have hzz : z * z = 1 := hQ.inv.sq
  rcases det_tw_comm_mod hQ ha hb with h | h
  · have h1 : a * b * a⁻¹ * b⁻¹ = 1 := by
      rw [← h]
      group
    rw [h1]
    exact Subgroup.one_mem _
  · have h1 : a * b = z * (b * a) := by
      calc a * b = z * (z * (a * b)) := by rw [← mul_assoc, hzz, one_mul]
        _ = z * (b * a) := by rw [h]
    have h2 : a * b * a⁻¹ * b⁻¹ = z := by
      rw [h1]
      group
    rw [h2]
    exact Subgroup.mem_zpowers z

private theorem e18a_cent {K : Subgroup G} {z i j : G} (hQ : Q8Data K z i j) {x : G}
    (hx : x ∈ K) (hc : ∀ y ∈ K, x * y = y * x) : x ∈ Subgroup.zpowers z := by
  by_contra hxz
  obtain ⟨w, hw, hne⟩ := det_tw_q8_noncomm hQ hx hxz
  exact hne (hc w hw)

private theorem e18a_zc {K : Subgroup G} {z i j : G} (hQ : Q8Data K z i j) {x : G}
    (hx : x ∈ K) : z * x = x * z :=
  det_tw_q8_central hQ hx

private theorem e18a_card_zpowers {z : G} (hzz : z * z = 1) (hz1 : z ≠ 1) :
    Nat.card ↥(Subgroup.zpowers z) = 2 := by
  rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hzz) hz1]

private def e18a_Good (X : Subgroup G) (z : G) : Prop :=
  z ∈ X ∧ (∀ x ∈ X, x * x ∈ Subgroup.zpowers z) ∧
    (∀ x ∈ X, ∀ y ∈ X, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.zpowers z) ∧
    (∀ x ∈ X, z * x = x * z) ∧ (∀ x ∈ X, (∀ y ∈ X, x * y = y * x) → x ∈ Subgroup.zpowers z)

private theorem e18a_base {K : Subgroup G} {z i j : G} (hQ : Q8Data K z i j) :
    e18a_Good K z :=
  ⟨hQ.inv.mem, fun x hx => e18a_sq hQ hx, fun x hx y hy => e18a_comm hQ hx hy,
    fun x hx => e18a_zc hQ hx, fun x hx hc => e18a_cent hQ hx hc⟩

private theorem e18a_mem_sup {X K : Subgroup G} (hXK : ∀ a ∈ X, ∀ k ∈ K, a * k = k * a)
    {y : G} (hy : y ∈ X ⊔ K) : ∃ a ∈ X, ∃ k ∈ K, y = a * k := by
  rw [Subgroup.sup_eq_closure] at hy
  induction hy using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, 1, K.one_mem, (mul_one x).symm⟩
    · exact ⟨1, X.one_mem, x, hx, (one_mul x).symm⟩
  | one => exact ⟨1, X.one_mem, 1, K.one_mem, (mul_one 1).symm⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha, k, hk, rfl⟩ := hx
    obtain ⟨a', ha', k', hk', rfl⟩ := hy
    refine ⟨a * a', X.mul_mem ha ha', k * k', K.mul_mem hk hk', ?_⟩
    calc a * k * (a' * k') = a * (k * a') * k' := by group
      _ = a * (a' * k) * k' := by rw [← hXK a' ha' k hk]
      _ = a * a' * (k * k') := by group
  | inv x _ hx =>
    obtain ⟨a, ha, k, hk, rfl⟩ := hx
    refine ⟨a⁻¹, X.inv_mem ha, k⁻¹, K.inv_mem hk, ?_⟩
    rw [hXK a ha k hk, mul_inv_rev]

private theorem e18a_comm_prod {K : Subgroup G} {a a' k k' : G}
    (ha : ∀ x ∈ K, a * x = x * a) (ha' : ∀ x ∈ K, a' * x = x * a')
    (hk : k ∈ K) (hk' : k' ∈ K) :
    a * k * (a' * k') * (a * k)⁻¹ * (a' * k')⁻¹ =
      (a * a' * a⁻¹ * a'⁻¹) * (k * k' * k⁻¹ * k'⁻¹) := by
  have hA : ∀ w ∈ K, w * a⁻¹ = a⁻¹ * w := by
    intro w hw
    have h := ha w hw
    calc w * a⁻¹ = a⁻¹ * (a * w) * a⁻¹ := by group
      _ = a⁻¹ * (w * a) * a⁻¹ := by rw [h]
      _ = a⁻¹ * w := by group
  have hA' : ∀ w ∈ K, w * a'⁻¹ = a'⁻¹ * w := by
    intro w hw
    have h := ha' w hw
    calc w * a'⁻¹ = a'⁻¹ * (a' * w) * a'⁻¹ := by group
      _ = a'⁻¹ * (w * a') * a'⁻¹ := by rw [h]
      _ = a'⁻¹ * w := by group
  have hk1 : k * a' = a' * k := (ha' k hk).symm
  have hw : k * k' * k⁻¹ ∈ K := K.mul_mem (K.mul_mem hk hk') (K.inv_mem hk)
  have hy : k * k' * k⁻¹ * k'⁻¹ ∈ K := K.mul_mem hw (K.inv_mem hk')
  calc a * k * (a' * k') * (a * k)⁻¹ * (a' * k')⁻¹
      = a * (k * a') * k' * k⁻¹ * a⁻¹ * k'⁻¹ * a'⁻¹ := by group
    _ = a * (a' * k) * k' * k⁻¹ * a⁻¹ * k'⁻¹ * a'⁻¹ := by rw [hk1]
    _ = a * a' * ((k * k' * k⁻¹) * a⁻¹) * k'⁻¹ * a'⁻¹ := by group
    _ = a * a' * (a⁻¹ * (k * k' * k⁻¹)) * k'⁻¹ * a'⁻¹ := by rw [hA _ hw]
    _ = a * a' * a⁻¹ * ((k * k' * k⁻¹ * k'⁻¹) * a'⁻¹) := by group
    _ = a * a' * a⁻¹ * (a'⁻¹ * (k * k' * k⁻¹ * k'⁻¹)) := by rw [hA' _ hy]
    _ = (a * a' * a⁻¹ * a'⁻¹) * (k * k' * k⁻¹ * k'⁻¹) := by group

private theorem e18a_inf {X K : Subgroup G} {z i j : G} (hQ : Q8Data K z i j) (hzX : z ∈ X)
    (hXK : ∀ a ∈ X, ∀ k ∈ K, a * k = k * a) : X ⊓ K = Subgroup.zpowers z := by
  apply le_antisymm
  · intro x hx
    exact e18a_cent hQ hx.2 (fun y hy => hXK x hx.1 y hy)
  · exact Subgroup.zpowers_le.mpr ⟨hzX, hQ.inv.mem⟩

private theorem e18a_chain {X K : Subgroup G} {z i j : G} (hX : e18a_Good X z)
    (hQ : Q8Data K z i j) (hK8 : Nat.card K = 8) (hzz : z * z = 1) (hz1 : z ≠ 1)
    (hXK : ∀ a ∈ X, ∀ k ∈ K, a * k = k * a) :
    e18a_Good (X ⊔ K) z ∧ Nat.card ↥(X ⊔ K) = 4 * Nat.card ↥X := by
  obtain ⟨hzX, hXsq, hXcomm, hXzc, hXcen⟩ := hX
  have hinf := e18a_inf hQ hzX hXK
  have hXN : X ≤ Subgroup.normalizer (K : Set G) :=
    Asc77.AscL62.le_normalizer_of_commutes
      (show Commutes X K from fun x hx y hy => hXK x hx y hy)
  have hcard : Nat.card ↥(X ⊔ K) * Nat.card ↥(X ⊓ K) = Nat.card ↥X * Nat.card ↥K :=
    Sec6Gen.card_sup_mul_card_inf_of_le_normalizer hXN
  rw [hinf, e18a_card_zpowers hzz hz1, hK8] at hcard
  refine ⟨⟨Subgroup.mem_sup_left hzX, ?_, ?_, ?_, ?_⟩, by omega⟩
  · intro x hx
    obtain ⟨a, ha, k, hk, rfl⟩ := e18a_mem_sup hXK hx
    have e : a * k * (a * k) = (a * a) * (k * k) := by
      have hka : k * a = a * k := (hXK a ha k hk).symm
      calc a * k * (a * k) = a * (k * a) * k := by group
        _ = a * (a * k) * k := by rw [hka]
        _ = (a * a) * (k * k) := by group
    rw [e]
    exact (Subgroup.zpowers z).mul_mem (hXsq a ha) (e18a_sq hQ hk)
  · intro x hx y hy
    obtain ⟨a, ha, k, hk, rfl⟩ := e18a_mem_sup hXK hx
    obtain ⟨a', ha', k', hk', rfl⟩ := e18a_mem_sup hXK hy
    rw [e18a_comm_prod (hXK a ha) (hXK a' ha') hk hk']
    exact (Subgroup.zpowers z).mul_mem (hXcomm a ha a' ha') (e18a_comm hQ hk hk')
  · intro x hx
    obtain ⟨a, ha, k, hk, rfl⟩ := e18a_mem_sup hXK hx
    calc z * (a * k) = (z * a) * k := by group
      _ = (a * z) * k := by rw [hXzc a ha]
      _ = a * (z * k) := by group
      _ = a * (k * z) := by rw [e18a_zc hQ hk]
      _ = a * k * z := by group
  · intro x hx hc
    obtain ⟨a, ha, k, hk, rfl⟩ := e18a_mem_sup hXK hx
    have hkc : k ∈ Subgroup.zpowers z := by
      apply e18a_cent hQ hk
      intro k' hk'
      have hK'a : k' * a = a * k' := (hXK a ha k' hk').symm
      have h1 : a * (k * k') = a * (k' * k) := by
        calc a * (k * k') = a * k * k' := by group
          _ = k' * (a * k) := hc k' (Subgroup.mem_sup_right hk')
          _ = (k' * a) * k := by group
          _ = (a * k') * k := by rw [hK'a]
          _ = a * (k' * k) := by group
      exact mul_left_cancel h1
    have hkX : k ∈ X := (Subgroup.zpowers_le.mpr hzX) hkc
    exact hXcen (a * k) (X.mul_mem ha hkX) (fun y hy => hc y (Subgroup.mem_sup_left hy))

private theorem e18a_sup_comm {A B K : Subgroup G} (hA : ∀ x ∈ A, ∀ k ∈ K, x * k = k * x)
    (hB : ∀ x ∈ B, ∀ k ∈ K, x * k = k * x) : ∀ x ∈ A ⊔ B, ∀ k ∈ K, x * k = k * x := by
  have hle : A ⊔ B ≤ Subgroup.centralizer (K : Set G) :=
    sup_le (fun x hx => Subgroup.mem_centralizer_iff.mpr fun k hk => (hA x hx k hk).symm)
      (fun x hx => Subgroup.mem_centralizer_iff.mpr fun k hk => (hB x hx k hk).symm)
  intro x hx k hk
  exact (Subgroup.mem_centralizer_iff.mp (hle hx) k hk).symm

private theorem e18a_iso_finrank {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    {β : LinearMap.BilinForm (ZMod 2) V} (hβ : β.Nondegenerate) {n : ℕ}
    (hV : Module.finrank (ZMod 2) V = 2 * n)
    (W : Submodule (ZMod 2) V) (hW : ∀ x ∈ W, ∀ y ∈ W, β x y = 0) :
    Module.finrank (ZMod 2) W ≤ n := by
  have h1 : W ≤ β.orthogonal W := fun x hx => by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    exact fun m hm => hW m hm x hx
  have h2 := Submodule.finrank_mono h1
  have h3 := LinearMap.BilinForm.finrank_orthogonal hβ W
  omega

private theorem e18a_bound {A : Type} [CommGroup A] [Finite A] {n : ℕ}
    (c : A → A → ZMod 2) (hL : ∀ a b d : A, c (a * b) d = c a d + c b d)
    (hsymm : ∀ a b : A, c a b = c b a) (hsq : ∀ a : A, a * a = 1)
    (hnd : ∀ a : A, (∀ b : A, c a b = 0) → a = 1)
    (hcard : Nat.card A = 2 ^ (2 * n)) (S : Subgroup A)
    (hS : ∀ a ∈ S, ∀ b ∈ S, c a b = 0) : Nat.card S ≤ 2 ^ n := by
  have h2 : ∀ x : Additive A, (2 : ℕ) • x = 0 := by
    intro x
    have e : (2 : ℕ) • x = Additive.ofMul (Additive.toMul x * Additive.toMul x) := by
      rw [two_nsmul]
      rfl
    rw [e, hsq]
    rfl
  letI : Module (ZMod 2) (Additive A) := AddCommGroup.zmodModule (n := 2) h2
  haveI : Finite (Additive A) := ‹Finite A›
  haveI : FiniteDimensional (ZMod 2) (Additive A) := inferInstance
  have hc1 : ∀ d : A, c 1 d = 0 := by
    intro d
    have h := hL 1 1 d
    rw [mul_one] at h
    have key : ∀ x : ZMod 2, x = x + x → x = 0 := by decide
    exact key _ (by simpa using h)
  have hc1' : ∀ d : A, c d 1 = 0 := fun d => by rw [hsymm]; exact hc1 d
  have hr : ∀ r : ZMod 2, r = 0 ∨ r = 1 := by decide
  let f : Additive A → Additive A → ZMod 2 :=
    fun x y => c (Additive.toMul x) (Additive.toMul y)
  let β : LinearMap.BilinForm (ZMod 2) (Additive A) :=
    LinearMap.mk₂ (ZMod 2) f
      (fun x y z => hL _ _ _)
      (fun r x y => by
        rcases hr r with rfl | rfl
        · simp [f, hc1]
        · simp [f])
      (fun x y z => by
        show c _ (Additive.toMul y * Additive.toMul z) = c _ _ + c _ _
        rw [hsymm, hL, hsymm (Additive.toMul y), hsymm (Additive.toMul z)])
      (fun r x y => by
        rcases hr r with rfl | rfl
        · simp [f, hc1']
        · simp [f])
  have hβ : ∀ x y : Additive A, β x y = c (Additive.toMul x) (Additive.toMul y) :=
    fun x y => rfl
  have hnd' : β.Nondegenerate := by
    refine ⟨fun x hx => ?_, fun y hy => ?_⟩
    · have h := hnd (Additive.toMul x) (fun b => by
        have := hx (Additive.ofMul b)
        rw [hβ] at this
        exact this)
      exact Additive.toMul.injective (h.trans rfl)
    · have h := hnd (Additive.toMul y) (fun b => by
        have := hy (Additive.ofMul b)
        rw [hβ, hsymm] at this
        exact this)
      exact Additive.toMul.injective (h.trans rfl)
  have hcardV : Nat.card (Additive A) = Nat.card A := Nat.card_congr Additive.ofMul.symm
  have hfin : Module.finrank (ZMod 2) (Additive A) = 2 * n := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive A)
    rw [Nat.card_zmod, hcardV, hcard] at h
    exact (Nat.pow_right_injective (le_refl 2) h).symm
  let W : Submodule (ZMod 2) (Additive A) :=
    { carrier := {x | Additive.toMul x ∈ S}
      add_mem' := fun {x y} hx hy => S.mul_mem hx hy
      zero_mem' := S.one_mem
      smul_mem' := fun r x hx => by
        show Additive.toMul (r • x) ∈ S
        rcases hr r with rfl | rfl
        · rw [zero_smul]
          exact S.one_mem
        · rw [one_smul]
          exact hx }
  have hWiso : ∀ x ∈ W, ∀ y ∈ W, β x y = 0 := fun x hx y hy => hS _ hx _ hy
  have hWn := e18a_iso_finrank hnd' hfin W hWiso
  have hinj : Function.Injective (fun s : S => (⟨Additive.ofMul s.1, s.2⟩ : W)) := by
    intro s t hst
    have := congrArg Subtype.val hst
    exact Subtype.ext (by simpa using this)
  have h1 := Nat.card_le_card_of_injective _ hinj
  have h2' : Nat.card W = 2 ^ Module.finrank (ZMod 2) W := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W)
    rwa [Nat.card_zmod] at h
  calc Nat.card S ≤ Nat.card W := h1
    _ = 2 ^ Module.finrank (ZMod 2) W := h2'
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hWn
open Classical in
private noncomputable def e18a_cfun {H : Type} [Group H] (a b : H) : ZMod 2 :=
  if a * b = b * a then 0 else 1

private theorem e18a_cfun_comm {H : Type} [Group H] (a b : H) : e18a_cfun a b = e18a_cfun b a := by
  unfold e18a_cfun
  by_cases h : a * b = b * a
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun h' => h h'.symm)]

private theorem e18a_cfun_eq_zero {H : Type} [Group H] {a b : H} (h : a * b = b * a) :
    e18a_cfun a b = 0 := by
  unfold e18a_cfun; rw [if_pos h]

private theorem e18a_cfun_eq_one {H : Type} [Group H] {a b : H} (h : a * b ≠ b * a) :
    e18a_cfun a b = 1 := by
  unfold e18a_cfun; rw [if_neg h]

private theorem e18a_cfun_mul_central {H : Type} [Group H] {n : H}
    (hn : ∀ x : H, n * x = x * n) (a b : H) :
    e18a_cfun (a * n) b = e18a_cfun a b ∧ e18a_cfun a (b * n) = e18a_cfun a b := by
  constructor
  · by_cases h : a * b = b * a
    · have h' : a * n * b = b * (a * n) := by
        have e1 : a * n * b = a * b * n := by rw [mul_assoc, hn b, ← mul_assoc]
        have e2 : b * (a * n) = b * a * n := by rw [mul_assoc]
        rw [e1, e2, h]
      rw [e18a_cfun_eq_zero h, e18a_cfun_eq_zero h']
    · have h' : a * n * b ≠ b * (a * n) := by
        intro h''
        apply h
        have e1 : a * n * b = a * b * n := by rw [mul_assoc, hn b, ← mul_assoc]
        have e2 : b * (a * n) = b * a * n := by rw [mul_assoc]
        rw [e1, e2] at h''
        exact mul_right_cancel h''
      rw [e18a_cfun_eq_one h, e18a_cfun_eq_one h']
  · by_cases h : a * b = b * a
    · have h' : a * (b * n) = b * n * a := by
        have e1 : a * (b * n) = a * b * n := by rw [mul_assoc]
        have e2 : b * n * a = b * a * n := by rw [mul_assoc, hn a, ← mul_assoc]
        rw [e1, e2, h]
      rw [e18a_cfun_eq_zero h, e18a_cfun_eq_zero h']
    · have h' : a * (b * n) ≠ b * n * a := by
        intro h''
        apply h
        have e1 : a * (b * n) = a * b * n := by rw [mul_assoc]
        have e2 : b * n * a = b * a * n := by rw [mul_assoc, hn a, ← mul_assoc]
        rw [e1, e2] at h''
        exact mul_right_cancel h''
      rw [e18a_cfun_eq_one h, e18a_cfun_eq_one h']

private theorem e18a_split {H : Type} [Group H] {z x d : H} (hz1 : z ≠ 1)
    (hx : x * d * x⁻¹ * d⁻¹ = 1 ∨ x * d * x⁻¹ * d⁻¹ = z) :
    x * d = d * x ∨ x * d = z * (d * x) := by
  rcases hx with h | h
  · left
    calc x * d = (x * d * x⁻¹ * d⁻¹) * (d * x) := by group
      _ = 1 * (d * x) := by rw [h]
      _ = d * x := one_mul _
  · right
    calc x * d = (x * d * x⁻¹ * d⁻¹) * (d * x) := by group
      _ = z * (d * x) := by rw [h]

private theorem e18a_ne_of_split {H : Type} [Group H] {z x d : H} (hz1 : z ≠ 1)
    (h : x * d = z * (d * x)) : x * d ≠ d * x := by
  intro h'
  apply hz1
  have : z * (d * x) = 1 * (d * x) := by rw [one_mul, ← h, h']
  exact mul_right_cancel this

private theorem e18a_cfun_mul {H : Type} [Group H] {z a b d : H} (hz1 : z ≠ 1) (hzz : z * z = 1)
    (hza : a * z = z * a)
    (ha : a * d * a⁻¹ * d⁻¹ = 1 ∨ a * d * a⁻¹ * d⁻¹ = z)
    (hb : b * d * b⁻¹ * d⁻¹ = 1 ∨ b * d * b⁻¹ * d⁻¹ = z) :
    e18a_cfun (a * b) d = e18a_cfun a d + e18a_cfun b d := by
  rcases e18a_split hz1 ha with ha' | ha' <;>
    rcases e18a_split hz1 hb with hb' | hb'
  · have hab : (a * b) * d = d * (a * b) := by
      calc a * b * d = a * (b * d) := by group
        _ = a * (d * b) := by rw [hb']
        _ = (a * d) * b := by group
        _ = (d * a) * b := by rw [ha']
        _ = d * (a * b) := by group
    rw [e18a_cfun_eq_zero hab, e18a_cfun_eq_zero ha', e18a_cfun_eq_zero hb']
    rfl
  · have e : a * b * d = z * (d * (a * b)) := by
      calc a * b * d = a * (b * d) := by group
        _ = a * (z * (d * b)) := by rw [hb']
        _ = z * (a * (d * b)) := by rw [← mul_assoc, hza, mul_assoc]
        _ = z * ((a * d) * b) := by group
        _ = z * ((d * a) * b) := by rw [ha']
        _ = z * (d * (a * b)) := by group
    have hab : (a * b) * d ≠ d * (a * b) := by
      rw [e]
      intro h
      apply hz1
      have : z * (d * (a * b)) = 1 * (d * (a * b)) := by rw [one_mul]; exact h
      exact mul_right_cancel this
    rw [e18a_cfun_eq_one hab, e18a_cfun_eq_zero ha', e18a_cfun_eq_one (e18a_ne_of_split hz1 hb')]
    rfl
  · have e : a * b * d = z * (d * (a * b)) := by
      calc a * b * d = a * (b * d) := by group
        _ = a * (d * b) := by rw [hb']
        _ = (a * d) * b := by group
        _ = (z * (d * a)) * b := by rw [ha']
        _ = z * (d * (a * b)) := by group
    have hab : (a * b) * d ≠ d * (a * b) := by
      rw [e]
      intro h
      apply hz1
      have : z * (d * (a * b)) = 1 * (d * (a * b)) := by rw [one_mul]; exact h
      exact mul_right_cancel this
    rw [e18a_cfun_eq_one hab, e18a_cfun_eq_one (e18a_ne_of_split hz1 ha'), e18a_cfun_eq_zero hb']
    rfl
  · have hab : (a * b) * d = d * (a * b) := by
      calc a * b * d = a * (b * d) := by group
        _ = a * (z * (d * b)) := by rw [hb']
        _ = z * (a * (d * b)) := by rw [← mul_assoc, hza, mul_assoc]
        _ = z * ((a * d) * b) := by group
        _ = z * ((z * (d * a)) * b) := by rw [ha']
        _ = (z * z) * (d * (a * b)) := by group
        _ = d * (a * b) := by rw [hzz, one_mul]
    rw [e18a_cfun_eq_zero hab, e18a_cfun_eq_one (e18a_ne_of_split hz1 ha'),
      e18a_cfun_eq_one (e18a_ne_of_split hz1 hb')]
    decide

private theorem e18a_x_eq_one_or {z : G} (hzz : z * z = 1) (hz1 : z ≠ 1) {x : G}
    (hx : x ∈ Subgroup.zpowers z) : x = 1 ∨ x = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have ho : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hzz) hz1
  rw [← zpow_mod_orderOf, ho]
  rcases Int.emod_two_eq_zero_or_one k with hk | hk <;> simp [hk]

open scoped IsMulCommutative in
private theorem e18a_group_bound {X : Subgroup G} {z : G}
    (hzz : z * z = 1) (hz1 : z ≠ 1) (hzX : z ∈ X)
    (hsq : ∀ x ∈ X, x * x ∈ Subgroup.zpowers z)
    (hcomm : ∀ x ∈ X, ∀ y ∈ X, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.zpowers z)
    (hzc : ∀ x ∈ X, z * x = x * z)
    (hcen : ∀ x ∈ X, (∀ y ∈ X, x * y = y * x) → x ∈ Subgroup.zpowers z)
    {n : ℕ} (hcard : Nat.card X = 2 ^ (2 * n + 1))
    {B : Subgroup G} (hB : B ≤ X) (hab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) :
    Nat.card B ≤ 2 ^ (n + 1) := by
  classical
  obtain ⟨zX, hzXdef⟩ : ∃ zX : X, (zX : G) = z := ⟨⟨z, hzX⟩, rfl⟩
  have hzX2 : zX * zX = 1 := Subtype.ext (by rw [Subgroup.coe_mul, hzXdef, hzz, Subgroup.coe_one])
  have hzX1 : zX ≠ 1 := fun h => hz1 (by rw [← hzXdef, h, Subgroup.coe_one])
  obtain ⟨N, hN⟩ : ∃ N : Subgroup X, N = Subgroup.zpowers zX := ⟨_, rfl⟩
  have hmemN : ∀ a : X, a ∈ N ↔ (a : G) ∈ Subgroup.zpowers z := by
    intro a
    rw [hN]
    constructor
    · intro ha
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ha
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      rw [← hk, Subgroup.coe_zpow, hzXdef]
    · intro ha
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ha
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext ?_⟩
      rw [Subgroup.coe_zpow, hzXdef, hk]
  have hzcen : ∀ a : X, zX * a = a * zX := by
    intro a
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hzXdef]
    exact hzc a a.2
  have hNc : N ≤ Subgroup.center X := by
    rw [hN, Subgroup.zpowers_le]
    exact Subgroup.mem_center_iff.mpr (fun g => (hzcen g).symm)
  have hNcomm : ∀ m ∈ N, ∀ x : X, m * x = x * m := fun m hm x =>
    ((Subgroup.mem_center_iff.mp (hNc hm)) x).symm
  haveI : N.Normal := Subgroup.normal_of_le_center hNc
  have hcomm' : _root_.commutator X ≤ N := by
    rw [commutator_def, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    rw [hmemN, commutatorElement_def]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact hcomm g₁ g₁.2 g₂ g₂.2
  haveI : IsMulCommutative (X ⧸ N) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcomm'
  have key : ∀ a a' b b' : X, a⁻¹ * a' ∈ N → b⁻¹ * b' ∈ N → e18a_cfun a b = e18a_cfun a' b' := by
    intro a a' b b' ha hb
    have ea : a' = a * (a⁻¹ * a') := by group
    have eb : b' = b * (b⁻¹ * b') := by group
    rw [ea, eb, (e18a_cfun_mul_central (hNcomm _ ha) a (b * (b⁻¹ * b'))).1,
      (e18a_cfun_mul_central (hNcomm _ hb) a b).2]
  let c : X ⧸ N → X ⧸ N → ZMod 2 := fun p q =>
    Quotient.liftOn₂' p q (fun a b => e18a_cfun a b) (fun a₁ b₁ a₂ b₂ ha hb =>
      key a₁ a₂ b₁ b₂ (QuotientGroup.leftRel_apply.mp ha) (QuotientGroup.leftRel_apply.mp hb))

  have hc : ∀ a b : X, c (a : X ⧸ N) (b : X ⧸ N) = e18a_cfun a b := fun a b => rfl
  have hcommX : ∀ a d : X, a * d * a⁻¹ * d⁻¹ = 1 ∨ a * d * a⁻¹ * d⁻¹ = zX := by
    intro a d
    have hm : a * d * a⁻¹ * d⁻¹ ∈ N := by
      rw [hmemN]
      have := hcomm a a.2 d d.2
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using this
    rw [hN] at hm
    exact e18a_x_eq_one_or hzX2 hzX1 hm
  have hzaX : ∀ a : X, a * zX = zX * a := fun a => (hzcen a).symm
  have hL : ∀ p q r : X ⧸ N, c (p * q) r = c p r + c q r := by
    intro p q r
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective p
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective r
    rw [← QuotientGroup.mk_mul, hc, hc, hc]
    exact e18a_cfun_mul hzX1 hzX2 (hzaX a) (hcommX a d) (hcommX b d)
  have hsymm' : ∀ p q : X ⧸ N, c p q = c q p := by
    intro p q
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective p
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hc, hc, e18a_cfun_comm]
  have hsq' : ∀ p : X ⧸ N, p * p = 1 := by
    intro p
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective p
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, hmemN]
    simpa only [Subgroup.coe_mul] using hsq a a.2
  have hnd' : ∀ p : X ⧸ N, (∀ q : X ⧸ N, c p q = 0) → p = 1 := by
    intro p hp
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective p
    rw [QuotientGroup.eq_one_iff]
    apply (hmemN a).mpr
    apply hcen a a.2
    intro y hy
    have h0 := hp (QuotientGroup.mk ⟨y, hy⟩)
    rw [hc] at h0
    have h1 : a * (⟨y, hy⟩ : X) = (⟨y, hy⟩ : X) * a := by
      by_contra hne
      rw [e18a_cfun_eq_one hne] at h0
      exact one_ne_zero h0
    have h2 := congrArg Subtype.val h1
    simpa only [Subgroup.coe_mul] using h2
  have hcardA : Nat.card (X ⧸ N) = 2 ^ (2 * n) := by
    have hN2 : Nat.card N = 2 := by
      rw [hN, Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hzX2) hzX1]
    have hsplit := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [hcard, hN2] at hsplit
    have h2 : Nat.card (X ⧸ N) * 2 = 2 ^ (2 * n) * 2 := by
      rw [← hsplit, pow_succ]
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h2
  let φ : (B.subgroupOf X) →* X ⧸ N := (QuotientGroup.mk' N).comp (B.subgroupOf X).subtype
  have hS : Nat.card φ.range ≤ 2 ^ n := by
    refine e18a_bound c hL hsymm' hsq' hnd' hcardA φ.range ?_
    intro a ha b hb
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp ha
    obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hb
    have hx : ((x : B.subgroupOf X) : G) ∈ B := (Subgroup.mem_subgroupOf).mp x.2
    have hy : ((y : B.subgroupOf X) : G) ∈ B := (Subgroup.mem_subgroupOf).mp y.2
    have e1 : φ x = QuotientGroup.mk ((x : B.subgroupOf X) : X) := rfl
    have e2 : φ y = QuotientGroup.mk ((y : B.subgroupOf X) : X) := rfl
    rw [e1, e2, hc]
    apply e18a_cfun_eq_zero
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact hab _ hx _ hy
  have hker : Nat.card φ.ker ≤ 2 := by
    have hN2 : Nat.card N = 2 := by
      rw [hN, Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hzX2) hzX1]
    rw [← hN2]
    refine Nat.card_le_card_of_injective (fun x : φ.ker =>
      (⟨((x.1 : B.subgroupOf X) : X), ?_⟩ : N)) ?_
    · have hx := MonoidHom.mem_ker.mp x.2
      have h1 : QuotientGroup.mk ((x.1 : B.subgroupOf X) : X) = (1 : X ⧸ N) := hx
      rw [QuotientGroup.eq_one_iff] at h1
      exact h1
    · intro s t hst
      have h1 : ((s.1 : B.subgroupOf X) : X) = ((t.1 : B.subgroupOf X) : X) := by
        have h2 := congrArg (fun u : N => (u : X)) hst
        exact h2
      exact Subtype.val_injective (Subtype.val_injective h1)
  have hsplit2 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  have hq : Nat.card (B.subgroupOf X ⧸ φ.ker) = Nat.card φ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
  have hBB : Nat.card (B.subgroupOf X) = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB).toEquiv
  calc Nat.card B = Nat.card (B.subgroupOf X) := hBB.symm
    _ = Nat.card φ.range * Nat.card φ.ker := by rw [hsplit2, hq]
    _ ≤ 2 ^ n * 2 := Nat.mul_le_mul hS hker
    _ = 2 ^ (n + 1) := by ring

private theorem e18a_q8 {Ω : Set (Subgroup G)} (h : EndHyp Ω) {L : Subgroup G} (hL : L ∈ Ω)
    {z : G} (hz : IsUniqueInvolution L z) : ∃ i j : G, Q8Data L z i j := by
  obtain ⟨i, j, hi, hj, hii, hjj, hji, hNF⟩ :=
    exists_q8_gen hz (Sec6Gen.isQuatSub_of_mem_RSet h.thmD.hyp
      (TC.mem_RSet_of_isPGroup hL (h.thmD.two L hL))) (h.card_eq_eight hL)
  exact ⟨i, j, hz, hi, hj, hii, hjj, hji, hNF⟩

private theorem e18a_mem_of_USet {Ω : Set (Subgroup G)} (h : EndHyp Ω) {L : Subgroup G}
    (hL : L ∈ Ω) {z : G} (hz : IsUniqueInvolution L z) {U : Subgroup G} (hU : U ∈ USet Ω)
    (hUL : U ≤ L) : z ∈ U := by
  obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := Sec6Gen.exists_data_of_mem_USet h.thmD.hyp hU
  have hdvd : Nat.card U ∣ 8 := by
    rw [← h.card_eq_eight hL]
    exact Subgroup.card_dvd_of_le hUL
  have h2 : 2 ∣ Nat.card U := by
    obtain ⟨m, hm⟩ : ∃ m, Nat.card U = m := ⟨_, rfl⟩
    rw [hm] at hdvd h4 ⊢
    have hle : m ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases m <;> omega
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := U) 2 h2
  have hy2 : y ^ 2 = 1 := by
    rw [← hy]
    exact pow_orderOf_eq_one y
  have hy1 : y ≠ 1 := by
    intro e
    rw [e, orderOf_one] at hy
    norm_num at hy
  have hyG : ((y : U) : G) * ((y : U) : G) = 1 := by
    have h' := congrArg Subtype.val hy2
    rw [pow_two] at h'
    simpa only [Subgroup.coe_mul, Subgroup.coe_one] using h'
  have hyL : ((y : U) : G) ∈ L := hUL y.2
  have hyne : ((y : U) : G) ≠ 1 := fun e => hy1 (Subtype.ext e)
  rcases hz.unique _ hyL hyG with e | e
  · exact absurd e hyne
  · rw [← e]
    exact y.2

private theorem e18a_exists_W {Ω : Set (Subgroup G)} (h : EndHyp Ω) {K : Subgroup G}
    (hK : K ∈ Ω) : ∃ W ∈ WSet Ω, ∀ J ∈ twinSet Ω K, J ∈ DSet Ω W := by
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution h.thmD.hyp hK
  obtain ⟨S, hKS⟩ := (h.thmD.two K hK).exists_le_sylow
  obtain ⟨η, hη, -, -, hKη⟩ := h.exists_wSet_of_le hK S hKS
  have hWS : (⨆ V ∈ η, V) ∈ WSet Ω := ⟨η, hη, rfl⟩
  obtain ⟨S', hS', -⟩ := hη
  have hKU : K ⊓ (⨆ V ∈ η, V) ∈ USet Ω := (hS'.1 hKη).1
  have hzW : z ∈ (⨆ V ∈ η, V) := (Subgroup.mem_inf.mp
    (e18a_mem_of_USet h hK hz hKU inf_le_left)).2
  refine ⟨_, hWS, fun J hJ => ?_⟩
  obtain ⟨hJΩ, z', hz'K, hz'J⟩ := hJ
  rw [← hz.eq hz'K] at hz'J
  exact h.mem_dSet_of_mem hWS hJΩ hz'J hzW

private theorem e18a_ncard {Ω : Set (Subgroup G)} (h : EndHyp Ω) (h9 : Perp9 Ω)
    (hwyl : ∀ W ∈ WSet Ω, MuIsoWylD4 Ω W) {K : Subgroup G} (hK : K ∈ Ω) :
    (twinSet Ω K).ncard = 4 := by
  obtain ⟨W, hW, hsub⟩ := e18a_exists_W h hK
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution h.thmD.hyp hK
  have hKD : K ∈ DSet Ω W := hsub K ⟨hK, z, hz, hz⟩
  have kp : KPerp Ω K = twinSet Ω K := EndHyp.kPerp_eq_twinSet_of_perp9 h h9 hK
  have hsub' : KPerp Ω K ⊆ DSet Ω W := by
    rw [kp]
    exact hsub
  have hcount := (dSet_class_ncard h hW hKD).2.2 (hwyl W hW)
  rw [Set.inter_eq_left.mpr hsub', kp] at hcount
  exact hcount

private theorem e18a_twin_inv {Ω : Set (Subgroup G)} {K J : Subgroup G} {z : G}
    (hz : IsUniqueInvolution K z) (hJ : J ∈ twinSet Ω K) : J ∈ Ω ∧ IsUniqueInvolution J z := by
  obtain ⟨hJΩ, z', hz'K, hz'J⟩ := hJ
  rw [← hz.eq hz'K] at hz'J
  exact ⟨hJΩ, hz'J⟩

private theorem e18a_twin_comm {Ω : Set (Subgroup G)} (h : EndHyp Ω) {K J J' : Subgroup G}
    {z : G} (hz : IsUniqueInvolution K z) (hJ : J ∈ twinSet Ω K) (hJ' : J' ∈ twinSet Ω K)
    (hne : J ≠ J') : Commutes J J' := by
  obtain ⟨hJΩ, hzJ⟩ := e18a_twin_inv hz hJ
  obtain ⟨hJ'Ω, hzJ'⟩ := e18a_twin_inv hz hJ'
  exact CFSG.ClassicalInvolution.Q3.TC.Thin.twin_comm h.thmD.hyp (fun L hL => h.thmD.two L hL)
    hJΩ hJ'Ω hne hzJ hzJ'

private theorem e18a_pair_good {Ω : Set (Subgroup G)} (h : EndHyp Ω) {K J J' : Subgroup G}
    {z : G} (hz : IsUniqueInvolution K z) (hJ : J ∈ twinSet Ω K) (hJ' : J' ∈ twinSet Ω K)
    (hne : J ≠ J') : e18a_Good (J ⊔ J') z ∧ Nat.card ↥(J ⊔ J') = 32 := by
  obtain ⟨hJΩ, hzJ⟩ := e18a_twin_inv hz hJ
  obtain ⟨hJ'Ω, hzJ'⟩ := e18a_twin_inv hz hJ'
  obtain ⟨i, j, hQ⟩ := e18a_q8 h hJΩ hzJ
  obtain ⟨i', j', hQ'⟩ := e18a_q8 h hJ'Ω hzJ'
  have hc : ∀ x ∈ J, ∀ k ∈ J', x * k = k * x := e18a_twin_comm h hz hJ hJ' hne
  obtain ⟨hG, hcard⟩ :=
    e18a_chain (e18a_base hQ) hQ' (h.card_eq_eight hJ'Ω) hzJ.sq hzJ.ne_one hc
  refine ⟨hG, ?_⟩
  rw [hcard, h.card_eq_eight hJΩ]

private theorem e18a_enum {V : Set (Subgroup G)} {K : Subgroup G} (hKV : K ∈ V)
    (hV : V.ncard = 4) :
    ∃ a b c : Subgroup G, K ≠ a ∧ K ≠ b ∧ K ≠ c ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      V = {K, a, b, c} := by
  have hfin : V.Finite := Set.finite_of_ncard_ne_zero (by rw [hV]; norm_num)
  have h3 : (V \ {K}).ncard = 3 := by
    rw [Set.ncard_diff_singleton_of_mem hKV, hV]
  obtain ⟨a, b, c, hab, hac, hbc, hVK⟩ := Set.ncard_eq_three.mp h3
  have hmemVK : ∀ x, x ∈ V \ {K} ↔ x = a ∨ x = b ∨ x = c := by
    intro x
    rw [hVK]
    simp
  have haV : a ∈ V \ {K} := (hmemVK a).mpr (Or.inl rfl)
  have hbV : b ∈ V \ {K} := (hmemVK b).mpr (Or.inr (Or.inl rfl))
  have hcV : c ∈ V \ {K} := (hmemVK c).mpr (Or.inr (Or.inr rfl))
  refine ⟨a, b, c, fun e => haV.2 (Set.mem_singleton_iff.mpr e.symm),
    fun e => hbV.2 (Set.mem_singleton_iff.mpr e.symm),
    fun e => hcV.2 (Set.mem_singleton_iff.mpr e.symm), hab, hac, hbc, ?_⟩
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hx
    by_cases hxK : x = K
    · exact Or.inl hxK
    · right
      exact (hmemVK x).mp ⟨hx, fun e => hxK (Set.mem_singleton_iff.mp e)⟩
  · rintro (rfl | rfl | rfl | rfl)
    · exact hKV
    · exact haV.1
    · exact hbV.1
    · exact hcV.1

private theorem e18a_span {Ω : Set (Subgroup G)} (h : EndHyp Ω) {K : Subgroup G} (hK : K ∈ Ω)
    {z : G} (hz : IsUniqueInvolution K z) (hV : (twinSet Ω K).ncard = 4) :
    e18a_Good (pSpan (twinSet Ω K)) z ∧ Nat.card ↥(pSpan (twinSet Ω K)) = 512 := by
  have hKV : K ∈ twinSet Ω K := ⟨hK, z, hz, hz⟩
  obtain ⟨a, b, c, hKa, hKb, hKc, hab, hac, hbc, hVeq⟩ := e18a_enum hKV hV
  have ha : a ∈ twinSet Ω K := by
    rw [hVeq]
    simp
  have hb : b ∈ twinSet Ω K := by
    rw [hVeq]
    simp
  have hc : c ∈ twinSet Ω K := by
    rw [hVeq]
    simp
  obtain ⟨haΩ, hza⟩ := e18a_twin_inv hz ha
  obtain ⟨hbΩ, hzb⟩ := e18a_twin_inv hz hb
  obtain ⟨hcΩ, hzc⟩ := e18a_twin_inv hz hc
  obtain ⟨ia, ja, hQa⟩ := e18a_q8 h haΩ hza
  obtain ⟨ib, jb, hQb⟩ := e18a_q8 h hbΩ hzb
  obtain ⟨ic, jc, hQc⟩ := e18a_q8 h hcΩ hzc
  obtain ⟨iK, jK, hQK⟩ := e18a_q8 h hK hz
  have cKa : ∀ x ∈ K, ∀ k ∈ a, x * k = k * x := e18a_twin_comm h hz hKV ha hKa
  have cKb : ∀ x ∈ K, ∀ k ∈ b, x * k = k * x := e18a_twin_comm h hz hKV hb hKb
  have cKc : ∀ x ∈ K, ∀ k ∈ c, x * k = k * x := e18a_twin_comm h hz hKV hc hKc
  have cab : ∀ x ∈ a, ∀ k ∈ b, x * k = k * x := e18a_twin_comm h hz ha hb hab
  have cac : ∀ x ∈ a, ∀ k ∈ c, x * k = k * x := e18a_twin_comm h hz ha hc hac
  have cbc : ∀ x ∈ b, ∀ k ∈ c, x * k = k * x := e18a_twin_comm h hz hb hc hbc
  have hzz : z * z = 1 := hz.sq
  have hz1 : z ≠ 1 := hz.ne_one
  obtain ⟨g2, c2⟩ := e18a_chain (e18a_base hQK) hQa (h.card_eq_eight haΩ) hzz hz1 cKa
  obtain ⟨g3, c3⟩ :=
    e18a_chain g2 hQb (h.card_eq_eight hbΩ) hzz hz1 (e18a_sup_comm cKb cab)
  obtain ⟨g4, c4⟩ := e18a_chain g3 hQc (h.card_eq_eight hcΩ) hzz hz1
    (e18a_sup_comm (e18a_sup_comm cKc cac) cbc)
  have hspan : pSpan (twinSet Ω K) = ((K ⊔ a) ⊔ b) ⊔ c := by
    apply le_antisymm
    · apply pSpan_le
      intro L hL
      rw [hVeq] at hL
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hL
      rcases hL with rfl | rfl | rfl | rfl
      · exact le_sup_left.trans (le_sup_left.trans le_sup_left)
      · exact le_sup_right.trans (le_sup_left.trans le_sup_left)
      · exact le_sup_right.trans le_sup_left
      · exact le_sup_right
    · exact sup_le (sup_le (sup_le (le_pSpan hKV) (le_pSpan ha)) (le_pSpan hb)) (le_pSpan hc)
  refine ⟨?_, ?_⟩
  · rw [hspan]
    exact g4
  · rw [hspan, c4, c3, c2, h.card_eq_eight hK]

private theorem e18a_abelian {X : Subgroup G} {z : G} (hzz : z * z = 1) (hz1 : z ≠ 1)
    (hX : e18a_Good X z) {n : ℕ} (hcard : Nat.card X = 2 ^ (2 * n + 1))
    {B : Subgroup G} (hB : B ≤ X) (hab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) :
    Nat.card B ≤ 2 ^ (n + 1) :=
  e18a_group_bound hzz hz1 hX.1 hX.2.1 hX.2.2.1 hX.2.2.2.1 hX.2.2.2.2 hcard hB hab

private theorem e18a_conj_le_of_normal {N : Subgroup G} [N.Normal] (g : G) {S : Subgroup G}
    (hS : S ≤ N) : conjSub g S ≤ N := by
  intro y hy
  unfold conjSub at hy
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
  exact Subgroup.Normal.conj_mem ‹N.Normal› x (hS hx) g

structure Hyp (Ω : Set (Subgroup G)) : Prop where
  endHyp : EndHyp Ω
  perp9 : Perp9 Ω
  wyl : ∀ W ∈ WSet Ω, MuIsoWylD4 Ω W
  ne : ∀ K ∈ Ω, zGroup Ω ≠ eGroup Ω K

namespace Hyp

variable {Ω : Set (Subgroup G)} (H : Hyp Ω)
include H

theorem kPerp_eq_twinSet {K : Subgroup G} (hK : K ∈ Ω) : KPerp Ω K = twinSet Ω K :=
  EndHyp.kPerp_eq_twinSet_of_perp9 H.endHyp H.perp9 hK

theorem ncard_twinSet {K : Subgroup G} (hK : K ∈ Ω) : (twinSet Ω K).ncard = 4 :=
  e18a_ncard H.endHyp H.perp9 H.wyl hK

theorem pCore_le_normalizer {W : Subgroup G} (hW : W ∈ WSet Ω) :
    pCore 2 G ≤ Subgroup.normalizer (W : Set G) := by
  obtain ⟨η, hη, rfl⟩ := hW
  obtain ⟨S, hηS, hinv⟩ := hη
  intro q hq
  have hqS : q ∈ (S : Subgroup G) := CFSG.pCore_isPGroup.le_sylow_of_normal S hq
  have hqS' : q⁻¹ ∈ (S : Subgroup G) := (S : Subgroup G).inv_mem hqS
  rw [mem_normalizer_iff_conjSub_eq, perpW_conjSub_iSup]
  apply le_antisymm
  · exact iSup₂_le fun U hU => le_iSup₂_of_le (conjSub q U) (hinv q hqS U hU) le_rfl
  · exact iSup₂_le fun U hU => le_iSup₂_of_le (conjSub q⁻¹ U) (hinv q⁻¹ hqS' U hU)
      (le_of_eq (conjSub_conjSub_inv q U).symm)

theorem exists_wSet_through {K : Subgroup G} (hK : K ∈ Ω) :
    ∃ W ∈ WSet Ω, twinSet Ω K ⊆ DSet Ω W := by
  obtain ⟨W, hW, hsub⟩ := e18a_exists_W H.endHyp hK
  exact ⟨W, hW, fun J hJ => hsub J hJ⟩

theorem sup_twin {K J J' : Subgroup G} {z : G} (hz : IsUniqueInvolution K z)
    (hJ : J ∈ twinSet Ω K) (hJ' : J' ∈ twinSet Ω K) (hne : J ≠ J') :
    Commutes J J' ∧ J ⊓ J' = Subgroup.zpowers z ∧ Nat.card ↥(J ⊔ J') = 32 := by
  obtain ⟨hJΩ, hzJ⟩ := e18a_twin_inv hz hJ
  obtain ⟨hJ'Ω, hzJ'⟩ := e18a_twin_inv hz hJ'
  have hc : ∀ x ∈ J, ∀ k ∈ J', x * k = k * x := e18a_twin_comm H.endHyp hz hJ hJ' hne
  obtain ⟨i', j', hQ'⟩ := e18a_q8 H.endHyp hJ'Ω hzJ'
  have hinf : J ⊓ J' = Subgroup.zpowers z := e18a_inf hQ' hzJ.mem hc
  exact ⟨e18a_twin_comm H.endHyp hz hJ hJ' hne, hinf,
    (e18a_pair_good H.endHyp hz hJ hJ' hne).2⟩

theorem card_span_twinSet {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) :
    Nat.card ↥(pSpan (twinSet Ω K)) = 2 ^ 9 ∧
      ∀ x ∈ pSpan (twinSet Ω K), (∀ y ∈ pSpan (twinSet Ω K), x * y = y * x) →
        x ∈ Subgroup.zpowers z := by
  obtain ⟨hX, hcard⟩ := e18a_span H.endHyp hK hz (H.ncard_twinSet hK)
  exact ⟨by rw [hcard]; norm_num, fun x hx hc => hX.2.2.2.2 x hx hc⟩

theorem card_abelian_le_span {K : Subgroup G} (hK : K ∈ Ω) {B : Subgroup G}
    (hB : B ≤ pSpan (twinSet Ω K)) (hab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) :
    Nat.card ↥B ≤ 32 := by
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution H.endHyp.thmD.hyp hK
  obtain ⟨hX, hcard⟩ := e18a_span H.endHyp hK hz (H.ncard_twinSet hK)
  have h := e18a_abelian hz.sq hz.ne_one hX (n := 4) (hcard.trans (by norm_num)) hB hab
  calc Nat.card ↥B ≤ 2 ^ (4 + 1) := h
    _ = 32 := by norm_num

theorem inf_pCore {K : Subgroup G} (hK : K ∈ Ω) {z : G} (hz : IsUniqueInvolution K z) :
    K ⊓ pCore 2 G = Subgroup.zpowers z := by
  have hzQ : z ∈ pCore 2 G := H.endHyp.mem_pCore hK hz
  refine le_antisymm ?_ (Subgroup.zpowers_le.mpr ⟨hz.mem, hzQ⟩)
  intro x hx
  by_contra hxz
  haveI : (pCore 2 G).Normal := CFSG.pCore_normal
  have hm4 : 4 ≤ Nat.card ↥(K ⊓ pCore 2 G) := by
    have hd1 : Nat.card ↥(Subgroup.zpowers z) ∣ Nat.card ↥(K ⊓ pCore 2 G) :=
      Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr ⟨hz.mem, hzQ⟩)
    have hd2 : Nat.card ↥(K ⊓ pCore 2 G) ∣ 8 := by
      rw [← H.endHyp.card_eq_eight hK]
      exact Subgroup.card_dvd_of_le inf_le_left
    rw [e18a_card_zpowers hz.sq hz.ne_one] at hd1
    have hne2 : Nat.card ↥(K ⊓ pCore 2 G) ≠ 2 := by
      intro h2
      have heq : Subgroup.zpowers z = K ⊓ pCore 2 G :=
        Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr ⟨hz.mem, hzQ⟩)
          (le_of_eq (by rw [e18a_card_zpowers hz.sq hz.ne_one, h2]))
      exact hxz (heq ▸ hx)
    have hpos : 0 < Nat.card ↥(K ⊓ pCore 2 G) := Nat.card_pos
    obtain ⟨m, hm⟩ : ∃ m, Nat.card ↥(K ⊓ pCore 2 G) = m := ⟨_, rfl⟩
    rw [hm] at hd1 hd2 hne2 hpos ⊢
    have hle : m ≤ 8 := Nat.le_of_dvd (by norm_num) hd2
    interval_cases m <;> omega
  have hconj : ∀ L ∈ Ω, 4 ≤ Nat.card ↥(L ⊓ pCore 2 G) := by
    intro L hL
    obtain ⟨g, rfl⟩ := H.endHyp.thmD.trans K hK L hL
    have hsub : conjSub g (K ⊓ pCore 2 G) ≤ conjSub g K ⊓ pCore 2 G :=
      le_inf (conjSub_mono inf_le_left) (e18a_conj_le_of_normal g inf_le_right)
    have hcard : Nat.card ↥(conjSub g (K ⊓ pCore 2 G)) = Nat.card ↥(K ⊓ pCore 2 G) :=
      Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
        (MulAut.conj g).injective
    have := Subgroup.card_le_of_le hsub
    omega
  obtain ⟨S, hQS⟩ := (CFSG.pCore_isPGroup (p := 2) (G := G)).exists_le_sylow
  obtain ⟨η, hηS, hinv⟩ := Sec6Gen.exists_invariant_mem_etaSet H.endHyp.thmD.hyp S
  have hη : η ∈ etaG Ω := ⟨S, hηS, hinv⟩
  have hηle : ∀ V ∈ η, V ≤ (S : Subgroup G) := fun V hV => (hηS.1 hV).2
  have hW : (⨆ V ∈ η, V) ∈ WSet Ω := ⟨η, hη, rfl⟩
  have hLW : ∀ L ∈ Ω, L ≤ Subgroup.normalizer ((⨆ V ∈ η, V : Subgroup G) : Set G) := by
    intro L hL
    have h2 : 2 < Nat.card ↥(L ⊓ (S : Subgroup G)) := by
      have h1 := Subgroup.card_le_of_le (inf_le_inf_left L hQS :
        L ⊓ pCore 2 G ≤ L ⊓ (S : Subgroup G))
      have h4 := hconj L hL
      omega
    have hLη := Sec6Gen.l6_11Gen G Ω H.endHyp.thmD.hyp S η hη hηle L hL h2
    have hUS : L ⊓ (⨆ V ∈ η, V) ∈ USet Ω := (hηS.1 hLη).1
    obtain ⟨uL, huL⟩ := Sec6Gen.exists_uniqueInvolution H.endHyp.thmD.hyp hL
    have huW : uL ∈ (⨆ V ∈ η, V : Subgroup G) :=
      (Subgroup.mem_inf.mp (e18a_mem_of_USet H.endHyp hL huL hUS inf_le_left)).2
    exact (H.endHyp.mem_dSet_iff.mp (H.endHyp.mem_dSet_of_mem hW hL huL huW)).2
  have htop : (⊤ : Subgroup G) ≤ Subgroup.normalizer ((⨆ V ∈ η, V : Subgroup G) : Set G) := by
    rw [← H.endHyp.thmD.gen]
    exact pSpan_le hLW
  have hnorm : (⨆ V ∈ η, V : Subgroup G).Normal :=
    Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp htop)
  exact H.endHyp.wSet_ne _ (wSet_eq_singleton_of_normal H.endHyp.thmD.hyp H.endHyp.thmD.two
    H.endHyp.thmD.trans H.endHyp.thmD.gen (fun hs => H.endHyp.not (Or.inl hs)) hW hnorm)

theorem normalizes_iff {K M : Subgroup G} (hK : K ∈ Ω) (hM : M ∈ Ω) {s : G}
    (hs : IsUniqueInvolution M s) :
    s ∈ Subgroup.normalizer (K : Set G) ↔ M ∈ twinSet Ω K ∨ M ∈ omegaStarNbr Ω K := by
  constructor
  · intro hsN
    exact (H.endHyp.mem_omegaStarNbr_or_twinSet H.perp9 hK hM hs hsN).symm
  · rintro (hMT | hMO)
    · obtain ⟨-, z', hz'K, hz'M⟩ := hMT
      rw [hs.eq hz'M]
      exact Subgroup.le_normalizer hz'K.mem
    · exact H.endHyp.eGroup_le_normalizer hK (H.endHyp.mem_eGroup_of_mem_omegaStarNbr hMO hs)

theorem mem_eGroup_iff_normalizes {K M : Subgroup G} (hK : K ∈ Ω) (hM : M ∈ Ω) {s : G}
    (hs : IsUniqueInvolution M s) :
    s ∈ eGroup Ω K ↔ s ∈ Subgroup.normalizer (K : Set G) :=
  ⟨fun hE => H.endHyp.eGroup_le_normalizer hK hE,
    fun hN => H.endHyp.mem_eGroup_of_normalizes H.perp9 hK hM hs hN⟩

end Hyp

end End18

end CFSG.ClassicalInvolution.Q3.Sec13
