module

public import CFSG.GH74.Uniqueness.SU.SU8Irr
public import Mathlib.Tactic.Basify
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.GH74.Uniqueness.SU.SU8

open Subgroup CFSG.GH74.Uniqueness.SU.SU8.Irr
open scoped commutatorElement

namespace UAbs

theorem card_eq_range_mul_ker {A B : Type*} [Group A] [Group B] (f : A →* B) :
    Nat.card A = Nat.card f.range * Nat.card f.ker := by
  have h1 := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker] at h1
  rw [mul_comm]; exact h1.symm

theorem card_le_two_of_forall {Hb : Type} [Group Hb] {z : Hb} {W : Subgroup Hb}
    (hW : ∀ w ∈ W, w = 1 ∨ w = z) : Nat.card W ≤ 2 := by
  have h1 : (W : Set Hb) ⊆ {1, z} := by
    intro w hw
    rcases hW w hw with h | h
    · simp [h]
    · simp [h]
  have h2 : (W : Set Hb).ncard ≤ ({1, z} : Set Hb).ncard :=
    Set.ncard_le_ncard h1 (Set.toFinite _)
  have h3 : ({1, z} : Set Hb).ncard ≤ 2 := by
    have := Set.ncard_insert_le (1 : Hb) ({z} : Set Hb)
    rw [Set.ncard_singleton] at this
    exact this
  have h4 : Nat.card W = (W : Set Hb).ncard := Nat.card_coe_set_eq (W : Set Hb)
  omega

theorem inv_conj_mem {X : Type*} [Group X] [Finite X] {A : Subgroup X} {g : X}
    (h : ∀ a ∈ A, g * a * g⁻¹ ∈ A) : ∀ a ∈ A, g⁻¹ * a * g ∈ A := by
  have hle : A.map (MulAut.conj g).toMonoidHom ≤ A := by
    rintro _ ⟨a, ha, rfl⟩
    exact h a ha
  have hcard : Nat.card (A.map (MulAut.conj g).toMonoidHom) = Nat.card A :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have heq : A.map (MulAut.conj g).toMonoidHom = A :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcard])
  intro a ha
  rw [← heq] at ha
  obtain ⟨a', ha', h'⟩ := Subgroup.mem_map.mp ha
  have h'' : g * a' * g⁻¹ = a := by simpa [MulAut.conj_apply] using h'
  have : a' = g⁻¹ * a * g := by rw [← h'']; group
  rw [← this]; exact ha'

theorem exists_proj {Hb : Type} [Group Hb] (K : Subgroup Hb)
    (hKC : K ⊓ centralizer (K : Set Hb) = ⊥) (V : Subgroup Hb)
    (hV : ∀ v ∈ V, ∃ k ∈ K, k⁻¹ * v ∈ centralizer (K : Set Hb)) :
    ∃ ι : ↥V →* ↥K, (∀ v : ↥V, ((ι v : ↥K) : Hb)⁻¹ * (v : Hb) ∈ centralizer (K : Set Hb)) ∧
      ∀ v : ↥V, (v : Hb) ∈ centralizer (K : Set Hb) → ι v = 1 := by
  classical
  have huniq : ∀ k k' : Hb, k ∈ K → k' ∈ K → ∀ v : Hb,
      k⁻¹ * v ∈ centralizer (K : Set Hb) → k'⁻¹ * v ∈ centralizer (K : Set Hb) → k = k' := by
    intro k k' hk hk' v h h'
    have h1 : k⁻¹ * k' ∈ K ⊓ centralizer (K : Set Hb) := by
      refine ⟨K.mul_mem (K.inv_mem hk) hk', ?_⟩
      have : k⁻¹ * k' = (k⁻¹ * v) * (k'⁻¹ * v)⁻¹ := by group
      rw [this]
      exact (centralizer (K : Set Hb)).mul_mem h ((centralizer (K : Set Hb)).inv_mem h')
    rw [hKC, Subgroup.mem_bot] at h1
    exact inv_mul_eq_one.mp h1
  let f : ↥V → ↥K := fun v => ⟨Classical.choose (hV v v.2), (Classical.choose_spec (hV v v.2)).1⟩
  have hf : ∀ v : ↥V, ((f v : ↥K) : Hb)⁻¹ * (v : Hb) ∈ centralizer (K : Set Hb) :=
    fun v => (Classical.choose_spec (hV v v.2)).2
  have hmul : ∀ v w : ↥V, f (v * w) = f v * f w := by
    intro v w
    apply Subtype.ext
    apply huniq ((f (v * w) : ↥K) : Hb) (((f v * f w : ↥K)) : Hb) (f (v * w)).2
      (K.mul_mem (f v).2 (f w).2) ((v * w : ↥V) : Hb) (hf (v * w))
    have h1 := hf v
    have h2 := hf w
    have hcomm : ∀ c ∈ centralizer (K : Set Hb), ∀ k ∈ K, c * k = k * c := fun c hc k hk =>
      (Subgroup.mem_centralizer_iff.mp hc k hk).symm
    have : (((f v * f w : ↥K)) : Hb)⁻¹ * ((v * w : ↥V) : Hb) =
        ((f v : Hb)⁻¹ * (v : Hb)) * ((f w : Hb)⁻¹ * (w : Hb)) := by
      have hc1 := hcomm _ h1 ((f w : Hb)⁻¹) (K.inv_mem (f w).2)
      simp only [Subgroup.coe_mul]
      calc ((f v : Hb) * f w)⁻¹ * ((v : Hb) * w)
          = (f w : Hb)⁻¹ * ((f v : Hb)⁻¹ * v) * w := by group
        _ = (f w : Hb)⁻¹ * (((f v : Hb)⁻¹ * v)) * w := rfl
        _ = ((f v : Hb)⁻¹ * v) * (f w : Hb)⁻¹ * w := by rw [← hc1]
        _ = ((f v : Hb)⁻¹ * (v : Hb)) * ((f w : Hb)⁻¹ * (w : Hb)) := by group
    rw [this]
    exact (centralizer (K : Set Hb)).mul_mem h1 h2
  have hone : f 1 = 1 := by
    apply Subtype.ext
    apply huniq ((f 1 : ↥K) : Hb) 1 (f 1).2 K.one_mem ((1 : ↥V) : Hb) (hf 1)
    simp
  refine ⟨{ toFun := f, map_one' := hone, map_mul' := hmul }, hf, ?_⟩
  intro v hv
  apply Subtype.ext
  apply huniq ((f v : ↥K) : Hb) 1 (f v).2 K.one_mem (v : Hb) (hf v)
  simpa using hv

structure UData {Hb : Type} [Group Hb] (K R Z : Subgroup Hb) (y z : Hb) : Prop where
  hRcard : Nat.card R = 64
  hZcard : Nat.card Z = 4
  hZR : Z ≤ R
  hZc : ∀ w ∈ Z, ∀ r ∈ R, w * r = r * w
  hZsq : ∀ w ∈ Z, w * w = 1
  hZcomm : Z ≤ ⁅R, R⁆
  hyN : ∀ r ∈ R, y * r * y⁻¹ ∈ R
  hyZ : ∀ w ∈ Z, y * w * y⁻¹ ∈ Z
  hyz : y * z * y⁻¹ = z
  hfpf : ∀ r ∈ R, y * r * y⁻¹ * r⁻¹ ∈ Z → r ∈ Z
  hper : ∀ r ∈ R, y ^ 5 * r * (y ^ 5)⁻¹ * r⁻¹ ∈ Z
  hzZ : z ∈ Z
  hz1 : z ≠ 1
  hzC : z ∈ centralizer (K : Set Hb)
  hZC : ∀ w ∈ Z, w ∈ centralizer (K : Set Hb) → w = 1 ∨ w = z

namespace UData

variable {Hb : Type} [Group Hb] [Finite Hb] {K R Z : Subgroup Hb} {y z : Hb}

theorem irr (d : UData K R Z y z) (U : Subgroup Hb) (hZU : Z ≤ U) (hUR : U ≤ R)
    (hyU : ∀ u ∈ U, y * u * y⁻¹ ∈ U) : U = Z ∨ U = R :=
  irr_of_aut_five y d.hZc (by rw [d.hRcard, d.hZcard]) d.hyZ d.hfpf d.hper U hZU hUR hyU

theorem R_le_V (d : UData K R Z y z) [K.Normal]
    (habel : ∀ h h' : Hb, ∃ k ∈ K, k⁻¹ * ⁅h, h'⁆ ∈ centralizer (K : Set Hb)) :
    R ≤ K ⊔ centralizer (K : Set Hb) := by
  have hV : ∀ h h' : Hb, ⁅h, h'⁆ ∈ K ⊔ centralizer (K : Set Hb) := by
    intro h h'
    obtain ⟨k, hk, hc⟩ := habel h h'
    have := Subgroup.mul_mem_sup hk hc
    simpa using this
  set U₀ : Subgroup Hb := Subgroup.closure ({w | ∃ s ∈ R, w = y * s * y⁻¹ * s⁻¹} ∪ (Z : Set Hb))
    with hU₀
  have hU₀R : U₀ ≤ R := by
    rw [hU₀, Subgroup.closure_le]
    rintro w (⟨s, hs, rfl⟩ | hw)
    · exact R.mul_mem (d.hyN s hs) (R.inv_mem hs)
    · exact d.hZR hw
  have hZU₀ : Z ≤ U₀ := fun w hw => Subgroup.subset_closure (Or.inr hw)
  have hinv : ∀ u ∈ U₀, y * u * y⁻¹ ∈ U₀ := by
    intro u hu
    induction hu using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with ⟨s, hs, rfl⟩ | hx
      · refine Subgroup.subset_closure (Or.inl ⟨y * s * y⁻¹, d.hyN s hs, ?_⟩)
        group
      · exact hZU₀ (d.hyZ x hx)
    | one => simp
    | mul a b _ _ ha hb =>
      have := U₀.mul_mem ha hb
      convert this using 1
      group
    | inv a _ ha =>
      have := U₀.inv_mem ha
      convert this using 1
      group
  rcases d.irr U₀ hZU₀ hU₀R hinv with h | h
  · exfalso
    have hRZ : R ≤ Z := by
      intro s hs
      apply d.hfpf s hs
      have : y * s * y⁻¹ * s⁻¹ ∈ U₀ := Subgroup.subset_closure (Or.inl ⟨s, hs, rfl⟩)
      rwa [h] at this
    have := Subgroup.card_le_of_le hRZ
    rw [d.hRcard, d.hZcard] at this
    omega
  · have hZV : Z ≤ K ⊔ centralizer (K : Set Hb) := by
      refine d.hZcomm.trans ?_
      rw [Subgroup.commutator_le]
      intro r _ s _
      exact hV r s
    have : U₀ ≤ K ⊔ centralizer (K : Set Hb) := by
      rw [hU₀, Subgroup.closure_le]
      rintro w (⟨s, hs, rfl⟩ | hw)
      · exact hV y s
      · exact hZV hw
    rw [← h]; exact this

theorem M0_sub (d : UData K R Z y z) [K.Normal] :
    ∀ m ∈ R ⊓ centralizer (K : Set Hb), m = 1 ∨ m = z := by
  set C : Subgroup Hb := centralizer (K : Set Hb) with hC
  have hCn : C.Normal := inferInstance
  set M₀ : Subgroup Hb := R ⊓ C with hM₀
  set U : Subgroup Hb := Subgroup.closure ((M₀ : Set Hb) ∪ (Z : Set Hb)) with hU
  have hUR : U ≤ R := by
    rw [hU, Subgroup.closure_le]
    rintro w (hw | hw)
    · exact hw.1
    · exact d.hZR hw
  have hZU : Z ≤ U := fun w hw => Subgroup.subset_closure (Or.inr hw)
  have hinv : ∀ u ∈ U, y * u * y⁻¹ ∈ U := by
    intro u hu
    induction hu using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · refine Subgroup.subset_closure (Or.inl ⟨d.hyN x hx.1, ?_⟩)
        exact hCn.conj_mem x hx.2 y
      · exact hZU (d.hyZ x hx)
    | one => simp
    | mul a b _ _ ha hb =>
      have := U.mul_mem ha hb
      convert this using 1
      group
    | inv a _ ha =>
      have := U.inv_mem ha
      convert this using 1
      group
  rcases d.irr U hZU hUR hinv with h | h
  · intro m hm
    have : m ∈ U := Subgroup.subset_closure (Or.inl hm)
    rw [h] at this
    exact d.hZC m this hm.2
  · exfalso
    have hform : ∀ u ∈ U, ∃ m ∈ M₀, ∃ w ∈ Z, u = m * w := by
      intro u hu
      induction hu using Subgroup.closure_induction with
      | mem x hx =>
        rcases hx with hx | hx
        · exact ⟨x, hx, 1, Z.one_mem, by simp⟩
        · exact ⟨1, M₀.one_mem, x, hx, by simp⟩
      | one => exact ⟨1, M₀.one_mem, 1, Z.one_mem, by simp⟩
      | mul a b _ _ ha hb =>
        obtain ⟨m, hm, w, hw, rfl⟩ := ha
        obtain ⟨m', hm', w', hw', rfl⟩ := hb
        refine ⟨m * m', M₀.mul_mem hm hm', w * w', Z.mul_mem hw hw', ?_⟩
        have hc := d.hZc w hw m' hm'.1
        calc m * w * (m' * w') = m * (w * m') * w' := by group
          _ = m * (m' * w) * w' := by rw [hc]
          _ = m * m' * (w * w') := by group
      | inv a _ ha =>
        obtain ⟨m, hm, w, hw, rfl⟩ := ha
        refine ⟨m⁻¹, M₀.inv_mem hm, w⁻¹, Z.inv_mem hw, ?_⟩
        have hc := d.hZc w hw m hm.1
        calc (m * w)⁻¹ = w⁻¹ * m⁻¹ := by group
          _ = m⁻¹ * w⁻¹ := by
            have : m * w = w * m := hc.symm
            calc w⁻¹ * m⁻¹ = (m * w)⁻¹ := by group
              _ = (w * m)⁻¹ := by rw [this]
              _ = m⁻¹ * w⁻¹ := by group
    have hcomm : ∀ r ∈ R, ∀ s ∈ R, ⁅r, s⁆ ∈ M₀ := by
      intro r hr s hs
      rw [← h] at hr hs
      obtain ⟨m, hm, w, hw, rfl⟩ := hform r hr
      obtain ⟨m', hm', w', hw', rfl⟩ := hform s hs
      have hg' : m' * w' ∈ R := R.mul_mem hm'.1 (d.hZR hw')
      have e1 : w * (m' * w') = (m' * w') * w := d.hZc w hw _ hg'
      have e2 : w' * m⁻¹ = m⁻¹ * w' := d.hZc w' hw' _ (R.inv_mem hm.1)
      have step : ⁅m * w, m' * w'⁆ = ⁅m, m' * w'⁆ := by
        calc ⁅m * w, m' * w'⁆ = m * (w * (m' * w') * w⁻¹) * m⁻¹ * (m' * w')⁻¹ := by
              simp only [commutatorElement_def]; group
          _ = m * (m' * w') * m⁻¹ * (m' * w')⁻¹ := by rw [e1]; group
          _ = ⁅m, m' * w'⁆ := by simp only [commutatorElement_def]
      have step2 : ⁅m, m' * w'⁆ = ⁅m, m'⁆ := by
        calc ⁅m, m' * w'⁆ = m * m' * (w' * m⁻¹) * w'⁻¹ * m'⁻¹ := by
              simp only [commutatorElement_def]; group
          _ = m * m' * (m⁻¹ * w') * w'⁻¹ * m'⁻¹ := by rw [e2]
          _ = ⁅m, m'⁆ := by simp only [commutatorElement_def]; group
      rw [step, step2]
      exact M₀.mul_mem (M₀.mul_mem (M₀.mul_mem hm hm') (M₀.inv_mem hm)) (M₀.inv_mem hm')
    have hZM : Z ≤ M₀ := d.hZcomm.trans (Subgroup.commutator_le.mpr hcomm)
    have := card_le_two_of_forall (z := z) (W := Z) (fun w hw => d.hZC w hw (hZM hw).2)
    have h4 := d.hZcard
    omega

theorem mem_Z_of_comm (d : UData K R Z y z) {r : Hb} (hr : r ∈ R)
    (hc : ∀ s ∈ R, ⁅r, s⁆ = 1 ∨ ⁅r, s⁆ = z) : r ∈ Z := by
  have hz2 : z * z = 1 := d.hZsq z d.hzZ
  have hzc : ∀ g ∈ R, g * z * g⁻¹ = z := fun g hg => by
    have := d.hZc z d.hzZ g hg
    calc g * z * g⁻¹ = (g * z) * g⁻¹ := rfl
      _ = (z * g) * g⁻¹ := by rw [← this]
      _ = z := by group
  have hyN' := inv_conj_mem (A := R) (g := y) d.hyN
  let Y₁ : Subgroup Hb :=
    { carrier := {r | r ∈ R ∧ ∀ s ∈ R, ⁅r, s⁆ = 1 ∨ ⁅r, s⁆ = z}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨R.mul_mem ha hb, fun s hs => ?_⟩
        have key : ⁅a * b, s⁆ = a * ⁅b, s⁆ * a⁻¹ * ⁅a, s⁆ := by
          simp only [commutatorElement_def]; group
        rw [key]
        rcases hb' s hs with h1 | h1 <;> rcases ha' s hs with h2 | h2
        · left; rw [h1, h2]; group
        · right; rw [h1, h2]; group
        · right; rw [h1, hzc a ha, h2]; group
        · left; rw [h1, hzc a ha, h2]; exact hz2
      one_mem' := ⟨R.one_mem, fun s _ => Or.inl (by simp [commutatorElement_def])⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨R.inv_mem ha, fun s hs => ?_⟩
        have key : ⁅a⁻¹, s⁆ = a⁻¹ * ⁅a, s⁆⁻¹ * a := by
          simp only [commutatorElement_def]; group
        rw [key]
        rcases ha' s hs with h1 | h1
        · left; rw [h1]; group
        · right
          have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
          rw [h1, hzi]
          have := hzc a⁻¹ (R.inv_mem ha)
          simpa using this }
  have hZY : Z ≤ Y₁ := by
    intro w hw
    refine ⟨d.hZR hw, fun s hs => Or.inl ?_⟩
    have := d.hZc w hw s hs
    simp only [commutatorElement_def]
    calc w * s * w⁻¹ * s⁻¹ = (w * s) * w⁻¹ * s⁻¹ := rfl
      _ = (s * w) * w⁻¹ * s⁻¹ := by rw [this]
      _ = 1 := by group
  have hYR : Y₁ ≤ R := fun r hr => hr.1
  have hinv : ∀ u ∈ Y₁, y * u * y⁻¹ ∈ Y₁ := by
    rintro u ⟨hu, hu'⟩
    refine ⟨d.hyN u hu, fun s hs => ?_⟩
    have hs' : y⁻¹ * s * y ∈ R := hyN' s hs
    have key : ⁅y * u * y⁻¹, s⁆ = y * ⁅u, y⁻¹ * s * y⁆ * y⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [key]
    rcases hu' _ hs' with h | h
    · left; rw [h]; group
    · right; rw [h, d.hyz]
  rcases d.irr Y₁ hZY hYR hinv with h | h
  · have : r ∈ Y₁ := ⟨hr, hc⟩
    rwa [h] at this
  · exfalso
    have hzord : orderOf z = 2 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact orderOf_eq_prime (by rw [sq]; exact hz2) d.hz1
    have hcomm : ⁅R, R⁆ ≤ Subgroup.zpowers z := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      have : a ∈ Y₁ := by rw [h]; exact ha
      rcases this.2 b hb with h1 | h1
      · rw [h1]; exact Subgroup.one_mem _
      · rw [h1]; exact Subgroup.mem_zpowers z
    have hZW : ∀ w ∈ Z, w = 1 ∨ w = z := by
      intro w hw
      have hw' := hcomm (d.hZcomm hw)
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw'
      rw [← zpow_mod_orderOf, hzord]
      rcases Int.emod_two_eq_zero_or_one j with h0 | h0
      · left
        have : j % ((2 : ℕ) : ℤ) = 0 := by simpa using h0
        rw [this]; simp
      · right
        have : j % ((2 : ℕ) : ℤ) = 1 := by simpa using h0
        rw [this]; simp
    have := card_le_two_of_forall (z := z) (W := Z) hZW
    have h4 := d.hZcard
    omega

theorem false_of (d : UData K R Z y z) [K.Normal]
    (hKC : K ⊓ centralizer (K : Set Hb) = ⊥)
    (habel : ∀ h h' : Hb, ∃ k ∈ K, k⁻¹ * ⁅h, h'⁆ ∈ centralizer (K : Set Hb))
    (K6 : ∀ M : Subgroup ↥K, IsPGroup 2 M → 32 ≤ Nat.card M →
      ∃ Z₁ : Subgroup ↥K, Z₁ ≤ M ∧ Nat.card Z₁ = 4 ∧ ∀ w ∈ Z₁, ∀ m ∈ M, w * m = m * w) :
    False := by
  classical
  set C : Subgroup Hb := centralizer (K : Set Hb) with hC
  have hRV := d.R_le_V habel
  have hV' : ∀ v ∈ R, ∃ k ∈ K, k⁻¹ * v ∈ C := by
    intro v hv
    obtain ⟨k, hk, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp (hRV hv)
    exact ⟨k, hk, by simpa using hc⟩
  obtain ⟨ι, hι, hιC⟩ := exists_proj K hKC R hV'
  have hker : ∀ r : ↥R, ι r = 1 ↔ (r : Hb) ∈ C := by
    intro r
    constructor
    · intro h
      have := hι r
      rw [h] at this
      simpa using this
    · exact hιC r
  have hkerle : Nat.card ι.ker ≤ 2 := by
    have h1 : Nat.card (ι.ker.map R.subtype) = Nat.card ι.ker :=
      Subgroup.card_map_of_injective R.subtype_injective
    rw [← h1]
    apply card_le_two_of_forall (z := z)
    rintro _ ⟨r, hr, rfl⟩
    have hrC : (r : Hb) ∈ C := (hker r).mp hr
    exact d.M0_sub _ ⟨r.2, hrC⟩
  have hcardR := card_eq_range_mul_ker ι
  have hrange32 : 32 ≤ Nat.card ι.range := by
    have hpos : 0 < Nat.card ι.ker := Nat.card_pos
    have := d.hRcard
    rw [hcardR] at this
    by_contra hlt
    push Not at hlt
    have : Nat.card ι.range * Nat.card ι.ker < 32 * 2 := by
      calc Nat.card ι.range * Nat.card ι.ker ≤ 31 * 2 :=
          Nat.mul_le_mul (by omega) hkerle
        _ < 32 * 2 := by norm_num
    omega
  have hR2 : IsPGroup 2 ↥R := by
    refine IsPGroup.of_card (n := 6) ?_
    rw [d.hRcard]; norm_num
  have hrange2 : IsPGroup 2 ι.range :=
    hR2.of_surjective ι.rangeRestrict (by exact ι.rangeRestrict_surjective)
  obtain ⟨Z₁, hZ₁le, hZ₁card, hZ₁c⟩ := K6 ι.range hrange2 hrange32
  have hzR : z ∈ R := d.hZR d.hzZ
  set Zt : Subgroup ↥R := Z.subgroupOf R with hZt
  let ιZ : ↥Zt →* ↥K := ι.comp Zt.subtype
  have hZtcard : Nat.card Zt = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe d.hZR).toEquiv]; exact d.hZcard
  have hzt : (⟨(⟨z, hzR⟩ : ↥R), Subgroup.mem_subgroupOf.mpr d.hzZ⟩ : ↥Zt) ∈ ιZ.ker := by
    rw [MonoidHom.mem_ker]
    exact (hker ⟨z, hzR⟩).mpr d.hzC
  have hkerZ : ιZ.ker ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.mem_bot] at hzt
    exact d.hz1 (congrArg (fun x : ↥Zt => ((x : ↥R) : Hb)) hzt)
  have hkerZcard : 2 ≤ Nat.card ιZ.ker := by
    have := (Subgroup.one_lt_card_iff_ne_bot ιZ.ker).2 hkerZ
    omega
  have hrangeZ : Nat.card ιZ.range ≤ 2 := by
    have h1 := card_eq_range_mul_ker ιZ
    rw [hZtcard] at h1
    have hpos : 0 < Nat.card ιZ.range := Nat.card_pos
    by_contra hlt
    push Not at hlt
    have : 3 * 2 ≤ Nat.card ιZ.range * Nat.card ιZ.ker := Nat.mul_le_mul hlt hkerZcard
    omega
  obtain ⟨u, huZ₁, huZ⟩ : ∃ u ∈ Z₁, u ∉ ιZ.range := by
    by_contra hall
    push Not at hall
    have hle : Z₁ ≤ ιZ.range := fun u hu => hall u hu
    have := Subgroup.card_le_of_le hle
    omega
  obtain ⟨r, hr⟩ := (MonoidHom.mem_range).mp (hZ₁le huZ₁)
  have hcomm : ∀ s ∈ R, ⁅(r : Hb), s⁆ = 1 ∨ ⁅(r : Hb), s⁆ = z := by
    intro s hs
    have h1 : ι ⁅r, ⟨s, hs⟩⁆ = 1 := by
      rw [map_commutatorElement, hr]
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact hZ₁c u huZ₁ _ ⟨⟨s, hs⟩, rfl⟩
    have h2 : ((⁅r, ⟨s, hs⟩⁆ : ↥R) : Hb) ∈ C := (hker _).mp h1
    exact d.M0_sub _ ⟨(⁅r, ⟨s, hs⟩⁆ : ↥R).2, h2⟩
  have hrZ : (r : Hb) ∈ Z := d.mem_Z_of_comm r.2 hcomm
  apply huZ
  refine ⟨⟨r, Subgroup.mem_subgroupOf.mpr hrZ⟩, ?_⟩
  exact hr

end UData

end UAbs

end CFSG.GH74.Uniqueness.SU.SU8
