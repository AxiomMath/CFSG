module

public import CFSG.LocalAnalysis.OddStandard.ONan76Sylow
public import CFSG.LocalAnalysis.OddStandard.ONanFusInvert
import Mathlib.Tactic.Group

public section

namespace CFSG.OddStandard.ONan76

open Subgroup CFSG.ABGLocalTools

variable {G : Type*} [Group G]

theorem mem_map_conj {F : Subgroup G} {g x : G} :
    x ∈ F.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ F := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro h
    exact ⟨g⁻¹ * x * g, h, by simp [mul_assoc]⟩

theorem mem_normalizer_of_conj_mem [Finite G] {F : Subgroup G} {x : G}
    (h : ∀ f ∈ F, x * f * x⁻¹ ∈ F) : x ∈ normalizer (F : Set G) := by
  have hle : F.map (MulAut.conj x).toMonoidHom ≤ F := by
    rintro _ ⟨f, hf, rfl⟩
    exact h f hf
  have heq : F.map (MulAut.conj x).toMonoidHom = F :=
    eq_of_le_of_card_ge hle (by rw [card_map_of_injective (MulAut.conj x).injective])
  refine mem_normalizer_iff.2 fun y => ⟨fun hy => h y hy, fun hy => ?_⟩
  rw [← heq, mem_map_conj] at hy
  simpa [mul_assoc] using hy

section Ext8

variable {H : Subgroup G} {i : G} (hi : i * i = 1) (hc : ∀ h ∈ H, h * i = i * h)
include hi hc

theorem comm_of_mul_mem {x : G} (hx : x * i ∈ H) : x * i = i * x := by
  have h := hc _ hx
  have h1 : x = i * x * i := by
    calc x = x * i * i := by rw [mul_assoc, hi, mul_one]
      _ = i * x * i := by rw [h, mul_assoc]
  calc x * i = i * x * i * i := by rw [← h1]
    _ = i * x := by rw [mul_assoc, hi, mul_one]

omit hc in
theorem inv_eq_self : i⁻¹ = i := inv_eq_of_mul_eq_one_right hi

end Ext8

def ext8 (H : Subgroup G) (i : G) (hi : i * i = 1) (hc : ∀ h ∈ H, h * i = i * h) :
    Subgroup G where
  carrier := {x | x ∈ H ∨ x * i ∈ H}
  mul_mem' := by
    rintro x y (hx | hx) (hy | hy)
    · exact Or.inl (mul_mem hx hy)
    · exact Or.inr (by rw [mul_assoc]; exact mul_mem hx hy)
    · refine Or.inr ?_
      rw [mul_assoc, hc y hy, ← mul_assoc]
      exact mul_mem hx hy
    · refine Or.inl ?_
      have e : x * y = x * i * (y * i) := by
        rw [comm_of_mul_mem hi hc hy, ← mul_assoc, mul_assoc x i i, hi, mul_one]
      rw [e]
      exact mul_mem hx hy
  one_mem' := Or.inl H.one_mem
  inv_mem' := by
    rintro x (hx | hx)
    · exact Or.inl (inv_mem hx)
    · refine Or.inr ?_
      have hxi := comm_of_mul_mem hi hc hx
      have e : x⁻¹ * i = (x * i)⁻¹ := by
        rw [mul_inv_rev, inv_eq_self hi]
        calc x⁻¹ * i = x⁻¹ * (i * x) * x⁻¹ := by group
          _ = x⁻¹ * (x * i) * x⁻¹ := by rw [hxi]
          _ = i * x⁻¹ := by group
      rw [e]
      exact inv_mem hx

section Ext8

variable {H : Subgroup G} {i : G} (hi : i * i = 1) (hc : ∀ h ∈ H, h * i = i * h)
include hi hc

theorem le_ext8 : H ≤ ext8 H i hi hc := fun _ hx => Or.inl hx

theorem mem_ext8_self : i ∈ ext8 H i hi hc := Or.inr (by rw [hi]; exact H.one_mem)

theorem mul_mem_iff (hiH : i ∉ H) {x y : G} (hx : x ∈ ext8 H i hi hc)
    (hy : y ∈ ext8 H i hi hc) : x * y ∈ H ↔ (x ∈ H ↔ y ∈ H) := by
  have key : ∀ {a : G}, a * i ∈ H → a ∉ H := fun {a} ha haH =>
    hiH (by simpa using mul_mem (inv_mem haH) ha)
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact iff_of_true (mul_mem hx hy) (iff_of_true hx hy)
  · exact iff_of_false (fun h => key hy (by simpa using mul_mem (inv_mem hx) h))
      (fun h => key hy (h.1 hx))
  · exact iff_of_false (fun h => key hx (by simpa using mul_mem h (inv_mem hy)))
      (fun h => key hx (h.2 hy))
  · refine iff_of_true ?_ (iff_of_false (key hx) (key hy))
    have e : x * y = x * i * (y * i) := by
      rw [comm_of_mul_mem hi hc hy, ← mul_assoc, mul_assoc x i i, hi, mul_one]
    rw [e]
    exact mul_mem hx hy

theorem mul_i_mul_i {a b : G} (hb : b ∈ H) : a * i * (b * i) = a * b := by
  calc a * i * (b * i) = a * (i * b) * i := by group
    _ = a * (b * i) * i := by rw [hc b hb]
    _ = a * b := by rw [mul_assoc, mul_assoc, hi, mul_one]

theorem ext8_comm (hHc : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) {x y : G}
    (hx : x ∈ ext8 H i hi hc) (hy : y ∈ ext8 H i hi hc) : x * y = y * x := by
  have key : ∀ {a : G}, a * i ∈ H → ∃ h ∈ H, a = h * i := fun {a} ha =>
    ⟨a * i, ha, by rw [mul_assoc, hi, mul_one]⟩
  have side : ∀ {a h : G}, a ∈ H → h ∈ H → a * (h * i) = h * i * a := by
    intro a h ha hh
    calc a * (h * i) = a * h * i := (mul_assoc _ _ _).symm
      _ = h * a * i := by rw [hHc a ha h hh]
      _ = h * (a * i) := mul_assoc _ _ _
      _ = h * (i * a) := by rw [hc a ha]
      _ = h * i * a := (mul_assoc _ _ _).symm
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact hHc x hx y hy
  · obtain ⟨h, hh, rfl⟩ := key hy
    exact side hx hh
  · obtain ⟨h, hh, rfl⟩ := key hx
    exact (side hy hh).symm
  · obtain ⟨h, hh, rfl⟩ := key hx
    obtain ⟨h', hh', rfl⟩ := key hy
    rw [mul_i_mul_i hi hc hh', mul_i_mul_i hi hc hh, hHc h hh h' hh']

theorem ext8_sq (hH2 : ∀ a ∈ H, a * a = 1) {x : G} (hx : x ∈ ext8 H i hi hc) : x * x = 1 := by
  rcases hx with hx | hx
  · exact hH2 x hx
  · obtain ⟨h, hh, rfl⟩ : ∃ h ∈ H, x = h * i := ⟨x * i, hx, by rw [mul_assoc, hi, mul_one]⟩
    rw [mul_i_mul_i hi hc hh, hH2 h hh]

theorem card_ext8 [Finite G] (hiH : i ∉ H) : Nat.card (ext8 H i hi hc) = 2 * Nat.card H := by
  have h2 : H.relIndex (ext8 H i hi hc) = 2 := by
    rw [relIndex_eq_two_iff]
    refine ⟨i, mem_ext8_self hi hc, fun b hb => ?_⟩
    rw [xor_iff_or_and_not_and]
    have key := mul_mem_iff hi hc hiH hb (mem_ext8_self hi hc)
    constructor
    · by_cases hbH : b ∈ H
      · exact Or.inr hbH
      · exact Or.inl (key.2 (iff_of_false hbH hiH))
    · rintro ⟨h1, h2⟩
      exact hiH ((key.1 h1).1 h2)
  have h3 := relIndex_mul_card (H := H) (K := ext8 H i hi hc)
  rw [h2, inf_of_le_left (le_ext8 hi hc)] at h3
  omega

end Ext8

theorem sq_of_two_trans {F : Subgroup G} (P₁ P₂ : G → Prop)
    (hFc : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x) (hF2 : ∀ x ∈ F, x * x = 1)
    (hP₁ : ∀ x ∈ F, ∀ y ∈ F, (P₁ (x * y) ↔ (P₁ x ↔ P₁ y)))
    (hP₂ : ∀ x ∈ F, ∀ y ∈ F, (P₂ (x * y) ↔ (P₂ x ↔ P₂ y)))
    {a₁ a₂ x₁ x₂ : G} (ha₁ : a₁ ∈ F) (ha₂ : a₂ ∈ F) (h11 : P₁ a₁) (h21 : P₂ a₁)
    (h12 : ¬ P₁ a₂) (h22 : P₂ a₂)
    (hx₁ : ∀ f ∈ F, (P₁ f → x₁ * f * x₁⁻¹ = f) ∧ (¬ P₁ f → x₁ * f * x₁⁻¹ = f * a₁))
    (hx₂ : ∀ f ∈ F, (P₂ f → x₂ * f * x₂⁻¹ = f) ∧ (¬ P₂ f → x₂ * f * x₂⁻¹ = f * a₂))
    {f : G} (hf : f ∈ F) :
    (P₂ f → (x₁ * x₂) ^ 2 * f * ((x₁ * x₂) ^ 2)⁻¹ = f) ∧
      (¬ P₂ f → (x₁ * x₂) ^ 2 * f * ((x₁ * x₂) ^ 2)⁻¹ = f * a₁) := by
  have hM2 : ∀ y : G, (x₁ * x₂) ^ 2 * y * ((x₁ * x₂) ^ 2)⁻¹ =
      x₁ * (x₂ * (x₁ * (x₂ * y * x₂⁻¹) * x₁⁻¹) * x₂⁻¹) * x₁⁻¹ := fun y => by
    rw [pow_two]; group
  have hfa₁ : f * a₁ ∈ F := mul_mem hf ha₁
  have hfa₂ : f * a₂ ∈ F := mul_mem hf ha₂
  have hfa₂a₁ : f * a₂ * a₁ ∈ F := mul_mem hfa₂ ha₁
  have hsq₁ : a₁ * a₁ = 1 := hF2 a₁ ha₁
  have hsq₂ : a₂ * a₂ = 1 := hF2 a₂ ha₂
  by_cases hf2 : P₂ f
  · refine ⟨fun _ => ?_, fun h => absurd hf2 h⟩
    by_cases hf1 : P₁ f
    · rw [hM2, (hx₂ f hf).1 hf2, (hx₁ f hf).1 hf1, (hx₂ f hf).1 hf2, (hx₁ f hf).1 hf1]
    · have hP₂' : P₂ (f * a₁) := (hP₂ f hf a₁ ha₁).2 (iff_of_true hf2 h21)
      have hP₁' : ¬ P₁ (f * a₁) := fun h => hf1 (((hP₁ f hf a₁ ha₁).1 h).2 h11)
      rw [hM2, (hx₂ f hf).1 hf2, (hx₁ f hf).2 hf1, (hx₂ _ hfa₁).1 hP₂', (hx₁ _ hfa₁).2 hP₁',
        mul_assoc f a₁ a₁, hsq₁, mul_one]
  · refine ⟨fun h => absurd h hf2, fun _ => ?_⟩
    have hP₂a : ¬ P₂ (f * a₂) := fun h => hf2 (((hP₂ f hf a₂ ha₂).1 h).2 h22)
    by_cases hf1 : P₁ f
    · have hP₁a : ¬ P₁ (f * a₂) := fun h => h12 (((hP₁ f hf a₂ ha₂).1 h).1 hf1)
      have hP₂b : ¬ P₂ (f * a₂ * a₁) := fun h => hP₂a (((hP₂ _ hfa₂ a₁ ha₁).1 h).2 h21)
      have hP₁b : ¬ P₁ (f * a₂ * a₁) := fun h => hP₁a (((hP₁ _ hfa₂ a₁ ha₁).1 h).2 h11)
      have hP₁c : P₁ (f * a₂ * a₁ * a₂) :=
        (hP₁ _ hfa₂a₁ a₂ ha₂).2 (iff_of_false hP₁b h12)
      rw [hM2, (hx₂ f hf).2 hf2, (hx₁ _ hfa₂).2 hP₁a, (hx₂ _ hfa₂a₁).2 hP₂b,
        (hx₁ _ (mul_mem hfa₂a₁ ha₂)).1 hP₁c]
      calc f * a₂ * a₁ * a₂ = f * a₁ * (a₂ * a₂) := by
            rw [mul_assoc f a₂ a₁, hFc a₂ ha₂ a₁ ha₁]; group
        _ = f * a₁ := by rw [hsq₂, mul_one]
    · have hP₁a : P₁ (f * a₂) := (hP₁ f hf a₂ ha₂).2 (iff_of_false hf1 h12)
      rw [hM2, (hx₂ f hf).2 hf2, (hx₁ _ hfa₂).1 hP₁a, (hx₂ _ hfa₂).2 hP₂a, mul_assoc f a₂ a₂,
        hsq₂, mul_one, (hx₁ f hf).2 hf1]

def actHom {N F : Subgroup G} (hNF : N ≤ normalizer (F : Set G)) : N →* MulAut F :=
  F.normalizerMonoidHom.comp (inclusion hNF)

theorem actHom_pow_apply {N F : Subgroup G} (hNF : N ≤ normalizer (F : Set G)) (y : N) (k : ℕ)
    (f : F) : (((actHom hNF y ^ k) f : F) : G) = (y : G) ^ k * f * ((y : G) ^ k)⁻¹ := by
  rw [← map_pow]
  rfl

theorem false_of_order_four [Finite G] {N F T₀ : Subgroup G} (hNF : N ≤ normalizer (F : Set G))
    (hT₀ : IsSylowOf 2 T₀ N) (hT₀sq : ∀ s ∈ T₀, ∀ f ∈ F, s * (s * f * s⁻¹) * s⁻¹ = f)
    {x : G} (hx : x ∈ N) (h4 : ∀ f ∈ F, x ^ 4 * f * (x ^ 4)⁻¹ = f) {e : G} (he : e ∈ F)
    (h2 : x ^ 2 * e * (x ^ 2)⁻¹ ≠ e) : False := by
  obtain ⟨T, hT⟩ := hT₀
  have hTsq : ∀ s ∈ (T : Subgroup N), actHom hNF s ^ 2 = 1 := by
    intro s hs
    have hsT : (s : G) ∈ T₀ := hT ▸ ⟨s, hs, rfl⟩
    refine MulEquiv.ext fun f => Subtype.ext ?_
    rw [actHom_pow_apply, MulAut.one_apply]
    calc (s : G) ^ 2 * f * ((s : G) ^ 2)⁻¹ = (s : G) * ((s : G) * f * (s : G)⁻¹) * (s : G)⁻¹ := by
          rw [pow_two]; group
      _ = f := hT₀sq _ hsT _ f.2
  have hx4 : actHom hNF ⟨x, hx⟩ ^ 4 = 1 :=
    MulEquiv.ext fun f => Subtype.ext (by rw [actHom_pow_apply, MulAut.one_apply]; exact h4 _ f.2)
  have hx2 := ONanRec.sq_eq_one_of_sylow_image (actHom hNF) T hTsq hx4
  apply h2
  have := congrArg (fun φ : MulAut F => ((φ ⟨e, he⟩ : F) : G)) hx2
  simpa only [actHom_pow_apply, MulAut.one_apply] using this

def modKer (N F : Subgroup G) (z : G) (hNF : N ≤ normalizer (F : Set G)) (hz2 : z * z = 1)
    (hzN : ∀ x ∈ N, x * z = z * x) : Subgroup G where
  carrier := {x | x ∈ N ∧ ∀ f ∈ F, x * f * x⁻¹ = f ∨ x * f * x⁻¹ = f * z}
  mul_mem' := by
    rintro x y ⟨hx, hxf⟩ ⟨hy, hyf⟩
    refine ⟨mul_mem hx hy, fun f hf => ?_⟩
    have e : x * y * f * (x * y)⁻¹ = x * (y * f * y⁻¹) * x⁻¹ := by group
    have hxz : x * z * x⁻¹ = z := by rw [hzN x hx, mul_inv_cancel_right]
    rcases hyf f hf with h | h <;> rw [e, h]
    · exact hxf f hf
    · rw [show x * (f * z) * x⁻¹ = x * f * x⁻¹ * (x * z * x⁻¹) by group, hxz]
      rcases hxf f hf with h' | h' <;> rw [h']
      · exact Or.inr rfl
      · exact Or.inl (by rw [mul_assoc, hz2, mul_one])
  one_mem' := ⟨one_mem _, fun f _ => Or.inl (by group)⟩
  inv_mem' := by
    rintro x ⟨hx, hxf⟩
    refine ⟨inv_mem hx, fun f hf => ?_⟩
    have hg : x⁻¹ * f * x ∈ F := by
      have := (mem_normalizer_iff.1 (hNF (inv_mem hx)) f).1 hf
      rwa [inv_inv] at this
    rw [inv_inv]
    rcases hxf _ hg with h | h
    · left
      rw [show x * (x⁻¹ * f * x) * x⁻¹ = f by group] at h
      exact h.symm
    · right
      rw [show x * (x⁻¹ * f * x) * x⁻¹ = f by group] at h
      calc x⁻¹ * f * x = x⁻¹ * f * x * z * z := by rw [mul_assoc _ z z, hz2, mul_one]
        _ = f * z := by rw [← h]

theorem three_le_card [Finite G] {L : Subgroup G} {a b c : G} (ha : a ∈ L) (hb : b ∈ L)
    (hc : c ∈ L) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : 3 ≤ Nat.card L := by
  classical
  have : Fintype L := Fintype.ofFinite L
  have hcard : ({⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩} : Finset L).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simpa [Subtype.ext_iff] using hbc
    · simp [Subtype.ext_iff, hab, hac]
  rw [Nat.card_eq_fintype_card, ← hcard]
  exact Finset.card_le_univ _

theorem conj_mem_of_frattini [Finite G] {N F A S V : Subgroup G} {z : G}
    (hNF : N ≤ normalizer (F : Set G)) (hz2 : z * z = 1) (hzN : ∀ x ∈ N, x * z = z * x)
    (hzA : z ∈ A) (hz1 : z ≠ 1) (hAF : A ≤ F) (hA4 : Nat.card A = 4)
    (hFV : ∀ y ∈ F, y ∈ V → y ∈ A) (hSyl : IsSylowOf 2 (S ⊓ N) N)
    (hScomm : ∀ a ∈ S, ∀ b ∈ S, a⁻¹ * b⁻¹ * a * b ∈ V) {y₀ y₁ : G} (hy₀ : y₀ ∈ S ⊓ N)
    (hy₁ : y₁ ∈ S ⊓ N) (hy₀z : ∀ f ∈ F, y₀ * f * y₀⁻¹ = f ∨ y₀ * f * y₀⁻¹ = f * z)
    (hy₁z : ∀ f ∈ F, y₁ * f * y₁⁻¹ = f ∨ y₁ * f * y₁⁻¹ = f * z)
    (hcA : y₁⁻¹ * y₀⁻¹ * y₁ * y₀ ∈ A) (hc1 : y₁⁻¹ * y₀⁻¹ * y₁ * y₀ ≠ 1)
    (hcz : y₁⁻¹ * y₀⁻¹ * y₁ * y₀ ≠ z) {x a : G} (hx : x ∈ N) (ha : a ∈ A) :
    x * a * x⁻¹ ∈ A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := modKer N F z hNF hz2 hzN with hZ
  have hZN : Z ≤ N := fun _ h => h.1
  have hNZ : N ≤ normalizer (Z : Set G) := fun m hm => mem_normalizer_of_conj_mem fun y hy => by
    refine ⟨mul_mem (mul_mem hm (hZN hy)) (inv_mem hm), fun f hf => ?_⟩
    have hf' : m⁻¹ * f * m ∈ F := by
      have := (mem_normalizer_iff.1 (hNF (inv_mem hm)) f).1 hf
      rwa [inv_inv] at this
    have hmz : m * z * m⁻¹ = z := by rw [hzN m hm, mul_inv_cancel_right]
    have e : m * y * m⁻¹ * f * (m * y * m⁻¹)⁻¹ = m * (y * (m⁻¹ * f * m) * y⁻¹) * m⁻¹ := by group
    rcases hy.2 _ hf' with h | h <;> rw [e, h]
    · exact Or.inl (by group)
    · exact Or.inr (by rw [show m * (m⁻¹ * f * m * z) * m⁻¹ = f * (m * z * m⁻¹) by group, hmz])
  have hY : IsSylowOf 2 ((S ⊓ N) ⊓ Z) Z := hSyl.inf_of_le_normalizer hZN hNZ
  obtain ⟨c, hcZ, hxc⟩ := exists_mul_mem_normalizer hNZ hY hx
  set ν := x * c with hν
  have hνN : ν ∈ N := mul_mem hx (hZN hcZ)
  have hy₀Y : y₀ ∈ (S ⊓ N) ⊓ Z := ⟨hy₀, (mem_inf.1 hy₀).2, hy₀z⟩
  have hy₁Y : y₁ ∈ (S ⊓ N) ⊓ Z := ⟨hy₁, (mem_inf.1 hy₁).2, hy₁z⟩
  have hconjY : ∀ y ∈ (S ⊓ N) ⊓ Z, ν * y * ν⁻¹ ∈ S := fun y hy =>
    (mem_inf.1 (mem_inf.1 ((mem_normalizer_iff.1 hxc y).1 hy)).1).1
  set L := A ⊓ A.map (MulAut.conj ν⁻¹).toMonoidHom with hL
  have hmemL : ∀ h, h ∈ L ↔ h ∈ A ∧ ν * h * ν⁻¹ ∈ A := fun h => by
    rw [hL, mem_inf, mem_map_conj, inv_inv]
  have hzL : z ∈ L := (hmemL z).2 ⟨hzA, by rw [hzN ν hνN, mul_inv_cancel_right]; exact hzA⟩
  have hcL : y₁⁻¹ * y₀⁻¹ * y₁ * y₀ ∈ L := by
    refine (hmemL _).2 ⟨hcA, hFV _ ?_ ?_⟩
    · exact (mem_normalizer_iff.1 (hNF hνN) _).1 (hAF hcA)
    · rw [show ν * (y₁⁻¹ * y₀⁻¹ * y₁ * y₀) * ν⁻¹ = (ν * y₁ * ν⁻¹)⁻¹ * (ν * y₀ * ν⁻¹)⁻¹ *
        (ν * y₁ * ν⁻¹) * (ν * y₀ * ν⁻¹) by group]
      exact hScomm _ (hconjY _ hy₁Y) _ (hconjY _ hy₀Y)
  have h3 : 3 ≤ Nat.card L := three_le_card (one_mem L) hzL hcL hz1.symm hc1.symm hcz.symm
  have hdvd : Nat.card L ∣ 4 := hA4 ▸ card_dvd_of_le inf_le_left
  have hL4 : Nat.card L = 4 := by
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (show Nat.card L ∣ 2 ^ 2 from hdvd)
    interval_cases k <;> simp_all
  have hLA : L = A := eq_of_le_of_card_ge inf_le_left (by rw [hL4, hA4])
  have hca : c⁻¹ * a * c ∈ A := by
    rcases (inv_mem hcZ).2 a (hAF ha) with h | h <;> rw [inv_inv] at h <;> rw [h]
    · exact ha
    · exact mul_mem ha hzA
  have h1 := ((hmemL _).1 (hLA ▸ hca : c⁻¹ * a * c ∈ L)).2
  rwa [show ν * (c⁻¹ * a * c) * ν⁻¹ = x * a * x⁻¹ by rw [hν]; group] at h1

structure ExtSetting (K S V W : Subgroup G) (j : G) : Prop where
  syl : IsSylowOf 2 S K
  VS : V ≤ S
  V_comm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a
  S_V : ∀ x ∈ S, ∀ v ∈ V, x * v * x⁻¹ ∈ V
  mem_W : ∀ w, w ∈ W ↔ w ∈ V ∧ w * w = 1
  card_W : Nat.card W = 8
  wc : ∀ g ∈ K, (∀ v ∈ V, g * v * g⁻¹ ∈ S) → ∀ v ∈ V, g * v * g⁻¹ ∈ V
  jS : j ∈ S
  jV : j ∉ V
  j2 : j * j = 1
  uic : ∀ x ∈ S, x ∉ V → x * x ∈ V → x * j ∈ V
  cSW : ∀ x ∈ S, (∀ w ∈ W, x * w = w * x) → x ∈ V
  card_H : Nat.card (W ⊓ centralizer ({j} : Set G) : Subgroup G) = 4
  comm : ∀ h ∈ W, h * j = j * h → ∃ v ∈ V, v * j * v⁻¹ = j * h

namespace ExtSetting

variable {K S V W : Subgroup G} {j : G} (hX : ExtSetting K S V W j)

local notation "𝐇" => W ⊓ centralizer (Singleton.singleton j : Set G)

include hX

theorem SK : S ≤ K := hX.syl.le

theorem VK : V ≤ K := hX.VS.trans hX.SK

theorem mem_H {h : G} : h ∈ 𝐇 ↔ h ∈ W ∧ h * j = j * h := by
  rw [mem_inf, mem_centralizer_singleton_iff]

theorem H_le_V : 𝐇 ≤ V := fun _ hh => ((hX.mem_W _).1 (mem_inf.1 hh).1).1

theorem H_sq {h : G} (hh : h ∈ 𝐇) : h * h = 1 := ((hX.mem_W _).1 (mem_inf.1 hh).1).2

theorem W_le_V : W ≤ V := fun _ hw => ((hX.mem_W _).1 hw).1

theorem j_inv : j⁻¹ = j := inv_eq_of_mul_eq_one_right hX.j2

theorem j_mul_mem {x : G} (hx : x * j ∈ V) : j * x ∈ V := by
  have h := hX.S_V j hX.jS _ hx
  rwa [hX.j_inv, mul_assoc, mul_assoc, hX.j2, mul_one] at h

theorem mul_j_mem {x : G} (hx : x ∈ S) (hxV : x ∉ V) (hx2 : x * x = 1) : x * j ∈ V :=
  hX.uic x hx hxV (by rw [hx2]; exact V.one_mem)

theorem comm_iff {x w : G} (hxj : x * j ∈ V) (hw : w ∈ V) : w * x = x * w ↔ w * j = j * w := by
  have hx : x = x * j * j := by rw [mul_assoc, hX.j2, mul_one]
  have hc := hX.V_comm w hw _ hxj
  constructor
  · intro h
    have h1 : x * j * (w * j) = x * j * (j * w) := by
      calc x * j * (w * j) = w * (x * j * j) := by rw [← mul_assoc, ← hc]; group
        _ = w * x := by rw [← hx]
        _ = x * w := h
        _ = x * j * (j * w) := by rw [← mul_assoc, ← hx]
    exact mul_left_cancel h1
  · intro h
    calc w * x = w * (x * j * j) := by rw [← hx]
      _ = x * j * (w * j) := by rw [← mul_assoc, hc]; group
      _ = x * j * (j * w) := by rw [h]
      _ = x * w := by rw [← mul_assoc, ← hx]

theorem H_comm {x h : G} (hxj : x * j ∈ V) (hh : h ∈ 𝐇) : h * x = x * h :=
  (hX.comm_iff hxj (hX.H_le_V hh)).2 ((hX.mem_H).1 hh).2

def F8 {j' : G} (hj'S : j' ∈ S) (hj'V : j' ∉ V) (hj'2 : j' * j' = 1) : Subgroup G :=
  ext8 𝐇 j' hj'2 (fun _ hh => hX.H_comm (hX.mul_j_mem hj'S hj'V hj'2) hh)

abbrev E : Subgroup G := hX.F8 hX.jS hX.jV hX.j2

section F8

variable {j' : G} (hj'S : j' ∈ S) (hj'V : j' ∉ V) (hj'2 : j' * j' = 1)
include hj'S hj'V hj'2

theorem mem_F8 {x : G} : x ∈ hX.F8 hj'S hj'V hj'2 ↔ x ∈ 𝐇 ∨ x * j' ∈ 𝐇 := Iff.rfl

theorem H_le_F8 : 𝐇 ≤ hX.F8 hj'S hj'V hj'2 := le_ext8 _ _

theorem self_mem_F8 : j' ∈ hX.F8 hj'S hj'V hj'2 := mem_ext8_self _ _

omit hj'S hj'2 in
theorem not_mem_H : j' ∉ 𝐇 := fun h => hj'V (hX.H_le_V h)

theorem F8_mul_mem_iff {x y : G} (hx : x ∈ hX.F8 hj'S hj'V hj'2) (hy : y ∈ hX.F8 hj'S hj'V hj'2) :
    x * y ∈ 𝐇 ↔ (x ∈ 𝐇 ↔ y ∈ 𝐇) :=
  mul_mem_iff _ _ (hX.not_mem_H hj'V) hx hy

theorem F8_le_S : hX.F8 hj'S hj'V hj'2 ≤ S := by
  rintro x (hx | hx)
  · exact hX.VS (hX.H_le_V hx)
  · have : x = x * j' * j' := by rw [mul_assoc, hj'2, mul_one]
    rw [this]
    exact mul_mem (hX.VS (hX.H_le_V hx)) hj'S

theorem F8_sq {x : G} (hx : x ∈ hX.F8 hj'S hj'V hj'2) : x * x = 1 :=
  ext8_sq _ _ (fun _ ha => hX.H_sq ha) hx

theorem F8_comm {x y : G} (hx : x ∈ hX.F8 hj'S hj'V hj'2) (hy : y ∈ hX.F8 hj'S hj'V hj'2) :
    x * y = y * x :=
  ext8_comm _ _ (fun a ha b hb => hX.V_comm a (hX.H_le_V ha) b (hX.H_le_V hb)) hx hy

theorem card_F8 [Finite G] : Nat.card (hX.F8 hj'S hj'V hj'2) = 8 := by
  rw [F8, card_ext8 _ _ (hX.not_mem_H hj'V), hX.card_H]

theorem mem_H_of_mem_F8 {x : G} (hx : x ∈ hX.F8 hj'S hj'V hj'2) (hxV : x ∈ V) : x ∈ 𝐇 := by
  rcases hx with hx | hx
  · exact hx
  · exact absurd (by simpa using mul_mem (inv_mem hxV) (hX.H_le_V hx)) hj'V

theorem exists_trans {h : G} (hh : h ∈ 𝐇) :
    ∃ v ∈ V, (∀ x ∈ 𝐇, v * x * v⁻¹ = x) ∧ ∀ x, x * j' ∈ 𝐇 → v * x * v⁻¹ = x * h := by
  obtain ⟨hW, hj⟩ := hX.mem_H.1 hh
  obtain ⟨v, hv, hvj⟩ := hX.comm h hW hj
  have hu : j * j' ∈ V := hX.j_mul_mem (hX.mul_j_mem hj'S hj'V hj'2)
  have hhV := hX.H_le_V hh
  have hvj' : v * j' * v⁻¹ = j' * h := by
    have e : j' = j * (j * j') := by rw [← mul_assoc, hX.j2, one_mul]
    calc v * j' * v⁻¹ = v * (j * (j * j')) * v⁻¹ := by rw [← e]
      _ = v * j * v⁻¹ * (v * (j * j') * v⁻¹) := by group
      _ = j * h * (j * j') := by
          rw [hvj, hX.V_comm v hv _ hu, mul_inv_cancel_right]
      _ = j * (j * j') * h := by rw [mul_assoc, hX.V_comm h hhV _ hu, ← mul_assoc]
      _ = j' * h := by rw [← e]
  refine ⟨v, hv, fun x hx => by rw [hX.V_comm v hv x (hX.H_le_V hx), mul_inv_cancel_right],
    fun x hx => ?_⟩
  obtain ⟨h₀, hh₀, rfl⟩ : ∃ h₀ ∈ 𝐇, x = h₀ * j' :=
    ⟨x * j', hx, by rw [mul_assoc, hj'2, mul_one]⟩
  calc v * (h₀ * j') * v⁻¹ = v * h₀ * v⁻¹ * (v * j' * v⁻¹) := by group
    _ = h₀ * j' * h := by
        rw [hvj', hX.V_comm v hv h₀ (hX.H_le_V hh₀), mul_inv_cancel_right, mul_assoc]

end F8

theorem exists_two [Finite G] : ∃ h₁ ∈ 𝐇, ∃ h₂ ∈ 𝐇, h₁ ≠ 1 ∧ h₂ ≠ 1 ∧ h₁ ≠ h₂ := by
  have h4 := hX.card_H
  obtain ⟨⟨h₁, hh₁⟩, hne⟩ := ne_bot_iff_exists_ne_one.1 ((one_lt_card_iff_ne_bot _).1
    (by rw [h4]; norm_num))
  have h1ne : h₁ ≠ 1 := fun h => hne (Subtype.ext h)
  have hz : zpowers h₁ ≤ 𝐇 := zpowers_le.2 hh₁
  have hcard : Nat.card (zpowers h₁) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact hX.H_sq hh₁) h1ne
  obtain ⟨h₂, hh₂, hnot⟩ : ∃ h₂ ∈ 𝐇, h₂ ∉ zpowers h₁ := by
    by_contra hcon
    push Not at hcon
    have := card_le_of_le (show 𝐇 ≤ zpowers h₁ from hcon)
    omega
  exact ⟨h₁, hh₁, h₂, hh₂, h1ne, fun h => hnot (h ▸ one_mem _),
    fun h => hnot (h ▸ mem_zpowers _)⟩

theorem normalize [Finite G] {k : G} (hk : k ∈ K) (hkj : k * j * k⁻¹ ∈ V) :
    ∃ k' ∈ K, k' * j * k'⁻¹ ∈ V ∧ ∀ e ∈ hX.E, k' * e * k'⁻¹ ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set w := k * j * k⁻¹ with hw
  set C : Subgroup G := K ⊓ centralizer (Singleton.singleton w : Set G) with hC
  have hVC : V ≤ C := fun v hv =>
    mem_inf.2 ⟨hX.VK hv, mem_centralizer_singleton_iff.2 (hX.V_comm v hv w hkj)⟩
  have hV2 : IsPGroup 2 V := hX.syl.isPGroup.to_le hX.VS
  obtain ⟨T, hT, hVT⟩ := exists_isSylowOf_ge hVC hV2
  obtain ⟨d, hdK, hd⟩ := exists_conj_le hX.syl (hT.le.trans inf_le_left) hT.isPGroup
  have hdV : ∀ v ∈ V, d * v * d⁻¹ ∈ V := hX.wc d hdK (fun v hv => hd v (hVT hv))
  have hES : hX.E ≤ S := hX.F8_le_S _ _ _
  have hEC : hX.E.map (MulAut.conj k).toMonoidHom ≤ C := by
    rintro _ ⟨e, he, rfl⟩
    refine mem_inf.2 ⟨?_, mem_centralizer_singleton_iff.2 ?_⟩
    · exact mul_mem (mul_mem hk (hX.SK (hES he))) (inv_mem hk)
    · have hej := hX.F8_comm hX.jS hX.jV hX.j2 he (hX.self_mem_F8 hX.jS hX.jV hX.j2)
      show k * e * k⁻¹ * (k * j * k⁻¹) = k * j * k⁻¹ * (k * e * k⁻¹)
      calc k * e * k⁻¹ * (k * j * k⁻¹) = k * (e * j) * k⁻¹ := by group
        _ = k * (j * e) * k⁻¹ := by rw [hej]
        _ = k * j * k⁻¹ * (k * e * k⁻¹) := by group
  have hE2 : IsPGroup 2 (hX.E.map (MulAut.conj k).toMonoidHom) :=
    (hX.syl.isPGroup.to_le hES).map _
  obtain ⟨c, hcC, hc⟩ := exists_conj_le hT hEC hE2
  have hcw : c * w = w * c := mem_centralizer_singleton_iff.1 (mem_inf.1 hcC).2
  refine ⟨d * c * k, mul_mem (mul_mem hdK (mem_inf.1 hcC).1) hk, ?_, fun e he => ?_⟩
  · have e1 : d * c * k * j * (d * c * k)⁻¹ = d * (c * w * c⁻¹) * d⁻¹ := by rw [hw]; group
    rw [e1, hcw, mul_inv_cancel_right]
    exact hdV w hkj
  · have h1 := hc (k * e * k⁻¹) ⟨e, he, rfl⟩
    have h2 := hd _ h1
    rwa [show d * (c * (k * e * k⁻¹) * c⁻¹) * d⁻¹ = d * c * k * e * (d * c * k)⁻¹ by group] at h2

theorem classify [Finite G] {F : Subgroup G} (hFS : F ≤ S) (hF2 : ∀ x ∈ F, x * x = 1)
    (hF8 : Nat.card F = 8) (hFc : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x) :
    F = W ∨ ∃ (j' : G) (hj'S : j' ∈ S) (hj'V : j' ∉ V) (hj'2 : j' * j' = 1),
      F = hX.F8 hj'S hj'V hj'2 := by
  by_cases hFV : F ≤ V
  · left
    have hle : F ≤ W := fun x hx => (hX.mem_W x).2 ⟨hFV hx, hF2 x hx⟩
    exact eq_of_le_of_card_ge hle (by rw [hF8, hX.card_W])
  · right
    obtain ⟨j', hj'F, hj'V⟩ := Set.not_subset.1 hFV
    have hj'S := hFS hj'F
    have hj'2 := hF2 j' hj'F
    have hj'j := hX.mul_j_mem hj'S hj'V hj'2
    refine ⟨j', hj'S, hj'V, hj'2, ?_⟩
    have hle : F ≤ hX.F8 hj'S hj'V hj'2 := by
      intro x hx
      by_cases hxV : x ∈ V
      · refine (hX.mem_F8 hj'S hj'V hj'2).2 (Or.inl ?_)
        refine hX.mem_H.2 ⟨(hX.mem_W x).2 ⟨hxV, hF2 x hx⟩, ?_⟩
        exact (hX.comm_iff hj'j hxV).1 (hFc x hx j' hj'F)
      · refine (hX.mem_F8 hj'S hj'V hj'2).2 (Or.inr ?_)
        have hxj : x * j ∈ V := hX.mul_j_mem (hFS hx) hxV (hF2 x hx)
        have hjj' : j * j' ∈ V := hX.j_mul_mem hj'j
        have hV' : x * j' ∈ V := by
          have e : x * j' = x * j * (j * j') := by rw [mul_assoc, ← mul_assoc j, hX.j2, one_mul]
          rw [e]
          exact mul_mem hxj hjj'
        have hF' : x * j' ∈ F := mul_mem hx hj'F
        refine hX.mem_H.2 ⟨(hX.mem_W _).2 ⟨hV', hF2 _ hF'⟩, ?_⟩
        exact (hX.comm_iff hj'j hV').1 (hFc _ hF' j' hj'F)
    exact eq_of_le_of_card_ge hle (by rw [hX.card_F8 hj'S hj'V hj'2, hF8])

theorem trans_act {j' : G} (hj'S : j' ∈ S) (hj'V : j' ∉ V) (hj'2 : j' * j' = 1) {v h : G}
    (hh : h ∈ 𝐇) (hvH : ∀ x ∈ 𝐇, v * x * v⁻¹ = x) (hvj : ∀ x, x * j' ∈ 𝐇 → v * x * v⁻¹ = x * h)
    {e : G} (he : e ∈ hX.F8 hj'S hj'V hj'2) :
    v * e * v⁻¹ ∈ hX.F8 hj'S hj'V hj'2 ∧ v * (v * e * v⁻¹) * v⁻¹ = e := by
  rcases (hX.mem_F8 _ _ _).1 he with heH | hej
  · rw [hvH e heH, hvH e heH]
    exact ⟨he, rfl⟩
  · have hhj' : h * j' = j' * h := hX.H_comm (hX.mul_j_mem hj'S hj'V hj'2) hh
    have heh : e * h * j' ∈ 𝐇 := by
      rw [mul_assoc, hhj', ← mul_assoc]
      exact mul_mem hej hh
    refine ⟨?_, ?_⟩
    · rw [hvj e hej]
      exact (hX.mem_F8 _ _ _).2 (Or.inr heh)
    · rw [hvj e hej, hvj (e * h) heh, mul_assoc, hX.H_sq hh, mul_one]

theorem S_le_normalizer_W [Finite G] : S ≤ normalizer (W : Set G) := fun x hx =>
  mem_normalizer_of_conj_mem fun w hw => by
    obtain ⟨hwV, hw2⟩ := (hX.mem_W w).1 hw
    refine (hX.mem_W _).2 ⟨hX.S_V x hx w hwV, ?_⟩
    calc x * w * x⁻¹ * (x * w * x⁻¹) = x * (w * w) * x⁻¹ := by group
      _ = 1 := by rw [hw2]; group

theorem false_of_conj_E_eq_W [Finite G] {g : G} (hg : g ∈ K)
    (hEW : ∀ x, x ∈ W ↔ g⁻¹ * x * g ∈ hX.E) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h₁, hh₁, h₂, hh₂, h1ne, h2ne, h12⟩ := hX.exists_two
  obtain ⟨v₁, hv₁, hv₁H, hv₁j⟩ := hX.exists_trans hX.jS hX.jV hX.j2 hh₁
  obtain ⟨v₂, hv₂, hv₂H, hv₂j⟩ := hX.exists_trans hX.jS hX.jV hX.j2 hh₂
  have hjj : j * j ∈ 𝐇 := by rw [hX.j2]; exact one_mem _
  have hxN : ∀ {v h : G}, h ∈ 𝐇 → v ∈ V → (∀ x ∈ 𝐇, v * x * v⁻¹ = x) →
      (∀ x, x * j ∈ 𝐇 → v * x * v⁻¹ = x * h) →
      g * v * g⁻¹ ∈ K ⊓ normalizer (W : Set G) := by
    intro v h hh hv hvH hvj
    refine mem_inf.2 ⟨mul_mem (mul_mem hg (hX.VK hv)) (inv_mem hg),
      mem_normalizer_of_conj_mem fun w hw => ?_⟩
    rw [hEW]
    have h1 := (hX.trans_act hX.jS hX.jV hX.j2 hh hvH hvj ((hEW w).1 hw)).1
    rwa [show g⁻¹ * (g * v * g⁻¹ * w * (g * v * g⁻¹)⁻¹) * g = v * (g⁻¹ * w * g) * v⁻¹ by
      group]
  set N : Subgroup G := K ⊓ normalizer (W : Set G) with hN
  have hSN : S ≤ N := fun x hx => mem_inf.2 ⟨hX.SK hx, hX.S_le_normalizer_W hx⟩
  obtain ⟨T, hT⟩ := hX.syl.of_le hSN inf_le_left
  set ρ : N →* MulAut W := W.normalizerMonoidHom.comp (inclusion inf_le_right) with hρdef
  have hρ : ∀ (x : N) (w : W), ((ρ x w : W) : G) = (x : G) * w * (x : G)⁻¹ := fun _ _ => rfl
  have hρext : ∀ x y : N, ρ x = ρ y ↔ ∀ w ∈ W, (x : G) * w * (x : G)⁻¹ =
      (y : G) * w * (y : G)⁻¹ := by
    intro x y
    constructor
    · intro h w hw
      have := congrArg (fun φ : MulAut W => ((φ ⟨w, hw⟩ : W) : G)) h
      simpa only [hρ] using this
    · intro h
      exact MulEquiv.ext fun w => Subtype.ext (by rw [hρ, hρ]; exact h w w.2)
  have hρone : ∀ x : N, ρ x = 1 ↔ ∀ w ∈ W, (x : G) * w * (x : G)⁻¹ = w := by
    intro x
    constructor
    · intro h w hw
      have := congrArg (fun φ : MulAut W => ((φ ⟨w, hw⟩ : W) : G)) h
      simpa only [hρ, MulAut.one_apply] using this
    · intro h
      exact MulEquiv.ext fun w => Subtype.ext (by rw [hρ]; exact h w w.2)
  have hρsq : ∀ x : N, ρ x ^ 2 = 1 ↔
      ∀ w ∈ W, (x : G) * ((x : G) * w * (x : G)⁻¹) * (x : G)⁻¹ = w := by
    intro x
    rw [pow_two, ← map_mul, hρone]
    simp only [Subgroup.coe_mul, mul_inv_rev]
    exact forall₂_congr fun w _ => by rw [show (x : G) * x * w * ((x : G)⁻¹ * (x : G)⁻¹) =
      (x : G) * ((x : G) * w * (x : G)⁻¹) * (x : G)⁻¹ by group]
  have hT' : ∀ a ∈ (T : Subgroup N), ∀ b ∈ (T : Subgroup N), ρ a ^ 2 = 1 → ρ b ^ 2 = 1 →
      ρ a ≠ 1 → ρ b ≠ 1 → ρ a = ρ b := by
    have hS : ∀ a ∈ (T : Subgroup N), (a : G) ∈ S := fun a ha => hT ▸ ⟨a, ha, rfl⟩
    have key : ∀ a ∈ (T : Subgroup N), ρ a ^ 2 = 1 → ρ a ≠ 1 → (a : G) * j ∈ V := by
      intro a ha h2 h1
      have haS := hS a ha
      have haV : (a : G) ∉ V := fun haV => h1 ((hρone a).2 fun w hw => by
        rw [hX.V_comm _ haV w (hX.W_le_V hw), mul_inv_cancel_right])
      refine hX.uic _ haS haV (hX.cSW _ (mul_mem haS haS) fun w hw => ?_)
      have := (hρsq a).1 h2 w hw
      calc (a : G) * a * w = (a : G) * ((a : G) * w * (a : G)⁻¹) * (a : G)⁻¹ *
            ((a : G) * (a : G)) := by group
        _ = w * ((a : G) * (a : G)) := by rw [this]
    intro a ha b hb ha2 hb2 ha1 hb1
    have haj := key a ha ha2 ha1
    have hbj := key b hb hb2 hb1
    have hba : (b : G)⁻¹ * a ∈ V := by
      have h1 := hX.S_V j hX.jS _ (mul_mem (inv_mem hbj) haj)
      rwa [hX.j_inv, show j * (((b : G) * j)⁻¹ * ((a : G) * j)) * j = (b : G)⁻¹ * a by
        rw [mul_inv_rev, hX.j_inv, show j * (j * (b : G)⁻¹ * ((a : G) * j)) * j =
          (j * j) * ((b : G)⁻¹ * a) * (j * j) by group, hX.j2, one_mul, mul_one]] at h1
    refine (hρext a b).2 fun w hw => ?_
    have hc := hX.V_comm _ hba w (hX.W_le_V hw)
    calc (a : G) * w * (a : G)⁻¹ = (b : G) * ((b : G)⁻¹ * a * w) * (a : G)⁻¹ := by group
      _ = (b : G) * (w * ((b : G)⁻¹ * a)) * (a : G)⁻¹ := by rw [hc]
      _ = (b : G) * w * (b : G)⁻¹ := by group
  set x₁ : N := ⟨g * v₁ * g⁻¹, hxN hh₁ hv₁ hv₁H hv₁j⟩
  set x₂ : N := ⟨g * v₂ * g⁻¹, hxN hh₂ hv₂ hv₂H hv₂j⟩
  have hsq : ∀ {v h : G}, h ∈ 𝐇 → (∀ x ∈ 𝐇, v * x * v⁻¹ = x) →
      (∀ x, x * j ∈ 𝐇 → v * x * v⁻¹ = x * h) → ∀ w ∈ W,
      g * v * g⁻¹ * (g * v * g⁻¹ * w * (g * v * g⁻¹)⁻¹) * (g * v * g⁻¹)⁻¹ = w := by
    intro v h hh hvH hvj w hw
    have h1 := (hX.trans_act hX.jS hX.jV hX.j2 hh hvH hvj ((hEW w).1 hw)).2
    calc g * v * g⁻¹ * (g * v * g⁻¹ * w * (g * v * g⁻¹)⁻¹) * (g * v * g⁻¹)⁻¹
        = g * (v * (v * (g⁻¹ * w * g) * v⁻¹) * v⁻¹) * g⁻¹ := by group
      _ = w := by rw [h1]; group
  have hw₀ : g * j * g⁻¹ ∈ W := (hEW _).2 (by
    rw [show g⁻¹ * (g * j * g⁻¹) * g = j by group]
    exact hX.self_mem_F8 _ _ _)
  have hval : ∀ {v h : G}, (∀ x, x * j ∈ 𝐇 → v * x * v⁻¹ = x * h) →
      g * v * g⁻¹ * (g * j * g⁻¹) * (g * v * g⁻¹)⁻¹ = g * (j * h) * g⁻¹ := by
    intro v h hvj
    rw [show g * v * g⁻¹ * (g * j * g⁻¹) * (g * v * g⁻¹)⁻¹ = g * (v * j * v⁻¹) * g⁻¹ by group,
      hvj j hjj]
  have hne1 : ρ x₁ ≠ 1 := by
    intro h
    have := (hρone x₁).1 h _ hw₀
    rw [show ((x₁ : N) : G) = g * v₁ * g⁻¹ from rfl, hval hv₁j] at this
    apply h1ne
    have := congrArg (fun y => j⁻¹ * (g⁻¹ * y * g)) this
    simpa [mul_assoc] using this
  have hne2 : ρ x₂ ≠ 1 := by
    intro h
    have := (hρone x₂).1 h _ hw₀
    rw [show ((x₂ : N) : G) = g * v₂ * g⁻¹ from rfl, hval hv₂j] at this
    apply h2ne
    have := congrArg (fun y => j⁻¹ * (g⁻¹ * y * g)) this
    simpa [mul_assoc] using this
  have hcomm : ρ x₁ * ρ x₂ = ρ x₂ * ρ x₁ := by
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show g * v₁ * g⁻¹ * (g * v₂ * g⁻¹) = g * v₂ * g⁻¹ * (g * v₁ * g⁻¹)
    rw [show g * v₁ * g⁻¹ * (g * v₂ * g⁻¹) = g * (v₁ * v₂) * g⁻¹ by group,
      hX.V_comm v₁ hv₁ v₂ hv₂]
    group
  have hx1sq : ρ x₁ ^ 2 = 1 := (hρsq x₁).2 (hsq hh₁ hv₁H hv₁j)
  have hx2sq : ρ x₂ ^ 2 = 1 := (hρsq x₂).2 (hsq hh₂ hv₂H hv₂j)
  have heq := eq_of_sylow_image ρ T hT' hx1sq hx2sq hcomm hne1 hne2
  have := (hρext x₁ x₂).1 heq _ hw₀
  rw [show ((x₁ : N) : G) = g * v₁ * g⁻¹ from rfl, show ((x₂ : N) : G) = g * v₂ * g⁻¹ from rfl,
    hval hv₁j, hval hv₂j] at this
  apply h12
  have := congrArg (fun y => j⁻¹ * (g⁻¹ * y * g)) this
  simpa [mul_assoc] using this

theorem sq_act_of_mem_V {j' : G} (hj'S : j' ∈ S) (hj'V : j' ∉ V) (hj'2 : j' * j' = 1) {u : G}
    (hu : u ∈ V) (huN : u ∈ normalizer (hX.F8 hj'S hj'V hj'2 : Set G)) {f : G}
    (hf : f ∈ hX.F8 hj'S hj'V hj'2) : u * (u * f * u⁻¹) * u⁻¹ = f := by
  by_cases hfH : f ∈ 𝐇
  · have h1 : u * f * u⁻¹ = f := by rw [hX.V_comm u hu f (hX.H_le_V hfH), mul_inv_cancel_right]
    rw [h1, h1]
  · have hfS : f ∈ S := hX.F8_le_S _ _ _ hf
    have hufu : u * f * u⁻¹ ∈ hX.F8 hj'S hj'V hj'2 := (mem_normalizer_iff.1 huN f).1 hf
    set d := f⁻¹ * (u * f * u⁻¹) with hd
    have hdV : d ∈ V := by
      have h1 : f⁻¹ * u * f ∈ V := by
        have := hX.S_V f⁻¹ (inv_mem hfS) u hu
        rwa [inv_inv] at this
      rw [hd, show f⁻¹ * (u * f * u⁻¹) = f⁻¹ * u * f * u⁻¹ by group]
      exact mul_mem h1 (inv_mem hu)
    have hdF : d ∈ hX.F8 hj'S hj'V hj'2 := mul_mem (inv_mem hf) hufu
    have hdH : d ∈ 𝐇 := hX.mem_H_of_mem_F8 hj'S hj'V hj'2 hdF hdV
    have h1 : u * f * u⁻¹ = f * d := by rw [hd]; group
    rw [h1, show u * (f * d) * u⁻¹ = (u * f * u⁻¹) * (u * d * u⁻¹) by group, h1,
      hX.V_comm u hu d hdV, mul_inv_cancel_right, mul_assoc, hX.H_sq hdH, mul_one]

theorem false_of_conj [Finite G]
    (halt : (∀ j₃ ∈ S, j₃ ∉ V → j₃ * j₃ = 1 → ∀ q ∈ S, q * j₃ * q⁻¹ * j₃ ∈ W →
        q ∈ V ∨ q * j ∈ V) ∨
      (∃ z ∈ 𝐇, z ≠ 1 ∧ (∀ x ∈ K, x * z = z * x) ∧
        (∀ a ∈ S, ∀ b ∈ S, a⁻¹ * b⁻¹ * a * b ∈ V) ∧
        ∀ j₃ ∈ S, j₃ ∉ V → j₃ * j₃ = 1 → ∃ y₀ ∈ S, ∃ y₁ ∈ S,
          (∀ f, f ∈ 𝐇 ∨ f * j₃ ∈ 𝐇 → y₀ * f * y₀⁻¹ = f ∨ y₀ * f * y₀⁻¹ = f * z) ∧
          (∀ f, f ∈ 𝐇 ∨ f * j₃ ∈ 𝐇 → y₁ * f * y₁⁻¹ = f ∨ y₁ * f * y₁⁻¹ = f * z) ∧
          y₁⁻¹ * y₀⁻¹ * y₁ * y₀ ∈ 𝐇 ∧ y₁⁻¹ * y₀⁻¹ * y₁ * y₀ ≠ 1 ∧
          y₁⁻¹ * y₀⁻¹ * y₁ * y₀ ≠ z))
    {k : G} (hk : k ∈ K) (hkj : k * j * k⁻¹ ∈ V) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k', hk', hk'j, hk'E⟩ := hX.normalize hk hkj
  have hjE : j ∈ hX.E := hX.self_mem_F8 _ _ _
  have hES : hX.E ≤ S := hX.F8_le_S _ _ _
  have hE2 : ∀ x ∈ hX.E, x * x = 1 := fun x hx => hX.F8_sq _ _ _ hx
  have hEc : ∀ x ∈ hX.E, ∀ y ∈ hX.E, x * y = y * x := fun x hx y hy => hX.F8_comm _ _ _ hx hy
  set F₀ := hX.E.map (MulAut.conj k').toMonoidHom with hF₀
  have hmem₀ : ∀ x, x ∈ F₀ ↔ k'⁻¹ * x * k' ∈ hX.E := fun x => mem_map_conj
  have hF₀S : F₀ ≤ S := by
    rintro _ ⟨e, he, rfl⟩
    exact hk'E e he
  have hF₀2 : ∀ x ∈ F₀, x * x = 1 := by
    rintro _ ⟨e, he, rfl⟩
    show k' * e * k'⁻¹ * (k' * e * k'⁻¹) = 1
    rw [show k' * e * k'⁻¹ * (k' * e * k'⁻¹) = k' * (e * e) * k'⁻¹ by group, hE2 e he]
    group
  have hF₀c : ∀ x ∈ F₀, ∀ y ∈ F₀, x * y = y * x := by
    rintro _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩
    show k' * e * k'⁻¹ * (k' * e' * k'⁻¹) = k' * e' * k'⁻¹ * (k' * e * k'⁻¹)
    rw [show k' * e * k'⁻¹ * (k' * e' * k'⁻¹) = k' * (e * e') * k'⁻¹ by group, hEc e he e' he']
    group
  have hF₀8 : Nat.card F₀ = 8 := by
    rw [hF₀, card_map_of_injective (MulAut.conj k').injective]
    exact hX.card_F8 _ _ _
  rcases hX.classify hF₀S hF₀2 hF₀8 hF₀c with hW | ⟨j₂, hj₂S, hj₂V, hj₂2, hF₀eq⟩
  · exact hX.false_of_conj_E_eq_W hk' fun x => (SetLike.ext_iff.1 hW x).symm.trans (hmem₀ x)
  set w := k' * j * k'⁻¹ with hw
  have hwF₀ : w ∈ F₀ := (hmem₀ w).2 (by rw [hw]; simpa [mul_assoc] using hjE)
  have hwH : w ∈ 𝐇 := hX.mem_H_of_mem_F8 hj₂S hj₂V hj₂2 (hF₀eq ▸ hwF₀) hk'j
  set N₀ : Subgroup G := K ⊓ normalizer (F₀ : Set G) with hN₀
  obtain ⟨Q, hQ⟩ := exists_isSylowOf 2 N₀
  obtain ⟨c, hcK, hc⟩ := exists_conj_le hX.syl (hQ.le.trans inf_le_left) hQ.isPGroup
  have hF₀Q : F₀ ≤ Q := le_of_isSylowOf hQ (fun x hx => ⟨hX.SK (hF₀S hx), le_normalizer hx⟩)
    (hX.syl.isPGroup.to_le hF₀S) inf_le_right
  set F₁ := F₀.map (MulAut.conj c).toMonoidHom with hF₁
  have hmem₁ : ∀ x, x ∈ F₁ ↔ c⁻¹ * x * c ∈ F₀ := fun x => mem_map_conj
  have hF₁S : F₁ ≤ S := by
    rintro _ ⟨y, hy, rfl⟩
    exact hc y (hF₀Q hy)
  have hF₁2 : ∀ x ∈ F₁, x * x = 1 := by
    rintro _ ⟨e, he, rfl⟩
    show c * e * c⁻¹ * (c * e * c⁻¹) = 1
    rw [show c * e * c⁻¹ * (c * e * c⁻¹) = c * (e * e) * c⁻¹ by group, hF₀2 e he]
    group
  have hF₁c : ∀ x ∈ F₁, ∀ y ∈ F₁, x * y = y * x := by
    rintro _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩
    show c * e * c⁻¹ * (c * e' * c⁻¹) = c * e' * c⁻¹ * (c * e * c⁻¹)
    rw [show c * e * c⁻¹ * (c * e' * c⁻¹) = c * (e * e') * c⁻¹ by group, hF₀c e he e' he']
    group
  have hF₁8 : Nat.card F₁ = 8 := by
    rw [hF₁, card_map_of_injective (MulAut.conj c).injective, hF₀8]
  set N₁ : Subgroup G := K ⊓ normalizer (F₁ : Set G) with hN₁
  have hN₁eq : N₀.map (MulAut.conj c).toMonoidHom = N₁ := by
    ext x
    rw [mem_map_conj, hN₀, hN₁, mem_inf, mem_inf]
    refine and_congr ⟨fun h => ?_, fun h => mul_mem (mul_mem (inv_mem hcK) h) hcK⟩ ⟨fun h => ?_,
      fun h => ?_⟩
    · simpa [mul_assoc] using mul_mem (mul_mem hcK h) (inv_mem hcK)
    · refine mem_normalizer_of_conj_mem fun f hf => (hmem₁ _).2 ?_
      have h1 := (mem_normalizer_iff.1 h _).1 ((hmem₁ f).1 hf)
      rwa [show c⁻¹ * x * c * (c⁻¹ * f * c) * (c⁻¹ * x * c)⁻¹ = c⁻¹ * (x * f * x⁻¹) * c by
        group] at h1
    · refine mem_normalizer_of_conj_mem fun f hf => ?_
      have h1 := (mem_normalizer_iff.1 h _).1 ((hmem₁ (c * f * c⁻¹)).2 (by
        rwa [show c⁻¹ * (c * f * c⁻¹) * c = f by group]))
      rw [hmem₁] at h1
      rwa [show c⁻¹ * (x * (c * f * c⁻¹) * x⁻¹) * c = c⁻¹ * x * c * f * (c⁻¹ * x * c)⁻¹ by
        group] at h1
  have hSyl₁ : IsSylowOf 2 (S ⊓ normalizer (F₁ : Set G)) N₁ := by
    have hQ₁ := isSylowOf_map_conj hQ c
    rw [hN₁eq] at hQ₁
    have hle : Q.map (MulAut.conj c).toMonoidHom ≤ S ⊓ normalizer (F₁ : Set G) := by
      rintro _ ⟨y, hy, rfl⟩
      refine mem_inf.2 ⟨hc y hy, ?_⟩
      have : (MulAut.conj c).toMonoidHom y ∈ N₁ := hN₁eq ▸ ⟨y, hQ.le hy, rfl⟩
      exact (mem_inf.1 this).2
    have heq := hQ₁.eq_of_le hle (fun x hx => mem_inf.2 ⟨hX.SK (mem_inf.1 hx).1, (mem_inf.1 hx).2⟩)
      (hX.syl.isPGroup.to_le inf_le_left)
    rw [heq]
    exact hQ₁
  rcases hX.classify hF₁S hF₁2 hF₁8 hF₁c with hW₁ | ⟨j₃, hj₃S, hj₃V, hj₃2, hF₁eq⟩
  · refine hX.false_of_conj_E_eq_W (g := c * k') (mul_mem hcK hk') fun x => ?_
    rw [← SetLike.ext_iff.1 hW₁ x, hmem₁, hmem₀]
    rw [show k'⁻¹ * (c⁻¹ * x * c) * k' = (c * k')⁻¹ * x * (c * k') by group]
  have hmemE₁ : ∀ x, x ∈ F₁ ↔ (c * k')⁻¹ * x * (c * k') ∈ hX.E := fun x => by
    rw [hmem₁, hmem₀, show k'⁻¹ * (c⁻¹ * x * c) * k' = (c * k')⁻¹ * x * (c * k') by group]
  have hmemF8 : ∀ x, x ∈ F₁ ↔ c⁻¹ * x * c ∈ hX.F8 hj₂S hj₂V hj₂2 := fun x => by
    rw [hmem₁, hF₀eq]
  have hP₁ : ∀ x ∈ F₁, ∀ y ∈ F₁, ((c * k')⁻¹ * (x * y) * (c * k') ∈ 𝐇 ↔
      ((c * k')⁻¹ * x * (c * k') ∈ 𝐇 ↔ (c * k')⁻¹ * y * (c * k') ∈ 𝐇)) := by
    intro x hx y hy
    rw [show (c * k')⁻¹ * (x * y) * (c * k') =
      ((c * k')⁻¹ * x * (c * k')) * ((c * k')⁻¹ * y * (c * k')) by group]
    exact hX.F8_mul_mem_iff _ _ _ ((hmemE₁ x).1 hx) ((hmemE₁ y).1 hy)
  have hP₂ : ∀ x ∈ F₁, ∀ y ∈ F₁, (c⁻¹ * (x * y) * c ∈ 𝐇 ↔
      (c⁻¹ * x * c ∈ 𝐇 ↔ c⁻¹ * y * c ∈ 𝐇)) := by
    intro x hx y hy
    rw [show c⁻¹ * (x * y) * c = (c⁻¹ * x * c) * (c⁻¹ * y * c) by group]
    exact hX.F8_mul_mem_iff _ _ _ ((hmemF8 x).1 hx) ((hmemF8 y).1 hy)
  have htrans₁ : ∀ {h₀ : G}, h₀ ∈ 𝐇 → ∃ t ∈ N₁, ∀ f ∈ F₁,
      ((c * k')⁻¹ * f * (c * k') ∈ 𝐇 → t * f * t⁻¹ = f) ∧
      ((c * k')⁻¹ * f * (c * k') ∉ 𝐇 → t * f * t⁻¹ = f * (c * k' * h₀ * (c * k')⁻¹)) := by
    intro h₀ hh₀
    obtain ⟨v, hv, hvH, hvj⟩ := hX.exists_trans hX.jS hX.jV hX.j2 hh₀
    have hact : ∀ f ∈ F₁,
        ((c * k')⁻¹ * f * (c * k') ∈ 𝐇 →
          c * k' * v * (c * k')⁻¹ * f * (c * k' * v * (c * k')⁻¹)⁻¹ = f) ∧
        ((c * k')⁻¹ * f * (c * k') ∉ 𝐇 →
          c * k' * v * (c * k')⁻¹ * f * (c * k' * v * (c * k')⁻¹)⁻¹ =
            f * (c * k' * h₀ * (c * k')⁻¹)) := by
      intro f hf
      have e : c * k' * v * (c * k')⁻¹ * f * (c * k' * v * (c * k')⁻¹)⁻¹ =
          (c * k') * (v * ((c * k')⁻¹ * f * (c * k')) * v⁻¹) * (c * k')⁻¹ := by group
      refine ⟨fun h => by rw [e, hvH _ h]; group, fun h => ?_⟩
      rw [e, hvj _ (((hmemE₁ f).1 hf).resolve_left h)]
      group
    refine ⟨c * k' * v * (c * k')⁻¹, mem_inf.2 ⟨mul_mem (mul_mem (mul_mem hcK hk') (hX.VK hv))
      (inv_mem (mul_mem hcK hk')), mem_normalizer_of_conj_mem fun f hf => ?_⟩, hact⟩
    by_cases h : (c * k')⁻¹ * f * (c * k') ∈ 𝐇
    · rw [(hact f hf).1 h]
      exact hf
    · rw [(hact f hf).2 h]
      refine mul_mem hf ((hmemE₁ _).2 ?_)
      rw [show (c * k')⁻¹ * (c * k' * h₀ * (c * k')⁻¹) * (c * k') = h₀ by group]
      exact hX.H_le_F8 _ _ _ hh₀
  have htrans₂ : ∀ {h₀ : G}, h₀ ∈ 𝐇 → ∃ t ∈ N₁, ∀ f ∈ F₁,
      (c⁻¹ * f * c ∈ 𝐇 → t * f * t⁻¹ = f) ∧
      (c⁻¹ * f * c ∉ 𝐇 → t * f * t⁻¹ = f * (c * h₀ * c⁻¹)) := by
    intro h₀ hh₀
    obtain ⟨v, hv, hvH, hvj⟩ := hX.exists_trans hj₂S hj₂V hj₂2 hh₀
    have hact : ∀ f ∈ F₁,
        (c⁻¹ * f * c ∈ 𝐇 → c * v * c⁻¹ * f * (c * v * c⁻¹)⁻¹ = f) ∧
        (c⁻¹ * f * c ∉ 𝐇 → c * v * c⁻¹ * f * (c * v * c⁻¹)⁻¹ = f * (c * h₀ * c⁻¹)) := by
      intro f hf
      have e : c * v * c⁻¹ * f * (c * v * c⁻¹)⁻¹ = c * (v * (c⁻¹ * f * c) * v⁻¹) * c⁻¹ := by
        group
      refine ⟨fun h => by rw [e, hvH _ h]; group, fun h => ?_⟩
      rw [e, hvj _ (((hmemF8 f).1 hf).resolve_left h)]
      group
    refine ⟨c * v * c⁻¹, mem_inf.2 ⟨mul_mem (mul_mem hcK (hX.VK hv)) (inv_mem hcK),
      mem_normalizer_of_conj_mem fun f hf => ?_⟩, hact⟩
    by_cases h : c⁻¹ * f * c ∈ 𝐇
    · rw [(hact f hf).1 h]
      exact hf
    · rw [(hact f hf).2 h]
      refine mul_mem hf ((hmemF8 _).2 ?_)
      rw [show c⁻¹ * (c * h₀ * c⁻¹) * c = h₀ by group]
      exact hX.H_le_F8 _ _ _ hh₀
  set a₂ := c * w * c⁻¹ with ha₂def
  have ha₂ : a₂ ∈ F₁ := (hmem₁ a₂).2 (by rw [ha₂def]; simpa [mul_assoc] using hwF₀)
  have h22 : c⁻¹ * a₂ * c ∈ 𝐇 := by rw [ha₂def]; simpa [mul_assoc] using hwH
  have h12 : (c * k')⁻¹ * a₂ * (c * k') ∉ 𝐇 := by
    rw [ha₂def, hw, show (c * k')⁻¹ * (c * (k' * j * k'⁻¹) * c⁻¹) * (c * k') = j by group]
    exact hX.not_mem_H hX.jV
  have hmem₃ : ∀ f, f ∈ F₁ ↔ f ∈ 𝐇 ∨ f * j₃ ∈ 𝐇 := fun f => by rw [hF₁eq]; rfl
  have hHF₁ : 𝐇 ≤ F₁ := fun h hh => (hmem₃ h).2 (Or.inl hh)
  rcases halt with hN2 | ⟨z, hzH, hz1, hzK, hScomm, hsp⟩
  ·
    obtain ⟨h₀, hh₀, h01, hk'h₀⟩ : ∃ h₀ ∈ 𝐇, h₀ ≠ 1 ∧ k' * h₀ * k'⁻¹ ∈ 𝐇 := by
      obtain ⟨h, hh, h', hh', hne, hne', hhh'⟩ := hX.exists_two
      have hmF : ∀ {x}, x ∈ 𝐇 → k' * x * k'⁻¹ ∈ hX.F8 hj₂S hj₂V hj₂2 := fun {x} hx => by
        rw [← hF₀eq]
        exact (hmem₀ _).2 (by simpa [mul_assoc] using hX.H_le_F8 _ _ _ hx)
      by_cases h1 : k' * h * k'⁻¹ ∈ 𝐇
      · exact ⟨h, hh, hne, h1⟩
      by_cases h2 : k' * h' * k'⁻¹ ∈ 𝐇
      · exact ⟨h', hh', hne', h2⟩
      refine ⟨h * h', mul_mem hh hh', fun he => hhh' ?_, ?_⟩
      · calc h = h * (h' * h') := by rw [hX.H_sq hh', mul_one]
          _ = h' := by rw [← mul_assoc, he, one_mul]
      · rw [show k' * (h * h') * k'⁻¹ = (k' * h * k'⁻¹) * (k' * h' * k'⁻¹) by group]
        exact (hX.F8_mul_mem_iff _ _ _ (hmF hh) (hmF hh')).2 (iff_of_false h1 h2)
    set a₁ := c * k' * h₀ * (c * k')⁻¹ with ha₁def
    have e₁ : (c * k')⁻¹ * a₁ * (c * k') = h₀ := by rw [ha₁def]; group
    have ha₁ : a₁ ∈ F₁ := (hmemE₁ a₁).2 (by rw [e₁]; exact hX.H_le_F8 _ _ _ hh₀)
    have h11 : (c * k')⁻¹ * a₁ * (c * k') ∈ 𝐇 := by rw [e₁]; exact hh₀
    have h21 : c⁻¹ * a₁ * c ∈ 𝐇 := by
      rw [ha₁def, show c⁻¹ * (c * k' * h₀ * (c * k')⁻¹) * c = k' * h₀ * k'⁻¹ by group]
      exact hk'h₀
    have ha₁1 : a₁ ≠ 1 := fun h => h01 (by rw [← e₁, h]; group)
    obtain ⟨t₁, ht₁N, ht₁⟩ := htrans₁ hh₀
    obtain ⟨t₂, ht₂N, ht₂⟩ := htrans₂ hwH
    have hM : ∀ f ∈ F₁, (c⁻¹ * f * c ∈ 𝐇 → (t₁ * t₂) ^ 2 * f * ((t₁ * t₂) ^ 2)⁻¹ = f) ∧
        (c⁻¹ * f * c ∉ 𝐇 → (t₁ * t₂) ^ 2 * f * ((t₁ * t₂) ^ 2)⁻¹ = f * a₁) :=
      fun f hf => sq_of_two_trans (F := F₁) (fun f => (c * k')⁻¹ * f * (c * k') ∈ 𝐇)
        (fun f => c⁻¹ * f * c ∈ 𝐇) hF₁c hF₁2 hP₁ hP₂ ha₁ ha₂ h11 h21 h12 h22 ht₁ ht₂ hf
    have h4 : ∀ f ∈ F₁, (t₁ * t₂) ^ 4 * f * ((t₁ * t₂) ^ 4)⁻¹ = f := by
      intro f hf
      rw [show (t₁ * t₂) ^ 4 * f * ((t₁ * t₂) ^ 4)⁻¹ = (t₁ * t₂) ^ 2 *
        ((t₁ * t₂) ^ 2 * f * ((t₁ * t₂) ^ 2)⁻¹) * ((t₁ * t₂) ^ 2)⁻¹ by
          rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add]; group]
      by_cases hP : c⁻¹ * f * c ∈ 𝐇
      · rw [(hM f hf).1 hP, (hM f hf).1 hP]
      · have hfa : f * a₁ ∈ F₁ := mul_mem hf ha₁
        have hP' : c⁻¹ * (f * a₁) * c ∉ 𝐇 := fun h => hP (((hP₂ f hf a₁ ha₁).1 h).2 h21)
        rw [(hM f hf).2 hP, (hM _ hfa).2 hP', mul_assoc, hF₁2 a₁ ha₁, mul_one]
    have he₂ : c * j₂ * c⁻¹ ∈ F₁ := (hmemF8 _).2 (by
      rw [show c⁻¹ * (c * j₂ * c⁻¹) * c = j₂ by group]
      exact hX.self_mem_F8 _ _ _)
    have hne₂ : c⁻¹ * (c * j₂ * c⁻¹) * c ∉ 𝐇 := by
      rw [show c⁻¹ * (c * j₂ * c⁻¹) * c = j₂ by group]
      exact hX.not_mem_H hj₂V
    have h2 : (t₁ * t₂) ^ 2 * (c * j₂ * c⁻¹) * ((t₁ * t₂) ^ 2)⁻¹ ≠ c * j₂ * c⁻¹ := by
      rw [(hM _ he₂).2 hne₂]
      intro h
      exact ha₁1 (by simpa using h)
    have hT₀sq : ∀ s ∈ S ⊓ normalizer (F₁ : Set G), ∀ f ∈ F₁, s * (s * f * s⁻¹) * s⁻¹ = f := by
      intro s hs f hf
      obtain ⟨hsS, hsN⟩ := mem_inf.1 hs
      have hsN' : s ∈ normalizer (hX.F8 hj₃S hj₃V hj₃2 : Set G) := hF₁eq ▸ hsN
      have hf' : f ∈ hX.F8 hj₃S hj₃V hj₃2 := hF₁eq ▸ hf
      have hsj : s * j₃ * s⁻¹ ∈ hX.F8 hj₃S hj₃V hj₃2 :=
        (mem_normalizer_iff.1 hsN' j₃).1 (hX.self_mem_F8 _ _ _)
      have hsjV : s * j₃ * s⁻¹ ∉ V := fun h => hj₃V (by
        simpa [mul_assoc] using hX.S_V s⁻¹ (inv_mem hsS) _ h)
      have hW' : s * j₃ * s⁻¹ * j₃ ∈ W :=
        (mem_inf.1 (((hX.mem_F8 _ _ _).1 hsj).resolve_left fun h => hsjV (hX.H_le_V h))).1
      have hj₃c : ∀ y ∈ hX.F8 hj₃S hj₃V hj₃2, j₃ * y * j₃⁻¹ = y := fun y hy => by
        rw [hX.F8_comm _ _ _ (hX.self_mem_F8 _ _ _) hy, mul_inv_cancel_right]
      rcases hN2 j₃ hj₃S hj₃V hj₃2 s hsS hW' with hsV | hsjV'
      · exact hX.sq_act_of_mem_V hj₃S hj₃V hj₃2 hsV hsN' hf'
      · set u := j₃ * s with hu
        have huV : u ∈ V := by
          rw [hu, show j₃ * s = j₃ * j * (j * s) by
            rw [mul_assoc j₃ j, ← mul_assoc j j, hX.j2, one_mul]]
          exact mul_mem (hX.mul_j_mem hj₃S hj₃V hj₃2) (hX.j_mul_mem hsjV')
        have huN : u ∈ normalizer (hX.F8 hj₃S hj₃V hj₃2 : Set G) :=
          mul_mem (le_normalizer (hX.self_mem_F8 _ _ _)) hsN'
        have hs : s = j₃ * u := by rw [hu, ← mul_assoc, hj₃2, one_mul]
        have hufu : u * f * u⁻¹ ∈ hX.F8 hj₃S hj₃V hj₃2 := (mem_normalizer_iff.1 huN f).1 hf'
        calc s * (s * f * s⁻¹) * s⁻¹
            = j₃ * (u * (j₃ * (u * f * u⁻¹) * j₃⁻¹) * u⁻¹) * j₃⁻¹ := by rw [hs]; group
          _ = j₃ * (u * (u * f * u⁻¹) * u⁻¹) * j₃⁻¹ := by rw [hj₃c _ hufu]
          _ = j₃ * f * j₃⁻¹ := by rw [hX.sq_act_of_mem_V hj₃S hj₃V hj₃2 huV huN hf']
          _ = f := hj₃c f hf'
    exact false_of_order_four inf_le_right hSyl₁ hT₀sq (mul_mem ht₁N ht₂N) h4 he₂ h2
  ·
    obtain ⟨y₀, hy₀S, y₁, hy₁S, hy₀z, hy₁z, hcH, hc1, hcz⟩ := hsp j₃ hj₃S hj₃V hj₃2
    have hzF : z ∈ F₁ := hHF₁ hzH
    have hz2 : z * z = 1 := hX.H_sq hzH
    have hyN : ∀ {y : G}, y ∈ S → (∀ f, f ∈ 𝐇 ∨ f * j₃ ∈ 𝐇 →
        y * f * y⁻¹ = f ∨ y * f * y⁻¹ = f * z) → y ∈ S ⊓ N₁ := by
      intro y hyS hyz
      refine mem_inf.2 ⟨hyS, mem_inf.2 ⟨hX.SK hyS, mem_normalizer_of_conj_mem fun f hf => ?_⟩⟩
      rcases hyz f ((hmem₃ f).1 hf) with h | h <;> rw [h]
      · exact hf
      · exact mul_mem hf hzF
    have hSyl' : IsSylowOf 2 (S ⊓ N₁) N₁ := by
      have : S ⊓ N₁ = S ⊓ normalizer (F₁ : Set G) := by
        rw [hN₁, ← inf_assoc, inf_of_le_left hX.SK]
      rw [this]
      exact hSyl₁
    obtain ⟨x, hxN, a, haH, hxa⟩ : ∃ x ∈ N₁, ∃ a ∈ 𝐇, x * a * x⁻¹ ∉ 𝐇 := by
      by_cases ha₂H : a₂ ∈ 𝐇
      · obtain ⟨h', hh', ha⟩ : ∃ h' ∈ 𝐇, c * k' * h' * (c * k')⁻¹ ∉ 𝐇 := by
          by_contra hcon
          push Not at hcon
          have hle : (𝐇).map (MulAut.conj (c * k')).toMonoidHom ≤ 𝐇 := by
            rintro _ ⟨h', hh', rfl⟩
            exact hcon h' hh'
          have heq := eq_of_le_of_card_ge hle
            (by rw [card_map_of_injective (MulAut.conj (c * k')).injective])
          apply h12
          have : a₂ ∈ (𝐇).map (MulAut.conj (c * k')).toMonoidHom := by rw [heq]; exact ha₂H
          exact mem_map_conj.1 this
        obtain ⟨t, htN, ht⟩ := htrans₁ hh'
        refine ⟨t, htN, a₂, ha₂H, ?_⟩
        rw [(ht a₂ ha₂).2 h12]
        intro h
        exact ha (by simpa using mul_mem (inv_mem ha₂H) h)
      · obtain ⟨h, hh, hcon⟩ : ∃ h ∈ 𝐇, c⁻¹ * h * c ∉ 𝐇 := by
          by_contra hcon
          push Not at hcon
          have hle : (𝐇).map (MulAut.conj c⁻¹).toMonoidHom ≤ 𝐇 := by
            rintro _ ⟨h, hh, rfl⟩
            simpa [mul_assoc] using hcon h hh
          have heq := eq_of_le_of_card_ge hle
            (by rw [card_map_of_injective (MulAut.conj c⁻¹).injective])
          apply ha₂H
          have : w ∈ (𝐇).map (MulAut.conj c⁻¹).toMonoidHom := by rw [heq]; exact hwH
          rw [mem_map_conj, inv_inv] at this
          exact this
        obtain ⟨t, htN, ht⟩ := htrans₂ hwH
        refine ⟨t, htN, h, hh, ?_⟩
        rw [(ht h (hHF₁ hh)).2 hcon]
        intro h'
        exact ha₂H (by simpa using mul_mem (inv_mem hh) h')
    exact hxa (conj_mem_of_frattini inf_le_right hz2 (fun x hx => hzK x (mem_inf.1 hx).1) hzH
      hz1 hHF₁ hX.card_H (fun y hy hyV => hX.mem_H_of_mem_F8 hj₃S hj₃V hj₃2 (hF₁eq ▸ hy) hyV)
      hSyl' hScomm (hyN hy₀S hy₀z) (hyN hy₁S hy₁z) (fun f hf => hy₀z f ((hmem₃ f).1 hf))
      (fun f hf => hy₁z f ((hmem₃ f).1 hf)) hcH hc1 hcz hxN haH)

end ExtSetting

end CFSG.OddStandard.ONan76
