module

public import CFSG.LocalAnalysis.EvenBN.U4.RootCenter
public import CFSG.LocalAnalysis.EvenBN.Common.CoprimeQuotient

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.Common
open scoped commutatorElement Pointwise

section ModelFacts

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

include h in
theorem odd_card_range_units {X : Type*} [Group X] (φ : Kˣ →* X) : Odd (Nat.card φ.range) := by
  have : Finite K := h.finite
  have hd := Subgroup.card_range_dvd φ
  rw [Nat.card_units, h.card] at hd
  refine Odd.of_dvd_nat ?_ hd
  have h1 : 1 ≤ 2 ^ (2 * f) := Nat.one_le_two_pow
  have h2 : Even (2 ^ (2 * f)) := (Nat.even_pow.2 ⟨even_two, by have := h.one_le; omega⟩)
  exact Nat.Even.sub_odd h1 h2 odd_one

theorem odd_card_miyamotoI2r1 : Odd (Nat.card (miyamotoI2r1 h)) := by
  have e : miyamotoI2r1 h =
      ((MulAut.conj (miyamotoR1 K)⁻¹).toMonoidHom.comp (miyamotoI2Hom h)).range := by
    rw [MonoidHom.range_comp]
    rfl
  rw [e]
  exact odd_card_range_units h _

theorem odd_card_miyamotoI2 : Odd (Nat.card (miyamotoI2 h)) :=
  odd_card_range_units h _

theorem exists_unit_weights_ne_one (hf : 2 ≤ f) : ∃ a : Kˣ,
    (a : K) ^ (2 ^ f - 1) * h.bar ((a : K) ^ 2) ≠ 1 ∧
      (a : K) ^ 2 * h.bar ((a : K) ^ 2) ≠ 1 := by
  obtain ⟨a, -, ha⟩ := exists_generator_units h
  have hq : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hbar : ∀ x : K, h.bar x = x ^ 2 ^ f := fun x => h.bar_apply x
  refine ⟨a, fun e => ?_, fun e => ?_⟩
  · have e' : a ^ (3 * 2 ^ f - 1) = 1 := by
      apply Units.ext
      rw [hbar, ← pow_mul] at e
      rw [Units.val_pow_eq_pow_val, Units.val_one, ← e, ← pow_add]
      congr 1
      omega
    refine pow_ne_one_of_lt (by omega) ?_ e'
    rw [ha]
    have : 2 ^ f * 4 ≤ 2 ^ f * 2 ^ f := Nat.mul_le_mul_left _ hq
    have : (2 ^ f) ^ 2 = 2 ^ f * 2 ^ f := sq _
    omega
  · have e' : a ^ (2 * 2 ^ f + 2) = 1 := by
      apply Units.ext
      rw [hbar, ← pow_mul] at e
      rw [Units.val_pow_eq_pow_val, Units.val_one, ← e, ← pow_add]
      congr 1
      ring
    refine pow_ne_one_of_lt (by omega) ?_ e'
    rw [ha]
    have : 2 ^ f * 4 ≤ 2 ^ f * 2 ^ f := Nat.mul_le_mul_left _ hq
    have : (2 ^ f) ^ 2 = 2 ^ f * 2 ^ f := sq _
    omega

theorem miyamotoXGL_rootC_mul (c c' : K) :
    miyamotoXGL h 0 0 c 0 * miyamotoXGL h 0 0 c' 0 = miyamotoXGL h 0 0 (c + c') 0 := by
  have : CharP K 2 := h.charP
  rw [miyamotoXGL_mul h (map_zero _), miyamotoXGL_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp

theorem miyamotoXGL_rootB_mul {b : K} (hb : h.bar b = b) (b' : K) :
    miyamotoXGL h 0 b 0 0 * miyamotoXGL h 0 b' 0 0 = miyamotoXGL h 0 (b + b') 0 0 := by
  have : CharP K 2 := h.charP
  rw [miyamotoXGL_mul h hb, miyamotoXGL_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp

theorem exists_I2r1_rootC (hf : 2 ≤ f) (c : K) : ∃ D ∈ miyamotoI2r1 h, ∃ c' : K,
    miyamotoXGL h 0 0 c 0 = (D⁻¹ * miyamotoXGL h 0 0 c' 0 * D) * (miyamotoXGL h 0 0 c' 0)⁻¹ := by
  have : CharP K 2 := h.charP
  obtain ⟨a, ha, -⟩ := exists_unit_weights_ne_one h hf
  set ω := (a : K) ^ (2 ^ f - 1) * h.bar ((a : K) ^ 2) with hω
  have hω1 : ω + 1 ≠ 0 := fun e => ha (by linear_combination e - CharTwo.two_eq_zero (R := K))
  refine ⟨_, (mem_miyamotoI2r1 h).2 ⟨a, rfl⟩, c / (ω + 1), ?_⟩
  rw [miyamotoI2r1Hom_conj]
  simp only [mul_zero]
  rw [← hω, eq_mul_inv_iff_mul_eq, miyamotoXGL_rootC_mul, miyamotoXGL_inj]
  refine ⟨rfl, rfl, ?_, rfl⟩
  field_simp
  linear_combination c * CharTwo.two_eq_zero (R := K)

theorem exists_I2r1_rootB (hf : 2 ≤ f) {b : K} (hb : h.bar b = b) : ∃ D ∈ miyamotoI2r1 h,
    ∃ b' : K, h.bar b' = b' ∧
      miyamotoXGL h 0 b 0 0 = (D⁻¹ * miyamotoXGL h 0 b' 0 0 * D) * (miyamotoXGL h 0 b' 0 0)⁻¹ := by
  have : CharP K 2 := h.charP
  obtain ⟨a, -, ha⟩ := exists_unit_weights_ne_one h hf
  set ω := (a : K) ^ 2 * h.bar ((a : K) ^ 2) with hω
  have hωF : h.bar ω = ω := by rw [hω, map_mul, h.bar_bar, mul_comm]
  have hω1 : ω + 1 ≠ 0 := fun e => ha (by linear_combination e - CharTwo.two_eq_zero (R := K))
  have hb' : h.bar (b / (ω + 1)) = b / (ω + 1) := by rw [map_div₀, map_add, map_one, hωF, hb]
  refine ⟨_, (mem_miyamotoI2r1 h).2 ⟨a, rfl⟩, b / (ω + 1), hb', ?_⟩
  rw [miyamotoI2r1Hom_conj]
  simp only [mul_zero]
  rw [← hω, eq_mul_inv_iff_mul_eq, miyamotoXGL_rootB_mul h hb, miyamotoXGL_inj]
  refine ⟨rfl, ?_, rfl, rfl⟩
  field_simp
  linear_combination b * CharTwo.two_eq_zero (R := K)

theorem conj_miyamotoIHom_mem_rootC (p : Kˣ × Kˣ) {y : GL (Fin 4) K} (hy : y ∈ miyamotoRootC h) :
    (miyamotoIHom h p)⁻¹ * y * miyamotoIHom h p ∈ miyamotoRootC h := by
  obtain ⟨c, rfl⟩ := hy
  rw [miyamotoIHom_conj_rootC]
  exact ⟨_, rfl⟩

theorem conj_miyamotoIHom_mem_rootB (p : Kˣ × Kˣ) {y : GL (Fin 4) K} (hy : y ∈ miyamotoRootB h) :
    (miyamotoIHom h p)⁻¹ * y * miyamotoIHom h p ∈ miyamotoRootB h := by
  obtain ⟨b, hb, rfl⟩ := hy
  rw [miyamotoIHom_conj_rootB]
  refine ⟨_, ?_, rfl⟩
  rw [coe_miyamotoWeightB, map_mul, map_mul, h.bar_bar, hb]
  ring

theorem miyamotoIHom_mem_normalizer {X : Subgroup (GL (Fin 4) K)}
    (hX : ∀ p : Kˣ × Kˣ, ∀ y ∈ X, (miyamotoIHom h p)⁻¹ * y * miyamotoIHom h p ∈ X)
    (p : Kˣ × Kˣ) : miyamotoIHom h p ∈ normalizer (X : Set (GL (Fin 4) K)) := by
  rw [mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have := hX p⁻¹ y hy
    rwa [map_inv, inv_inv] at this
  · intro hy
    have := hX p _ hy
    rwa [show (miyamotoIHom h p)⁻¹ * (miyamotoIHom h p * y * (miyamotoIHom h p)⁻¹) *
      miyamotoIHom h p = y by group] at this

theorem miyamotoI_le_normalizer_rootC :
    miyamotoI h ≤ normalizer (miyamotoRootC h : Set (GL (Fin 4) K)) := by
  rintro _ ⟨p, -, rfl⟩
  exact miyamotoIHom_mem_normalizer h (fun p _ hy => conj_miyamotoIHom_mem_rootC h p hy) p

theorem miyamotoI_le_normalizer_rootB :
    miyamotoI h ≤ normalizer (miyamotoRootB h : Set (GL (Fin 4) K)) := by
  rintro _ ⟨p, -, rfl⟩
  exact miyamotoIHom_mem_normalizer h (fun p _ hy => conj_miyamotoIHom_mem_rootB h p hy) p

theorem miyamotoR2_conj_mem_I2r1 {D : GL (Fin 4) K} (hD : D ∈ miyamotoI2r1 h) :
    (miyamotoR2 K)⁻¹ * D * miyamotoR2 K ∈ miyamotoI2r1 h := by
  obtain ⟨a, rfl⟩ := (mem_miyamotoI2r1 h).1 hD
  rw [miyamotoR2_conj_miyamotoIHom]
  refine (mem_miyamotoI2r1 h).2 ⟨(Units.map h.bar.toMonoidHom a)⁻¹, ?_⟩
  congr 1
  refine Prod.ext ?_ ?_
  · apply Units.ext
    simp only [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.coe_map,
      RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass]
    rw [inv_pow, ← map_pow, bar_pow_sub_one h a.ne_zero, inv_inv]
  · change (Units.map h.bar.toMonoidHom (a ^ 2))⁻¹ = ((Units.map h.bar.toMonoidHom a)⁻¹) ^ 2
    rw [inv_pow, map_pow]

theorem miyamotoR2_mem_normalizer_I2r1 :
    miyamotoR2 K ∈ normalizer (miyamotoI2r1 h : Set (GL (Fin 4) K)) := by
  have hr : (miyamotoR2 K)⁻¹ = miyamotoR2 K := miyamotoR2_inv
  rw [mem_normalizer_iff]
  intro D
  constructor
  · intro hD
    have := miyamotoR2_conj_mem_I2r1 h hD
    rw [hr] at this
    exact this
  · intro hD
    have := miyamotoR2_conj_mem_I2r1 h hD
    rwa [hr, show miyamotoR2 K * (miyamotoR2 K * D * miyamotoR2 K) * miyamotoR2 K =
      (miyamotoR2 K * miyamotoR2 K) * D * (miyamotoR2 K * miyamotoR2 K) by group,
      miyamotoR2_mul_self, one_mul, mul_one] at this

end ModelFacts

section Generic

variable {G : Type*} [Group G]

theorem conj_eq_of_crossed_mem {y : G} {X Z S : Subgroup G}
    (hfix : ∀ x ∈ X, x⁻¹ * (y * x * y⁻¹) ∈ Z) (hZX : ∀ z ∈ Z, ∀ x ∈ X, z * x = x * z)
    (hSy : ∀ s ∈ S, s * y = y * s) (hSZ : ∀ s ∈ S, ∀ z ∈ Z, s * z = z * s)
    (hSX : S ≤ normalizer (X : Set G))
    (hgen : ∀ x ∈ X, ∃ s ∈ S, ∃ x' ∈ X, x = (s⁻¹ * x' * s) * x'⁻¹) {x : G} (hx : x ∈ X) :
    y * x * y⁻¹ = x := by
  set φ : G → G := fun x => x⁻¹ * (y * x * y⁻¹) with hφ
  have hmul : ∀ x₁ ∈ X, ∀ x₂ ∈ X, φ (x₁ * x₂) = φ x₁ * φ x₂ := by
    intro x₁ h₁ x₂ h₂
    have hc := hZX _ (hfix x₁ h₁) x₂ h₂
    simp only [hφ]
    calc (x₁ * x₂)⁻¹ * (y * (x₁ * x₂) * y⁻¹) =
        x₂⁻¹ * (x₁⁻¹ * (y * x₁ * y⁻¹) * x₂) * (x₂⁻¹ * (y * x₂ * y⁻¹)) := by group
      _ = x₂⁻¹ * (x₂ * (x₁⁻¹ * (y * x₁ * y⁻¹))) * (x₂⁻¹ * (y * x₂ * y⁻¹)) := by rw [hc]
      _ = _ := by group
  have hinv : ∀ x' ∈ X, φ x'⁻¹ = (φ x')⁻¹ := by
    intro x' hx'
    have := hmul x' hx' x'⁻¹ (inv_mem hx')
    rw [mul_inv_cancel] at this
    have h1 : φ 1 = 1 := by simp [hφ]
    rw [h1] at this
    exact (eq_inv_of_mul_eq_one_right this.symm)
  have hconj : ∀ s ∈ S, ∀ x' ∈ X, φ (s⁻¹ * x' * s) = φ x' := by
    intro s hs x' hx'
    have hsy : Commute s y := hSy s hs
    have hsy' : s⁻¹ * y = y * s⁻¹ := (Commute.inv_left hsy).eq
    have hsy'' : s * y⁻¹ = y⁻¹ * s := (Commute.inv_right hsy).eq
    have hz := hSZ s hs _ (hfix x' hx')
    simp only [hφ]
    calc (s⁻¹ * x' * s)⁻¹ * (y * (s⁻¹ * x' * s) * y⁻¹) =
        s⁻¹ * x'⁻¹ * s * (y * s⁻¹) * x' * (s * y⁻¹) := by group
      _ = s⁻¹ * x'⁻¹ * s * (s⁻¹ * y) * x' * (y⁻¹ * s) := by rw [← hsy', hsy'']
      _ = s⁻¹ * (x'⁻¹ * (y * x' * y⁻¹)) * s := by group
      _ = s⁻¹ * (s * (x'⁻¹ * (y * x' * y⁻¹))) := by rw [mul_assoc, hz]
      _ = x'⁻¹ * (y * x' * y⁻¹) := by group
  obtain ⟨s, hs, x', hx', rfl⟩ := hgen x hx
  have hsx : s⁻¹ * x' * s ∈ X := by
    have := (mem_normalizer_iff.1 (inv_mem (hSX hs)) x').1 hx'
    rwa [inv_inv] at this
  have h1 : φ ((s⁻¹ * x' * s) * x'⁻¹) = 1 := by
    rw [hmul _ hsx _ (inv_mem hx'), hconj s hs x' hx', hinv x' hx', mul_inv_cancel]
  simp only [hφ] at h1
  have := (inv_mul_eq_one.1 h1)
  exact this.symm

@[expose] def actsLike (I Y : Subgroup G) (hIY : I ≤ normalizer (Y : Set G)) : Subgroup G where
  carrier := {x | ∃ i ∈ I, ∀ y ∈ Y, x * y * x⁻¹ = i * y * i⁻¹}
  mul_mem' := by
    rintro x₁ x₂ ⟨i₁, hi₁, h₁⟩ ⟨i₂, hi₂, h₂⟩
    refine ⟨i₁ * i₂, mul_mem hi₁ hi₂, fun y hy => ?_⟩
    have hy₂ : i₂ * y * i₂⁻¹ ∈ Y := (mem_normalizer_iff.1 (hIY hi₂) y).1 hy
    calc x₁ * x₂ * y * (x₁ * x₂)⁻¹ = x₁ * (x₂ * y * x₂⁻¹) * x₁⁻¹ := by group
      _ = x₁ * (i₂ * y * i₂⁻¹) * x₁⁻¹ := by rw [h₂ y hy]
      _ = i₁ * (i₂ * y * i₂⁻¹) * i₁⁻¹ := h₁ _ hy₂
      _ = i₁ * i₂ * y * (i₁ * i₂)⁻¹ := by group
  one_mem' := ⟨1, one_mem _, fun y _ => by group⟩
  inv_mem' := by
    rintro x ⟨i, hi, hx⟩
    refine ⟨i⁻¹, inv_mem hi, fun y hy => ?_⟩
    have hy' : i⁻¹ * y * i⁻¹⁻¹ ∈ Y := (mem_normalizer_iff.1 (hIY (inv_mem hi)) y).1 hy
    have e := hx _ hy'
    calc x⁻¹ * y * x⁻¹⁻¹ = x⁻¹ * (i * (i⁻¹ * y * i⁻¹⁻¹) * i⁻¹) * x := by group
      _ = x⁻¹ * (x * (i⁻¹ * y * i⁻¹⁻¹) * x⁻¹) * x := by rw [e]
      _ = i⁻¹ * y * i⁻¹⁻¹ := by group

end Generic

section Pull

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {G : Type} [Group G]
  (L : Subgroup G) (η : L ≃* gramSU h (miyamotoJ4 K))

theorem exists_mul_of_mem_miyamotoPull {M N X : Subgroup (GL (Fin 4) K)}
    (hM : M ≤ gramSU h (miyamotoJ4 K)) (hN : N ≤ gramSU h (miyamotoJ4 K))
    (hX : (M : Set (GL (Fin 4) K)) * (N : Set (GL (Fin 4) K)) = X) {x : G}
    (hx : x ∈ miyamotoPull h L η X) :
    ∃ m ∈ miyamotoPull h L η M, ∃ n ∈ miyamotoPull h L η N, x = m * n := by
  obtain ⟨g, hg, rfl⟩ := (mem_miyamotoPull h L η).1 hx
  have hg' : (g : GL (Fin 4) K) ∈ (M : Set (GL (Fin 4) K)) * (N : Set (GL (Fin 4) K)) := by
    rw [hX]
    exact hg
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.1 hg'
  refine ⟨_, (symm_mem_miyamotoPull_iff h L η (g := ⟨a, hM ha⟩)).2 ha, _,
    (symm_mem_miyamotoPull_iff h L η (g := ⟨b, hN hb⟩)).2 hb, ?_⟩
  rw [← coe_mul, ← map_mul]
  congr 2
  exact Subtype.ext hab.symm

theorem coe_symm_conj_inv (g k : gramSU h (miyamotoJ4 K)) :
    ((η.symm (g⁻¹ * k * g) : L) : G) =
      ((η.symm g : L) : G)⁻¹ * ((η.symm k : L) : G) * ((η.symm g : L) : G) := by
  simp only [map_mul, map_inv, coe_mul, coe_inv]

end Pull

@[expose] def miyamotoYG {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {G : Type}
    [Group G] (L : Subgroup G) (η : L ≃* gramSU h (miyamotoJ4 K)) (Q : Subgroup G) :
    Subgroup G :=
  miyamotoM0 Q ⊓ centralizer (miyamotoA2G h L η : Set G)

@[expose] noncomputable def miyamotoEG {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    {G : Type} [Group G] (L : Subgroup G) (η : L ≃* gramSU h (miyamotoJ4 K)) (Q : Subgroup G) :
    Subgroup G :=
  ⁅miyamotoI2G h L η, miyamotoYG h L η Q⁆ ⊔ miyamotoZG h L η

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

theorem S_le_L (_hS : Setting h L η t Q T) : miyamotoI2r1G h L η ≤ L := miyamotoPull_le h L η _

theorem S_le_C (hS : Setting h L η t Q T) :
    miyamotoI2r1G h L η ≤ centralizer ({t} : Set G) :=
  hS.S_le_L.trans hS.L_le_centralizer

theorem ZP_le_centralizer_S (hS : Setting h L η t Q T) :
    miyamotoZG h L η ≤ centralizer (miyamotoI2r1G h L η : Set G) := by
  have : CharP K 2 := h.charP
  have hPS : miyamotoPG h L η ⊓ centralizer (miyamotoI2r1G h L η : Set G) = miyamotoZG h L η :=
    (miyamoto_two_one_two_centralizersG h L η hS.two_le).2.2.2
  rw [← hPS]
  exact inf_le_right

theorem S_le_centralizer_ZP (hS : Setting h L η t Q T) :
    miyamotoI2r1G h L η ≤ centralizer (miyamotoZG h L η : Set G) :=
  le_centralizer_iff.1 hS.ZP_le_centralizer_S

theorem S_le_K0 (hS : Setting h L η t Q T) :
    miyamotoI2r1G h L η ≤ centralizer (CFSG.centerIn Q : Set G) := fun _ hs =>
  hS.L_inf_centralizer_ZP_le_K0 ⟨hS.S_le_L hs, hS.S_le_centralizer_ZP hs⟩

theorem S_le_H (hS : Setting h L η t Q T) :
    miyamotoI2r1G h L η ≤ normalizer (CFSG.centerIn Q : Set G) :=
  hS.S_le_K0.trans (Subgroup.centralizer_le_normalizer _)

theorem H_le_normalizer_M (hS : Setting h L η t Q T) :
    normalizer (CFSG.centerIn Q : Set G) ≤ normalizer (miyamotoM0 Q : Set G) := by
  rw [hS.miyamotoM0_eq]
  exact CFSG.EvenSmallLie.UnitarySix.YamadaD.le_normalizer_oTwo _

theorem isPGroup_M (hS : Setting h L η t Q T) : IsPGroup 2 (miyamotoM0 Q) := by
  rw [hS.miyamotoM0_eq]
  exact CFSG.EvenSmallLie.UnitarySix.YamadaD.isPGroup_oTwo _

theorem odd_card_S (_hS : Setting h L η t Q T) : Odd (Nat.card (miyamotoI2r1G h L η)) := by
  rw [card_miyamotoPull h L η ((miyamotoI2r1_le_I h).trans (miyamotoI_le_gramSU h))]
  exact odd_card_miyamotoI2r1 h

theorem odd_card_I2 (_hS : Setting h L η t Q T) : Odd (Nat.card (miyamotoI2G h L η)) := by
  rw [card_miyamotoPull h L η ((miyamotoI2_le_I h).trans (miyamotoI_le_gramSU h))]
  exact odd_card_miyamotoI2 h

omit [Finite G] in
theorem coprime_of_odd_of_isPGroup [Finite G] {X Y : Subgroup G} (hX : Odd (Nat.card X))
    (hY : IsPGroup 2 Y) : (Nat.card X).Coprime (Nat.card Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hY
  rw [hk]
  exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 hX)

theorem B2_le_M (hS : Setting h L η t Q T) : miyamotoB2 h L η t ≤ miyamotoM0 Q := by
  obtain ⟨-, -, hMC, -, -⟩ := hS.two_core_M
  rw [← hMC]
  exact inf_le_left

theorem M_le_normalizer_B2 (hS : Setting h L η t Q T) :
    miyamotoM0 Q ≤ normalizer (miyamotoB2 h L η t : Set G) :=
  hS.M_le_H.trans hS.H_le_normalizer_B2

theorem S_le_normalizer_M (hS : Setting h L η t Q T) :
    miyamotoI2r1G h L η ≤ normalizer (miyamotoM0 Q : Set G) :=
  hS.S_le_H.trans hS.H_le_normalizer_M

theorem exists_mul_Y0 (hS : Setting h L η t Q T) {m : G} (hm : m ∈ miyamotoM0 Q) :
    ∃ y ∈ miyamotoM0 Q ⊓ centralizer (miyamotoI2r1G h L η : Set G),
      ∃ b ∈ miyamotoB2 h L η t, m = y * b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hMK, -, -, -⟩ := hS.two_core_M
  have hsolv : Group.IsSolvable (miyamotoM0 Q) := by
    have := hS.isPGroup_M.isNilpotent
    infer_instance
  refine exists_mem_inf_centralizer_mul_of_coprime hS.B2_le_M hS.M_le_normalizer_B2
    hS.S_le_normalizer_M (hS.S_le_H.trans hS.H_le_normalizer_B2) hsolv
    (coprime_of_odd_of_isPGroup hS.odd_card_S hS.isPGroup_M) hm fun s hs => ?_
  have hsK : s ∈ normalizer (CFSG.centerIn Q : Set G) ⊓ centralizer (miyamotoZG h L η : Set G) ⊓
      centralizer ({t} : Set G) := ⟨⟨hS.S_le_H hs, hS.S_le_centralizer_ZP hs⟩, hS.S_le_C hs⟩
  have h1 := hMK m hm s hsK
  have h2 := (mem_normalizer_iff.1 (inv_mem (hS.M_le_normalizer_B2 hm)) _).1 h1
  have e : m⁻¹ * (s * m * s⁻¹) = (m⁻¹ * (m * s * m⁻¹ * s⁻¹) * m⁻¹⁻¹)⁻¹ := by group
  rw [e]
  exact inv_mem h2

theorem Y0_inf_B2 (hS : Setting h L η t Q T) :
    miyamotoM0 Q ⊓ centralizer (miyamotoI2r1G h L η : Set G) ⊓ miyamotoB2 h L η t =
      CFSG.centerIn Q := by
  have : CharP K 2 := h.charP
  have hPS : miyamotoPG h L η ⊓ centralizer (miyamotoI2r1G h L η : Set G) = miyamotoZG h L η :=
    (miyamoto_two_one_two_centralizersG h L η hS.two_le).2.2.2
  have htS : t ∈ centralizer (miyamotoI2r1G h L η : Set G) := mem_centralizer_iff.2 fun s hs =>
    mem_centralizer_singleton_iff.1 (hS.S_le_C hs)
  apply le_antisymm
  · rintro x ⟨⟨-, hxS⟩, hxB⟩
    obtain ⟨u, hu, a, ha, rfl⟩ := hS.exists_of_mem_B2 hxB
    have huS : u ∈ centralizer (miyamotoI2r1G h L η : Set G) := (zpowers_le.2 htS) hu
    have haS : a ∈ centralizer (miyamotoI2r1G h L η : Set G) := by
      have := mul_mem (inv_mem huS) hxS
      rwa [inv_mul_cancel_left] at this
    have haZ : a ∈ miyamotoZG h L η := by
      rw [← hPS]
      exact ⟨miyamotoPull_mono h L η (miyamotoA2_le_P h) ha, haS⟩
    rw [hS.centerIn_Q']
    exact mul_mem (mem_sup_right hu) (mem_sup_left haZ)
  · intro x hx
    have hxB : x ∈ miyamotoB2 h L η t := by
      rw [hS.centerIn_Q'] at hx
      exact (sup_le (hS.ZP_le_B2) (le_sup_left (a := zpowers t))) hx |> fun h' => by
        simpa [miyamotoB2] using h'
    refine ⟨⟨hS.B2_le_M hxB, ?_⟩, hxB⟩
    rw [hS.centerIn_Q'] at hx
    exact (sup_le hS.ZP_le_centralizer_S (zpowers_le.2 htS)) hx

theorem B2_sup_Y0 (hS : Setting h L η t Q T) :
    miyamotoB2 h L η t ⊔ (miyamotoM0 Q ⊓ centralizer (miyamotoI2r1G h L η : Set G)) =
      miyamotoM0 Q := by
  refine le_antisymm (sup_le hS.B2_le_M inf_le_left) fun m hm => ?_
  obtain ⟨y, hy, b, hb, rfl⟩ := hS.exists_mul_Y0 hm
  rw [show y * b = y * b * y⁻¹ * y by group]
  exact mul_mem (mul_mem (mul_mem (mem_sup_right hy) (mem_sup_left hb)) (inv_mem
    (mem_sup_right hy))) (mem_sup_right hy)

theorem card_Y0 (hS : Setting h L η t Q T) :
    Nat.card (miyamotoM0 Q ⊓ centralizer (miyamotoI2r1G h L η : Set G) : Subgroup G) =
      2 * (2 ^ f) ^ 2 := by
  have hle : miyamotoM0 Q ⊓ centralizer (miyamotoI2r1G h L η : Set G) ≤
      normalizer (miyamotoB2 h L η t : Set G) := inf_le_left.trans hS.M_le_normalizer_B2
  have e := card_sup_mul_card_inf_eq hle
  rw [hS.B2_sup_Y0, inf_comm, hS.Y0_inf_B2, hS.card_M, hS.card_B2, hS.centerIn_Q', sup_comm,
    hS.card_zpowers_sup hS.ZP_le_L, hS.card_ZP] at e
  have hq : 0 < 2 ^ f := by positivity
  have e' : (2 * (2 ^ f) ^ 5) * Nat.card (miyamotoM0 Q ⊓
      centralizer (miyamotoI2r1G h L η : Set G) : Subgroup G) =
      (2 * (2 ^ f) ^ 5) * (2 * (2 ^ f) ^ 2) := by
    rw [← e]
    ring
  exact Nat.eq_of_mul_eq_mul_left (by positivity) e'

theorem M_le_normalizer_B1 (hS : Setting h L η t Q T) :
    miyamotoM0 Q ≤ normalizer (miyamotoB1 h L η t : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro m hm
  have hmQ := hS.M_le_normalizer_Q hm
  set X := (miyamotoB1 h L η t).map (MulAut.conj m).toMonoidHom with hX
  have hXQ : X ≤ Q := by
    rintro _ ⟨b, hb, rfl⟩
    exact (mem_normalizer_iff.1 hmQ b).1 (hS.B1_le_Q hb)
  have : CFSG.IsElementaryAbelian 2 (miyamotoB1 h L η t) := hS.isElementaryAbelian_B1
  have hXe : CFSG.IsElementaryAbelian 2 X := CFSG.IsElementaryAbelian.map _
  have hcard : Nat.card X = 2 * (2 ^ f) ^ 4 := by
    rw [hX, card_map_of_injective (MulAut.conj m).injective, hS.card_B1]
  have hXB := (hS.card_le_of_le_T (hXQ.trans hS.Q_le_T) hXe).2 hcard
  refine mem_normalizer_fintype fun b hb => ?_
  have : m * b * m⁻¹ ∈ X := ⟨b, hb, rfl⟩
  rwa [hXB] at this

theorem M_le_normalizer_Z2Q (hS : Setting h L η t Q T) :
    miyamotoM0 Q ≤ normalizer ((miyamotoB1 h L η t ⊓ miyamotoB2 h L η t : Subgroup G) : Set G) :=
  fun _ hm => mem_normalizer_inf (hS.M_le_normalizer_B1 hm) (hS.M_le_normalizer_B2 hm)

theorem centerIn_Q_le_Z2Q (hS : Setting h L η t Q T) :
    CFSG.centerIn Q ≤ miyamotoB1 h L η t ⊓ miyamotoB2 h L η t := by
  rw [hS.centerIn_Q']
  refine sup_le (le_inf (hS.ZP_le_A1.trans le_sup_right) hS.ZP_le_B2)
    (le_inf le_sup_left le_sup_left)

theorem rootC_le_Z2Q (_hS : Setting h L η t Q T) :
    miyamotoPull h L η (miyamotoRootC h) ≤ miyamotoB1 h L η t ⊓ miyamotoB2 h L η t := by
  have : CharP K 2 := h.charP
  have hZ2 : miyamotoPull h L η (miyamotoRootC h) ≤ miyamotoPull h L η (miyamotoZ2 h) :=
    miyamotoPull_mono h L η (miyamotoRootC_le_Z2 h)
  rw [← miyamotoA1G_inf_miyamotoA2G] at hZ2
  exact le_inf (hZ2.trans (inf_le_left.trans le_sup_right))
    (hZ2.trans (inf_le_right.trans le_sup_right))

theorem Z2Q_le_Q (hS : Setting h L η t Q T) :
    miyamotoB1 h L η t ⊓ miyamotoB2 h L η t ≤ Q :=
  inf_le_left.trans hS.B1_le_Q

theorem exists_mul_of_mem_Z2Q (hS : Setting h L η t Q T) {x : G}
    (hx : x ∈ miyamotoB1 h L η t ⊓ miyamotoB2 h L η t) :
    ∃ w ∈ CFSG.centerIn Q, ∃ c ∈ miyamotoPull h L η (miyamotoRootC h), x = w * c := by
  have : CharP K 2 := h.charP
  obtain ⟨hx1, hx2⟩ := mem_inf.1 hx
  obtain ⟨u, hu, a, ha, rfl⟩ := hS.exists_of_mem_B2 hx2
  have hab : ∀ u' ∈ zpowers t, ∀ a' ∈ miyamotoA1G h L η, u * a = u' * a' →
      a ∈ miyamotoA1G h L η := by
    intro u' hu' a' ha' e
    have hL : u'⁻¹ * u ∈ zpowers t ⊓ L := by
      refine mem_inf.2 ⟨mul_mem (inv_mem hu') hu, ?_⟩
      have : u'⁻¹ * u = a' * a⁻¹ := by
        calc u'⁻¹ * u = u'⁻¹ * (u * a) * a⁻¹ := by group
          _ = u'⁻¹ * (u' * a') * a⁻¹ := by rw [e]
          _ = a' * a⁻¹ := by group
      rw [this]
      exact mul_mem (miyamotoPull_le h L η _ ha') (inv_mem (miyamotoPull_le h L η _ ha))
    rw [inf_comm, hS.inf_zpowers_eq_bot le_rfl, mem_bot] at hL
    have : u = u' := by rw [← mul_left_cancel_iff (a := u'⁻¹), hL, inv_mul_cancel]
    subst this
    rw [mul_left_cancel_iff] at e
    rw [e]
    exact ha'
  obtain ⟨u', hu', a', ha', e⟩ :=
    exists_mul_of_mem_sup_of_commute (hS.zpowers_comm_of_le_L (miyamotoPull_le h L η _)) hx1
  have ha1 := hab u' hu' a' ha' e
  have ha12 : a ∈ miyamotoPull h L η (miyamotoZ2 h) := by
    rw [← miyamotoA1G_inf_miyamotoA2G]
    exact ⟨ha1, ha⟩
  have hZ : miyamotoZ h ≤ gramSU h (miyamotoJ4 K) :=
    (miyamotoZ_le_P h).trans (miyamotoUnipotent_le_SU h false false)
  have hC : miyamotoRootC h ≤ gramSU h (miyamotoJ4 K) :=
    ((miyamotoRootC_le_Z2 h).trans ((miyamotoZ2_le_A1 h).trans (miyamotoA1_le_P h))).trans
      (miyamotoUnipotent_le_SU h false false)
  obtain ⟨z, hz, c, hc, rfl⟩ :=
    exists_mul_of_mem_miyamotoPull h L η hZ hC (miyamotoZ_mul_rootC h) ha12
  refine ⟨u * z, mul_mem ?_ (hS.ZP_le_centerIn_Q hz), c, hc, by group⟩
  exact (zpowers_le.2 hS.t_mem_centerIn_Q) hu

theorem exists_rootC_not_mem_centerIn_Q (hS : Setting h L η t Q T) :
    ∃ c ∈ miyamotoPull h L η (miyamotoRootC h), c ∉ CFSG.centerIn Q := by
  have : CharP K 2 := h.charP
  have hC : miyamotoRootC h ≤ gramSU h (miyamotoJ4 K) :=
    ((miyamotoRootC_le_Z2 h).trans ((miyamotoZ2_le_A1 h).trans (miyamotoA1_le_P h))).trans
      (miyamotoUnipotent_le_SU h false false)
  have hcard : 1 < Nat.card (miyamotoPull h L η (miyamotoRootC h)) := by
    rw [card_miyamotoPull h L η hC, card_miyamotoRootC]
    have : 2 ≤ 2 ^ f := Nat.le_self_pow (by have := hS.two_le; omega) 2
    nlinarith
  obtain ⟨⟨c, hc⟩, hc1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1
    ((Subgroup.one_lt_card_iff_ne_bot _).1 hcard)
  refine ⟨c, hc, fun hcZ => hc1 (Subtype.ext ?_)⟩
  rcases hS.mem_centerIn_Q_iff.1 hcZ with h1 | h1
  · have : c ∈ miyamotoPull h L η (miyamotoZ h ⊓ miyamotoRootC h) := by
      rw [miyamotoPull_inf]
      exact ⟨h1, hc⟩
    rwa [miyamotoZ_inf_rootC, miyamotoPull_bot, mem_bot] at this
  · exfalso
    apply hS.t_not_mem_L
    have := mul_mem (inv_mem (miyamotoPull_le h L η _ hc)) (hS.ZP_le_L h1)
    rwa [inv_mul_cancel_left] at this

theorem rootC_transitive (hS : Setting h L η t Q T) {c c' : G}
    (hc : c ∈ miyamotoPull h L η (miyamotoRootC h))
    (hc' : c' ∈ miyamotoPull h L η (miyamotoRootC h))
    (hc1 : c ≠ 1) (hc1' : c' ≠ 1) : ∃ i ∈ miyamotoIG h L η, i⁻¹ * c * i = c' := by
  have : CharP K 2 := h.charP
  have htr := (miyamoto_two_one_threeG h L η hS.two_le).2.1
  rw [(miyamoto_two_one_two_centralizersG h L η hS.two_le).2.1] at htr
  exact htr c hc c' hc' hc1 hc1'

theorem rootC_fix (hS : Setting h L η t Q T) {c : G}
    (hc : c ∈ miyamotoPull h L η (miyamotoRootC h)) {m : G} (hm : m ∈ miyamotoM0 Q) :
    c⁻¹ * (m * c * m⁻¹) ∈ CFSG.centerIn Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := CFSG.centerIn Q with hZdef
  set Fix : G → Prop := fun x => ∀ m ∈ miyamotoM0 Q, x⁻¹ * (m * x * m⁻¹) ∈ Z with hFix
  have hQZ : ∀ x ∈ Q, ∀ z ∈ Z, x * z * x⁻¹ ∈ Z := fun x hx z hz =>
    (mem_normalizer_iff.1 (hS.Q_le_H hx) z).1 hz
  have hfixZ : ∀ w ∈ Z, Fix w := fun w hw m hm =>
    mul_mem (inv_mem hw) ((mem_normalizer_iff.1 (hS.M_le_H hm) w).1 hw)
  have hfixmul : ∀ x ∈ Q, ∀ x' ∈ Q, Fix x → Fix x' → Fix (x * x') := by
    intro x hx x' hx' h1 h2 m hm
    have e : (x * x')⁻¹ * (m * (x * x') * m⁻¹) =
        (x'⁻¹ * (x⁻¹ * (m * x * m⁻¹)) * x'⁻¹⁻¹) * (x'⁻¹ * (m * x' * m⁻¹)) := by group
    rw [e]
    exact mul_mem (hQZ _ (inv_mem hx') _ (h1 m hm)) (h2 m hm)
  have hfixinv : ∀ x ∈ Q, Fix x → Fix x⁻¹ := by
    intro x hx h1 m hm
    have e : x⁻¹⁻¹ * (m * x⁻¹ * m⁻¹) = x * (x⁻¹ * (m * x * m⁻¹))⁻¹ * x⁻¹ := by group
    rw [e]
    exact hQZ x hx _ (inv_mem (h1 m hm))
  have hfixconj : ∀ i ∈ miyamotoIG h L η, ∀ x, Fix x → Fix (i⁻¹ * x * i) := by
    intro i hi x h1 m hm
    have hiM : i * m * i⁻¹ ∈ miyamotoM0 Q :=
      (mem_normalizer_iff.1 (hS.H_le_normalizer_M (hS.IG_le_H hi)) m).1 hm
    have e : (i⁻¹ * x * i)⁻¹ * (m * (i⁻¹ * x * i) * m⁻¹) =
        i⁻¹ * (x⁻¹ * ((i * m * i⁻¹) * x * (i * m * i⁻¹)⁻¹)) * i⁻¹⁻¹ := by group
    rw [e]
    exact (mem_normalizer_iff.1 (inv_mem (hS.IG_le_H hi)) _).1 (h1 _ hiM)
  obtain ⟨c₁, hc₁, hc₁Z⟩ := hS.exists_rootC_not_mem_centerIn_Q
  obtain ⟨z₀, hz₀, hz₀Z, hz₀fix⟩ := exists_mem_forall_conj_mem_of_isPGroup hS.isPGroup_M
    (hS.isPGroup_Q.to_le hS.Z2Q_le_Q) hS.centerIn_Q_le_Z2Q
    (fun hle => hc₁Z (hle (hS.rootC_le_Z2Q hc₁))) hS.M_le_normalizer_Z2Q hS.M_le_H
    (hS.Z2Q_le_Q.trans hS.Q_le_H)
  obtain ⟨w, hw, c₀, hc₀, rfl⟩ := hS.exists_mul_of_mem_Z2Q hz₀
  have hwQ : w ∈ Q := (inf_le_left : CFSG.centerIn Q ≤ Q) hw
  have hc₀Q : c₀ ∈ Q := hS.Z2Q_le_Q (hS.rootC_le_Z2Q hc₀)
  have hfix₀ : Fix c₀ := by
    have := hfixmul _ (inv_mem hwQ) _ (mul_mem hwQ hc₀Q) (hfixinv w hwQ (hfixZ w hw)) hz₀fix
    rwa [inv_mul_cancel_left] at this
  have hc₀1 : c₀ ≠ 1 := fun e => hz₀Z (by rw [e, mul_one]; exact hw)
  by_cases hc1 : c = 1
  · rw [hc1, inv_one, one_mul, mul_one, mul_inv_cancel]
    exact one_mem _
  obtain ⟨i, hi, rfl⟩ := hS.rootC_transitive hc₀ hc hc₀1 hc1
  exact hfixconj i hi c₀ hfix₀ m hm

theorem rootC_le_SU (_hS : Setting h L η t Q T) :
    miyamotoRootC h ≤ gramSU h (miyamotoJ4 K) := by
  have : CharP K 2 := h.charP
  exact ((miyamotoRootC_le_Z2 h).trans ((miyamotoZ2_le_A1 h).trans (miyamotoA1_le_P h))).trans
    (miyamotoUnipotent_le_SU h false false)

theorem rootB_le_SU (_hS : Setting h L η t Q T) :
    miyamotoRootB h ≤ gramSU h (miyamotoJ4 K) := by
  have : CharP K 2 := h.charP
  exact ((miyamotoRootB_le_A1 h).trans (miyamotoA1_le_P h)).trans
    (miyamotoUnipotent_le_SU h false false)

theorem S_le_normalizer_rootC (hS : Setting h L η t Q T) :
    miyamotoI2r1G h L η ≤ normalizer (miyamotoPull h L η (miyamotoRootC h) : Set G) := by
  have hle : miyamotoI2r1 h ≤ gramSU h (miyamotoJ4 K) ⊓
      normalizer (miyamotoRootC h : Set (GL (Fin 4) K)) :=
    le_inf ((miyamotoI2r1_le_I h).trans (miyamotoI_le_gramSU h))
      ((miyamotoI2r1_le_I h).trans (miyamotoI_le_normalizer_rootC h))
  have := miyamotoPull_mono h L η hle
  rw [miyamotoPull_inf_normalizer h L η hS.rootC_le_SU] at this
  exact this.trans inf_le_right

theorem S_le_normalizer_rootB (hS : Setting h L η t Q T) :
    miyamotoI2r1G h L η ≤ normalizer (miyamotoPull h L η (miyamotoRootB h) : Set G) := by
  have hle : miyamotoI2r1 h ≤ gramSU h (miyamotoJ4 K) ⊓
      normalizer (miyamotoRootB h : Set (GL (Fin 4) K)) :=
    le_inf ((miyamotoI2r1_le_I h).trans (miyamotoI_le_gramSU h))
      ((miyamotoI2r1_le_I h).trans (miyamotoI_le_normalizer_rootB h))
  have := miyamotoPull_mono h L η hle
  rw [miyamotoPull_inf_normalizer h L η hS.rootB_le_SU] at this
  exact this.trans inf_le_right

theorem exists_S_rootC (hS : Setting h L η t Q T) {c : G}
    (hc : c ∈ miyamotoPull h L η (miyamotoRootC h)) :
    ∃ s ∈ miyamotoI2r1G h L η, ∃ c' ∈ miyamotoPull h L η (miyamotoRootC h),
      c = (s⁻¹ * c' * s) * c'⁻¹ := by
  obtain ⟨g, ⟨γ, hγ⟩, rfl⟩ := (mem_miyamotoPull h L η).1 hc
  obtain ⟨D, hD, γ', e⟩ := exists_I2r1_rootC h hS.two_le γ
  have hDS : D ∈ gramSU h (miyamotoJ4 K) := (miyamotoI2r1_le_I h).trans (miyamotoI_le_gramSU h) hD
  have hxS : miyamotoXGL h 0 0 γ' 0 ∈ gramSU h (miyamotoJ4 K) := hS.rootC_le_SU ⟨γ', rfl⟩
  refine ⟨_, (symm_mem_miyamotoPull_iff h L η (g := ⟨D, hDS⟩)).2 hD, _,
    (symm_mem_miyamotoPull_iff h L η (g := ⟨_, hxS⟩)).2 ⟨γ', rfl⟩, ?_⟩
  have e' : g = ((⟨D, hDS⟩ : gramSU h (miyamotoJ4 K))⁻¹ * ⟨_, hxS⟩ * ⟨D, hDS⟩) *
      (⟨_, hxS⟩ : gramSU h (miyamotoJ4 K))⁻¹ := by
    apply Subtype.ext
    rw [hγ, e]
    simp only [coe_mul, coe_inv]
  rw [e']
  simp only [map_mul, map_inv, coe_mul, coe_inv]

theorem exists_S_rootB (hS : Setting h L η t Q T) {b : G}
    (hb : b ∈ miyamotoPull h L η (miyamotoRootB h)) :
    ∃ s ∈ miyamotoI2r1G h L η, ∃ b' ∈ miyamotoPull h L η (miyamotoRootB h),
      b = (s⁻¹ * b' * s) * b'⁻¹ := by
  obtain ⟨g, ⟨β, hβ, hgβ⟩, rfl⟩ := (mem_miyamotoPull h L η).1 hb
  obtain ⟨D, hD, β', hβ', e⟩ := exists_I2r1_rootB h hS.two_le hβ
  have hDS : D ∈ gramSU h (miyamotoJ4 K) := (miyamotoI2r1_le_I h).trans (miyamotoI_le_gramSU h) hD
  have hxS : miyamotoXGL h 0 β' 0 0 ∈ gramSU h (miyamotoJ4 K) := hS.rootB_le_SU ⟨β', hβ', rfl⟩
  refine ⟨_, (symm_mem_miyamotoPull_iff h L η (g := ⟨D, hDS⟩)).2 hD, _,
    (symm_mem_miyamotoPull_iff h L η (g := ⟨_, hxS⟩)).2 ⟨β', hβ', rfl⟩, ?_⟩
  have e' : g = ((⟨D, hDS⟩ : gramSU h (miyamotoJ4 K))⁻¹ * ⟨_, hxS⟩ * ⟨D, hDS⟩) *
      (⟨_, hxS⟩ : gramSU h (miyamotoJ4 K))⁻¹ := by
    apply Subtype.ext
    rw [hgβ, e]
    simp only [coe_mul, coe_inv]
  rw [e']
  simp only [map_mul, map_inv, coe_mul, coe_inv]

theorem centerIn_Q_comm (_hS : Setting h L η t Q T) {z x : G} (hz : z ∈ CFSG.centerIn Q)
    (hx : x ∈ Q) : z * x = x * z :=
  (mem_centralizer_iff.1 (mem_inf.1 hz).2 x hx).symm

theorem Y0_comm_rootC (hS : Setting h L η t Q T) {y : G}
    (hy : y ∈ miyamotoM0 Q ⊓ centralizer (miyamotoI2r1G h L η : Set G)) {c : G}
    (hc : c ∈ miyamotoPull h L η (miyamotoRootC h)) : y * c * y⁻¹ = c :=
  conj_eq_of_crossed_mem (fun _ hx => hS.rootC_fix hx hy.1)
    (fun _ hz _ hx => hS.centerIn_Q_comm hz (hS.Z2Q_le_Q (hS.rootC_le_Z2Q hx)))
    (fun s hs => mem_centralizer_iff.1 hy.2 s hs)
    (fun _ hs z hz => (mem_centralizer_iff.1 (hS.S_le_K0 hs) z hz).symm)
    hS.S_le_normalizer_rootC (fun _ hx => hS.exists_S_rootC hx) hc

theorem R2G_mem_normalizer_S (_hS : Setting h L η t Q T) :
    miyamotoR2G h L η ∈ normalizer (miyamotoI2r1G h L η : Set G) := by
  have : CharP K 2 := h.charP
  have hr : miyamotoR2 K ∈ gramSU h (miyamotoJ4 K) ⊓
      normalizer (miyamotoI2r1 h : Set (GL (Fin 4) K)) :=
    ⟨miyamotoR2_mem_gramSU h, miyamotoR2_mem_normalizer_I2r1 h⟩
  have := (symm_mem_miyamotoPull_iff h L η (g := ⟨_, miyamotoR2_mem_gramSU h⟩)).2 hr
  rw [miyamotoPull_inf_normalizer h L η ((miyamotoI2r1_le_I h).trans (miyamotoI_le_gramSU h))]
    at this
  exact this.2

theorem R2G_mem_K0 (hS : Setting h L η t Q T) :
    miyamotoR2G h L η ∈ centralizer (CFSG.centerIn Q : Set G) := by
  have : CharP K 2 := h.charP
  refine hS.L_inf_centralizer_ZP_le_K0 ⟨(η.symm _).2, mem_centralizer_iff.2 fun z hz => ?_⟩
  obtain ⟨g, ⟨d, hd, hgd⟩, rfl⟩ := (mem_miyamotoPull h L η).1 hz
  rw [miyamotoR2G, ← coe_mul, ← coe_mul, ← map_mul, ← map_mul]
  congr 2
  apply Subtype.ext
  rw [coe_mul, coe_mul, hgd]
  have e := miyamotoR2_conj_Z h d
  rw [miyamotoR2_inv] at e
  calc miyamotoXGL h 0 0 0 d * miyamotoR2 K =
      miyamotoR2 K * (miyamotoR2 K * miyamotoXGL h 0 0 0 d * miyamotoR2 K) := by
        rw [← mul_assoc, ← mul_assoc, miyamotoR2_mul_self, one_mul]
    _ = miyamotoR2 K * miyamotoXGL h 0 0 0 d := by rw [e]

theorem R2G_mem_normalizer_Y0 (hS : Setting h L η t Q T) :
    miyamotoR2G h L η ∈ normalizer ((miyamotoM0 Q ⊓
      centralizer (miyamotoI2r1G h L η : Set G) : Subgroup G) : Set G) :=
  mem_normalizer_inf (hS.H_le_normalizer_M (hS.K0_le_H hS.R2G_mem_K0))
    (mem_normalizer_centralizer hS.R2G_mem_normalizer_S)

theorem Y0_comm_rootA (hS : Setting h L η t Q T) {y : G}
    (hy : y ∈ miyamotoM0 Q ⊓ centralizer (miyamotoI2r1G h L η : Set G)) {u : G}
    (hu : u ∈ miyamotoPull h L η (miyamotoRootA h)) : y * u * y⁻¹ = u := by
  have : CharP K 2 := h.charP
  set r := miyamotoR2G h L η with hr
  obtain ⟨g, ⟨a, hga⟩, rfl⟩ := (mem_miyamotoPull h L η).1 hu
  have hxS : miyamotoXGL h 0 0 a 0 ∈ gramSU h (miyamotoJ4 K) := hS.rootC_le_SU ⟨a, rfl⟩
  set c := ((η.symm ⟨_, hxS⟩ : L) : G) with hcdef
  have hc : c ∈ miyamotoPull h L η (miyamotoRootC h) :=
    (symm_mem_miyamotoPull_iff h L η).2 ⟨a, rfl⟩
  have hgu : ((η.symm g : L) : G) = r⁻¹ * c * r := by
    rw [hr, miyamotoR2G, hcdef, ← coe_symm_conj_inv]
    congr 2
    apply Subtype.ext
    rw [hga, coe_mul, coe_mul, coe_inv]
    exact (miyamotoR2_conj_rootC h a).symm
  have hy' : r * y * r⁻¹ ∈ miyamotoM0 Q ⊓ centralizer (miyamotoI2r1G h L η : Set G) :=
    (mem_normalizer_iff.1 hS.R2G_mem_normalizer_Y0 y).1 hy
  have hc' := hS.Y0_comm_rootC hy' hc
  rw [hgu]
  calc y * (r⁻¹ * c * r) * y⁻¹ = r⁻¹ * ((r * y * r⁻¹) * c * (r * y * r⁻¹)⁻¹) * r := by group
    _ = r⁻¹ * c * r := by rw [hc']

theorem Y0_le_centralizer_A2 (hS : Setting h L η t Q T) :
    miyamotoM0 Q ⊓ centralizer (miyamotoI2r1G h L η : Set G) ≤
      centralizer (miyamotoA2G h L η : Set G) := by
  have : CharP K 2 := h.charP
  obtain ⟨hMZ, -, -, -, -⟩ := hS.two_core_M
  intro y hy
  rw [mem_centralizer_iff]
  intro a ha
  have hZ : miyamotoZ h ≤ gramSU h (miyamotoJ4 K) :=
    (miyamotoZ_le_P h).trans (miyamotoUnipotent_le_SU h false false)
  have hZ2 : miyamotoZ2 h ≤ gramSU h (miyamotoJ4 K) :=
    ((miyamotoZ2_le_A1 h).trans (miyamotoA1_le_P h)).trans (miyamotoUnipotent_le_SU h false false)
  have hA : miyamotoRootA h ≤ gramSU h (miyamotoJ4 K) :=
    ((miyamotoRootA_le_A2 h).trans (miyamotoA2_le_P h)).trans
      (miyamotoUnipotent_le_SU h false false)
  obtain ⟨z₂, hz₂, u, hu, rfl⟩ :=
    exists_mul_of_mem_miyamotoPull h L η hZ2 hA (miyamotoZ2_mul_rootA h) ha
  obtain ⟨z, hz, c, hc, rfl⟩ :=
    exists_mul_of_mem_miyamotoPull h L η hZ hS.rootC_le_SU (miyamotoZ_mul_rootC h) hz₂
  have h1 : y * z * y⁻¹ = z := by
    have := mem_centralizer_iff.1 (hMZ hy.1) z hz
    calc y * z * y⁻¹ = z * y * y⁻¹ := by rw [this]
      _ = z := by group
  have h2 := hS.Y0_comm_rootC hy hc
  have h3 := hS.Y0_comm_rootA hy hu
  have e : y * (z * c * u) * y⁻¹ = (y * z * y⁻¹) * (y * c * y⁻¹) * (y * u * y⁻¹) := by group
  have e' : z * c * u * y = y * (z * c * u) := by
    calc z * c * u * y = y * (y⁻¹ * (z * c * u) * y) := by group
      _ = y * (z * c * u) := by
        congr 1
        have : y * (z * c * u) * y⁻¹ = z * c * u := by rw [e, h1, h2, h3]
        calc y⁻¹ * (z * c * u) * y = y⁻¹ * (y * (z * c * u) * y⁻¹) * y := by rw [this]
          _ = z * c * u := by group
  exact e'

theorem P_le_normalizer_A2 (_hS : Setting h L η t Q T) :
    miyamotoPG h L η ≤ normalizer (miyamotoA2G h L η : Set G) := by
  have : CharP K 2 := h.charP
  have hle : miyamotoP h ≤ miyamotoA2 h ⊔ (miyamotoI2 h ⊔ miyamotoN2 h) := by
    intro g hg
    have hg' : g ∈ (miyamotoA2 h : Set (GL (Fin 4) K)) *
        (miyamotoRootB h : Set (GL (Fin 4) K)) := by
      rw [miyamotoA2_mul_rootB h]
      exact hg
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hg'
    exact mul_mem (mem_sup_left ha) (mem_sup_right (mem_sup_right (miyamotoRootB_le_N2 h hb)))
  have := miyamotoPull_mono h L η hle
  rw [miyamotoPull_sup h L η (miyamotoUnipotent_le_SU h false true)
    (sup_le (miyamotoI2_le_SU h) (miyamotoN2_le_gramSU h)),
    miyamotoPull_sup h L η (miyamotoI2_le_SU h) (miyamotoN2_le_gramSU h),
    ← normalizer_miyamotoA2G] at this
  exact this.trans inf_le_right

theorem B2_inf_centralizer_A2 (hS : Setting h L η t Q T) :
    miyamotoB2 h L η t ⊓ centralizer (miyamotoA2G h L η : Set G) ≤ CFSG.centerIn Q := by
  have : CharP K 2 := h.charP
  have hA2 : CFSG.centerIn (miyamotoA2G h L η) = miyamotoZG h L η := by
    rw [miyamotoA2G, centerIn_miyamotoPull h L η (miyamotoUnipotent_le_SU h false true)]
    exact congrArg (miyamotoPull h L η) (centerIn_miyamotoA2 h)
  rintro x ⟨hxB, hxC⟩
  obtain ⟨u, hu, a, ha, rfl⟩ := hS.exists_of_mem_B2 hxB
  have huC : u ∈ centralizer (miyamotoA2G h L η : Set G) := by
    rw [mem_centralizer_iff]
    intro b hb
    exact (hS.zpowers_comm_of_le_L (miyamotoPull_le h L η _) u hu b hb).symm
  have haC : a ∈ centralizer (miyamotoA2G h L η : Set G) := by
    have := mul_mem (inv_mem huC) hxC
    rwa [inv_mul_cancel_left] at this
  have haZ : a ∈ miyamotoZG h L η := by
    rw [← hA2]
    exact ⟨ha, haC⟩
  rw [hS.centerIn_Q']
  exact mul_mem (mem_sup_right hu) (mem_sup_left haZ)

theorem Y0_comm_rootB (hS : Setting h L η t Q T) {y : G}
    (hy : y ∈ miyamotoM0 Q ⊓ centralizer (miyamotoI2r1G h L η : Set G)) {b : G}
    (hb : b ∈ miyamotoPull h L η (miyamotoRootB h)) : y * b * y⁻¹ = b := by
  have : CharP K 2 := h.charP
  obtain ⟨-, hMK, -, -, -⟩ := hS.two_core_M
  have hBP : ∀ x ∈ miyamotoPull h L η (miyamotoRootB h), x ∈ miyamotoPG h L η := fun x hx =>
    miyamotoPull_mono h L η ((miyamotoRootB_le_A1 h).trans (miyamotoA1_le_P h)) hx
  have hyA := hS.Y0_le_centralizer_A2 hy
  have hfix : ∀ x ∈ miyamotoPull h L η (miyamotoRootB h), x⁻¹ * (y * x * y⁻¹) ∈
      CFSG.centerIn Q := by
    intro x hx
    have hxP := hBP x hx
    have hxQ : x ∈ Q := hS.P_le_Q hxP
    refine hS.B2_inf_centralizer_A2 (mem_inf.2 ⟨?_, ?_⟩)
    · have hK : x ∈ normalizer (CFSG.centerIn Q : Set G) ⊓
          centralizer (miyamotoZG h L η : Set G) ⊓ centralizer ({t} : Set G) := by
        rw [hS.centralizer_centerIn_Q_eq]
        exact hS.Q_le_K0 hxQ
      have h1 := hMK y hy.1 x hK
      have h2 := (mem_normalizer_iff.1 (inv_mem (hS.H_le_normalizer_B2 (hS.Q_le_H hxQ))) _).1 h1
      have e : x⁻¹ * (y * x * y⁻¹) = x⁻¹ * (y * x * y⁻¹ * x⁻¹) * x⁻¹⁻¹ := by group
      rw [e]
      exact h2
    · rw [mem_centralizer_iff]
      intro a ha
      have hxa : x * a * x⁻¹ ∈ miyamotoA2G h L η :=
        (mem_normalizer_iff.1 (hS.P_le_normalizer_A2 hxP) a).1 ha
      have c1 : y * (x * a * x⁻¹) = (x * a * x⁻¹) * y := (mem_centralizer_iff.1 hyA _ hxa).symm
      have c3 : a * y = y * a := mem_centralizer_iff.1 hyA a ha
      have c3' : y⁻¹ * a = a * y⁻¹ := (Commute.inv_left (show Commute a y from c3).symm).eq
      calc a * (x⁻¹ * (y * x * y⁻¹)) = x⁻¹ * ((x * a * x⁻¹) * y) * x * y⁻¹ := by group
        _ = x⁻¹ * (y * (x * a * x⁻¹)) * x * y⁻¹ := by rw [c1]
        _ = x⁻¹ * y * x * (a * y⁻¹) := by group
        _ = x⁻¹ * y * x * (y⁻¹ * a) := by rw [c3']
        _ = (x⁻¹ * (y * x * y⁻¹)) * a := by group
  exact conj_eq_of_crossed_mem hfix
    (fun _ hz x hx => hS.centerIn_Q_comm hz (hS.P_le_Q (hBP x hx)))
    (fun s hs => mem_centralizer_iff.1 hy.2 s hs)
    (fun _ hs z hz => (mem_centralizer_iff.1 (hS.S_le_K0 hs) z hz).symm)
    hS.S_le_normalizer_rootB (fun _ hx => hS.exists_S_rootB hx) hb

theorem Y0_le_centralizer_P (hS : Setting h L η t Q T) :
    miyamotoM0 Q ⊓ centralizer (miyamotoI2r1G h L η : Set G) ≤
      centralizer (miyamotoPG h L η : Set G) := by
  have : CharP K 2 := h.charP
  intro y hy
  rw [mem_centralizer_iff]
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_miyamotoPull h L η
    (miyamotoUnipotent_le_SU h false true) hS.rootB_le_SU (miyamotoA2_mul_rootB h) hx
  have h1 : a * y = y * a := mem_centralizer_iff.1 (hS.Y0_le_centralizer_A2 hy) a ha
  have h2 := hS.Y0_comm_rootB hy hb
  calc a * b * y = a * (b * y) := by group
    _ = a * (y * b * y⁻¹ * y) := by rw [h2]
    _ = a * y * b := by group
    _ = y * a * b := by rw [h1]
    _ = y * (a * b) := by group

theorem card_Y_le (hS : Setting h L η t Q T) : Nat.card (miyamotoYG h L η Q) ≤ 2 * (2 ^ f) ^ 2 := by
  have hle : miyamotoYG h L η Q ≤ normalizer (miyamotoB2 h L η t : Set G) :=
    inf_le_left.trans hS.M_le_normalizer_B2
  have e := card_sup_mul_card_inf_eq hle
  have h1 : Nat.card (miyamotoB2 h L η t ⊔ miyamotoYG h L η Q : Subgroup G) ≤
      Nat.card (miyamotoM0 Q) :=
    Subgroup.card_le_of_le (sup_le hS.B2_le_M inf_le_left)
  have h2 : Nat.card (miyamotoB2 h L η t ⊓ miyamotoYG h L η Q : Subgroup G) ≤
      Nat.card (CFSG.centerIn Q) := by
    refine Subgroup.card_le_of_le fun x hx => hS.B2_inf_centralizer_A2 ⟨hx.1, hx.2.2⟩
  have hZQ : Nat.card (CFSG.centerIn Q) = 2 * 2 ^ f := by
    rw [hS.centerIn_Q', sup_comm, hS.card_zpowers_sup hS.ZP_le_L, hS.card_ZP]
  rw [hS.card_M, hS.card_B2] at *
  rw [hZQ] at h2
  have h3 : 2 * (2 ^ f) ^ 5 * Nat.card (miyamotoYG h L η Q) ≤
      2 * (2 ^ f) ^ 5 * (2 * (2 ^ f) ^ 2) := by
    rw [← e]
    calc Nat.card (miyamotoB2 h L η t ⊔ miyamotoYG h L η Q : Subgroup G) *
          Nat.card (miyamotoB2 h L η t ⊓ miyamotoYG h L η Q : Subgroup G) ≤
          2 * (2 ^ f) ^ 6 * (2 * 2 ^ f) := Nat.mul_le_mul h1 h2
      _ = 2 * (2 ^ f) ^ 5 * (2 * (2 ^ f) ^ 2) := by ring
  exact Nat.le_of_mul_le_mul_left h3 (by positivity)

theorem Y_eq_Y0 (hS : Setting h L η t Q T) :
    miyamotoYG h L η Q = miyamotoM0 Q ⊓ centralizer (miyamotoI2r1G h L η : Set G) := by
  have hle : miyamotoM0 Q ⊓ centralizer (miyamotoI2r1G h L η : Set G) ≤ miyamotoYG h L η Q :=
    fun y hy => ⟨hy.1, hS.Y0_le_centralizer_A2 hy⟩
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [hS.card_Y0]
  exact hS.card_Y_le

theorem Y_le_centralizer_P (hS : Setting h L η t Q T) :
    miyamotoYG h L η Q ≤ centralizer (miyamotoPG h L η : Set G) := by
  rw [hS.Y_eq_Y0]
  exact hS.Y0_le_centralizer_P

theorem card_Y (hS : Setting h L η t Q T) : Nat.card (miyamotoYG h L η Q) = 2 * (2 ^ f) ^ 2 := by
  rw [hS.Y_eq_Y0, hS.card_Y0]

theorem Y_inf_B2 (hS : Setting h L η t Q T) :
    miyamotoYG h L η Q ⊓ miyamotoB2 h L η t = CFSG.centerIn Q := by
  rw [hS.Y_eq_Y0, hS.Y0_inf_B2]

theorem B2_sup_Y (hS : Setting h L η t Q T) :
    miyamotoB2 h L η t ⊔ miyamotoYG h L η Q = miyamotoM0 Q := by
  rw [hS.Y_eq_Y0, hS.B2_sup_Y0]

theorem exists_mul_Y (hS : Setting h L η t Q T) {m : G} (hm : m ∈ miyamotoM0 Q) :
    ∃ y ∈ miyamotoYG h L η Q, ∃ b ∈ miyamotoB2 h L η t, m = y * b := by
  rw [hS.Y_eq_Y0]
  exact hS.exists_mul_Y0 hm

theorem B2_inf_L (hS : Setting h L η t Q T) : miyamotoB2 h L η t ⊓ L = miyamotoA2G h L η := by
  refine le_antisymm (fun x hx => ?_) (le_inf le_sup_right (miyamotoPull_le h L η _))
  obtain ⟨hxB, hxL⟩ := mem_inf.1 hx
  obtain ⟨u, hu, a, ha, rfl⟩ := hS.exists_of_mem_B2 hxB
  have huL : u ∈ L := by
    have := mul_mem hxL (inv_mem (miyamotoPull_le h L η _ ha))
    rwa [mul_inv_cancel_right] at this
  have hu1 : u ∈ L ⊓ zpowers t := ⟨huL, hu⟩
  rw [hS.inf_zpowers_eq_bot le_rfl, mem_bot] at hu1
  rw [hu1, one_mul]
  exact ha

theorem B2_le_normalizer_A2 (hS : Setting h L η t Q T) :
    miyamotoB2 h L η t ≤ normalizer (miyamotoA2G h L η : Set G) := by
  refine sup_le ?_ le_normalizer
  rw [zpowers_le]
  exact Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun a ha =>
    (hS.comm_t_of_mem_L (miyamotoPull_le h L η _ ha)))

theorem H_le_normalizer_A2 (hS : Setting h L η t Q T) :
    normalizer (CFSG.centerIn Q : Set G) ≤ normalizer (miyamotoA2G h L η : Set G) := by
  obtain ⟨-, -, -, -, hH⟩ := hS.two_core_M
  intro g hg
  obtain ⟨c, hc, d, hd, rfl⟩ := hH g hg
  refine mul_mem ?_ ?_
  · have hcL := hS.centralizer_le_normalizer hc.2
    have hcB := hS.H_le_normalizer_B2 hc.1
    have := mem_normalizer_inf hcB hcL
    rwa [hS.B2_inf_L] at this
  · obtain ⟨y, hy, b, hb, rfl⟩ := hS.exists_mul_Y hd
    exact mul_mem (Subgroup.centralizer_le_normalizer _ hy.2) (hS.B2_le_normalizer_A2 hb)

theorem H_le_normalizer_Y (hS : Setting h L η t Q T) :
    normalizer (CFSG.centerIn Q : Set G) ≤ normalizer (miyamotoYG h L η Q : Set G) :=
  fun _ hg => mem_normalizer_inf (hS.H_le_normalizer_M hg)
    (mem_normalizer_centralizer (hS.H_le_normalizer_A2 hg))

theorem Y_le_M (_hS : Setting h L η t Q T) : miyamotoYG h L η Q ≤ miyamotoM0 Q := inf_le_left

theorem ZP_le_Y (hS : Setting h L η t Q T) : miyamotoZG h L η ≤ miyamotoYG h L η Q := by
  rw [hS.Y_eq_Y0]
  exact fun z hz => ⟨hS.B2_le_M (hS.ZP_le_B2 hz), hS.ZP_le_centralizer_S hz⟩

theorem mem_centerIn_Q_of_mem_Y_of_comm (hS : Setting h L η t Q T) {y : G}
    (hy : y ∈ miyamotoYG h L η Q) (hyt : y * t = t * y) : y ∈ CFSG.centerIn Q := by
  obtain ⟨-, -, hMC, -, -⟩ := hS.two_core_M
  have hyB : y ∈ miyamotoB2 h L η t := by
    rw [← hMC]
    exact ⟨hy.1, mem_centralizer_singleton_iff.2 hyt⟩
  rw [← hS.Y_inf_B2]
  exact ⟨hy, hyB⟩

theorem crossed_mem_ZP_of_mem_M (hS : Setting h L η t Q T) {y : G} (hy : y ∈ miyamotoM0 Q) :
    y⁻¹ * t * y * t ∈ miyamotoZG h L η :=
  hS.crossed_mem_ZP (hS.M_le_H hy)

theorem crossed_mul (hS : Setting h L η t Q T) {x x' : G} (hx : x ∈ miyamotoM0 Q)
    (hx' : x' ∈ miyamotoM0 Q) :
    (x * x')⁻¹ * t * (x * x') * t = (x⁻¹ * t * x * t) * (x'⁻¹ * t * x' * t) := by
  obtain ⟨hMZ, -, -, -, -⟩ := hS.two_core_M
  have hc : Commute (x⁻¹ * t * x * t) x' :=
    (mem_centralizer_iff.1 (hMZ hx') _ (hS.crossed_mem_ZP_of_mem_M hx))
  have hc' : x'⁻¹ * (x⁻¹ * t * x * t) = (x⁻¹ * t * x * t) * x'⁻¹ := (hc.inv_right).eq.symm
  have htt := hS.t_mul_t
  calc (x * x')⁻¹ * t * (x * x') * t = x'⁻¹ * (x⁻¹ * t * x * (t * t)) * x' * t := by
        rw [htt]; group
    _ = (x'⁻¹ * (x⁻¹ * t * x * t)) * (t * x' * t) := by group
    _ = ((x⁻¹ * t * x * t) * x'⁻¹) * (t * x' * t) := by rw [hc']
    _ = (x⁻¹ * t * x * t) * (x'⁻¹ * t * x' * t) := by group

theorem mul_self_mem_ZP_of_mem_Y (hS : Setting h L η t Q T) {y : G}
    (hy : y ∈ miyamotoYG h L η Q) : y * y ∈ miyamotoZG h L η := by
  have hZe := hS.isElementaryAbelian_ZP
  have hQe := hS.isElementaryAbelian_centerIn_Q
  have hsq : ∀ z ∈ miyamotoZG h L η, z * z = 1 := fun z hz => by
    rw [← sq]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian z hz
  have hsqQ : ∀ z ∈ CFSG.centerIn Q, z * z = 1 := fun z hz => by
    rw [← sq]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian z hz
  have hcr := hS.crossed_mul hy.1 hy.1
  have hyy : y * y ∈ CFSG.centerIn Q := by
    refine hS.mem_centerIn_Q_of_mem_Y_of_comm (mul_mem hy hy) ?_
    rw [hsq _ (hS.crossed_mem_ZP_of_mem_M hy.1)] at hcr
    have e : (y * y)⁻¹ * t * (y * y) * t = 1 := hcr
    have e2 : (y * y)⁻¹ * t * (y * y) = t := by
      have := eq_inv_of_mul_eq_one_left e
      rwa [hS.t_inv] at this
    calc y * y * t = (y * y) * ((y * y)⁻¹ * t * (y * y)) := by rw [e2]
      _ = t * (y * y) := by group
  rcases hS.mem_centerIn_Q_iff.1 hyy with h1 | h1
  · exact h1
  · exfalso
    set z := y * y * t with hz
    have hz' : z = t * (y * y) := by
      rw [hz]
      have hc : (y * y * t) * t = t * (y * y * t) :=
        mem_centralizer_singleton_iff.1 (hS.ZP_le_centralizer_t h1)
      calc y * y * t = t * (y * y * t) * t⁻¹ := by rw [← hc]; group
        _ = t * (y * y) * (t * t⁻¹) := by group
        _ = t * (y * y) := by group
    obtain ⟨-, -, -, hMt, -⟩ := hS.two_core_M
    obtain ⟨d, hd, hdt⟩ := hMt z h1
    have hyd : d * y * d⁻¹ ∈ miyamotoYG h L η Q :=
      (mem_normalizer_iff.1 (hS.H_le_normalizer_Y (hS.M_le_H hd)) y).1 hy
    have hsq' : (d * y * d⁻¹) * (d * y * d⁻¹) = t := by
      have e1 : y * y = t * z := by
        rw [hz']
        rw [← mul_assoc, hS.t_mul_t, one_mul]
      calc (d * y * d⁻¹) * (d * y * d⁻¹) = d * (y * y) * d⁻¹ := by group
        _ = d * (t * z) * d⁻¹ := by rw [e1]
        _ = d * (d⁻¹ * t * d) * d⁻¹ := by rw [hdt]
        _ = t := by group
    have hcomm : (d * y * d⁻¹) * t = t * (d * y * d⁻¹) := by
      rw [← hsq']
      group
    have hyQ := hS.mem_centerIn_Q_of_mem_Y_of_comm hyd hcomm
    rw [hsqQ _ hyQ] at hsq'
    exact hS.t_ne_one hsq'.symm

theorem commutator_mem_ZP_of_mem_Y (hS : Setting h L η t Q T) {y y' : G}
    (hy : y ∈ miyamotoYG h L η Q) (hy' : y' ∈ miyamotoYG h L η Q) :
    y * y' * y⁻¹ * y'⁻¹ ∈ miyamotoZG h L η := by
  have e : y * y' * y⁻¹ * y'⁻¹ = (y * y) * ((y⁻¹ * y') * (y⁻¹ * y')) * (y' * y')⁻¹ := by group
  rw [e]
  exact mul_mem (mul_mem (hS.mul_self_mem_ZP_of_mem_Y hy)
    (hS.mul_self_mem_ZP_of_mem_Y (mul_mem (inv_mem hy) hy')))
    (inv_mem (hS.mul_self_mem_ZP_of_mem_Y hy'))

theorem I2_le_H (hS : Setting h L η t Q T) :
    miyamotoI2G h L η ≤ normalizer (CFSG.centerIn Q : Set G) :=
  (miyamotoPull_mono h L η (miyamotoI2_le_I h)).trans hS.IG_le_H

theorem I2_le_C (hS : Setting h L η t Q T) :
    miyamotoI2G h L η ≤ centralizer ({t} : Set G) :=
  (miyamotoPull_le h L η _).trans hS.L_le_centralizer

theorem E_le_Y (hS : Setting h L η t Q T) : miyamotoEG h L η Q ≤ miyamotoYG h L η Q := by
  refine sup_le (commutator_le.2 fun i hi y hy => ?_) hS.ZP_le_Y
  rw [commutatorElement_def]
  exact mul_mem ((mem_normalizer_iff.1 (hS.H_le_normalizer_Y (hS.I2_le_H hi)) y).1 hy)
    (inv_mem hy)

theorem ZP_le_E (_hS : Setting h L η t Q T) : miyamotoZG h L η ≤ miyamotoEG h L η Q :=
  le_sup_right

theorem commutator_mem_E (_hS : Setting h L η t Q T) {i y : G} (hi : i ∈ miyamotoI2G h L η)
    (hy : y ∈ miyamotoYG h L η Q) : i * y * i⁻¹ * y⁻¹ ∈ miyamotoEG h L η Q := by
  have := commutator_mem_commutator hi hy
  rw [commutatorElement_def] at this
  exact mem_sup_left this

theorem t_not_mem_E (hS : Setting h L η t Q T) : t ∉ miyamotoEG h L η Q := by
  intro htE
  refine hS.t_not_mem_ZP (mem_of_mem_commutator_sup_of_fixed hS.ZP_le_Y
    (fun y hy y' hy' => hS.commutator_mem_ZP_of_mem_Y hy hy')
    (fun i hi => hS.H_le_normalizer_Y (hS.I2_le_H hi))
    (fun i hi => hS.H_le_normalizer_ZP (hS.I2_le_H hi))
    (coprime_of_odd_of_isPGroup hS.odd_card_I2 (hS.isPGroup_M.to_le hS.Y_le_M)) htE
    fun i hi => ?_)
  have hit : i * t = t * i := (mem_centralizer_singleton_iff.1 (hS.I2_le_C hi))
  rw [hit, mul_inv_cancel_right, mul_inv_cancel]
  exact one_mem _

theorem exists_I2_fpf_ZP (hS : Setting h L η t Q T) : ∃ i ∈ miyamotoI2G h L η,
    ∀ z ∈ miyamotoZG h L η, i * z * i⁻¹ = z → z = 1 := by
  have : CharP K 2 := h.charP
  obtain ⟨a, -, ha⟩ := exists_unit_weights_ne_one h hS.two_le
  have hDS : miyamotoI2Hom h a ∈ gramSU h (miyamotoJ4 K) := miyamotoI2Hom_mem_gramSU h a
  refine ⟨_, (symm_mem_miyamotoPull_iff h L η (g := ⟨_, hDS⟩)).2 ⟨a, rfl⟩, fun z hz e => ?_⟩
  obtain ⟨g, hg, rfl⟩ := (mem_miyamotoPull h L η).1 hz
  obtain ⟨d, hd, hgd⟩ := (mem_Z h).1 hg
  have e' : (⟨_, hDS⟩ : gramSU h (miyamotoJ4 K)) * g * (⟨_, hDS⟩)⁻¹ = g := by
    apply η.symm.injective
    apply Subtype.ext
    simpa only [map_mul, map_inv, coe_mul, coe_inv] using e
  have e2 : (miyamotoI2Hom h a)⁻¹ * (g : GL (Fin 4) K) * miyamotoI2Hom h a = g := by
    have := congrArg Subtype.val e'
    simp only [coe_mul, coe_inv] at this
    calc (miyamotoI2Hom h a)⁻¹ * (g : GL (Fin 4) K) * miyamotoI2Hom h a =
        (miyamotoI2Hom h a)⁻¹ * (miyamotoI2Hom h a * g * (miyamotoI2Hom h a)⁻¹) *
          miyamotoI2Hom h a := by rw [this]
      _ = g := by group
  rw [hgd, miyamotoI2Hom_conj, miyamotoXGL_inj] at e2
  obtain ⟨-, -, -, e3⟩ := e2
  have hd0 : d = 0 := by
    have : ((a : K) ^ 2 * h.bar ((a : K) ^ 2) - 1) * d = 0 := by linear_combination e3
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 ha)
  have : g = 1 := Subtype.ext (by rw [hgd, hd0, miyamotoXGL_zero, OneMemClass.coe_one])
  rw [this, map_one, OneMemClass.coe_one]

theorem exists_Y_crossed_eq (hS : Setting h L η t Q T) {z : G} (hz : z ∈ miyamotoZG h L η) :
    ∃ y ∈ miyamotoYG h L η Q, y⁻¹ * t * y * t = z := by
  obtain ⟨-, -, -, hMt, -⟩ := hS.two_core_M
  obtain ⟨d, hd, hdt⟩ := hMt z hz
  obtain ⟨y, hy, b, hb, rfl⟩ := hS.exists_mul_Y hd
  refine ⟨y, hy, ?_⟩
  have hbt : b * t = t * b := mem_centralizer_singleton_iff.1 (hS.B2_le_C hb)
  have hcb : b⁻¹ * t * b * t = 1 := by
    calc b⁻¹ * t * b * t = b⁻¹ * (t * b) * t := by group
      _ = b⁻¹ * (b * t) * t := by rw [hbt]
      _ = t * t := by group
      _ = 1 := hS.t_mul_t
  have := hS.crossed_mul hy.1 (hS.B2_le_M hb)
  rw [hcb, mul_one, hdt] at this
  rw [← this, show t * z = z * t from (mem_centralizer_singleton_iff.1
    (hS.ZP_le_centralizer_t hz)).symm, mul_assoc, hS.t_mul_t, mul_one]

theorem exists_E_crossed_eq (hS : Setting h L η t Q T) {z : G} (hz : z ∈ miyamotoZG h L η) :
    ∃ e ∈ miyamotoEG h L η Q, e⁻¹ * t * e * t = z := by
  have hZe := hS.isElementaryAbelian_ZP
  obtain ⟨i, hi, hfpf⟩ := hS.exists_I2_fpf_ZP
  have hiZ := hS.H_le_normalizer_ZP (hS.I2_le_H hi)
  set ψ : miyamotoZG h L η → miyamotoZG h L η := fun z' =>
    ⟨i * z' * i⁻¹ * (z' : G)⁻¹, mul_mem ((mem_normalizer_iff.1 hiZ z').1 z'.2) (inv_mem z'.2)⟩
  have hcomm : ∀ a ∈ miyamotoZG h L η, ∀ b ∈ miyamotoZG h L η, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : miyamotoZG h L η) ⟨b, hb⟩)
  have hinj : Function.Injective ψ := by
    intro z₁ z₂ e
    have e' : i * (z₁ : G) * i⁻¹ * (z₁ : G)⁻¹ = i * z₂ * i⁻¹ * (z₂ : G)⁻¹ := congrArg Subtype.val e
    have hw : (z₂ : G)⁻¹ * z₁ ∈ miyamotoZG h L η := mul_mem (inv_mem z₂.2) z₁.2
    have h1 : i * ((z₂ : G)⁻¹ * z₁) * i⁻¹ = (z₂ : G)⁻¹ * z₁ := by
      have hc1 := hcomm _ ((mem_normalizer_iff.1 hiZ z₂).1 z₂.2) _ (inv_mem z₁.2)
      have hc2 := hcomm _ ((mem_normalizer_iff.1 (inv_mem hiZ) z₁).1 z₁.2) _ (inv_mem z₂.2)
      calc i * ((z₂ : G)⁻¹ * z₁) * i⁻¹ = (i * z₂ * i⁻¹)⁻¹ * (i * z₁ * i⁻¹) := by group
        _ = (i * z₂ * i⁻¹)⁻¹ * (i * z₂ * i⁻¹ * (z₂ : G)⁻¹ * z₁) := by
            rw [show i * (z₁ : G) * i⁻¹ = i * z₁ * i⁻¹ * (z₁ : G)⁻¹ * z₁ by group, e']
        _ = (z₂ : G)⁻¹ * z₁ := by group
    have := hfpf _ hw h1
    exact Subtype.ext (by rw [← mul_left_cancel_iff (a := (z₂ : G)⁻¹), this, inv_mul_cancel])
  obtain ⟨z', hz'⟩ := (Finite.injective_iff_surjective.1 hinj) ⟨z, hz⟩
  have hz'v : i * (z' : G) * i⁻¹ * (z' : G)⁻¹ = z := congrArg Subtype.val hz'
  obtain ⟨y, hy, hyz⟩ := hS.exists_Y_crossed_eq z'.2
  refine ⟨i * y * i⁻¹ * y⁻¹, hS.commutator_mem_E hi hy, ?_⟩
  have hiy : i * y * i⁻¹ ∈ miyamotoM0 Q :=
    (mem_normalizer_iff.1 (hS.H_le_normalizer_M (hS.I2_le_H hi)) y).1 hy.1
  have h1 := hS.crossed_mul hiy (inv_mem hy.1)
  have hit : i * t = t * i := mem_centralizer_singleton_iff.1 (hS.I2_le_C hi)
  have h2 := CFSG.EvenSmallLie.UnitarySix.YamadaD.crossed_conj (x := y) hit
  have h3 := hS.crossed_mul hy.1 (inv_mem hy.1)
  rw [mul_inv_cancel] at h3
  have h4 : y⁻¹⁻¹ * t * y⁻¹ * t = (y⁻¹ * t * y * t)⁻¹ := by
    have e1 : (1 : G)⁻¹ * t * 1 * t = 1 := by rw [inv_one, one_mul, mul_one, hS.t_mul_t]
    rw [e1] at h3
    exact eq_inv_of_mul_eq_one_right h3.symm
  rw [h1, h2, h4, hyz, hz'v]

theorem E_sup_centerIn_Q (hS : Setting h L η t Q T) :
    miyamotoEG h L η Q ⊔ CFSG.centerIn Q = miyamotoYG h L η Q := by
  refine le_antisymm (sup_le hS.E_le_Y ?_) fun y hy => ?_
  · intro x hx
    have : x ∈ miyamotoYG h L η Q ⊓ miyamotoB2 h L η t := by rw [hS.Y_inf_B2]; exact hx
    exact this.1
  · obtain ⟨e, he, hez⟩ := hS.exists_E_crossed_eq (hS.crossed_mem_ZP_of_mem_M hy.1)
    have heY := hS.E_le_Y he
    have h1 := hS.crossed_mul (inv_mem heY.1) hy.1
    have h3 := hS.crossed_mul heY.1 (inv_mem heY.1)
    rw [mul_inv_cancel] at h3
    have h4 : e⁻¹⁻¹ * t * e⁻¹ * t = (e⁻¹ * t * e * t)⁻¹ := by
      have e1 : (1 : G)⁻¹ * t * 1 * t = 1 := by rw [inv_one, one_mul, mul_one, hS.t_mul_t]
      rw [e1] at h3
      exact eq_inv_of_mul_eq_one_right h3.symm
    rw [h4, hez, inv_mul_cancel] at h1
    have hw : e⁻¹ * y ∈ CFSG.centerIn Q := by
      refine hS.mem_centerIn_Q_of_mem_Y_of_comm (mul_mem (inv_mem heY) hy) ?_
      have e2 : (e⁻¹ * y)⁻¹ * t * (e⁻¹ * y) = t := by
        have := eq_inv_of_mul_eq_one_left h1
        rwa [hS.t_inv] at this
      calc e⁻¹ * y * t = (e⁻¹ * y) * ((e⁻¹ * y)⁻¹ * t * (e⁻¹ * y)) := by rw [e2]
        _ = t * (e⁻¹ * y) := by group
    rw [show y = e * (e⁻¹ * y) by group]
    exact mul_mem (mem_sup_left he) (mem_sup_right hw)

theorem E_inf_centerIn_Q (hS : Setting h L η t Q T) :
    miyamotoEG h L η Q ⊓ CFSG.centerIn Q = miyamotoZG h L η := by
  refine le_antisymm (fun x hx => ?_) (le_inf hS.ZP_le_E hS.ZP_le_centerIn_Q)
  obtain ⟨hxE, hxZ⟩ := mem_inf.1 hx
  rcases hS.mem_centerIn_Q_iff.1 hxZ with h1 | h1
  · exact h1
  · exfalso
    apply hS.t_not_mem_E
    have := mul_mem (inv_mem hxE) (hS.ZP_le_E h1)
    rwa [inv_mul_cancel_left] at this

theorem card_E (hS : Setting h L η t Q T) : Nat.card (miyamotoEG h L η Q) = (2 ^ f) ^ 2 := by
  have hle : miyamotoEG h L η Q ≤ normalizer (CFSG.centerIn Q : Set G) :=
    (hS.E_le_Y.trans hS.Y_le_M).trans hS.M_le_H
  have e := card_sup_mul_card_inf_eq hle
  rw [sup_comm, hS.E_sup_centerIn_Q, inf_comm, hS.E_inf_centerIn_Q, hS.card_Y, hS.card_ZP,
    hS.centerIn_Q', sup_comm, hS.card_zpowers_sup hS.ZP_le_L, hS.card_ZP] at e
  have e' : (2 * 2 ^ f) * Nat.card (miyamotoEG h L η Q) = (2 * 2 ^ f) * (2 ^ f) ^ 2 := by
    rw [← e]
    ring
  exact Nat.eq_of_mul_eq_mul_left (by positivity) e'

theorem E_inf_B2 (hS : Setting h L η t Q T) :
    miyamotoEG h L η Q ⊓ miyamotoB2 h L η t = miyamotoZG h L η := by
  refine le_antisymm (fun x hx => ?_) (le_inf hS.ZP_le_E hS.ZP_le_B2)
  have hxZ : x ∈ CFSG.centerIn Q := by
    rw [← hS.Y_inf_B2]
    exact ⟨hS.E_le_Y hx.1, hx.2⟩
  rw [← hS.E_inf_centerIn_Q]
  exact ⟨hx.1, hxZ⟩

theorem E_sup_B2 (hS : Setting h L η t Q T) :
    miyamotoEG h L η Q ⊔ miyamotoB2 h L η t = miyamotoM0 Q := by
  refine le_antisymm (sup_le (hS.E_le_Y.trans hS.Y_le_M) hS.B2_le_M) ?_
  rw [← hS.B2_sup_Y, ← hS.E_sup_centerIn_Q, sup_comm]
  refine sup_le (sup_le le_sup_left ?_) le_sup_right
  intro x hx
  have : x ∈ miyamotoYG h L η Q ⊓ miyamotoB2 h L η t := by rw [hS.Y_inf_B2]; exact hx
  exact mem_sup_right this.2

theorem E_le_centralizer_P (hS : Setting h L η t Q T) :
    miyamotoEG h L η Q ≤ centralizer (miyamotoPG h L η : Set G) :=
  hS.E_le_Y.trans hS.Y_le_centralizer_P

theorem M_sup_Q (hS : Setting h L η t Q T) :
    miyamotoM0 Q ⊔ Q = miyamotoEG h L η Q ⊔ Q := by
  refine le_antisymm (sup_le ?_ le_sup_right) (sup_le_sup_right (hS.E_le_Y.trans hS.Y_le_M) _)
  rw [← hS.E_sup_B2]
  exact sup_le le_sup_left (hS.B2_le_Q.trans le_sup_right)

theorem M_comm_Y (hS : Setting h L η t Q T) {d y : G} (hd : d ∈ miyamotoM0 Q)
    (hy : y ∈ miyamotoYG h L η Q) : d * y * d⁻¹ * y⁻¹ ∈ miyamotoZG h L η := by
  obtain ⟨hMZ, -, -, -, -⟩ := hS.two_core_M
  obtain ⟨y', hy', b, hb, rfl⟩ := hS.exists_mul_Y hd
  obtain ⟨u, hu, a, ha, rfl⟩ := hS.exists_of_mem_B2 hb
  have hay : a * y * a⁻¹ = y := by
    have := mem_centralizer_iff.1 hy.2 a ha
    calc a * y * a⁻¹ = y * a * a⁻¹ := by rw [this]
      _ = y := by group
  have huy : u * y * u⁻¹ * y⁻¹ ∈ miyamotoZG h L η := by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hu
    rcases hS.zpow_t_eq k with h1 | h1
    · rw [h1, one_mul, inv_one, mul_one, mul_inv_cancel]
      exact one_mem _
    · rw [h1]
      have hc := hS.crossed_mem_ZP_of_mem_M (inv_mem hy.1)
      have e : t * y * t⁻¹ * y⁻¹ = (y⁻¹⁻¹ * t * y⁻¹ * t)⁻¹ := by
        calc t * y * t⁻¹ * y⁻¹ = t⁻¹ * y * t⁻¹ * y⁻¹ := by rw [hS.t_inv]
          _ = (y⁻¹⁻¹ * t * y⁻¹ * t)⁻¹ := by group
      rw [e]
      exact inv_mem hc
  set w := u * y * u⁻¹ * y⁻¹ with hw
  have hwy' : y' * w * y'⁻¹ = w := by
    have := mem_centralizer_iff.1 (hMZ hy'.1) w huy
    calc y' * w * y'⁻¹ = w * y' * y'⁻¹ := by rw [this]
      _ = w := by group
  have e : y' * (u * a) * y * (y' * (u * a))⁻¹ * y⁻¹ =
      (y' * w * y'⁻¹) * (y' * y * y'⁻¹ * y⁻¹) := by
    calc y' * (u * a) * y * (y' * (u * a))⁻¹ * y⁻¹ = y' * u * (a * y * a⁻¹) * u⁻¹ * y'⁻¹ * y⁻¹ := by
          group
      _ = y' * (u * y * u⁻¹ * y⁻¹) * y'⁻¹ * (y' * y * y'⁻¹ * y⁻¹) := by rw [hay]; group
  rw [e, hwy']
  exact mul_mem huy (hS.commutator_mem_ZP_of_mem_Y hy' hy)

theorem N2G_le_centralizer_Y (hS : Setting h L η t Q T) :
    miyamotoN2G h L η ≤ centralizer (miyamotoYG h L η Q : Set G) := by
  have : CharP K 2 := h.charP
  have hQe := hS.isElementaryAbelian_centerIn_Q
  have hN2Z : miyamotoN2G h L η ≤ L ⊓ centralizer (miyamotoZG h L η : Set G) := by
    rw [centralizer_miyamotoZG]
    exact le_sup_right.trans le_sup_right
  have hN2K : miyamotoN2G h L η ≤ centralizer (CFSG.centerIn Q : Set G) :=
    hN2Z.trans hS.L_inf_centralizer_ZP_le_K0
  intro n hn
  rw [mem_centralizer_iff]
  intro y hy
  have hφ : ∀ n ∈ miyamotoN2G h L η, n * y * n⁻¹ * y⁻¹ ∈ CFSG.centerIn Q := by
    intro n hn
    have hnH : n ∈ normalizer (CFSG.centerIn Q : Set G) := hS.K0_le_H (hN2K hn)
    have hny : n * y * n⁻¹ ∈ miyamotoYG h L η Q :=
      (mem_normalizer_iff.1 (hS.H_le_normalizer_Y hnH) y).1 hy
    refine hS.mem_centerIn_Q_of_mem_Y_of_comm (mul_mem hny (inv_mem hy)) ?_
    have hnt : n * t = t * n := hS.comm_t_of_mem_L (hN2Z hn).1
    have h1 := hS.crossed_mul hny.1 (inv_mem hy.1)
    have h2 := CFSG.EvenSmallLie.UnitarySix.YamadaD.crossed_conj (x := y) hnt
    have hcy := hS.crossed_mem_ZP_of_mem_M hy.1
    have h3 : n * (y⁻¹ * t * y * t) * n⁻¹ = y⁻¹ * t * y * t := by
      have := mem_centralizer_iff.1 (hN2Z hn).2 _ hcy
      calc n * (y⁻¹ * t * y * t) * n⁻¹ = (y⁻¹ * t * y * t) * n * n⁻¹ := by rw [this]
        _ = y⁻¹ * t * y * t := by group
    have h4 := hS.crossed_mul hy.1 (inv_mem hy.1)
    rw [mul_inv_cancel] at h4
    have h5 : y⁻¹⁻¹ * t * y⁻¹ * t = (y⁻¹ * t * y * t)⁻¹ := by
      have e1 : (1 : G)⁻¹ * t * 1 * t = 1 := by rw [inv_one, one_mul, mul_one, hS.t_mul_t]
      rw [e1] at h4
      exact eq_inv_of_mul_eq_one_right h4.symm
    rw [h2, h3, h5, mul_inv_cancel] at h1
    have e2 : (n * y * n⁻¹ * y⁻¹)⁻¹ * t * (n * y * n⁻¹ * y⁻¹) = t := by
      have := eq_inv_of_mul_eq_one_left h1
      rwa [hS.t_inv] at this
    calc n * y * n⁻¹ * y⁻¹ * t =
        (n * y * n⁻¹ * y⁻¹) * ((n * y * n⁻¹ * y⁻¹)⁻¹ * t * (n * y * n⁻¹ * y⁻¹)) := by rw [e2]
      _ = t * (n * y * n⁻¹ * y⁻¹) := by group
  have hcomm : ∀ a ∈ CFSG.centerIn Q, ∀ b ∈ CFSG.centerIn Q, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : CFSG.centerIn Q) ⟨b, hb⟩)
  have hmul : ∀ n₁ ∈ miyamotoN2G h L η, ∀ n₂ ∈ miyamotoN2G h L η,
      n₁ * n₂ * y * (n₁ * n₂)⁻¹ * y⁻¹ = (n₁ * y * n₁⁻¹ * y⁻¹) * (n₂ * y * n₂⁻¹ * y⁻¹) := by
    intro n₁ h₁ n₂ h₂
    have hc := mem_centralizer_iff.1 (hN2K h₁) _ (hφ n₂ h₂)
    calc n₁ * n₂ * y * (n₁ * n₂)⁻¹ * y⁻¹ =
        n₁ * (n₂ * y * n₂⁻¹ * y⁻¹) * n₁⁻¹ * (n₁ * y * n₁⁻¹ * y⁻¹) := by group
      _ = (n₂ * y * n₂⁻¹ * y⁻¹) * n₁ * n₁⁻¹ * (n₁ * y * n₁⁻¹ * y⁻¹) := by rw [← hc]
      _ = (n₂ * y * n₂⁻¹ * y⁻¹) * (n₁ * y * n₁⁻¹ * y⁻¹) := by group
      _ = _ := hcomm _ (hφ n₂ h₂) _ (hφ n₁ h₁)
  have hinv : ∀ n ∈ miyamotoN2G h L η,
      n⁻¹ * y * n⁻¹⁻¹ * y⁻¹ = (n * y * n⁻¹ * y⁻¹)⁻¹ := by
    intro n hn
    have := hmul n hn n⁻¹ (inv_mem hn)
    rw [mul_inv_cancel, one_mul, inv_one, mul_one, mul_inv_cancel] at this
    exact eq_inv_of_mul_eq_one_right this.symm
  have hle : ⁅miyamotoN2G h L η, miyamotoN2G h L η⁆ ≤ centralizer ({y} : Set G) := by
    refine commutator_le.2 fun a ha b hb => ?_
    rw [mem_centralizer_singleton_iff, commutatorElement_def]
    have e1 := hmul (a * b) (mul_mem ha hb) (a⁻¹ * b⁻¹) (mul_mem (inv_mem ha) (inv_mem hb))
    have e2 := hmul a ha b hb
    have e3 := hmul a⁻¹ (inv_mem ha) b⁻¹ (inv_mem hb)
    rw [hinv a ha, hinv b hb] at e3
    have e4 : (a * b * (a⁻¹ * b⁻¹)) * y * (a * b * (a⁻¹ * b⁻¹))⁻¹ * y⁻¹ = 1 := by
      have := hcomm _ (hφ a ha) _ (hφ b hb)
      rw [e1, e2, e3, this]
      group
    have e5 : a * b * a⁻¹ * b⁻¹ * y = y * (a * b * a⁻¹ * b⁻¹) := by
      have := mul_eq_one_iff_eq_inv.1 e4
      rw [inv_inv] at this
      calc a * b * a⁻¹ * b⁻¹ * y = (a * b * (a⁻¹ * b⁻¹)) * y * (a * b * (a⁻¹ * b⁻¹))⁻¹ *
          (a * b * a⁻¹ * b⁻¹) := by group
        _ = y * (a * b * a⁻¹ * b⁻¹) := by rw [this]
    exact e5
  rw [← hS.commutator_N2G] at hn
  exact (mem_centralizer_singleton_iff.1 (hle hn)).symm

theorem exists_I2_act (hS : Setting h L η t Q T) {g i : G}
    (hg : g ∈ normalizer (CFSG.centerIn Q : Set G)) (hi : i ∈ miyamotoI2G h L η) :
    ∃ i' ∈ miyamotoI2G h L η, ∀ y ∈ miyamotoYG h L η Q,
      (i' * y * i'⁻¹)⁻¹ * ((g * i * g⁻¹) * y * (g * i * g⁻¹)⁻¹) ∈ miyamotoZG h L η := by
  have : CharP K 2 := h.charP
  obtain ⟨hMZ, -, -, -, hH⟩ := hS.two_core_M
  obtain ⟨c, hc, d, hd, rfl⟩ := hH g hg
  have hiH := hS.I2_le_H hi
  have hw : i⁻¹ * d * i * d⁻¹ ∈ miyamotoM0 Q := by
    have := (mem_normalizer_iff.1 (hS.H_le_normalizer_M (inv_mem hiH)) d).1 hd
    rw [inv_inv] at this
    exact mul_mem this (inv_mem hd)
  set w' := c * (i⁻¹ * d * i * d⁻¹) * c⁻¹ with hw'
  have hw'M : w' ∈ miyamotoM0 Q :=
    (mem_normalizer_iff.1 (hS.H_le_normalizer_M hc.1) _).1 hw
  have hgi : c * d * i * (c * d)⁻¹ = (c * i * c⁻¹) * w' := by
    rw [hw']
    group
  have hciL : c * i * c⁻¹ ∈ L :=
    (mem_normalizer_iff.1 (hS.centralizer_le_normalizer hc.2) i).1 (miyamotoPull_le h L η _ hi)
  have hciZ : c * i * c⁻¹ ∈ normalizer (miyamotoZG h L η : Set G) :=
    mul_mem (mul_mem (hS.H_le_normalizer_ZP hc.1) (hS.H_le_normalizer_ZP hiH))
      (inv_mem (hS.H_le_normalizer_ZP hc.1))
  have hlevi : c * i * c⁻¹ ∈ miyamotoA2G h L η ⊔ (miyamotoI2G h L η ⊔ miyamotoN2G h L η) := by
    rw [← normalizer_miyamotoA2G, ← normalizer_miyamotoZG]
    exact ⟨hciL, hciZ⟩
  have hIY : miyamotoI2G h L η ≤ normalizer (miyamotoYG h L η Q : Set G) :=
    fun i hi => hS.H_le_normalizer_Y (hS.I2_le_H hi)
  have hact : miyamotoA2G h L η ⊔ (miyamotoI2G h L η ⊔ miyamotoN2G h L η) ≤
      actsLike (miyamotoI2G h L η) (miyamotoYG h L η Q) hIY := by
    refine sup_le (fun a ha => ⟨1, one_mem _, fun y hy => ?_⟩) (sup_le
      (fun j hj => ⟨j, hj, fun _ _ => rfl⟩) fun n hn => ⟨1, one_mem _, fun y hy => ?_⟩)
    · have := mem_centralizer_iff.1 hy.2 a ha
      calc a * y * a⁻¹ = y * a * a⁻¹ := by rw [this]
        _ = 1 * y * 1⁻¹ := by group
    · have := mem_centralizer_iff.1 (hS.N2G_le_centralizer_Y hn) y hy
      calc n * y * n⁻¹ = y * n * n⁻¹ := by rw [← this]
        _ = 1 * y * 1⁻¹ := by group
  obtain ⟨i', hi', hci⟩ := hact hlevi
  refine ⟨i', hi', fun y hy => ?_⟩
  rw [hgi]
  have hz := hS.M_comm_Y hw'M hy
  set z := w' * y * w'⁻¹ * y⁻¹ with hz'
  have hcz : (c * i * c⁻¹) * z * (c * i * c⁻¹)⁻¹ ∈ miyamotoZG h L η :=
    (mem_normalizer_iff.1 hciZ z).1 hz
  have e : ((c * i * c⁻¹) * w') * y * ((c * i * c⁻¹) * w')⁻¹ =
      ((c * i * c⁻¹) * z * (c * i * c⁻¹)⁻¹) * ((c * i * c⁻¹) * y * (c * i * c⁻¹)⁻¹) := by
    rw [hz']
    group
  rw [e, hci y hy]
  have hzc : (c * i * c⁻¹) * z * (c * i * c⁻¹)⁻¹ * (i' * y * i'⁻¹) =
      (i' * y * i'⁻¹) * ((c * i * c⁻¹) * z * (c * i * c⁻¹)⁻¹) := by
    have hy'Y : i' * y * i'⁻¹ ∈ miyamotoYG h L η Q := (mem_normalizer_iff.1 (hIY hi') y).1 hy
    exact (mem_centralizer_iff.1 (hMZ hy'Y.1) _ hcz)
  rw [hzc]
  simpa [mul_assoc] using hcz

theorem H_le_normalizer_E (hS : Setting h L η t Q T) :
    normalizer (CFSG.centerIn Q : Set G) ≤ normalizer (miyamotoEG h L η Q : Set G) := by
  obtain ⟨hMZ, -, -, -, -⟩ := hS.two_core_M
  intro g hg
  have key : miyamotoEG h L η Q ≤ (miyamotoEG h L η Q).comap (MulAut.conj g).toMonoidHom := by
    refine sup_le (commutator_le.2 fun i hi y hy => ?_) fun z hz => ?_
    · rw [mem_comap]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      obtain ⟨i', hi', hact⟩ := hS.exists_I2_act hg hi
      have hy' : g * y * g⁻¹ ∈ miyamotoYG h L η Q :=
        (mem_normalizer_iff.1 (hS.H_le_normalizer_Y hg) y).1 hy
      have hz := hact _ hy'
      set z := (i' * (g * y * g⁻¹) * i'⁻¹)⁻¹ * ((g * i * g⁻¹) * (g * y * g⁻¹) *
        (g * i * g⁻¹)⁻¹) with hzdef
      have hcz : z * (g * y * g⁻¹)⁻¹ = (g * y * g⁻¹)⁻¹ * z :=
        mem_centralizer_iff.1 (hMZ (inv_mem hy'.1)) z hz
      have e : g * ⁅i, y⁆ * g⁻¹ =
          (i' * (g * y * g⁻¹) * i'⁻¹ * (g * y * g⁻¹)⁻¹) * z := by
        rw [commutatorElement_def]
        calc g * (i * y * i⁻¹ * y⁻¹) * g⁻¹ =
            (g * i * g⁻¹) * (g * y * g⁻¹) * (g * i * g⁻¹)⁻¹ * (g * y * g⁻¹)⁻¹ := by group
          _ = (i' * (g * y * g⁻¹) * i'⁻¹) * z * (g * y * g⁻¹)⁻¹ := by rw [hzdef]; group
          _ = (i' * (g * y * g⁻¹) * i'⁻¹) * (z * (g * y * g⁻¹)⁻¹) := by group
          _ = (i' * (g * y * g⁻¹) * i'⁻¹) * ((g * y * g⁻¹)⁻¹ * z) := by rw [hcz]
          _ = _ := by group
      rw [e]
      exact mul_mem (hS.commutator_mem_E hi' hy') (hS.ZP_le_E hz)
    · rw [mem_comap]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact hS.ZP_le_E ((mem_normalizer_iff.1 (hS.H_le_normalizer_ZP hg) z).1 hz)
  exact mem_normalizer_fintype fun e he => key he

theorem sec3_3 (hS : Setting h L η t Q T) :
    miyamotoEG h L η Q ≤ centralizer (miyamotoPG h L η : Set G) ∧
      Nat.card (miyamotoEG h L η Q) = (2 ^ f) ^ 2 ∧
      miyamotoEG h L η Q ⊔ miyamotoB2 h L η t = miyamotoM0 Q ∧
      miyamotoEG h L η Q ⊓ miyamotoB2 h L η t = miyamotoZG h L η ∧
      normalizer (CFSG.centerIn Q : Set G) ≤ normalizer (miyamotoEG h L η Q : Set G) ∧
      (∀ e ∈ miyamotoEG h L η Q, e⁻¹ * t * e * t ∈ miyamotoZG h L η) ∧
      (∀ e ∈ miyamotoEG h L η Q, e⁻¹ * t * e * t = 1 ↔ e ∈ miyamotoZG h L η) ∧
      (∀ z ∈ miyamotoZG h L η, ∃ e ∈ miyamotoEG h L η Q, e⁻¹ * t * e * t = z) ∧
      (∀ c ∈ normalizer (CFSG.centerIn Q : Set G) ⊓ centralizer ({t} : Set G),
        ∀ e ∈ miyamotoEG h L η Q,
          (c * e * c⁻¹)⁻¹ * t * (c * e * c⁻¹) * t = c * (e⁻¹ * t * e * t) * c⁻¹) ∧
      miyamotoM0 Q ⊔ Q = miyamotoEG h L η Q ⊔ Q := by
  refine ⟨hS.E_le_centralizer_P, hS.card_E, hS.E_sup_B2, hS.E_inf_B2, hS.H_le_normalizer_E,
    fun e he => hS.crossed_mem_ZP_of_mem_M (hS.E_le_Y he).1,
    fun e he => ⟨fun h1 => ?_, fun h1 => ?_⟩,
    fun z hz => hS.exists_E_crossed_eq hz,
    fun c hc e _ => CFSG.EvenSmallLie.UnitarySix.YamadaD.crossed_conj
      (mem_centralizer_singleton_iff.1 hc.2), hS.M_sup_Q⟩
  · have hcomm : e * t = t * e := by
      have e2 : e⁻¹ * t * e = t := by
        have := eq_inv_of_mul_eq_one_left h1
        rwa [hS.t_inv] at this
      calc e * t = e * (e⁻¹ * t * e) := by rw [e2]
        _ = t * e := by group
    have := hS.mem_centerIn_Q_of_mem_Y_of_comm (hS.E_le_Y he) hcomm
    rw [← hS.E_inf_centerIn_Q]
    exact ⟨he, this⟩
  · have hct : e * t = t * e := mem_centralizer_singleton_iff.1 (hS.ZP_le_centralizer_t h1)
    calc e⁻¹ * t * e * t = e⁻¹ * (t * e) * t := by group
      _ = e⁻¹ * (e * t) * t := by rw [hct]
      _ = t * t := by group
      _ = 1 := hS.t_mul_t

end Setting

end CFSG.LocalAnalysis.EvenBN.U4
