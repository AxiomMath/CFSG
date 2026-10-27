module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32NonabFB2a
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.RankThree.PartOne.Census3 (IsoLie)
open scoped Pointwise

section CompHelpers

variable {Y : Type} [Group Y]

private theorem r3_eq_one_of_central {K : Subgroup Y} (hZ : Subgroup.center ↥K = ⊥)
    {b : Y} (hb : b ∈ K) (hc : ∀ g ∈ K, g * b = b * g) : b = 1 := by
  have hmem : (⟨b, hb⟩ : ↥K) ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hc g g.2)
  rw [hZ, Subgroup.mem_bot] at hmem
  exact congrArg Subtype.val hmem

private theorem r3_comm_of_ne [Finite Y] {K L : Subgroup Y} (hK : CFSG.IsComponent K)
    (hL : CFSG.IsComponent L) (hne : K ≠ L) {x y : Y} (hx : x ∈ K) (hy : y ∈ L) :
    x * y = y * x := by
  rcases CFSG.LocalCores.distinct_components_commute hK hL with h | h
  · exact absurd h hne
  · have hm : x * y * x⁻¹ * y⁻¹ ∈ ⁅K, L⁆ := Subgroup.commutator_mem_commutator hx hy
    rw [h, Subgroup.mem_bot] at hm
    calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
      _ = y * x := by rw [hm, one_mul]

private theorem r3_eq_one_of_mem_of_ne [Finite Y] {K L : Subgroup Y} (hK : CFSG.IsComponent K)
    (hL : CFSG.IsComponent L) (hne : K ≠ L) (hZ : Subgroup.center ↥K = ⊥) {x : Y}
    (hxK : x ∈ K) (hxL : x ∈ L) : x = 1 :=
  r3_eq_one_of_central hZ hxK (fun g hg => r3_comm_of_ne hK hL hne hg hxL)

private theorem r3_mul_eq_one [Finite Y] {K₁ K₂ K₃ : Subgroup Y}
    (c₁ : CFSG.IsComponent K₁) (c₂ : CFSG.IsComponent K₂) (c₃ : CFSG.IsComponent K₃)
    (h12 : K₁ ≠ K₂) (h13 : K₁ ≠ K₃) (h23 : K₂ ≠ K₃)
    (z₁ : Subgroup.center ↥K₁ = ⊥) (z₂ : Subgroup.center ↥K₂ = ⊥)
    {a b : Y} (ha : a ∈ K₁) (hb : b ∈ K₂) (hab : a * b ∈ K₃) : a * b = 1 := by
  have hb1 : b = 1 := by
    refine r3_eq_one_of_central z₂ hb (fun g hg => ?_)
    have hga : g * a = a * g := r3_comm_of_ne c₂ c₁ h12.symm hg ha
    have hgc : g * (a * b) = a * b * g := r3_comm_of_ne c₂ c₃ h23 hg hab
    have key : a * (g * b) = a * (b * g) := by
      calc a * (g * b) = (a * g) * b := (mul_assoc _ _ _).symm
        _ = (g * a) * b := by rw [hga]
        _ = g * (a * b) := mul_assoc _ _ _
        _ = a * b * g := hgc
        _ = a * (b * g) := mul_assoc _ _ _
    exact mul_left_cancel key
  have ha3 : a ∈ K₃ := by
    rw [hb1, mul_one] at hab
    exact hab
  rw [hb1, mul_one]
  exact r3_eq_one_of_mem_of_ne c₁ c₃ h13 z₁ ha ha3

private theorem r3_exists_order_five [Finite Y] {K : Subgroup Y} (h5 : 5 ∣ Nat.card ↥K) :
    ∃ s : Y, s ∈ K ∧ orderOf s = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 5 h5
  exact ⟨x.1, x.2, (Subgroup.orderOf_coe x).trans hx⟩

private theorem r3_zpowers_comm {s x y : Y} (hx : x ∈ Subgroup.zpowers s)
    (hy : y ∈ Subgroup.zpowers s) : x * y = y * x := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact ((Commute.refl s).zpow_zpow m n).eq

private theorem r3_mem_sup_comm {H K : Subgroup Y} (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h)
    {x : Y} (hx : x ∈ H ⊔ K) : ∃ h ∈ H, ∃ k ∈ K, h * k = x := by
  let T : Subgroup Y :=
    { carrier := {x | ∃ h ∈ H, ∃ k ∈ K, h * k = x}
      mul_mem' := by
        rintro _ _ ⟨h₁, hh₁, k₁, hk₁, rfl⟩ ⟨h₂, hh₂, k₂, hk₂, rfl⟩
        refine ⟨h₁ * h₂, H.mul_mem hh₁ hh₂, k₁ * k₂, K.mul_mem hk₁ hk₂, ?_⟩
        calc h₁ * h₂ * (k₁ * k₂) = h₁ * (h₂ * k₁) * k₂ := by group
          _ = h₁ * (k₁ * h₂) * k₂ := by rw [hc h₂ hh₂ k₁ hk₁]
          _ = h₁ * k₁ * (h₂ * k₂) := by group
      one_mem' := ⟨1, H.one_mem, 1, K.one_mem, one_mul 1⟩
      inv_mem' := by
        rintro _ ⟨h, hh, k, hk, rfl⟩
        refine ⟨h⁻¹, H.inv_mem hh, k⁻¹, K.inv_mem hk, ?_⟩
        rw [mul_inv_rev]
        exact ((show Commute h k from hc h hh k hk).inv_inv).eq }
  have hle : H ⊔ K ≤ T :=
    sup_le (fun h hh => ⟨h, hh, 1, K.one_mem, mul_one h⟩)
      (fun k hk => ⟨1, H.one_mem, k, hk, one_mul k⟩)
  exact hle hx

private theorem r3_card_sup [Finite Y] {H K : Subgroup Y}
    (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) (hd : H ⊓ K = ⊥) :
    Nat.card ↥(H ⊔ K) = Nat.card H * Nat.card K := by
  have hinj : Function.Injective (fun p : H × K => (p.1 : Y) * (p.2 : Y)) :=
    Subgroup.mul_injective_of_disjoint (disjoint_iff.mpr hd)
  have hset : ((H ⊔ K : Subgroup Y) : Set Y) =
      Set.range (fun p : H × K => (p.1 : Y) * (p.2 : Y)) := by
    ext x
    constructor
    · intro hx
      obtain ⟨h, hh, k, hk, rfl⟩ := r3_mem_sup_comm hc hx
      exact ⟨(⟨h, hh⟩, ⟨k, hk⟩), rfl⟩
    · rintro ⟨⟨h, k⟩, rfl⟩
      exact mul_mem (Subgroup.mem_sup_left h.2) (Subgroup.mem_sup_right k.2)
  calc Nat.card ↥(H ⊔ K) = Nat.card ↥((H ⊔ K : Subgroup Y) : Set Y) := rfl
    _ = Nat.card ↥(Set.range (fun p : H × K => (p.1 : Y) * (p.2 : Y))) := by rw [hset]
    _ = Nat.card (H × K) := Nat.card_range_of_injective hinj
    _ = Nat.card H * Nat.card K := Nat.card_prod _ _

private theorem r3_comm_sup {H K : Subgroup Y}
    (hH : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x) (hK : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x)
    (hHK : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) :
    ∀ x ∈ H ⊔ K, ∀ y ∈ H ⊔ K, x * y = y * x := by
  intro x hx y hy
  obtain ⟨h, hh, k, hk, rfl⟩ := r3_mem_sup_comm hHK hx
  obtain ⟨h', hh', k', hk', rfl⟩ := r3_mem_sup_comm hHK hy
  calc h * k * (h' * k') = h * (k * h') * k' := by group
    _ = h * (h' * k) * k' := by rw [← hHK h' hh' k hk]
    _ = (h * h') * (k * k') := by group
    _ = (h' * h) * (k' * k) := by rw [hH h hh h' hh', hK k hk k' hk']
    _ = h' * (h * k') * k := by group
    _ = h' * (k' * h) * k := by rw [hHK h hh k' hk']
    _ = h' * k' * (h * k) := by group

private theorem r3_cross_sup {H K L : Subgroup Y}
    (hH : ∀ h ∈ H, ∀ l ∈ L, h * l = l * h) (hK : ∀ k ∈ K, ∀ l ∈ L, k * l = l * k) :
    ∀ x ∈ H ⊔ K, ∀ l ∈ L, x * l = l * x := by
  intro x hx l hl
  have hle : H ⊔ K ≤ Subgroup.centralizer (L : Set Y) :=
    sup_le (fun h hh => Subgroup.mem_centralizer_iff.mpr (fun l' hl' => (hH h hh l' hl').symm))
      (fun k hk => Subgroup.mem_centralizer_iff.mpr (fun l' hl' => (hK k hk l' hl').symm))
  exact (Subgroup.mem_centralizer_iff.mp (hle hx) l hl).symm

end CompHelpers

section Part

variable {Y : Type} [Group Y] [Finite Y] {F Γ B R₀ : Subgroup Y} {x : Y}

private theorem r3_sylow_comm {F E : Subgroup Y}
    (hF : CFSG.ABGLocalTools.IsSylowOf 5 F ⊤) (hFc : Nat.card F = 125) (hEc : Nat.card E = 125)
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hFcard : Nat.card F = 5 ^ (Nat.card Y).factorization 5 := by
    have := hF.card_eq
    rwa [Subgroup.card_top] at this
  have hEcard : Nat.card E = 5 ^ (Nat.card Y).factorization 5 :=
    hEc.trans (hFc.symm.trans hFcard)
  haveI : Finite (Sylow 5 Y) :=
    Finite.of_injective (fun P : Sylow 5 Y => (P : Set Y))
      (fun P Q hPQ => SetLike.coe_injective hPQ)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y (Sylow.ofCard F hFcard) (Sylow.ofCard E hEcard)
  have hconj : ∀ x ∈ F, MulAut.conj g x ∈ E := by
    intro x hx
    have h1 : MulAut.conj g • ((Sylow.ofCard F hFcard : Sylow 5 Y) : Set Y) =
        ((Sylow.ofCard E hEcard : Sylow 5 Y) : Set Y) := by
      rw [← Sylow.coe_smul, hg]
    have hmem : MulAut.conj g x ∈
        MulAut.conj g • ((Sylow.ofCard F hFcard : Sylow 5 Y) : Set Y) :=
      Set.mem_smul_set.mpr ⟨x, hx, rfl⟩
    rw [h1] at hmem
    exact hmem
  intro x hx y hy
  apply (MulAut.conj g).injective
  rw [map_mul, map_mul]
  exact hcomm _ (hconj x hx) _ (hconj y hy)

theorem nf5_rank_three (h : NF5 F Γ B R₀ x)
    (hZ : ∀ L : Subgroup Y, IsComponentOf L ⊤ → Subgroup.center ↥L = ⊥)
    {K₁ K₂ K₃ : Subgroup Y} (h₁ : IsComponentOf K₁ ⊤) (h₂ : IsComponentOf K₂ ⊤)
    (h₃ : IsComponentOf K₃ ⊤) (h12 : K₁ ≠ K₂) (h13 : K₁ ≠ K₃) (h23 : K₂ ≠ K₃) : False := by
  have c₁ : CFSG.IsComponent K₁ := (CFSG.isComponent_iff_open K₁).mpr h₁
  have c₂ : CFSG.IsComponent K₂ := (CFSG.isComponent_iff_open K₂).mpr h₂
  have c₃ : CFSG.IsComponent K₃ := (CFSG.isComponent_iff_open K₃).mpr h₃
  have z₁ : Subgroup.center ↥K₁ = ⊥ := hZ K₁ h₁
  have z₂ : Subgroup.center ↥K₂ = ⊥ := hZ K₂ h₂
  obtain ⟨s₁, hs₁, o₁⟩ := r3_exists_order_five (nf5_five_dvd h h₁)
  obtain ⟨s₂, hs₂, o₂⟩ := r3_exists_order_five (nf5_five_dvd h h₂)
  obtain ⟨s₃, hs₃, o₃⟩ := r3_exists_order_five (nf5_five_dvd h h₃)
  have hA₁ : Subgroup.zpowers s₁ ≤ K₁ := Subgroup.zpowers_le.mpr hs₁
  have hA₂ : Subgroup.zpowers s₂ ≤ K₂ := Subgroup.zpowers_le.mpr hs₂
  have hA₃ : Subgroup.zpowers s₃ ≤ K₃ := Subgroup.zpowers_le.mpr hs₃
  have c12 : ∀ x ∈ Subgroup.zpowers s₁, ∀ y ∈ Subgroup.zpowers s₂, x * y = y * x :=
    fun x hx y hy => r3_comm_of_ne c₁ c₂ h12 (hA₁ hx) (hA₂ hy)
  have c13 : ∀ x ∈ Subgroup.zpowers s₁, ∀ y ∈ Subgroup.zpowers s₃, x * y = y * x :=
    fun x hx y hy => r3_comm_of_ne c₁ c₃ h13 (hA₁ hx) (hA₃ hy)
  have c23 : ∀ x ∈ Subgroup.zpowers s₂, ∀ y ∈ Subgroup.zpowers s₃, x * y = y * x :=
    fun x hx y hy => r3_comm_of_ne c₂ c₃ h23 (hA₂ hx) (hA₃ hy)
  have d12 : Subgroup.zpowers s₁ ⊓ Subgroup.zpowers s₂ = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    exact Subgroup.mem_bot.mpr (r3_eq_one_of_mem_of_ne c₁ c₂ h12 z₁ (hA₁ hx1) (hA₂ hx2))
  have hS : Nat.card ↥(Subgroup.zpowers s₁ ⊔ Subgroup.zpowers s₂) = 25 := by
    rw [r3_card_sup c12 d12, Nat.card_zpowers, Nat.card_zpowers, o₁, o₂]
  have d3 : (Subgroup.zpowers s₁ ⊔ Subgroup.zpowers s₂) ⊓ Subgroup.zpowers s₃ = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx, hx3⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := r3_mem_sup_comm c12 hx
    exact Subgroup.mem_bot.mpr
      (r3_mul_eq_one c₁ c₂ c₃ h12 h13 h23 z₁ z₂ (hA₁ ha) (hA₂ hb) (hA₃ hx3))
  have c3S : ∀ x ∈ Subgroup.zpowers s₁ ⊔ Subgroup.zpowers s₂,
      ∀ y ∈ Subgroup.zpowers s₃, x * y = y * x :=
    r3_cross_sup c13 c23
  have hE : Nat.card ↥((Subgroup.zpowers s₁ ⊔ Subgroup.zpowers s₂) ⊔ Subgroup.zpowers s₃) = 125 := by
    rw [r3_card_sup c3S d3, hS, Nat.card_zpowers, o₃]
  have hSc : ∀ x ∈ Subgroup.zpowers s₁ ⊔ Subgroup.zpowers s₂,
      ∀ y ∈ Subgroup.zpowers s₁ ⊔ Subgroup.zpowers s₂, x * y = y * x :=
    r3_comm_sup (H := Subgroup.zpowers s₁) (K := Subgroup.zpowers s₂)
      (fun x hx y hy => r3_zpowers_comm hx hy) (fun x hx y hy => r3_zpowers_comm hx hy) c12
  have hEc : ∀ x ∈ (Subgroup.zpowers s₁ ⊔ Subgroup.zpowers s₂) ⊔ Subgroup.zpowers s₃,
      ∀ y ∈ (Subgroup.zpowers s₁ ⊔ Subgroup.zpowers s₂) ⊔ Subgroup.zpowers s₃,
        x * y = y * x :=
    r3_comm_sup (H := Subgroup.zpowers s₁ ⊔ Subgroup.zpowers s₂) (K := Subgroup.zpowers s₃)
      hSc (fun x hx y hy => r3_zpowers_comm hx hy) c3S
  exact h.nonab ⟨⟨fun a b => Subtype.ext (r3_sylow_comm h.sylow h.card hE hEc a a.2 b b.2)⟩⟩

end Part

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
