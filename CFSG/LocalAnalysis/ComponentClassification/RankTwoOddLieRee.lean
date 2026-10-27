module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieGamma
public import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalSmallReeWardKleidman
public import CFSG.LieType.Simplicity.ReeSmall

public section

namespace CFSG.ComponentClassification.RankTwoOddLie

open Subgroup CFSG.Open CFSG.ComponentClassification.AS76b CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped commutatorElement

variable {H : Type} [Group H] {B T X : Subgroup H}

theorem mem_inner_of_sq_eq_one {G : Type*} [Group G] [Finite (Outer G)]
    (hodd : Odd (Nat.card (Outer G))) {α : MulAut G} (hα : α ^ 2 = 1) : α ∈ inner G := by
  have h1 : (QuotientGroup.mk α : Outer G) ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow, hα, QuotientGroup.mk_one]
  have h2 : orderOf (QuotientGroup.mk α : Outer G) ∣ 2 := orderOf_dvd_of_pow_eq_one h1
  have h3 : orderOf (QuotientGroup.mk α : Outer G) ∣ Nat.card (Outer G) := orderOf_dvd_natCard _
  have h4 : orderOf (QuotientGroup.mk α : Outer G) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
    · exact h
    · rw [h] at h3
      exact absurd (even_iff_two_dvd.mpr h3) (Nat.not_even_iff_odd.mpr hodd)
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h4
  exact h4

theorem Hyp46.false_of_smallRee [Finite H] (h : Hyp46 B T X) (hB : Open.IsQuasisimple B)
    {f : ℕ} (hR : ReeTitsModel B .twistedG2 3 f) : False := by
  obtain ⟨hadm, a, hfa, -⟩ := id hR
  obtain ⟨-, -, -, -, -, h3⟩ := hadm
  have ha : 1 ≤ a := by omega
  subst hfa
  obtain ⟨-, ⟨⟨x₀, hx₀⟩, -⟩, hcent, hmax, -, -, hodd⟩ :=
    LiteratureLocal.ward_kleidman_small_Ree_involution_centralizer_maximal a ha B hR
  have : Finite (Outer B) := inferInstance
  let φ : T →* MulAut B := B.normalizerMonoidHom.comp (Subgroup.inclusion h.le_normalizer)
  have hφ : ∀ (t : T) (y : B), ((φ t y : B) : H) = (t : H) * y * (t : H)⁻¹ := fun t y => by
    simp [φ, Subgroup.normalizerMonoidHom_apply_apply_coe]
  have hT2 : ∀ t : T, t ^ 2 = 1 := fun t => Subtype.ext (by simpa using h.elem.2 t t.2)
  have hinner : ∀ t : T, ∃ b : B, φ t = MulAut.conj b := by
    intro t
    have hsq : (φ t) ^ 2 = 1 := by rw [← map_pow, hT2 t, map_one]
    obtain ⟨b, hb⟩ := mem_inner_of_sq_eq_one hodd hsq
    exact ⟨b, hb.symm⟩
  choose b hb using hinner
  have hsimple := (CFSG.LieType.Simplicity.fam_2g2_simplicity B 3 (2 * a + 1) hR).2
  have hZ : center B = ⊥ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal (center B) with h1 | h1
    · exact h1
    · exfalso
      obtain ⟨y, hy⟩ := _root_.exists_ne (1 : B)
      have hcomm : commutator B = ⊥ := by
        rw [commutator_def, eq_bot_iff, Subgroup.commutator_le]
        intro g₁ _ g₂ _
        have : g₁ ∈ center B := h1 ▸ Subgroup.mem_top g₁
        rw [Subgroup.mem_center_iff] at this
        rw [commutatorElement_def, ← this g₂, mul_inv_cancel_right, mul_inv_cancel,
          Subgroup.mem_bot]
      have : y ∈ commutator B := hB.1 ▸ Subgroup.mem_top y
      rw [hcomm, Subgroup.mem_bot] at this
      exact hy this
  have hφ1 : ∀ t : T, φ t = 1 → t = 1 := by
    intro t ht
    have htC : (t : H) ∈ centralizer (B : Set H) := by
      rw [mem_centralizer_iff]
      intro y hy
      have := hφ t ⟨y, hy⟩
      rw [ht, MulAut.one_apply] at this
      calc y * t = (t : H) * y * (t : H)⁻¹ * t := by rw [← this]
        _ = t * y := by group
    have : (t : H) ∈ T ⊓ centralizer (B : Set H) := Subgroup.mem_inf.mpr ⟨t.2, htC⟩
    rw [h.faithful, Subgroup.mem_bot] at this
    exact Subtype.ext this
  have hb2 : ∀ t : T, t ≠ 1 → orderOf (b t) = 2 := by
    intro t ht
    have hsq : MulAut.conj (b t ^ 2) = 1 := by rw [map_pow, ← hb, ← map_pow, hT2 t, map_one]
    have hcen : b t ^ 2 ∈ center B := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := congrArg (fun α : MulAut B => α g) hsq
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc g * b t ^ 2 = b t ^ 2 * g * (b t ^ 2)⁻¹ * b t ^ 2 := by rw [this]
        _ = b t ^ 2 * g := by group
    rw [hZ, Subgroup.mem_bot] at hcen
    refine orderOf_eq_prime hcen fun h1 => ht (hφ1 t ?_)
    rw [hb, h1, map_one]
  obtain ⟨⟨t₁, ht₁⟩, ht₁1⟩ : ∃ t : T, t ≠ 1 := by
    have : Nontrivial T := Finite.one_lt_card_iff_nontrivial.mp (by linarith [h.four_le])
    exact _root_.exists_ne 1
  have ht₁1' : t₁ ≠ 1 := fun h1 => ht₁1 (Subtype.ext h1)
  obtain ⟨t₂, ht₂, ht₂1', ht₂₁⟩ := h.exists_ne ht₁
  have ht₂1 : (⟨t₂, ht₂⟩ : T) ≠ 1 := fun h1 => ht₂1' (congrArg Subtype.val h1)
  set b₁ := b ⟨t₁, ht₁⟩
  set b₂ := b ⟨t₂, ht₂⟩
  have hb₁ : orderOf b₁ = 2 := hb2 _ ht₁1
  have hb₂ : orderOf b₂ = 2 := hb2 _ ht₂1
  have hne : b₁ ≠ b₂ := by
    intro heq
    apply ht₂₁
    have h1 : φ (⟨t₂, ht₂⟩ * (⟨t₁, ht₁⟩ : T)⁻¹) = 1 := by
      rw [map_mul, map_inv, hb, hb, show b ⟨t₂, ht₂⟩ = b₂ from rfl,
        show b ⟨t₁, ht₁⟩ = b₁ from rfl, heq, mul_inv_cancel]
    have := congrArg Subtype.val (hφ1 _ h1)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, OneMemClass.coe_one] at this
    exact mul_inv_eq_one.mp this
  have hCne : centralizer ({b₁} : Set B) ≠ centralizer ({b₂} : Set B) := by
    intro heq
    obtain ⟨L₁, -, -, -, -, hz₁⟩ := hcent b₁ hb₁
    obtain ⟨L₂, -, -, -, -, hz₂⟩ := hcent b₂ hb₂
    rw [heq] at hz₁
    have hb₂mem : b₂ ∈ zpowers b₁ := by rw [← hz₁, hz₂]; exact mem_zpowers b₂
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hb₂mem
    rw [← zpow_mod_orderOf, hb₁] at hk
    have hk2 : k % (2 : ℕ) = 0 ∨ k % (2 : ℕ) = 1 := by omega
    rcases hk2 with h0 | h1
    · have : b₂ = 1 := by rw [← hk, h0, zpow_zero]
      rw [this, orderOf_one] at hb₂
      omega
    · rw [h1, zpow_one] at hk
      exact hne hk
  have hsup := IsCoatom.sup_eq_top_of_ne (hmax b₁ hb₁) (hmax b₂ hb₂) hCne
  have hCX : ∀ (t : H) (ht : t ∈ T), t ≠ 1 →
      (centralizer ({b ⟨t, ht⟩} : Set B)).map B.subtype ≤ normalizer (X : Set H) := by
    rintro t ht ht1 _ ⟨y, hy, rfl⟩
    refine h.inf_centralizer_le_of_mem ht ht1 (Subgroup.mem_inf.mpr ⟨mem_sup_right y.2, ?_⟩)
    rw [mem_centralizer_singleton_iff]
    have h1 := hφ ⟨t, ht⟩ y
    rw [hb, MulAut.conj_apply, ← mem_centralizer_singleton_iff.mp hy, mul_inv_cancel_right] at h1
    calc (y : H) * t = t * y * t⁻¹ * t := by rw [← h1]
      _ = t * y := by group
  have hBX : B ≤ normalizer (X : Set H) := by
    have hB' : B = (centralizer ({b₁} : Set B)).map B.subtype ⊔
        (centralizer ({b₂} : Set B)).map B.subtype := by
      rw [← Subgroup.map_sup, hsup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [hB']
    exact sup_le (hCX t₁ ht₁ ht₁1') (hCX t₂ ht₂ ht₂1')
  have heven : Even (Nat.card B) := by
    rw [even_iff_two_dvd, ← hb₁]
    exact orderOf_dvd_natCard b₁
  exact h.false_of_le_normalizer hB heven hBX

end CFSG.ComponentClassification.RankTwoOddLie
