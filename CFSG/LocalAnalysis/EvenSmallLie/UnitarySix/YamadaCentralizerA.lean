module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaCentralizerAOrbit
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaCentralizerAPerm
public import CFSG.LieType.Simplicity.Classical

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie.UnitarySix.Yamada

open Subgroup CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open SolomonWong (mul_comm_of_sq_eq_one)

theorem card_outer_K_dvd {Q : Type} [Group Q] (D : ToddParabolic Q) :
    Nat.card (Outer D.K) ∣ 12 := by
  rcases D.lieModel_K with ⟨-, hK⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · have := (LocalAnalysis.ComponentInitial.linear_model_outer_two_part_bound D.K 3 2 2
      hK).2.2.2.2 le_rfl
    norm_num at this
    exact this
  all_goals exact absurd h0 (by norm_num)

namespace Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {D : ToddParabolic L} {t : G}

theorem exists_mem_centralizer_toddA_not_comm
    (h : Setting G L D t)
    (hΩ : omegaSet D t = {e | ∃ a ∈ toddA D, e = a * t}) :
    ∃ c ∈ normalizer (toddE D t : Set G), (∀ a ∈ toddA D, c * a = a * c) ∧ c * t ≠ t * c := by
  by_contra hcon
  push Not at hcon
  set X := normalizer (toddE D t : Set G)
  set Δ := conjClass (toddK D) (D.a₁ : G)
  set φ := conjPermHom (h.conj_mem_delta_of_omega hΩ) with hφ
  have hΔE : ∀ y ∈ Δ, y ∈ toddE D t := fun y hy =>
    toddA_le_toddE D t (conjClass_toddK_subset D D.a_mem.1 hy)
  have hker : ∀ x : X, φ x = 1 ↔ (x : G) ∈ toddE D t := by
    intro x
    constructor
    · intro hx
      have hfix : ∀ y ∈ Δ, y * x = x * y := fun y hy => by
        have := congrArg (fun σ : Equiv.Perm Δ => ((σ ⟨y, hy⟩ : Δ) : G)) hx
        simp only [hφ, conjPermHom_apply, Equiv.Perm.coe_one, id_eq] at this
        calc y * x = x * y * (x : G)⁻¹ * x := by rw [this]
          _ = x * y := by group
      have hA : ∀ a ∈ toddA D, (x : G) * a * (x : G)⁻¹ = a := by
        intro a ha
        rw [← h.closure_delta_eq] at ha
        have hle : closure Δ ≤ centralizer ({(x : G)} : Set G) := by
          rw [closure_le]
          exact fun y hy => mem_centralizer_singleton_iff.2 (hfix y hy)
        rw [← mem_centralizer_singleton_iff.1 (hle ha), mul_inv_cancel_right]
      have hxt : (x : G) * t = t * x := hcon x x.2 fun a ha => by
        calc (x : G) * a = x * a * (x : G)⁻¹ * x := by group
          _ = a * x := by rw [hA a ha]
      refine h.mem_toddE_of_comm hA ?_
      rw [hxt, mul_inv_cancel_right]
    · intro hx
      refine Equiv.ext fun y => Subtype.ext ?_
      rw [hφ, conjPermHom_apply, Equiv.Perm.coe_one, id_eq,
        mul_comm_of_sq_eq_one h.toddE_sq hx (hΔE y y.2), mul_inv_cancel_right]
  have hEX : toddE D t ≤ X := le_normalizer
  have hkerE : φ.ker = (toddE D t).subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    exact hker x
  have hcardXb : Nat.card φ.range * 2 ^ 10 = Nat.card X := by
    rw [← h.card_toddE, ← Nat.card_congr (subgroupOfEquivOfLe hEX).toEquiv, ← hkerE, mul_comm,
      ← index_ker, card_mul_index]
  set N := Nat.card (normalizer (toddA D : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G)
  have hNHA : 2 ^ 10 * 20160 ∣ N ∧ N ∣ 2 ^ 10 * 20160 * 6 := h.card_NHA
  have hXc : Nat.card X = 2 ^ 9 * N := h.card_X_of_omega hΩ
  have hN2 : N = 2 * Nat.card φ.range := by omega
  have hdvd : Nat.card φ.range ∣ 2 ^ 16 * 3 ^ 3 * 5 * 7 := by
    have h1 := hNHA.2
    rw [hN2, show 2 ^ 10 * 20160 * 6 = 2 * (2 ^ 16 * 3 ^ 3 * 5 * 7) by norm_num] at h1
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h1
  have hge : 20160 * 12 < Nat.card φ.range := by
    have h1 : 2 ^ 10 * 20160 ≤ N := Nat.le_of_dvd Nat.card_pos hNHA.1
    omega
  have h2 : MulAction.IsMultiplyPretransitive φ.range Δ 2 := by
    rw [MulAction.is_two_pretransitive_iff]
    intro a b c d hab hcd
    obtain ⟨k, hk, hka, hkb⟩ := h.two_trans_delta a.2 b.2 c.2 d.2
      (fun e => hab (Subtype.ext e)) (fun e => hcd (Subtype.ext e))
    exact ⟨φ.rangeRestrict ⟨k, h.toddK_le_X hk⟩, Subtype.ext hka, Subtype.ext hkb⟩
  have hXtop : X ≠ ⊤ := by
    intro htop
    have : (toddE D t).Normal := normalizer_eq_top_iff.1 htop
    have := h.std.simple
    rcases Subgroup.Normal.eq_bot_or_eq_top (toddE D t) with hb | ht
    · apply h.t_ne_one
      have := t_mem_toddE D t
      rwa [hb, mem_bot] at this
    · obtain ⟨a, b, hab⟩ := h.std.nonab
      have hmem : ∀ x : G, x ∈ toddE D t := fun x => by rw [ht]; exact mem_top x
      exact hab (mul_comm_of_sq_eq_one h.toddE_sq (hmem a) (hmem b))
  have hcat : ∀ T : Subgroup φ.range, IsSimpleGroup T → (∃ a b : T, a * b ≠ b * a) →
      CFSG.Blueprint.Catalog T := fun T hT hnonab => by
    have := hT
    exact CatalogOrders.catalog_of_kProper_of_le_quotient h.std.kProper hXtop φ.rangeRestrict
      φ.rangeRestrict_surjective T hnonab
  let ι₀ : D.K →* X :=
    (L.subtype.comp D.K.subtype).codRestrict X fun k => h.toddK_le_X ⟨k, k.2, rfl⟩
  have hι : Function.Injective (φ.rangeRestrict.comp ι₀) := by
    rw [injective_iff_map_eq_one]
    intro k hk
    have h1 : φ (ι₀ k) = 1 := congrArg Subtype.val hk
    rw [hker] at h1
    exact Subtype.ext (Subtype.ext
      (h.eq_one_of_mem_toddK_of_mem_toddE (k := ((k : L) : G)) ⟨k, k.2, rfl⟩ h1))
  have : IsSimpleGroup D.K := by
    rcases D.lieModel_K with ⟨-, hK⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 2 hK).2
    all_goals exact absurd h0 (by norm_num)
  exact false_of_two_pretransitive (by rw [Nat.card_coe_set_eq]; exact (ncard_delta D).1) h2
    hdvd hge hcat _ hι D.card_K (card_outer_K_dvd D)

end Setting

end CFSG.EvenSmallLie.UnitarySix.Yamada
