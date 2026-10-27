module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergCCSeriesCoset

public section

namespace CFSG.LocalAnalysis.EvenBN.Common

open Subgroup CFSG.LocalAnalysis.ComponentInitial

theorem fixed_eq_range_of_card_eq_sq {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (α : MulAut E) (hα : ∀ x, α (α x) = x) (hcard : Nat.card E = Nat.card {x | α x = x} ^ 2) :
    {x | α x = x} = Set.range fun x => x⁻¹ * α x := by
  let β : E →* E := MonoidHom.mk' (fun x => x⁻¹ * α x) (inv_mul_apply_mul α)
  have hsub : (Set.range fun x => x⁻¹ * α x) ⊆ {x | α x = x} := by
    rintro _ ⟨x, rfl⟩
    change α (x⁻¹ * α x) = x⁻¹ * α x
    rw [map_mul, map_inv, hα]
    have h1 : (α x)⁻¹ = α x := inv_eq_of_mul_eq_one_right
      (mul_self_eq_one_of_isElementaryAbelian_two (α x))
    have h2 : x⁻¹ = x := inv_eq_of_mul_eq_one_right (mul_self_eq_one_of_isElementaryAbelian_two x)
    rw [h1, h2, mul_comm' (α x) x]
  have hker : (β.ker : Set E) = {x | α x = x} := by
    ext x
    change x⁻¹ * α x = 1 ↔ α x = x
    rw [inv_mul_eq_one, eq_comm]
  have hcard' : Nat.card E = Nat.card {x | α x = x} * Nat.card (Set.range fun x => x⁻¹ * α x) := by
    calc Nat.card E = Nat.card β.ker * β.ker.index := (card_mul_index _).symm
      _ = Nat.card β.ker * Nat.card β.range := by rw [index_ker]
      _ = _ := by
          congr 1
          rw [← hker]
          rfl
  have hpos : 0 < Nat.card {x | α x = x} :=
    Nat.card_pos_iff.mpr ⟨⟨⟨1, map_one α⟩⟩, Set.toFinite _⟩
  have heq : Nat.card (Set.range fun x => x⁻¹ * α x) = Nat.card {x | α x = x} := by
    rw [hcard, sq] at hcard'
    exact (Nat.eq_of_mul_eq_mul_left hpos hcard').symm
  refine (Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)).symm
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, heq]

theorem sectionRightConj_sectionRightConj {G : Type*} [Group G] {K L : Subgroup G}
    [(L.subgroupOf K).Normal] {g : G} (hK : g ∈ normalizer (K : Set G))
    (hL : g ∈ normalizer (L : Set G)) (hg : g * g = 1) (q : K ⧸ L.subgroupOf K) :
    sectionRightConj hK hL (sectionRightConj hK hL q) = q := by
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
  let k' : K := ⟨g⁻¹ * k * g, inv_mul_mul_mem_of_mem_normalizer hK k.2⟩
  rw [sectionRightConj_mk hK hL k k' rfl, sectionRightConj_mk hK hL k' k ?_]
  have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg
  change (k : G) = g⁻¹ * (g⁻¹ * k * g) * g
  rw [hginv]
  calc (k : G) = (g * g) * k * (g * g) := by rw [hg, one_mul, mul_one]
    _ = g * (g * k * g) * g := by group

theorem section_fixed_eq_range_of_card_sq {G : Type*} [Group G] [Finite G] {a : G}
    (ha : orderOf a = 2) {r : ℕ} (V : Fin (r + 1) → Subgroup G) (hV0 : V 0 = ⊥)
    (hVle : ∀ i : Fin r, V i.castSucc ≤ V i.succ) (haV : ∀ i, a ∈ normalizer (V i : Set G))
    [∀ i : Fin r, ((V i.castSucc).subgroupOf (V i.succ)).Normal]
    [∀ i : Fin r, IsElementaryAbelian 2 (V i.succ ⧸ (V i.castSucc).subgroupOf (V i.succ))]
    (hcard : ∀ i : Fin r,
      Nat.card (V i.succ ⊓ centralizer {a} : Subgroup G) ^ 2 = Nat.card (V i.succ)) :
    (∀ i : Fin r, {x | sectionRightConj (haV i.succ) (haV i.castSucc) x = x} =
      Set.range fun x => x⁻¹ * sectionRightConj (haV i.succ) (haV i.castSucc) x) ∧
    ∀ i : Fin (r + 1), ∀ k ∈ V i, a * k * (a * k) = 1 → ∃ m ∈ V i, a * k = m⁻¹ * a * m := by
  have ha2 : a * a = 1 := by rw [← pow_two, ← ha, pow_orderOf_eq_one]
  have hcard' : ∀ i : Fin (r + 1),
      Nat.card (V i ⊓ centralizer {a} : Subgroup G) ^ 2 = Nat.card (V i) := by
    intro i
    induction i using Fin.cases with
    | zero => rw [hV0, bot_inf_eq, card_bot, one_pow]
    | succ i => exact hcard i
  have hfac : ∀ i : Fin r,
      (∀ k ∈ V i.castSucc, a * k * (a * k) = 1 → ∃ m ∈ V i.castSucc, a * k = m⁻¹ * a * m) →
      {x | sectionRightConj (haV i.succ) (haV i.castSucc) x = x} =
        Set.range fun x => x⁻¹ * sectionRightConj (haV i.succ) (haV i.castSucc) x := by
    intro i hconj
    have h1 := card_inf_centralizer_eq_mul_card_fixed (hVle i) (haV i.succ) (haV i.castSucc) ha2
      hconj
    have h2 := card_eq_card_quotient_mul_card_subgroup ((V i.castSucc).subgroupOf (V i.succ))
    rw [Nat.card_congr (subgroupOfEquivOfLe (hVle i)).toEquiv] at h2
    have h3 := hcard i
    have h4 := hcard' i.castSucc
    set c := Nat.card (V i.castSucc ⊓ centralizer {a} : Subgroup G)
    set f := Nat.card {x | sectionRightConj (haV i.succ) (haV i.castSucc) x = x}
    set q := Nat.card (V i.succ ⧸ (V i.castSucc).subgroupOf (V i.succ))
    have hpos : 0 < c ^ 2 := pow_pos Nat.card_pos 2
    have e : c ^ 2 * f ^ 2 = c ^ 2 * q := by
      rw [← mul_pow, ← h1, h3, h2, ← h4, mul_comm]
    exact fixed_eq_range_of_card_eq_sq _
      (sectionRightConj_sectionRightConj (haV i.succ) (haV i.castSucc) ha2)
      (Nat.eq_of_mul_eq_mul_left hpos e).symm
  have key : ∀ i : Fin (r + 1), ∀ k ∈ V i, a * k * (a * k) = 1 →
      ∃ m ∈ V i, a * k = m⁻¹ * a * m := by
    intro i
    induction i using Fin.induction with
    | zero =>
      rw [hV0]
      intro k hk _
      rw [mem_bot.mp hk]
      exact ⟨1, one_mem _, by group⟩
    | succ i ih =>
      exact fun k hk hsq =>
        coset_conj_of_section (hVle i) (haV i.succ) (haV i.castSucc) ha2 (hfac i ih) ih hk hsq
  exact ⟨fun i => hfac i (key i.castSucc), key⟩

theorem involution_coset_eq_conj_orbit_of_card_sq {G : Type*} [Group G] [Finite G]
    {W : Subgroup G} {a : G} (ha : orderOf a = 2) {r : ℕ} (V : Fin (r + 1) → Subgroup G)
    (hV0 : V 0 = ⊥) (hVr : V (Fin.last r) = W) (hVle : ∀ i : Fin r, V i.castSucc ≤ V i.succ)
    (haV : ∀ i, a ∈ normalizer (V i : Set G))
    [∀ i : Fin r, ((V i.castSucc).subgroupOf (V i.succ)).Normal]
    [∀ i : Fin r, IsElementaryAbelian 2 (V i.succ ⧸ (V i.castSucc).subgroupOf (V i.succ))]
    (hcard : ∀ i : Fin r,
      Nat.card (V i.succ ⊓ centralizer {a} : Subgroup G) ^ 2 = Nat.card (V i.succ)) :
    {x | (∃ w ∈ W, x = a * w) ∧ orderOf x = 2} = {x | ∃ w ∈ W, x = w⁻¹ * a * w} := by
  have hconj := (section_fixed_eq_range_of_card_sq ha V hV0 hVle haV hcard).2 (Fin.last r)
  have haW : a ∈ normalizer (W : Set G) := hVr ▸ haV (Fin.last r)
  rw [hVr] at hconj
  ext x
  constructor
  · rintro ⟨⟨w, hw, rfl⟩, hx⟩
    have hx2 : a * w * (a * w) = 1 := by rw [← pow_two, ← hx, pow_orderOf_eq_one]
    exact hconj w hw hx2
  · rintro ⟨w, hw, rfl⟩
    refine ⟨⟨a⁻¹ * w⁻¹ * a * w,
      W.mul_mem (inv_mul_mul_mem_of_mem_normalizer haW (W.inv_mem hw)) hw, by group⟩, ?_⟩
    have h := MulEquiv.orderOf_eq (MulAut.conj w⁻¹) a
    rw [MulAut.conj_apply, inv_inv] at h
    rw [h, ha]

theorem involution_coset_conj_of_card_sq {G : Type*} [Group G] [Finite G] {W : Subgroup G}
    {a : G} (ha : orderOf a = 2) {r : ℕ} (V : Fin (r + 1) → Subgroup G) (hV0 : V 0 = ⊥)
    (hVr : V (Fin.last r) = W) (hVle : ∀ i : Fin r, V i.castSucc ≤ V i.succ)
    (haV : ∀ i, a ∈ normalizer (V i : Set G))
    [∀ i : Fin r, ((V i.castSucc).subgroupOf (V i.succ)).Normal]
    [∀ i : Fin r, IsElementaryAbelian 2 (V i.succ ⧸ (V i.castSucc).subgroupOf (V i.succ))]
    (hcard : ∀ i : Fin r,
      Nat.card (V i.succ ⊓ centralizer {a} : Subgroup G) ^ 2 = Nat.card (V i.succ))
    {w : G} (hw : w ∈ W) (hx : orderOf (a * w) = 2) : ∃ m ∈ W, a * w = m⁻¹ * a * m := by
  have hconj := (section_fixed_eq_range_of_card_sq ha V hV0 hVle haV hcard).2 (Fin.last r)
  rw [hVr] at hconj
  exact hconj w hw (by rw [← pow_two, ← hx, pow_orderOf_eq_one])

theorem elementary_series_involution_coset_conjugacy_of_card_sq {G : Type*} [Group G] [Finite G]
    {W : Subgroup G} (hW : IsPGroup 2 W) {a : G} (ha : orderOf a = 2)
    (haW : a ∈ normalizer (W : Set G)) (haW' : a ∉ W) {r : ℕ} (hr : 1 ≤ r)
    (V : Fin (r + 1) → Subgroup G) (hV0 : V 0 = ⊥) (hVr : V (Fin.last r) = W)
    (hVle : ∀ i : Fin r, V i.castSucc ≤ V i.succ) (hVW : ∀ i, ((V i).subgroupOf W).Normal)
    (haV : ∀ i, a ∈ normalizer (V i : Set G))
    [∀ i : Fin r, ((V i.castSucc).subgroupOf (V i.succ)).Normal]
    [∀ i : Fin r, IsElementaryAbelian 2 (V i.succ ⧸ (V i.castSucc).subgroupOf (V i.succ))]
    (hcard : ∀ i : Fin r,
      Nat.card (V i.succ ⊓ centralizer {a} : Subgroup G) ^ 2 = Nat.card (V i.succ)) :
    {x | (∃ w ∈ W, x = a * w) ∧ orderOf x = 2} = {x | ∃ w ∈ W, x = w⁻¹ * a * w} ∧
      Nat.card (W ⊓ centralizer {a} : Subgroup G) =
        ∏ i : Fin r, Nat.card {x | sectionRightConj (haV i.succ) (haV i.castSucc) x = x} ∧
      Nat.card (W ⊓ centralizer {a} : Subgroup G) ^ 2 = Nat.card W ∧
      Nat.card {x | (∃ w ∈ W, x = a * w) ∧ orderOf x = 2} =
        Nat.card (W ⊓ centralizer {a} : Subgroup G) :=
  elementary_series_involution_coset_conjugacy hW ha haW haW' hr V hV0 hVr hVle hVW haV
    (section_fixed_eq_range_of_card_sq ha V hV0 hVle haV hcard).1

end CFSG.LocalAnalysis.EvenBN.Common
