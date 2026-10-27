module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPermOdd
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoInvolutionPerm
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPTwoThreeLift
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPTwoThreePerm
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoTypes

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

open Equiv Subgroup

namespace JankoPTwoThree

open Janko JankoInvolution

theorem card_alternatingGroup_nine : Nat.card (alternatingGroup (Fin 9)) = 181440 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card (α := Fin 9), Fintype.card_fin]
  decide

theorem exists_ne_comm_of_card_eq {B : Subgroup (alternatingGroup (Fin 9))}
    (hB : Nat.card B = 81) : ∃ a ∈ B, ∃ b ∈ B, a * b ≠ b * a := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hcomm
  simp only [not_exists, not_and, not_not] at hcomm
  have hsyl : ∀ X : Subgroup (alternatingGroup (Fin 9)), Nat.card X = 81 →
      ∃ S : Sylow 3 (alternatingGroup (Fin 9)), (S : Subgroup _) = X := by
    intro X hX
    obtain ⟨S, hS⟩ := IsPGroup.exists_le_sylow (p := 3) (P := X)
      (IsPGroup.of_card (n := 4) (by rw [hX]; norm_num))
    refine ⟨S, (eq_of_le_of_card_ge hS ?_).symm⟩
    rw [hX, JankoPerm.card_sylow_eq S (k := 4) (m := 2240)
      (by rw [card_alternatingGroup_nine]; norm_num) (by rw [card_alternatingGroup_nine]; norm_num)
      (by norm_num)]
    norm_num
  obtain ⟨S₁, hS₁⟩ := hsyl B hB
  obtain ⟨S₂, hS₂⟩ := hsyl Pbar card_Pbar
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 9)) S₁ S₂
  have hmem : ∀ x ∈ Pbar, ∃ y ∈ B, g * y * g⁻¹ = x := by
    intro x hx
    rw [← hS₂, ← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨y, hS₁ ▸ hy, by rw [MulAut.smul_def, MulAut.conj_apply]⟩
  obtain ⟨a, ha, hga⟩ := hmem sbar₁ sbar₁_mem_Pbar
  obtain ⟨b, hb, hgb⟩ := hmem ρbar ρbar_mem_Pbar
  refine ρbar_mul_sbar₁_ne ?_
  rw [← hga, ← hgb]
  calc g * b * g⁻¹ * (g * a * g⁻¹) = g * (b * a) * g⁻¹ := by group
    _ = g * (a * b) * g⁻¹ := by rw [hcomm b hb a ha]
    _ = g * a * g⁻¹ * (g * b * g⁻¹) := by group

variable {J : Type*} [Group J] (hJ : IsTwoANine J)
include hJ

private theorem exists_conj_proj_eq_sbar₃ (e : J ⧸ center J ≃* alternatingGroup (Fin 9)) {x : J}
    (hx3 : x ^ 3 = 1)
    (hxc : Nat.card (centralizer ({x} : Set J)) = 162) :
    x ≠ 1 ∧ ∃ c, c * proj e x * c⁻¹ = sbar₃ := by
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [show centralizer ({1} : Set J) = ⊤ from
      eq_top_iff.mpr fun g _ => mem_centralizer_singleton_iff.mpr (by rw [mul_one, one_mul]),
      card_top, hJ.card_eq] at hxc
    norm_num at hxc
  obtain ⟨hox, hx3', hx1'⟩ := hJ.orderOf_eq_three_of_pow_three e hx3 hx1
  have hc81 : Nat.card (centralizer ({proj e x} : Set (alternatingGroup (Fin 9)))) = 81 := by
    have := hJ.card_centralizer_of_odd e (x := x) (by rw [hox]; exact ⟨1, rfl⟩)
    omega
  refine ⟨hx1, ?_⟩
  rcases isConj_sbar_of_pow_three_eq_one hx3' hx1' with h | h | h <;>
    obtain ⟨c, hc⟩ := isConj_iff.mp h
  · rw [← hc, card_centralizer_conj_eq, card_centralizer_sbar₁] at hc81
    norm_num at hc81
  · rw [← hc, card_centralizer_conj_eq, card_centralizer_sbar₂] at hc81
    norm_num at hc81
  · exact ⟨c⁻¹, by rw [← hc]; group⟩

theorem card_centralizer_inf_eq_six {x b : J} (hx3 : x ^ 3 = 1)
    (hxc : Nat.card (centralizer ({x} : Set J)) = 162) (hb : orderOf b = 2)
    (hbx : b * x * b⁻¹ = x⁻¹) :
    Nat.card (centralizer ({x} : Set J) ⊓ centralizer ({b} : Set J) : Subgroup J) = 6 := by
  obtain ⟨e⟩ := hJ.nonempty_mulEquiv
  obtain ⟨hx1, c, hc⟩ := exists_conj_proj_eq_sbar₃ hJ e hx3 hxc
  have hxo : Odd (orderOf x) := by
    rw [(hJ.orderOf_eq_three_of_pow_three e hx3 hx1).1]
    exact ⟨1, rfl⟩
  have hb2 : (c * proj e b * c⁻¹) ^ 2 = 1 := by
    rw [conj_pow, ← map_pow, ← hb, pow_orderOf_eq_one, map_one, mul_one, mul_inv_cancel]
  have hbs : c * proj e b * c⁻¹ * sbar₃ * (c * proj e b * c⁻¹)⁻¹ = sbar₃⁻¹ := by
    rw [← hc]
    have h := congrArg (proj e) hbx
    rw [map_mul, map_mul, map_inv, map_inv] at h
    calc c * proj e b * c⁻¹ * (c * proj e x * c⁻¹) * (c * proj e b * c⁻¹)⁻¹
        = c * (proj e b * proj e x * (proj e b)⁻¹) * c⁻¹ := by group
      _ = (c * proj e x * c⁻¹)⁻¹ := by rw [h]; group
  have h3 : Nat.card (centralizer {proj e x} ⊓ centralizer {proj e b} :
      Subgroup (alternatingGroup (Fin 9))) = 3 := by
    rw [← card_centralizer_inf_conj_eq c, hc]
    exact card_centralizer_sbar₃_inf hb2 hbs
  have hY : Odd (Nat.card (centralizer {proj e x} ⊓ centralizer {proj e b} :
      Subgroup (alternatingGroup (Fin 9)))) := by
    rw [h3]
    exact ⟨1, rfl⟩
  have heq : centralizer ({x} : Set J) ⊓ centralizer {b} =
      (centralizer {proj e x} ⊓ centralizer {proj e b}).comap (proj e) := by
    refine le_antisymm (fun g hg => ?_) (le_inf ?_ ?_)
    · rw [mem_comap, mem_inf, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff,
        ← map_mul, ← map_mul, ← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp hg.1,
        mem_centralizer_singleton_iff.mp hg.2]
      exact ⟨rfl, rfl⟩
    · rw [hJ.centralizer_eq_comap_of_odd e hxo]
      exact comap_mono inf_le_left
    · exact comap_le_centralizer hJ e hY inf_le_right
  rw [heq, hJ.card_comap_proj e, h3]

end JankoPTwoThree

namespace Janko

open JankoPTwoThree JankoInvolution

variable {G : Type*} [Group G] {z : G} (hH : IsTwoANine (centralizer ({z} : Set G)))
include hH

theorem exists_orderOf_nine : ∃ x ∈ centralizer ({z} : Set G), orderOf x = 9 := by
  obtain ⟨e⟩ := hH.nonempty_mulEquiv
  have ho : Odd (orderOf (ρbar * sbar₁)) := by
    rw [orderOf_ρbar_mul_sbar₁]
    exact ⟨4, rfl⟩
  refine ⟨(liftOdd e (ρbar * sbar₁) : centralizer ({z} : Set G)), (liftOdd e _).2, ?_⟩
  rw [Subgroup.orderOf_coe, hH.orderOf_liftOdd e ho, orderOf_ρbar_mul_sbar₁]

omit hH in
private theorem card_subgroupOf {B : Subgroup G} (hB : B ≤ centralizer ({z} : Set G)) :
    Nat.card (B.subgroupOf (centralizer ({z} : Set G))) = Nat.card B :=
  Nat.card_congr (subgroupOfEquivOfLe hB).toEquiv

theorem exists_ne_comm : ∀ B : Subgroup G, B ≤ centralizer ({z} : Set G) → Nat.card B = 81 →
    ∃ a ∈ B, ∃ b ∈ B, a * b ≠ b * a := by
  intro B hB h81
  obtain ⟨e⟩ := hH.nonempty_mulEquiv
  have hB' := card_subgroupOf hB
  rw [h81] at hB'
  have hodd : Odd (Nat.card (B.subgroupOf (centralizer ({z} : Set G)))) := by
    rw [hB']
    exact ⟨40, rfl⟩
  obtain ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, hab⟩ := exists_ne_comm_of_card_eq
    (B := (B.subgroupOf (centralizer ({z} : Set G))).map (proj e))
    (by rw [hH.card_map_proj_of_odd e hodd, hB'])
  refine ⟨a, mem_subgroupOf.mp ha, b, mem_subgroupOf.mp hb, fun h => hab ?_⟩
  rw [← map_mul, ← map_mul, show a * b = b * a from Subtype.ext h]

theorem card_eq_of_odd : ∀ B : Subgroup G, B ≤ centralizer ({z} : Set G) → Odd (Nat.card B) →
    81 ∣ Nat.card B → Nat.card B = 81 := by
  intro B hB hodd h81
  obtain ⟨e⟩ := hH.nonempty_mulEquiv
  rw [← card_subgroupOf hB] at hodd h81 ⊢
  have hc := hH.card_map_proj_of_odd e hodd
  rw [← hc] at hodd h81 ⊢
  exact JankoPerm.card_eq_eightyOne_of_odd_alt hodd h81

theorem card_centralizer_inv : ∀ x ∈ centralizer ({z} : Set G), x ^ 3 = 1 →
    Nat.card (centralizer ({x} : Set G) ⊓ centralizer ({z} : Set G) : Subgroup G) = 162 →
    ∀ b ∈ centralizer ({z} : Set G), orderOf b = 2 → b * x * b⁻¹ = x⁻¹ →
      Nat.card (centralizer ({x} : Set G) ⊓ centralizer ({b} : Set G) ⊓
        centralizer ({z} : Set G) : Subgroup G) = 6 := by
  intro x hx hx3 hxc b hb hb2 hbx
  obtain ⟨e⟩ := hH.nonempty_mulEquiv
  rw [show x = ((⟨x, hx⟩ : centralizer ({z} : Set G)) : G) from rfl,
    card_centralizer_inf_eq] at hxc
  rw [show x = ((⟨x, hx⟩ : centralizer ({z} : Set G)) : G) from rfl,
    show b = ((⟨b, hb⟩ : centralizer ({z} : Set G)) : G) from rfl, inf_inf_distrib_right,
    centralizer_inf_eq_map_subtype, centralizer_inf_eq_map_subtype,
    ← map_inf _ _ _ (centralizer ({z} : Set G)).subtype_injective,
    card_map_of_injective (centralizer ({z} : Set G)).subtype_injective]
  exact card_centralizer_inf_eq_six hH (Subtype.ext hx3) hxc
    (by rwa [Subgroup.orderOf_mk]) (Subtype.ext hbx)

end Janko

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine
