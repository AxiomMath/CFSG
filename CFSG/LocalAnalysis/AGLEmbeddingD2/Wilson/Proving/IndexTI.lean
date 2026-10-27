module

public import Mathlib.GroupTheory.GroupAction.CardCommute
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Proving

open MulAction

theorem card_modEq_one_of_free_except {H β : Type*} [Group H] [Finite H] [MulAction H β]
    [Finite β] (a : β)
    (hfix : ∀ b : β, (∀ h : H, h • b = b) ↔ b = a)
    (hfree : ∀ b : β, b ≠ a → ∀ h : H, h • b = b → h = 1) :
    Nat.card β ≡ 1 [MOD Nat.card H] := by
  classical
  haveI : Fintype H := Fintype.ofFinite H
  haveI : Fintype β := Fintype.ofFinite β
  have hstab : ∀ x : β,
      Nat.card (stabilizer H x) = if x = a then Nat.card H else 1 := by
    intro x
    split_ifs with hx
    · have htop : stabilizer H x = ⊤ := by
        rw [Subgroup.eq_top_iff']
        intro h
        exact (hfix x).mpr hx h
      rw [htop, Subgroup.card_top]
    · have hbot : stabilizer H x = ⊥ := by
        rw [Subgroup.eq_bot_iff_forall]
        intro h hh
        exact hfree x hx h hh
      rw [hbot, Subgroup.card_bot]
  have hiff : ∀ ω : Quotient (orbitRel H β), ω.out = a ↔ ω = ⟦a⟧ := by
    intro ω
    constructor
    · intro e
      rw [← e, Quotient.out_eq]
    · intro e
      rw [e]
      have hr : (⟦a⟧ : Quotient (orbitRel H β)).out ∈ orbit H a :=
        (orbitRel_apply).mp (Quotient.mk_out (s := orbitRel H β) a)
      obtain ⟨x, hx⟩ := mem_orbit_iff.mp hr
      rw [← hx]
      exact (hfix a).mpr rfl x
  have hterm : ∀ ω : Quotient (orbitRel H β),
      Nat.card H / Nat.card (stabilizer H ω.out) =
        if ω = ⟦a⟧ then 1 else Nat.card H := by
    intro ω
    rw [hstab ω.out]
    have hH : 0 < Nat.card H := Nat.card_pos
    by_cases h : ω = ⟦a⟧
    · have h' : ω.out = a := (hiff ω).mpr h
      rw [if_pos h', if_pos h, Nat.div_self hH]
    · have h' : ω.out ≠ a := fun e => h ((hiff ω).mp e)
      rw [if_neg h', if_neg h, Nat.div_one]
  have hsum := MulAction.card_eq_sum_card_group_div_card_stabilizer H β
  simp only [← Nat.card_eq_fintype_card] at hsum
  have hterm2 : ∀ ω : Quotient (orbitRel H β),
      (if ω = ⟦a⟧ then 1 else Nat.card H) % Nat.card H =
        if ω = ⟦a⟧ then 1 % Nat.card H else 0 := by
    intro ω
    by_cases h : ω = ⟦a⟧
    · simp [h]
    · simp [h]
  rw [hsum]
  simp only [hterm]
  unfold Nat.ModEq
  rw [Finset.sum_nat_mod, Finset.sum_congr rfl (fun ω _ => hterm2 ω)]
  simp

section TITheory

open Subgroup

variable {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]

theorem smul_eq_smul_iff_inv_mul_mem_normalizer [Finite G] (P : Sylow p G) (a b : G) :
    a • P = b • P ↔ b⁻¹ * a ∈ normalizer P := by
  rw [← Sylow.smul_eq_iff_mem_normalizer, mul_smul, inv_smul_eq_iff]

theorem mem_normalizer_smul_iff [Finite G] (P : Sylow p G) (y x : G) :
    x ∈ normalizer (y • P) ↔ y⁻¹ * x * y ∈ normalizer P := by
  rw [← Sylow.smul_eq_iff_mem_normalizer, ← mul_smul,
    smul_eq_smul_iff_inv_mul_mem_normalizer, mul_assoc]

theorem eq_of_le_sylow [Finite G] (P Q : Sylow p G) (h : (P : Subgroup G) ≤ Q) : P = Q := by
  refine Sylow.ext (Subgroup.eq_of_le_of_card_ge h ?_)
  rw [Sylow.card_eq_multiplicity Q, Sylow.card_eq_multiplicity P]

theorem inf_normalizer_smul_eq_bot [Finite G] (P : Sylow p G)
    (hTI : ∀ g : G, g ∉ normalizer P →
      (P : Subgroup G) ⊓ (P : Subgroup G).map (MulAut.conj g).toMonoidHom = ⊥)
    (y : G) (hy : y ∉ normalizer P) :
    (P : Subgroup G) ⊓ normalizer (y • P : Sylow p G) = ⊥ := by
  rw [P.isPGroup'.inf_normalizer_sylow (y • P), Sylow.coe_subgroup_smul]
  exact hTI y hy

theorem mk_eq_one_iff [Finite G] (P : Sylow p G) (Y : Subgroup G) (y : Y) :
    (QuotientGroup.mk y : Y ⧸ (normalizer P).subgroupOf Y) = QuotientGroup.mk (1 : Y)
      ↔ ((y : Y) : G) ∈ normalizer P := by
  rw [QuotientGroup.eq, mul_one, Subgroup.mem_subgroupOf, Subgroup.coe_inv, inv_mem_iff]

theorem mk_mul_eq_mk_iff [Finite G] (P : Sylow p G) (Y : Subgroup G) (h y : Y) :
    (QuotientGroup.mk ((h : Y) * y) : Y ⧸ (normalizer P).subgroupOf Y) = QuotientGroup.mk y
      ↔ ((h : Y) : G) ∈ normalizer ((y : G) • P : Sylow p G) := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  have e : (((h : Y) : G) * (y : G))⁻¹ * (y : G) = ((y : G)⁻¹ * ((h : Y) : G) * (y : G))⁻¹ := by
    group
  rw [mem_normalizer_smul_iff, e, inv_mem_iff]

theorem fixed_cosets_iff [Finite G] (P : Sylow p G) (Y : Subgroup G) (hPY : (P : Subgroup G) ≤ Y)
    (b : Y ⧸ (normalizer P).subgroupOf Y) :
    (∀ h : ↥((P : Subgroup G).subgroupOf Y), (h : Y) • b = b)
      ↔ b = QuotientGroup.mk (1 : Y) := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  constructor
  · intro hf
    have hP : (P : Subgroup G) ≤ normalizer ((y : G) • P : Sylow p G) := by
      intro x hx
      have h1 := hf ⟨⟨x, hPY hx⟩, Subgroup.mem_subgroupOf.mpr hx⟩
      rw [MulAction.Quotient.smul_mk, smul_eq_mul] at h1
      exact (mk_mul_eq_mk_iff P Y _ y).mp h1
    have hle : (P : Subgroup G) ≤ ((y : G) • P : Sylow p G) := by
      have h1 := P.isPGroup'.inf_normalizer_sylow ((y : G) • P : Sylow p G)
      rw [inf_eq_left.mpr hP] at h1
      exact inf_eq_left.mp h1.symm
    have hPeq : P = ((y : G) • P : Sylow p G) := eq_of_le_sylow P _ hle
    exact (mk_eq_one_iff P Y y).mpr (Sylow.smul_eq_iff_mem_normalizer.mp hPeq.symm)
  · intro hy h
    have hyN : ((y : Y) : G) ∈ normalizer P := (mk_eq_one_iff P Y y).mp hy
    have hsm : ((y : Y) : G) • P = P := Sylow.smul_eq_iff_mem_normalizer.mpr hyN
    rw [MulAction.Quotient.smul_mk, smul_eq_mul]
    refine (mk_mul_eq_mk_iff P Y h y).mpr ?_
    rw [hsm]
    exact le_normalizer (Subgroup.mem_subgroupOf.mp h.2)

theorem fixed_free [Finite G] (P : Sylow p G) (Y : Subgroup G)
    (hTI : ∀ g : G, g ∉ normalizer P →
      (P : Subgroup G) ⊓ (P : Subgroup G).map (MulAut.conj g).toMonoidHom = ⊥)
    (b : Y ⧸ (normalizer P).subgroupOf Y) (hb : b ≠ QuotientGroup.mk (1 : Y))
    (h : ↥((P : Subgroup G).subgroupOf Y)) (hh : (h : Y) • b = b) : h = 1 := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  have hyN' : ((y : Y) : G) ∉ normalizer P := fun hy => hb ((mk_eq_one_iff P Y y).mpr hy)
  rw [MulAction.Quotient.smul_mk, smul_eq_mul] at hh
  have hmem := (mk_mul_eq_mk_iff P Y h y).mp hh
  have h1 : ((h : Y) : G) ∈ (P : Subgroup G) ⊓ normalizer ((y : G) • P : Sylow p G) :=
    ⟨Subgroup.mem_subgroupOf.mp h.2, hmem⟩
  rw [inf_normalizer_smul_eq_bot P hTI _ hyN'] at h1
  have h2 : ((h : Y) : G) = 1 := Subgroup.mem_bot.mp h1
  exact Subtype.ext (Subtype.ext (by simpa using h2))

theorem index_modEq_one_of_TI [Finite G] (P : Sylow p G)
    (hTI : ∀ g : G, g ∉ normalizer P →
      (P : Subgroup G) ⊓ (P : Subgroup G).map (MulAut.conj g).toMonoidHom = ⊥)
    (Y : Subgroup G) (hY : normalizer P ≤ Y) :
    (normalizer P).relIndex Y ≡ 1 [MOD Nat.card (P : Subgroup G)] := by
  have hPY : (P : Subgroup G) ≤ Y := le_trans le_normalizer hY
  have hcard : Nat.card ((P : Subgroup G).subgroupOf Y) = Nat.card (P : Subgroup G) :=
    Nat.card_congr (subgroupOfEquivOfLe hPY).toEquiv
  letI : MulAction ↥((P : Subgroup G).subgroupOf Y) (Y ⧸ (normalizer P).subgroupOf Y) :=
    MulAction.compHom _ ((P : Subgroup G).subgroupOf Y).subtype
  have key := card_modEq_one_of_free_except
    (QuotientGroup.mk (1 : Y) : Y ⧸ (normalizer P).subgroupOf Y)
    (fun b => fixed_cosets_iff P Y hPY b)
    (fun b hb h hh => fixed_free P Y hTI b hb h hh)
  have hidx : Nat.card (Y ⧸ (normalizer P).subgroupOf Y) = (normalizer P).relIndex Y := rfl
  rw [hidx, hcard] at key
  exact key

end TITheory

end CFSG.AGLEmbeddingD2.Wilson.Proving
