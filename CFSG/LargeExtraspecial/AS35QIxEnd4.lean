module

public import CFSG.GroupTheory.ThompsonIndexTwo
public import CFSG.LargeExtraspecial.AS35QIxBasic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35QIx

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem le_M_of_le (S : Setting G) {P : Subgroup G} (hP : IsPGroup 2 P) (hQP : S.QG ≤ P) :
    P ≤ S.M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzP : S.z ∈ P := hQP S.z_mem_QG
  have : Nontrivial P := ⟨⟨⟨S.z, hzP⟩, 1, fun h => S.z_ne_one (congrArg Subtype.val h)⟩⟩
  have := hP.center_nontrivial
  obtain ⟨⟨c, hcZ⟩, hc1⟩ := exists_ne (1 : center P)
  have hcomm : ∀ x ∈ P, (c : G) * x = x * c := fun x hx =>
    congrArg Subtype.val ((mem_center_iff.mp hcZ ⟨x, hx⟩).symm)
  have hcz : (c : G) * S.z = S.z * c := hcomm _ hzP
  have hcM : (c : G) ∈ S.M := S.mem_M_iff.mpr hcz
  have hcQ : (c : G) ∈ S.QG := S.mem_QG_of_commute hcM fun y hy => hcomm y (hQP hy)
  rcases S.eq_one_or_z_of_commute hcQ (fun y hy => hcomm y (hQP hy)) with h | h
  · exact absurd (Subtype.ext (Subtype.ext h)) hc1
  · intro x hx
    rw [S.mem_M_iff, ← h]
    exact (hcomm x hx).symm

namespace IxSetup

variable (T : IxSetup S)

@[expose] noncomputable def M0 : Subgroup G :=
  ((centralizer {T.ζ} : Subgroup S.O).comap S.ρ).map S.M.subtype

theorem mem_M0 {x : G} : x ∈ T.M0 ↔ ∃ hx : x ∈ S.M, S.ρ ⟨x, hx⟩ * T.ζ = T.ζ * S.ρ ⟨x, hx⟩ := by
  constructor
  · rintro ⟨⟨y, hy⟩, hyc, rfl⟩
    exact ⟨hy, mem_centralizer_singleton_iff.mp hyc⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, mem_centralizer_singleton_iff.mpr h, rfl⟩

include T in
theorem card_QG_gt_two : 2 < Nat.card S.QG := by
  rw [S.card_QG_eq, S.card_Qt, T.finrank_Qt]
  norm_num

theorem exists_conj_mem_M0 (hS : S.SixHyp) {a : G} (ha : a ∈ S.M) (haa : a * a = 1)
    (haζ : S.ρ ⟨a, ha⟩ * T.ζ ≠ T.ζ * S.ρ ⟨a, ha⟩) : ∃ k : G, k⁻¹ * a * k ∈ T.M0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsimp := T.isSimpleGroup hS
  have haQ : zpowers a ≤ normalizer (S.QG : Set G) := by
    rw [zpowers_le]
    exact mem_normalizer_iff.mpr fun y => ⟨fun hy => S.conj_mem_QG ha hy, fun hy => by
      have := S.conj_mem_QG (S.M.inv_mem ha) hy
      rwa [show a⁻¹ * (a * y * a⁻¹) * a⁻¹⁻¹ = y by group] at this⟩
  have ha2 : IsPGroup 2 (zpowers a) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime (by rw [pow_two]; exact haa) (fun h => haζ (by
      rw [show (⟨a, ha⟩ : S.M) = 1 from Subtype.ext h, map_one, one_mul, mul_one]))
  have hP : IsPGroup 2 (S.QG ⊔ zpowers a : Subgroup G) :=
    S.isPGroup_QG.to_sup_of_normal_left' ha2 haQ
  obtain ⟨T₂, hT₂⟩ := hP.exists_le_sylow
  have hT₂M : (T₂ : Subgroup G) ≤ S.M := le_M_of_le S T₂.2 (le_sup_left.trans hT₂)
  have haT : a ∈ (T₂ : Subgroup G) := hT₂ (le_sup_right (a := S.QG) (mem_zpowers a))
  set U : Subgroup G := (T₂ : Subgroup G) ⊓ T.M0 with hU
  have haU : a ∉ U := fun h => haζ ((T.mem_M0.mp (mem_inf.mp h).2).2)
  have hmemU : ∀ x (hx : x ∈ (T₂ : Subgroup G)), x ∈ U ↔
      S.ρ ⟨x, hT₂M hx⟩ * T.ζ = T.ζ * S.ρ ⟨x, hT₂M hx⟩ := by
    intro x hx
    rw [hU, mem_inf, T.mem_M0]
    exact ⟨fun ⟨_, ⟨_, h⟩⟩ => h, fun h => ⟨hx, ⟨hT₂M hx, h⟩⟩⟩
  have hidx : U.relIndex T₂ = 2 := by
    rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
    refine ⟨⟨a, haT⟩, fun b => ?_⟩
    rw [mem_subgroupOf, mem_subgroupOf, Subgroup.coe_mul, hmemU _ (mul_mem b.2 haT),
      hmemU _ b.2]
    have e : (⟨(b : G) * a, hT₂M (mul_mem b.2 haT)⟩ : S.M) = ⟨b, hT₂M b.2⟩ * ⟨a, ha⟩ := rfl
    rw [e, map_mul]
    have hainv := T.conj_inv_of_not_comm (⟨_, rfl⟩ : S.ρ ⟨a, ha⟩ ∈ S.Mbar) haζ
    by_cases hb : S.ρ ⟨b, hT₂M b.2⟩ * T.ζ = T.ζ * S.ρ ⟨b, hT₂M b.2⟩
    · refine Or.inr ⟨hb, fun hba => ?_⟩
      apply haζ
      calc S.ρ ⟨a, ha⟩ * T.ζ =
          (S.ρ ⟨b, hT₂M b.2⟩)⁻¹ * ((S.ρ ⟨b, hT₂M b.2⟩ * S.ρ ⟨a, ha⟩) * T.ζ) := by group
        _ = (S.ρ ⟨b, hT₂M b.2⟩)⁻¹ * (T.ζ * (S.ρ ⟨b, hT₂M b.2⟩ * S.ρ ⟨a, ha⟩)) := by rw [hba]
        _ = (S.ρ ⟨b, hT₂M b.2⟩)⁻¹ * (T.ζ * S.ρ ⟨b, hT₂M b.2⟩) * S.ρ ⟨a, ha⟩ := by group
        _ = (S.ρ ⟨b, hT₂M b.2⟩)⁻¹ * (S.ρ ⟨b, hT₂M b.2⟩ * T.ζ) * S.ρ ⟨a, ha⟩ := by rw [hb]
        _ = T.ζ * S.ρ ⟨a, ha⟩ := by group
    · exact Or.inl ⟨T.comm_of_inv_of_inv (T.conj_inv_of_not_comm ⟨_, rfl⟩ hb) hainv, hb⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨N, hN, hNidx⟩ := CFSG.ThompsonIndexTwo.exists_normal_index_two_of_thompson T₂.2
    T₂.not_dvd_index inf_le_left hidx haT haU (fun y hyT hyU => by
      rw [orderOf_eq_prime (by rw [pow_two]; exact haa) (fun h => haU (by rw [h]; exact one_mem U))]
      refine Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨(orderOf_pos y).ne', fun h => hyU ?_⟩
      rw [orderOf_eq_one_iff.mp h]
      exact one_mem U)
    (fun k hk => hcon k (mem_inf.mp hk).2)
  rcases hsimp.eq_bot_or_eq_top_of_normal N with h | h
  · rw [h, index_bot] at hNidx
    have := Nat.card_le_card_of_injective _ (S.QG.subtype_injective)
    have := T.card_QG_gt_two
    omega
  · rw [h, index_top] at hNidx
    omega

end IxSetup

end CFSG.LargeExtraspecial.AS35QIx
