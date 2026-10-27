
module

public import CFSG.Quasithin.Background.A1cRank
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

namespace L238

section Rank

variable {Y : Type*} [Group Y] [Finite Y]

theorem false_of_three_commuting (hY : CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≤ 2)
    {x₁ x₂ x₃ : Y} (h₂ : orderOf x₂ = 3) (h₃ : orderOf x₃ = 3) (h₁ : orderOf x₁ = 3)
    (c₁₂ : Commute x₁ x₂) (c₁₃ : Commute x₁ x₃) (c₂₃ : Commute x₂ x₃)
    (i₃ : x₃ ∉ Subgroup.zpowers x₂) (i₁ : x₁ ∉ Subgroup.zpowers x₂ ⊔ Subgroup.zpowers x₃) :
    False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hbot : IsElemAbelian 3 (⊥ : Subgroup Y) :=
    ⟨inferInstance, fun x hx => by rw [Subgroup.mem_bot.1 hx, one_pow]⟩
  have hx₂ : x₂ ∉ (⊥ : Subgroup Y) := fun h => by
    have := Subgroup.mem_bot.1 h
    rw [this] at h₂
    simp at h₂
  obtain ⟨hE₁, hc₁⟩ := exists_elemAbelian_sup_zpowers hbot h₂
    (fun e he => by rw [Subgroup.mem_bot.1 he]; exact Commute.one_left _) hx₂
  have hcomm₃ : ∀ e ∈ (⊥ ⊔ Subgroup.zpowers x₂ : Subgroup Y), Commute e x₃ := by
    intro e he
    rw [bot_sup_eq] at he
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 he
    exact c₂₃.zpow_left k
  have hx₃ : x₃ ∉ (⊥ ⊔ Subgroup.zpowers x₂ : Subgroup Y) := by
    rw [bot_sup_eq]
    exact i₃
  obtain ⟨hE₂, hc₂⟩ := exists_elemAbelian_sup_zpowers hE₁ h₃ hcomm₃ hx₃
  have hcomm₁ : ∀ e ∈ (⊥ ⊔ Subgroup.zpowers x₂ ⊔ Subgroup.zpowers x₃ : Subgroup Y),
      Commute e x₁ := by
    intro e he
    rw [bot_sup_eq] at he
    have hle : Subgroup.zpowers x₂ ⊔ Subgroup.zpowers x₃ ≤ Subgroup.centralizer {x₁} := by
      refine sup_le ?_ ?_
      · refine Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_iff.2 fun h hh => ?_)
        rw [Set.mem_singleton_iff.1 hh]
        exact c₁₂.eq
      · refine Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_iff.2 fun h hh => ?_)
        rw [Set.mem_singleton_iff.1 hh]
        exact c₁₃.eq
    exact (Subgroup.mem_centralizer_iff.1 (hle he) x₁ rfl).symm
  have hx₁ : x₁ ∉ (⊥ ⊔ Subgroup.zpowers x₂ ⊔ Subgroup.zpowers x₃ : Subgroup Y) := by
    rw [bot_sup_eq]
    exact i₁
  obtain ⟨hE₃, hc₃⟩ := exists_elemAbelian_sup_zpowers hE₂ h₁ hcomm₁ hx₁
  have hcard : Nat.card ↥(⊥ ⊔ Subgroup.zpowers x₂ ⊔ Subgroup.zpowers x₃ ⊔ Subgroup.zpowers x₁ :
      Subgroup Y) = 3 ^ 3 := by
    rw [hc₃, hc₂, hc₁, Subgroup.card_bot]
    norm_num
  have h3 : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Y) := le_pRank Nat.prime_three le_top hE₃ hcard
  omega

end Rank

section Orders

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem orderOf_mk_pCore_eq_three {X : Subgroup G} {x : ↥X} (hx : orderOf x = 3) :
    orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥X) x) = 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥X) x) ∣ 3 := hx ▸ orderOf_map_dvd _ x
  rcases (Nat.dvd_prime Nat.prime_three).1 h1 with h | h
  · exfalso
    have hx1 : QuotientGroup.mk' (CFSG.pCore 2 ↥X) x = 1 := orderOf_eq_one_iff.1 h
    have hxQ : x ∈ CFSG.pCore 2 ↥X := (QuotientGroup.eq_one_iff x).1 hx1
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (G := ↥X) (p := 2)) ⟨x, hxQ⟩
    have hk' : x ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have h3 : 3 ∣ 2 ^ k := hx ▸ orderOf_dvd_of_pow_eq_one hk'
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  · exact h

theorem exists_orderOf_three {X B : Subgroup G} (hBX : B ≤ X) (h3 : 3 ∣ Nat.card B) :
    ∃ x : ↥X, (x : G) ∈ B ∧ orderOf x = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥B) 3 h3
  refine ⟨⟨(y : G), hBX y.2⟩, y.2, ?_⟩
  have h1 : orderOf (y : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hy
  rw [← Subgroup.orderOf_coe]
  exact h1

end Orders

end L238

end CFSG.QuasithinUnique
