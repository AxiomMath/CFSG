module

public import CFSG.LocalAnalysis.SectionRank.SubgroupRank
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.GrpA
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G]

private theorem card_sup_of_inf_eq_bot_of_commute {X Y : Subgroup G}
    (hc : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) (hXY : X ⊓ Y = ⊥) :
    Nat.card (X ⊔ Y : Subgroup G) = Nat.card X * Nat.card Y := by
  have h := (CFSG.GH74.GLS.Stage1.Thm3.Sec7.A.card_sup_mul_card_inf_of_commute
    (A := X) (B := Y) hc)
  rwa [hXY, Subgroup.card_bot, mul_one] at h

private theorem eq_one_or_eq_of_sq_eq_one {a x : G} (ha : a ^ 2 = 1)
    (hx : x ∈ Subgroup.zpowers a) : x = 1 ∨ x = a := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  obtain ⟨k, hk | hk⟩ := Int.even_or_odd' n
  · left
    rw [hk, zpow_mul, zpow_ofNat, ha, one_zpow]
  · right
    rw [hk, zpow_add, zpow_mul, zpow_ofNat, ha, one_zpow, one_mul, zpow_one]

private theorem zpowers_inf_zpowers_eq_bot {a b : G} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) :
    Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxa, hxb⟩ := Subgroup.mem_inf.mp hx
  rcases eq_one_or_eq_of_sq_eq_one ha hxa with rfl | rfl
  · exact Subgroup.mem_bot.mpr rfl
  · rcases eq_one_or_eq_of_sq_eq_one hb hxb with h | h
    · exact Subgroup.mem_bot.mpr h
    · exact absurd h hab

theorem isE3_closure_of_commuting {u₁ u₂ u₃ : G} (h1 : u₁ ^ 2 = 1) (h2 : u₂ ^ 2 = 1)
    (h3 : u₃ ^ 2 = 1) (c12 : u₁ * u₂ = u₂ * u₁) (c13 : u₁ * u₃ = u₃ * u₁)
    (c23 : u₂ * u₃ = u₃ * u₂) (n1 : u₁ ∉ closure {u₂, u₃}) (n2 : u₂ ≠ 1) (n3 : u₃ ≠ 1)
    (n23 : u₂ ≠ u₃) :
    IsElemAbelian 2 (closure {u₁, u₂, u₃}) ∧ Nat.card ↥(closure {u₁, u₂, u₃}) = 8 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A : Subgroup G := closure {u₁, u₂, u₃} with hA
  set B : Subgroup G := closure {u₂, u₃} with hB
  set H : Subgroup G := closure {u₁} with hH
  have hA_comm : IsMulCommutative A := by
    rw [hA]
    refine Subgroup.isMulCommutative_closure ?_
    intro a ha b hb _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      simp [Commute, SemiconjBy, c12, c13, c23]
  have hA2 : IsElemAbelian 2 A := by
    refine ⟨hA_comm, ?_⟩
    intro x hx
    refine Subgroup.closure_induction (p := fun y _ => y ^ 2 = 1) ?_ ?_ ?_ ?_ hx
    · intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact h3
    · exact one_pow 2
    · intro y z hy hz hy2 hz2
      have hyz : Commute y z :=
        congrArg Subtype.val (hA_comm.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
      rw [hyz.mul_pow, hy2, hz2, one_mul]
    · intro y _ hy2
      rw [inv_pow, hy2, inv_one]
  have hAeq : A = H ⊔ B := by
    rw [hA, hH, hB]
    rw [show ({u₁, u₂, u₃} : Set G) = {u₁} ∪ ({u₂, u₃} : Set G) by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union, or_assoc]]
    rw [Subgroup.closure_union]
  have hHA : H ≤ A := by rw [hAeq]; exact le_sup_left
  have hBA : B ≤ A := by rw [hAeq]; exact le_sup_right
  have hB_eq : B = Subgroup.zpowers u₂ ⊔ Subgroup.zpowers u₃ := by
    rw [hB]
    rw [show ({u₂, u₃} : Set G) = {u₂} ∪ {u₃} by ext x; simp [or_comm]]
    rw [Subgroup.closure_union]
    simp only [← Subgroup.zpowers_eq_closure]
  have hz2B : Subgroup.zpowers u₂ ≤ B := by
    rw [hB]; exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
  have hz3B : Subgroup.zpowers u₃ ≤ B := by
    rw [hB]; exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
  have hu1ne : u₁ ≠ 1 := fun h => n1 (by rw [h]; exact B.one_mem)
  have hcardH : Nat.card H = 2 := by
    rw [hH, ← Subgroup.zpowers_eq_closure, Nat.card_zpowers, orderOf_eq_prime h1 hu1ne]
  have hcommHA : ∀ x ∈ H, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA_comm.is_comm.comm ⟨x, hHA hx⟩ ⟨y, hBA hy⟩)
  have hcomm23 : ∀ x ∈ Subgroup.zpowers u₂, ∀ y ∈ Subgroup.zpowers u₃, x * y = y * x :=
    fun x hx y hy => congrArg Subtype.val
      (hA_comm.is_comm.comm ⟨x, hBA (hz2B hx)⟩ ⟨y, hBA (hz3B hy)⟩)
  have hHB : H ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxH, hxB⟩ := Subgroup.mem_inf.mp hx
    rw [hH, ← Subgroup.zpowers_eq_closure] at hxH
    rcases eq_one_or_eq_of_sq_eq_one h1 hxH with h | h
    · exact Subgroup.mem_bot.mpr h
    · exact absurd (h ▸ hxB) n1
  have hcardB : Nat.card B = 4 := by
    rw [hB_eq, card_sup_of_inf_eq_bot_of_commute hcomm23
      (zpowers_inf_zpowers_eq_bot h2 h3 n2 n3 n23), Nat.card_zpowers, Nat.card_zpowers,
      orderOf_eq_prime h2 n2, orderOf_eq_prime h3 n3]
  have hcardA : Nat.card A = 8 := by
    rw [hAeq, card_sup_of_inf_eq_bot_of_commute hcommHA hHB, hcardH, hcardB]
  exact ⟨hA2, hcardA⟩

theorem card_le_eight_of_pRank [Finite G] {X : Subgroup G} (hX : pRank 2 X = 3) :
    ∀ E : Subgroup G, E ≤ X → IsElemAbelian 2 E → Nat.card E ≤ 8 := by
  intro E hEX hE
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 E := fun x => ⟨1, by
    apply Subtype.ext
    simpa using hE.2 x x.2⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 hP
  have hX' : CFSG.Open.pRank 2 X = 3 := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 2) X,
      ← CFSG.SectionRank.pRank_eq_open_pRank_top 2 ↥X]
    exact hX
  have hk_le : k ≤ CFSG.Open.pRank 2 X :=
    CFSG.SectionRank.le_pRank (p := 2) (by norm_num) hEX hE hk
  rw [hX'] at hk_le
  calc Nat.card E = 2 ^ k := hk
    _ ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hk_le
    _ = 8 := by norm_num

end CFSG.OddStandard.HigherRank.YamadaG23
