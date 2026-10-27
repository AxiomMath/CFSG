module

public import CFSG.LargeExtraspecial.S14C12TOrd
public import CFSG.LargeExtraspecial.S14C12TSp
public import CFSG.Blueprint.ThreeFourPlusTranspositionClass
public import CFSG.Timmesfeld.Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup CFSG.Open CFSG.Blueprint

@[expose] def SmithU62ThreeFourInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 10 →
    Nonempty (Mbar0 S ≃* timmesfeldPSU 6) →
      (∀ a b : G, IsConj S.z a → IsConj S.z b →
        orderOf (a * b) ∈ ({1, 2, 3, 4} : Set ℕ) ∧
          (orderOf (a * b) = 4 → IsConj S.z ((a * b) ^ 2))) ∧
      ∃ a b : G, IsConj S.z a ∧ IsConj S.z b ∧ orderOf (a * b) = 4

variable {G : Type} [Group G]

theorem setOf_isConj_eq_range (z : G) :
    {g | IsConj z g} = Set.range fun h : G => h⁻¹ * z * h := by
  ext g
  simp only [Set.mem_ofPred_eq, Set.mem_range, isConj_iff]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c⁻¹, by rw [inv_inv]⟩
  · rintro ⟨h, rfl⟩
    exact ⟨h⁻¹, by rw [inv_inv]⟩

theorem closure_setOf_isConj_eq_top [IsSimpleGroup G] {z : G} (hz : z ≠ 1) :
    closure {g | IsConj z g} = ⊤ := by
  have h : {g | IsConj z g} = Group.conjugatesOfSet {z} := by
    ext g
    simp [Group.conjugatesOfSet, conjugatesOf]
  rw [h]
  change normalClosure {z} = ⊤
  rcases Subgroup.Normal.eq_bot_or_eq_top (normalClosure ({z} : Set G)) with h0 | h0
  · exact absurd ((Subgroup.mem_bot).mp (h0 ▸ subset_normalClosure (Set.mem_singleton z))) hz
  · exact h0

theorem commutator_eq_sq_of_orderOf {a b : G} (ha : orderOf a = 2) (hb : orderOf b = 2) :
    a⁻¹ * b⁻¹ * a * b = (a * b) ^ 2 := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by rw [← sq, ← ha, pow_orderOf_eq_one])
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by rw [← sq, ← hb, pow_orderOf_eq_one])
  rw [ha', hb', sq]
  group

theorem threeFourPlusClass_of_products [IsSimpleGroup G] (S : Setting G)
    (hprod : ∀ a b : G, IsConj S.z a → IsConj S.z b →
      orderOf (a * b) ∈ ({1, 2, 3, 4} : Set ℕ) ∧
        (orderOf (a * b) = 4 → IsConj S.z ((a * b) ^ 2))) :
    ThreeFourPlusClass G {g | IsConj S.z g} := by
  have hinv : ∀ d ∈ {g | IsConj S.z g}, orderOf d = 2 := fun d hd => by
    obtain ⟨c, rfl⟩ := isConj_iff.mp hd
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, S.orderOf_z]
  refine ⟨⟨S.z, setOf_isConj_eq_range S.z⟩, hinv, closure_setOf_isConj_eq_top S.z_ne_one,
    fun a ha b hb => (hprod a b ha hb).1, fun a ha b hb h4 => ?_⟩
  rw [commutator_eq_sq_of_orderOf (hinv a ha) (hinv b hb)]
  exact (hprod a b ha hb).2 h4

theorem hyp_of_threeFourPlusClass [Finite G] [IsSimpleGroup G] {D : Set G}
    (hD : ThreeFourPlusClass G D) (hnd : ∃ a ∈ D, ∃ b ∈ D, orderOf (a * b) = 4) :
    Timmesfeld.Hyp G D := by
  obtain ⟨a, ha, b, hb, h4⟩ := hnd
  have h2G : 2 ∣ Nat.card G := hD.2.1 a ha ▸ orderOf_dvd_natCard a
  refine ⟨inferInstance, ?_, ⟨hD.2.1, fun d hd e he => ?_, fun d hd e he h4 => ?_⟩, hD.2.2.1,
    fun N hN hodd => ?_, fun N hN hp => ?_, ⟨a, ha, b, hb, h4⟩⟩
  · obtain ⟨d₀, rfl⟩ := hD.1
    exact ⟨d₀, (setOf_isConj_eq_range d₀).symm⟩
  · have h := hD.2.2.2.1 d hd e he
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h | h | h
    · exact .inr (.inr (h ▸ odd_one))
    · exact .inl h
    · exact .inr (.inr (h ▸ by decide))
    · exact .inr (.inl h)
  · rw [← commutator_eq_sq_of_orderOf (hD.2.1 d hd) (hD.2.1 e he)]
    exact hD.2.2.2.2 d hd e he h4
  · rcases Subgroup.Normal.eq_bot_or_eq_top N with h | h
    · exact h
    · rw [h, Subgroup.card_top] at hodd
      exact absurd h2G (by have := Nat.odd_iff.mp hodd; omega)
  · rcases Subgroup.Normal.eq_bot_or_eq_top N with h | h
    · exact h
    · exfalso
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hG : IsPGroup 2 G := by
        rw [h] at hp
        exact hp.of_equiv Subgroup.topEquiv
      have : Nontrivial G := ⟨⟨a, 1, fun h1 => by
        have := hD.2.1 a ha
        rw [h1, orderOf_one] at this
        exact absurd this (by norm_num)⟩⟩
      have hc := hG.center_nontrivial
      have hctop : center G = ⊤ := by
        rcases Subgroup.Normal.eq_bot_or_eq_top (center G) with h' | h'
        · exact absurd h' ((Subgroup.nontrivial_iff_ne_bot (center G)).mp hc)
        · exact h'
      have hac : a ∈ center G := by rw [hctop]; exact Subgroup.mem_top a
      have hcomm : a * b = b * a := (Subgroup.mem_center_iff.mp hac b).symm
      have ha2 : a * a = 1 := by rw [← sq, ← hD.2.1 a ha, pow_orderOf_eq_one]
      have hb2 : b * b = 1 := by rw [← sq, ← hD.2.1 b hb, pow_orderOf_eq_one]
      have hsq : (a * b) ^ 2 = 1 := by
        rw [sq, mul_assoc, ← mul_assoc b a b, ← hcomm, mul_assoc a b b, hb2, mul_one, ha2]
      have := orderOf_dvd_of_pow_eq_one hsq
      rw [h4] at this
      norm_num at this

theorem twistedE6_of_outcome
    [Finite G] (S : Setting G) (hw : S.width = 10)
    (hU : Nonempty (Mbar0 S ≃* timmesfeldPSU 6)) (ho : Timmesfeld.Outcome G) :
    ChevalleyExceptionalModel G .twistedE6 2 1 := by
  rcases outcome_PSp12_or_twistedE6 ho (factorization_card_of_U6 S hw hU)
      (eleven_dvd_card_of_U6 S hU) with hSp | hE
  · exact absurd (Sp12.seventeen_dvd_card_centralizer_PSp12 hSp (exists_sylow_le_M S))
      (not_seventeen_dvd_card_M S hw hU)
  · exact Timmesfeld.Final.chevalleyExceptionalModel_of_lieModel (by decide) hE

end CFSG.LargeExtraspecial.S14
