module

public import CFSG.RankThree.PartOne.S12.PushingUp
public import CFSG.RankThree.PartOne.Assembly

public section

namespace CFSG.CGT.PushingUpLit.STT

open CFSG CFSG.RankThree.PartOne

theorem isPerfect_alternatingGroup {n : ℕ} (hn : 2 ≤ n) :
    Group.IsPerfect (alternatingGroup (Fin (2 * n + 1))) := by
  refine ⟨commutator_alternatingGroup_eq_top ?_⟩
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
  omega

theorem not_isSolvable_of_naturalAlt {X : Type} [Group X] {n : ℕ} (hn : 2 ≤ n)
    (hnat : IsNaturalAltModule X n) : ¬ Group.IsSolvable X := by
  intro hsolv
  obtain ⟨φ, -⟩ := hnat
  have hq : Group.IsSolvable (X ⧸ pCore 2 X) := inferInstance
  have hA : Group.IsSolvable (alternatingGroup (Fin (2 * n + 1))) :=
    Group.isSolvable_of_isSolvable_injective (f := φ.symm.toMonoidHom) φ.symm.injective
  have := isPerfect_alternatingGroup hn
  have hnt : Nontrivial (alternatingGroup (Fin (2 * n + 1))) :=
    alternatingGroup.nontrivial_of_three_le_card (by
      simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
      omega)
  exact Group.IsPerfect.not_isSolvable _ hA

theorem exists_noncomm_of_naturalAlt {G : Type} [Group G] {X : Subgroup G} {n : ℕ} (hn : 2 ≤ n)
    (hnat : IsNaturalAltModule ↥X n) : ∃ a b : G, a * b ≠ b * a := by
  by_contra hcomm
  push Not at hcomm
  obtain ⟨φ, -⟩ := hnat
  have hAc : IsMulCommutative (alternatingGroup (Fin (2 * n + 1))) := by
    refine ⟨⟨fun a b => ?_⟩⟩
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (φ.symm a)
    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (φ.symm b)
    have hxy : x * y = y * x := Subtype.ext (hcomm _ _)
    have h1 : φ.symm a * φ.symm b = φ.symm b * φ.symm a := by
      rw [← hx, ← hy, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hxy]
    have h2 := congrArg φ h1
    simpa using h2
  have := alternatingGroup.isMulCommutative_iff_card_le_three.1 hAc
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at this
  omega

theorem map_sylow_ne_bot {G : Type} [Group G] [Finite G] {K : Subgroup G} (hev : Even (Nat.card ↥K))
    (R : Sylow 2 ↥K) : (R : Subgroup ↥K).map K.subtype ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hb
  have hR : (R : Subgroup ↥K) = ⊥ := by
    rwa [Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective] at hb
  have hcard : Nat.card ↥(R : Subgroup ↥K) = 2 ^ (Nat.card ↥K).factorization 2 :=
    Sylow.card_eq_multiplicity R
  rw [hR, Subgroup.card_bot] at hcard
  have hdvd : 2 ∣ Nat.card ↥K := even_iff_two_dvd.mp hev
  have hK0 : Nat.card ↥K ≠ 0 := Nat.card_pos.ne'
  have hpos : 0 < (Nat.card ↥K).factorization 2 :=
    Nat.Prime.factorization_pos_of_dvd Nat.prime_two hK0 hdvd
  have : 2 ^ 1 ≤ 2 ^ (Nat.card ↥K).factorization 2 := Nat.pow_le_pow_right (by norm_num) hpos
  omega

end CFSG.CGT.PushingUpLit.STT
