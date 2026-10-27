module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviOutAut
public import CFSG.LocalAnalysis.AGLEmbedding.BlockThreeCentCoprimeOut
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSeitzCycExc
public import CFSG.Adapters.LieModelSimple
public import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.Adapters.StatedClassicalUnitaryOrders
public import CFSG.RankThree.PartOne.N143.Inspect613Even
public import Certificates.Data.A5

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi

open TauCeti Subgroup CFSG.Open

theorem center_eq_bot_of_simple_of_not_comm {G : Type*} [Group G] [IsSimpleGroup G] {a b : G}
    (hab : a * b ≠ b * a) : Subgroup.center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · exact h
  · exfalso
    have hb : b ∈ Subgroup.center G := by
      rw [h]
      exact Subgroup.mem_top b
    exact hab (Subgroup.mem_center_iff.1 hb a)

theorem center_eq_bot_of_simple_of_not_prime {G : Type*} [Group G] [IsSimpleGroup G]
    (hG : ¬ (Nat.card G).Prime) : Subgroup.center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · exact h
  · exfalso
    have hcomm : ∀ a b : G, a * b = b * a := by
      intro a b
      have ha : a ∈ Subgroup.center G := by
        rw [h]
        exact Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.1 ha b).symm
    letI : CommGroup G := { ‹Group G› with mul_comm := hcomm }
    exact hG IsSimpleGroup.prime_card

theorem center_eq_bot_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (hH : Subgroup.center H = ⊥) : Subgroup.center G = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have h1 : e x ∈ Subgroup.center H := by
    rw [Subgroup.mem_center_iff]
    intro y
    have h2 := Subgroup.mem_center_iff.mp hx (e.symm y)
    have h3 := congrArg e h2
    simpa using h3
  rw [hH, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot]
  exact e.injective (by rw [map_one]; exact h1)

theorem alt_exists_not_comm {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 8) :
    ∃ a b : alternatingGroup (Fin n), a * b ≠ b * a := by
  rcases hn with rfl | rfl | rfl
  · exact ⟨⟨List.formPerm [0, 1, 2], Equiv.Perm.mem_alternatingGroup.2 (by decide +kernel)⟩,
      ⟨List.formPerm [1, 2, 3], Equiv.Perm.mem_alternatingGroup.2 (by decide +kernel)⟩,
      fun h => by
        have := congrArg Subtype.val h
        revert this
        decide +kernel⟩
  · exact ⟨⟨List.formPerm [0, 1, 2], Equiv.Perm.mem_alternatingGroup.2 (by decide +kernel)⟩,
      ⟨List.formPerm [1, 2, 3], Equiv.Perm.mem_alternatingGroup.2 (by decide +kernel)⟩,
      fun h => by
        have := congrArg Subtype.val h
        revert this
        decide +kernel⟩
  · exact ⟨⟨List.formPerm [0, 1, 2], Equiv.Perm.mem_alternatingGroup.2 (by decide +kernel)⟩,
      ⟨List.formPerm [1, 2, 3], Equiv.Perm.mem_alternatingGroup.2 (by decide +kernel)⟩,
      fun h => by
        have := congrArg Subtype.val h
        revert this
        decide +kernel⟩

theorem alt_false {A : Type} [Group A] [Finite A] {K K₀ B : Subgroup A} {z : A} {p : ℕ}
    (S : E3Setting K K₀ B z p) {n : ℕ} (hn : 5 ≤ n) (h : n = 5 ∨ n = 6 ∨ n = 8)
    (e : Nonempty (↥K ≃* alternatingGroup (Fin n))) : False := by
  obtain ⟨e⟩ := e
  haveI : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact hn)
  obtain ⟨a, b, hab⟩ := alt_exists_not_comm h
  have hZ : Subgroup.center ↥K = ⊥ :=
    center_eq_bot_of_mulEquiv e (center_eq_bot_of_simple_of_not_comm hab)
  exact false_of_not_dvd_card_outer S hZ
    (CFSG.AGLEmbedding.not_dvd_card_outer_of_mulEquiv_alternatingGroup e hn S.hp S.hp5)

theorem a1seven_false {A : Type} [Group A] [Finite A] {K K₀ B : Subgroup A} {z : A} {p : ℕ}
    (S : E3Setting K K₀ B z p) {q : PrimePower} (hq : q.card = 7)
    (hv : (LieTypeIndex.A 1 q).Valid)
    (e : Nonempty (↥K ≃* ValidLieTypeIndex.Group ⟨.A 1 q, hv⟩)) : False := by
  obtain ⟨e⟩ := e
  have hpow : q.p ^ q.exponent = 7 := (TauCeti.PrimePower.card_def q).symm.trans hq
  obtain ⟨hp7, hf⟩ := (Nat.Prime.pow_eq_iff Nat.prime_seven).1 hpow
  have h := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
  rw [hp7, hf] at h
  haveI : IsSimpleGroup ↥K := CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel h
  have hcard : Nat.card ↥K = 168 := CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_seven h
  have hZ : Subgroup.center ↥K = ⊥ :=
    center_eq_bot_of_simple_of_not_prime (by rw [hcard]; norm_num)
  exact false_of_not_dvd_card_outer S hZ
    (CFSG.AGLEmbedding.not_dvd_card_outer_of_psl_seven_of_five_le h S.hp S.hp5)

theorem tA2three_false {A : Type} [Group A] [Finite A] {K K₀ B : Subgroup A} {z : A} {p : ℕ}
    (S : E3Setting K K₀ B z p) {q : PrimePower} (hq : q.card = 3)
    (hv : (LieTypeIndex.twistedA 2 q).Valid)
    (e : Nonempty (↥K ≃* ValidLieTypeIndex.Group ⟨.twistedA 2 q, hv⟩)) : False := by
  obtain ⟨e⟩ := e
  have hpow : q.p ^ q.exponent = 3 := (TauCeti.PrimePower.card_def q).symm.trans hq
  obtain ⟨hp3, hf⟩ := (Nat.Prime.pow_eq_iff Nat.prime_three).1 hpow
  have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
  rw [hp3, hf] at h
  haveI : IsSimpleGroup ↥K := CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel h
  have hcard : Nat.card ↥K = 6048 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_three h
  have hZ : Subgroup.center ↥K = ⊥ :=
    center_eq_bot_of_simple_of_not_prime (by rw [hcard]; norm_num)
  exact false_of_not_dvd_card_outer S hZ
    (CFSG.AGLEmbedding.not_dvd_card_outer_of_psu_prime_of_five_le h (Or.inr rfl) S.hp S.hp5)

section Tits

theorem tits_false {A : Type} [Group A] [Finite A] {K K₀ B : Subgroup A} {z : A} {p : ℕ}
    (S : E3Setting K K₀ B z p) (hv : LieTypeIndex.tits.Valid)
    (e : Nonempty (↥K ≃* ValidLieTypeIndex.Group ⟨.tits, hv⟩)) : False := by
  obtain ⟨e⟩ := e
  have hmodel := CFSG.RankThree.PartOne.CTP.reeTitsModel_tits (S := ↥K) ⟨hv, ⟨e⟩⟩
  obtain ⟨F, _, _, _, hF, ⟨φ⟩⟩ := CFSG.SectionRank.exists_mulEquiv_titsGroup_of_model hmodel
  haveI := CFSG.Sporadic.Schreier.Tits.commutator_reeFixed_simple hF
  haveI : IsSimpleGroup ↥K := φ.isSimpleGroup
  have hZ : Subgroup.center ↥K = ⊥ :=
    center_eq_bot_of_mulEquiv φ
      (CFSG.LocalAnalysis.ComponentInitial.center_commutator_reeFixed_eq_bot hF)
  have h5 := S.hp5
  exact false_of_not_dvd_card_outer S hZ
    (CFSG.AGLEmbedding.not_dvd_card_outer_tits hv e S.hp (by omega))

end Tits

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi
