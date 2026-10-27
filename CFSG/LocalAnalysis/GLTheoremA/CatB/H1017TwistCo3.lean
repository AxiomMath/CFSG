module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Twist
public import Certificates.Certificate431008

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.Co3 CFSG.RankThree.Native


theorem co3Twist_spec :
    ∃ P : Subgroup (Equiv.Perm (Fin 276)), P ≤ co3P ∧ Nat.card P = 2187 ∧
      ∀ E : Subgroup (Equiv.Perm (Fin 276)), E ≤ P → (∀ x ∈ E, x ^ 3 = 1) →
        (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → Nat.card E = 9 →
        ∀ a ∈ co3P, ∀ b ∈ co3P, a ∈ Subgroup.centralizer (E : Set (Equiv.Perm (Fin 276))) →
          b ∈ Subgroup.centralizer (E : Set (Equiv.Perm (Fin 276))) →
          (∃ m, a ^ 3 ^ m = 1) → (∃ m, b ^ 3 ^ m = 1) → ∃ m, (a * b) ^ 3 ^ m = 1 :=
  Certificates.certificate431008

@[expose] noncomputable def P3 : Subgroup (Equiv.Perm (Fin 276)) := Classical.choose co3Twist_spec

theorem P3_le : P3 ≤ co3P := (Classical.choose_spec co3Twist_spec).1

theorem card_P3 : Nat.card P3 = 2187 := (Classical.choose_spec co3Twist_spec).2.1

theorem factorization_card_co3P_three : (Nat.card co3P).factorization 3 = 7 := by
  rw [card_co3P, show (495766656000 : ℕ) = 3 ^ 7 * 226688000 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

@[expose] noncomputable def P3syl : Sylow 3 co3P :=
  Sylow.ofCard (P3.subgroupOf co3P) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe P3_le).toEquiv, card_P3,
      factorization_card_co3P_three]
    norm_num)

theorem closed_of_le_P3 (D : Subgroup co3P) (hDP : D ≤ (P3syl : Subgroup co3P))
    (hD : IsElemAbelian 3 D) (hc : Nat.card D = 9) :
    PElemsClosed 3 (Subgroup.centralizer (D : Set co3P)) := by
  have hP : ∀ z ∈ D, (z : Equiv.Perm (Fin 276)) ∈ P3 := fun z hz => by
    have := hDP hz
    rw [P3syl, Sylow.coe_ofCard] at this
    exact Subgroup.mem_subgroupOf.1 this
  set E := D.map co3P.subtype with hE
  have hEP : E ≤ P3 := by
    rintro _ ⟨z, hz, rfl⟩
    exact hP z hz
  have h3 : ∀ x ∈ E, x ^ 3 = 1 := by
    rintro _ ⟨z, hz, rfl⟩
    have := congrArg Subtype.val (hD.2 z hz)
    simpa using this
  have hab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    rintro _ ⟨z, hz, rfl⟩ _ ⟨z', hz', rfl⟩
    have := congrArg Subtype.val (comm_of_isElemAbelian' hD hz hz')
    simpa using this
  have hcE : Nat.card E = 9 := by
    rw [hE, Subgroup.card_map_of_injective co3P.subtype_injective, hc]
  have hcen : ∀ a ∈ Subgroup.centralizer (D : Set co3P),
      (a : Equiv.Perm (Fin 276)) ∈ Subgroup.centralizer (E : Set (Equiv.Perm (Fin 276))) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨z, hz, rfl⟩
    have := congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 ha z hz)
    simpa using this
  intro a ha b hb ⟨m, hm⟩ ⟨m', hm'⟩
  obtain ⟨n, hn⟩ := (Classical.choose_spec co3Twist_spec).2.2 E hEP h3 hab hcE a a.2 b b.2
    (hcen a ha) (hcen b hb) ⟨m, by simpa using congrArg Subtype.val hm⟩
    ⟨m', by simpa using congrArg Subtype.val hm'⟩
  exact ⟨n, Subtype.ext (by simpa using hn)⟩

theorem i1017CoThreeTwist_holds :
    I1017CoThreeTwist := by
  have hb0 : Nonempty (CFSG.Blueprint.NativeSporadic.Co3 ≃*
      (TauCeti.CFSGIndex.sporadic .Co3).Group) := CFSG.Sporadic.Bridge.Co3.nonempty_mulEquiv
  obtain ⟨b⟩ := hb0
  have hbr : Nonempty (↥co3P ≃* (TauCeti.CFSGIndex.sporadic .Co3).Group) :=
    ⟨co3PermEquiv.symm.trans b⟩
  refine noTwistRank_of_model (s := .Co3) (r := 3) (X := ↥co3P) hbr ?_
  intro E hE hcard T hT hET
  refine noTwist_of_closed (r := 3) (by norm_num) ?_ E hE hcard T hT hET
  refine closed_of_sylow (r := 3) P3syl ?_
  intro E' D hEP _ _ hDE hDc
  exact closed_of_le_P3 D (hDE.trans hEP) (CFSG.Open.IsElemAbelian.mono ‹_› hDE)
    (by simpa using hDc)

end CFSG.LocalAnalysis.GLTheoremA.H1017
