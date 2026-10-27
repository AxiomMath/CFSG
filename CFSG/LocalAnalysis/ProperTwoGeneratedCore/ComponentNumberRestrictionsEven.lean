module

public import CFSG.CharacterTheory.TwoRankLowerBound.RankOneClassification
public import CFSG.LocalAnalysis.ComponentClassification.LocalComponents
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoprimeQuotientRank

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ComponentClassification
open CFSG.TwoRankLowerBound.Helpers

universe u

variable {G : Type u} [Group G] [Finite G]

theorem rank_one_noncyclic_two_group_noncentral_order_four
    (P : Type*) [Group P] [Finite P] (htwo : IsPGroup 2 P)
    (hrank : twoRank P ≤ 1) (hncyclic : ¬ IsCyclic P) :
    ∃ y : P, orderOf y = 4 ∧ y ∉ Subgroup.center P := by
  obtain hcyclic | ⟨exponent, hexponent, ⟨e⟩⟩ :=
    rank_one_two_group_cyclic_or_quaternion P htwo hrank
  · exact (hncyclic hcyclic).elim
  let n := 2 ^ (exponent - 2)
  have hn : 2 ≤ n := by
    change 2 ≤ 2 ^ (exponent - 2)
    exact (by decide : 2 ≤ 2 ^ 1).trans (Nat.pow_le_pow_right (by decide) (by omega))
  let : NeZero n := ⟨by omega⟩
  let y := e.symm (QuaternionGroup.xa (0 : ZMod (2 * n)))
  refine ⟨y, (e.symm.orderOf_eq _).trans (QuaternionGroup.orderOf_xa 0), ?_⟩
  intro hy
  have hcomm := congrArg e (Subgroup.mem_center_iff.mp hy
    (e.symm (QuaternionGroup.a (1 : ZMod (2 * n)))))
  have heq : (1 : ZMod (2 * n)) = -1 := by
    apply QuaternionGroup.xa.inj
    simpa only [map_mul, MulEquiv.apply_symm_apply, y,
      QuaternionGroup.xa_mul_a, QuaternionGroup.a_mul_xa, zero_add,
      zero_sub] using hcomm.symm
  have htwozero : (2 : ZMod (2 * n)) = 0 := by
    calc
      (2 : ZMod (2 * n)) = 1 + 1 := by norm_num
      _ = -1 + 1 := congrArg (fun x : ZMod (2 * n) => x + 1) heq
      _ = 0 := by simp
  have hdiv : 2 * n ∣ 2 := (ZMod.natCast_eq_zero_iff 2 (2 * n)).mp htwozero
  have hsmall := Nat.le_of_dvd (by decide : 0 < 2) hdiv
  omega

theorem commuting_rank_one_noncyclic_two_subgroups_join_rank
    (P Q : Subgroup G) (hP : IsPGroup 2 P) (hQ : IsPGroup 2 Q)
    (hPrank : twoRank P ≤ 1) (hQrank : twoRank Q ≤ 1)
    (hPncyclic : ¬ IsCyclic P) (hQncyclic : ¬ IsCyclic Q)
    (hcomm : ⁅P, Q⁆ = ⊥) : 2 ≤ pRank 2 (P ⊔ Q) := by
  let R := P ⊔ Q
  have hcommute (p : P) (q : Q) : Commute (p : G) (q : G) :=
    Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm p.property)
      q q.property |>.symm
  obtain ⟨p, hporder, hpnoncentral⟩ :=
    rank_one_noncyclic_two_group_noncentral_order_four P hP hPrank hPncyclic
  obtain ⟨q, hqorder, _⟩ :=
    rank_one_noncyclic_two_group_noncentral_order_four Q hQ hQrank hQncyclic
  let a : R := ⟨p, (le_sup_left : P ≤ R) p.property⟩
  let b : R := ⟨q, (le_sup_right : Q ≤ R) q.property⟩
  have haorder : orderOf a = 4 := (Subgroup.orderOf_coe a).symm.trans
    ((Subgroup.orderOf_coe p).trans hporder)
  have hborder : orderOf b = 4 := (Subgroup.orderOf_coe b).symm.trans
    ((Subgroup.orderOf_coe q).trans hqorder)
  have hab : Commute a b := Subtype.ext (hcommute p q)
  have ha2order : orderOf (a ^ 2) = 2 := by rw [orderOf_pow, haorder]; norm_num
  have hb2order : orderOf (b ^ 2) = 2 := by rw [orderOf_pow, hborder]; norm_num
  have hRrank : 2 ≤ twoRank R := by
    by_cases ht : a ^ 2 = b ^ 2
    · have hvorder : orderOf (a * b) = 2 := by
        let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        apply orderOf_eq_prime_iff.mpr
        refine ⟨?_, ?_⟩
        · rw [hab.mul_pow, ht, ← pow_add]
          norm_num
          rw [← hborder, pow_orderOf_eq_one]
        · intro hv
          have hpq : (p : G) * (q : G) = 1 := congrArg Subtype.val hv
          have hpQ : (p : G) ∈ Q := by
            have heq : (p : G) = (q : G)⁻¹ := mul_eq_one_iff_eq_inv.mp hpq
            rw [heq]
            exact Q.inv_mem q.property
          apply hpnoncentral
          apply Subgroup.mem_center_iff.mpr
          intro x
          apply Subtype.ext
          exact (hcommute x ⟨p, hpQ⟩).eq
      have hdistinct : a ^ 2 ≠ a * b := by
        intro heq
        have habval : (p : G) ^ 2 = (p : G) * (q : G) := congrArg Subtype.val heq
        have hpq : (p : G) = (q : G) := by
          apply mul_left_cancel (a := (p : G))
          simpa only [pow_two] using habval
        have hpQ : (p : G) ∈ Q := hpq ▸ q.property
        apply hpnoncentral
        apply Subgroup.mem_center_iff.mpr
        intro x
        apply Subtype.ext
        exact (hcommute x ⟨p, hpQ⟩).eq
      exact two_le_twoRank_of_commuting_involutions R (a ^ 2) (a * b)
        ha2order hvorder hdistinct ((Commute.pow_left (Commute.refl a) 2).mul_right
          (hab.pow_left 2))
    · exact two_le_twoRank_of_commuting_involutions R (a ^ 2) (b ^ 2)
        ha2order hb2order ht (hab.pow_pow 2 2)
  rwa [twoRank, ← pRank_subgroup_eq_internal_top 2 (by decide) R] at hRrank

theorem distinct_even_component_sylow_join_rank
    (L M : Subgroup G) (hL : IsComponentOf L ⊤) (hM : IsComponentOf M ⊤)
    (hne : L ≠ M) (hLeven : Even (Nat.card L)) (hMeven : Even (Nat.card M))
    (T : Sylow 2 L) (U : Sylow 2 M) :
    2 ≤ pRank 2 ((T : Subgroup L).map L.subtype ⊔
      (U : Subgroup M).map M.subtype) := by
  let P := (T : Subgroup L).map L.subtype
  let Q := (U : Subgroup M).map M.subtype
  have hcomm : ⁅P, Q⁆ = ⊥ := by
    apply le_bot_iff.mp
    calc
      ⁅P, Q⁆ ≤ ⁅L, M⁆ := Subgroup.commutator_mono
        (Subgroup.map_subtype_le _) (Subgroup.map_subtype_le _)
      _ = ⊥ := LocalComponents.commute_of_ne L M hL hM hne
  by_cases hPrank : 2 ≤ pRank 2 P
  · exact hPrank.trans (pRank_mono 2 (by decide) le_sup_left)
  by_cases hQrank : 2 ≤ pRank 2 Q
  · exact hQrank.trans (pRank_mono 2 (by decide) le_sup_right)
  have hPrank' : twoRank P ≤ 1 := by
    rw [twoRank, ← pRank_subgroup_eq_internal_top 2 (by decide) P]
    omega
  have hQrank' : twoRank Q ≤ 1 := by
    rw [twoRank, ← pRank_subgroup_eq_internal_top 2 (by decide) Q]
    omega
  let : Group.IsPerfect L := ⟨hL.2.2.1⟩
  let : Group.IsPerfect M := ⟨hM.2.2.1⟩
  have hPncyclic : ¬ IsCyclic P := by
    intro hcyclic
    let := hcyclic
    let e := (T : Subgroup L).equivMapOfInjective L.subtype L.subtype_injective
    exact sylow_two_not_isCyclic_of_perfect L hLeven T
      (isCyclic_of_injective e.toMonoidHom e.injective)
  have hQncyclic : ¬ IsCyclic Q := by
    intro hcyclic
    let := hcyclic
    let e := (U : Subgroup M).equivMapOfInjective M.subtype M.subtype_injective
    exact sylow_two_not_isCyclic_of_perfect M hMeven U
      (isCyclic_of_injective e.toMonoidHom e.injective)
  exact commuting_rank_one_noncyclic_two_subgroups_join_rank P Q
    (T.isPGroup'.map L.subtype) (U.isPGroup'.map M.subtype)
    hPrank' hQrank' hPncyclic hQncyclic hcomm

end CFSG.ProperTwoGeneratedCore
