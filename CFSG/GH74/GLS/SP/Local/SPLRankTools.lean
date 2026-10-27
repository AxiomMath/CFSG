module

public import CFSG.GH74.Generic.Certificates
public import CFSG.GH74.E2.Shapes
import CFSG.GH74.Generic.AltCerts
import CFSG.GH74.E2.CompCerts
import CFSG.FeitThompson.OddOrderTheorem
import CFSG.CharacterTheory.TwoRankLowerBound.Helpers

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.GLS

private theorem isCyclic_closure_of_card_le_one {G : Type} [Group G] (s : Finset G)
    (hs : s.card ≤ 1) : IsCyclic ↥(Subgroup.closure (s : Set G)) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hs with h0 | h1
  · rw [Finset.card_eq_zero.mp h0, Finset.coe_empty, Subgroup.closure_empty]
    infer_instance
  · obtain ⟨g, rfl⟩ := Finset.card_eq_one.mp h1
    rw [Finset.coe_singleton, ← Subgroup.zpowers_eq_closure]
    infer_instance

theorem rankCertified_one_of_quasisimple {K : Type} [Group K] [Finite K]
    (h : CFSG.IsQuasisimple K) : RankCertified K 1 := by
  obtain ⟨hperf, -, a, b, hab⟩ := h
  have hnt : Nontrivial K := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    refine ⟨⟨x * y, y * x, fun hxy => hab ?_⟩⟩
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hxy]
  have heven : Even (Nat.card K) := by
    by_contra hodd
    exact Group.IsPerfect.not_isSolvable K
      (CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.not_even_iff_odd.mp hodd))
  obtain ⟨S⟩ : Nonempty (Sylow 2 K) := inferInstance
  have hnc : ¬ IsCyclic ↥(S : Subgroup K) :=
    CFSG.TwoRankLowerBound.Helpers.sylow_two_not_isCyclic_of_perfect K heven S
  refine rankCertified_of_not_sectionalTwoRankLE fun hle => hnc ?_
  obtain ⟨s, hs, hcl⟩ := hle (S : Subgroup K) S.isPGroup'
  rw [← hcl]
  exact isCyclic_closure_of_card_le_one s hs

theorem rankCertified_sup_of_commute {X : Type} [Group X] {A K : Subgroup X}
    (hc : ∀ a ∈ A, ∀ k ∈ K, a * k = k * a) (hd : A ⊓ K = ⊥) {a b : ℕ}
    (hA : RankCertified ↥A a) (hK : RankCertified ↥K b) : RankCertified ↥(A ⊔ K) (a + b + 1) := by
  let φ : ↥A × ↥K →* ↥(A ⊔ K) :=
    { toFun := fun p => ⟨(p.1 : X) * (p.2 : X), Subgroup.mul_mem_sup p.1.2 p.2.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun p q => by
        apply Subtype.ext
        have hpq := hc (q.1 : X) q.1.2 (p.2 : X) p.2.2
        calc (((p * q).1 : ↥A) : X) * (((p * q).2 : ↥K) : X)
            = (p.1 : X) * ((q.1 : X) * (p.2 : X)) * (q.2 : X) := by
              simp [mul_assoc]
          _ = (p.1 : X) * ((p.2 : X) * (q.1 : X)) * (q.2 : X) := by rw [hpq]
          _ = ((p.1 : X) * (p.2 : X)) * ((q.1 : X) * (q.2 : X)) := by simp [mul_assoc] }
  have hφ : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨x, y⟩ hxy
    have h1 : (x : X) * (y : X) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hxy)
    have hxK : (x : X) ∈ K := by
      have : (x : X) = (y : X)⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [this]
      exact K.inv_mem y.2
    have hx1 : (x : X) = 1 := by
      have : (x : X) ∈ A ⊓ K := ⟨x.2, hxK⟩
      rwa [hd, Subgroup.mem_bot] at this
    have hy1 : (y : X) = 1 := by
      rw [hx1, one_mul] at h1
      exact h1
    rw [Subgroup.mem_bot]
    exact Prod.ext (Subtype.ext hx1) (Subtype.ext hy1)
  exact (hA.prod hK).of_injective φ hφ

theorem rankCertified_two_of_doubleCoverAlt {K : Type} [Group K] [Finite K] {n : ℕ}
    (hn : 8 ≤ n) (h : IsDoubleCoverOfAlt K n) : RankCertified K 2 := by
  obtain ⟨-, -, ⟨e⟩⟩ := h
  exact (((rankCertified_alternating hn).mono (by norm_num)).of_mulEquiv e.symm).of_quotient
    (center K)

theorem rankCertified_two_of_L34Cover {K : Type} [Group K] [Finite K] (hL : IsL34Quotient K) :
    RankCertified K 2 :=
  ((CFSG.GH74.E2.rank3_L3_4 hL).mono (by norm_num)).of_quotient (center K)

theorem rankCertified_two_of_2M12 {K : Type} [Group K] [Finite K] (h : CFSG.GH74.E2.Shape2M12 K) :
    RankCertified K 2 :=
  ((CFSG.GH74.E2.rank3_M12 h.2.2).mono (by norm_num)).of_quotient (center K)

theorem rankCertified_two_of_2Sz8 {K : Type} [Group K] [Finite K]
    (h : CFSG.GH74.E2.Shape2Sz8 K) : RankCertified K 2 :=
  (CFSG.GH74.E2.rank2_Sz8 h.2.2).of_quotient (center K)

end CFSG.GH74.GLS.SP.Local
