module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporM24Nine
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporRuNine

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.ThreeOne

open CFSG.Open
open CFSG.RankThree.PartTwo.Sec4.Item434SporGen (FixGen fixGen_of_ex27Check)

theorem glbCore_one_eq_top_of_fixGen_map {K X : Type*} [Group K] [Finite K] [Group X] {p : ℕ}
    (hp : p.Prime) (φ : K ≃* X) {A : Subgroup K} (hA : IsElemAbelian p A)
    (h : FixGen (A.map φ.toMonoidHom)) : GLBCore p 1 A = ⊤ := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨S, hS, hσ⟩ := h
  have hle : Subgroup.closure (φ.symm '' S) ≤ GLBCore p 1 A := by
    rw [Subgroup.closure_le]
    rintro _ ⟨σ, hσS, rfl⟩
    obtain ⟨-, q, hq, hq1, hqσ⟩ := hσ σ hσS
    obtain ⟨a, haA, rfl⟩ := Subgroup.mem_map.1 hq
    have ha1 : a ≠ 1 := fun h1 => hq1 (by rw [h1, map_one])
    have hap : a ^ p = 1 := hA.2 a haA
    have hrank : 1 ≤ CFSG.Open.pRank p (Subgroup.zpowers a) :=
      CFSG.SectionRank.le_pRank hp.one_lt le_rfl (CFSG.Open.isElemAbelian_zpowers hap)
        (by rw [Nat.card_zpowers, orderOf_eq_prime hap ha1, pow_one])
    have hN : Subgroup.normalizer ((Subgroup.zpowers a : Subgroup K) : Set K) ≤ GLBCore p 1 A :=
      le_sSup ⟨Subgroup.zpowers a, Subgroup.zpowers_le.2 haA, hrank, rfl⟩
    have hcomm : a * φ.symm σ = φ.symm σ * a := by
      apply φ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hqσ
    refine hN (Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 ?_))
    rintro y ⟨n, rfl⟩
    exact (Commute.zpow_left (show Commute a (φ.symm σ) from hcomm) n).eq
  rw [eq_top_iff]
  intro k _
  apply hle
  have hk : φ.symm.toMonoidHom (φ k) ∈ (Subgroup.closure S).map φ.symm.toMonoidHom :=
    Subgroup.mem_map_of_mem _ (hS (Subgroup.mem_top _))
  rw [MonoidHom.map_closure] at hk
  simpa using hk

section M24


open CFSG.RankThree.PartTwo.Sec4.Item434SporGen (m24_check rep_m24GenA rep_m24GenB
  factorization_card_m24)

theorem glbCore_one_eq_top_M24 (K : Type) [Group K] [Finite K]
    (hK : Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic .M24).Group)) (A : Subgroup K)
    (hA : IsElemAbelian 3 A) (hc : Nat.card A = 3 ^ 2) : GLBCore 3 1 A = ⊤ := by
  obtain ⟨e₁⟩ := hK
  obtain ⟨e₂⟩ := CFSG.Sporadic.Bridge.M24.nonempty_mulEquiv
  let φ : K ≃* CFSG.Blueprint.NativeSporadic.M24 := e₁.trans e₂.symm
  have : Finite CFSG.Blueprint.NativeSporadic.M24 :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Mathieu.card_M24]; norm_num)
  have h9 : Nat.card (A.map φ.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective φ.injective, hc]
    norm_num
  exact glbCore_one_eq_top_of_fixGen_map Nat.prime_three φ hA
    (fixGen_of_ex27Check rep_m24GenA rep_m24GenB CFSG.Sporadic.Mathieu.m24_eq
      factorization_card_m24 m24_check _ h9)

end M24

section Ru


open CFSG.RankThree.PartTwo.Sec4.Item434SporGen (ru_check factorization_card_ruP)
open CFSG.Sporadic.RuSchreier (ruP ruArr4060 rep_ruA0 rep_ruA1 ruEquivP card_ruP')

theorem glbCore_one_eq_top_Ru (K : Type) [Group K] [Finite K]
    (hK : Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic .Ru).Group)) (A : Subgroup K)
    (hA : IsElemAbelian 3 A) (hc : Nat.card A = 3 ^ 2) : GLBCore 3 1 A = ⊤ := by
  obtain ⟨e₁⟩ := hK
  obtain ⟨e₂⟩ := CFSG.Sporadic.Bridge.Ru.nonempty_mulEquiv
  let φ : K ≃* ruP := (e₁.trans e₂.symm).trans ruEquivP
  have : Finite ruP := Nat.finite_of_card_ne_zero (by rw [card_ruP']; norm_num)
  have h9 : Nat.card (A.map φ.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective φ.injective, hc]
    norm_num
  exact glbCore_one_eq_top_of_fixGen_map Nat.prime_three φ hA
    (fixGen_of_ex27Check (ga := ruArr4060 0) (gb := ruArr4060 1) (X := ruP) rep_ruA0 rep_ruA1
      rfl factorization_card_ruP ru_check _ h9)

end Ru

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.ThreeOne
