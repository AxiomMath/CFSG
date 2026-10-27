module

public import CFSG.LocalAnalysis.RankThreeUC.K37HRCover
public import CFSG.RankThree.PartOne.KP.BExclusion

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K37H

open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.Open (IsElemAbelian)
open CFSG.RankThree.PartOne

theorem K37RCoverRankFour.of_quasisimple_in_centralizer {S C : Type} [Group S] [Group C] {s : S}
    {K : Subgroup (Subgroup.centralizer ({s} : Set S))} (hK : CFSG.IsQuasisimple K)
    (hZ : Nat.card (Subgroup.center K) = 2) (eQ : K ⧸ Subgroup.center K ≃* C)
    (hcov : ∀ (Y : Type) [Group Y] [Finite Y] (f : Y →* C), Function.Surjective f →
      f.ker ≤ Subgroup.center Y → ∃ V : Subgroup Y, IsElemAbelian 3 V ∧ Nat.card V = 3 ^ 4) :
    K37RCoverRankFour S := by
  haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hK.2.1
  have hperf : commutator C = ⊤ :=
    k37R_commutator_eq_top_of_mulEquiv eQ.symm (k37R_commutator_eq_top_of_simple hK.2.2)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite ↥(Subgroup.center ↥K) := Nat.finite_of_card_ne_zero (by rw [hZ]; norm_num)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center ↥K) 2 (by rw [hZ])
  let P : Subgroup S := Subgroup.centralizer ({s} : Set S)
  let Mi : Subgroup S := K.map P.subtype
  let κ : ↥K ≃* ↥Mi := K.equivMapOfInjective P.subtype Subtype.val_injective
  have hzK : (z : ↥K) ∈ Subgroup.center ↥K := z.2
  have hz2 : orderOf (z : ↥K) = 2 := by rw [Subgroup.orderOf_coe]; exact hz
  have hMa : ∀ m ∈ Mi, m * ((κ (z : ↥K) : Mi) : S) = ((κ (z : ↥K) : Mi) : S) * m := by
    intro m hm
    obtain ⟨k, hk, rfl⟩ := hm
    have hc := Subgroup.mem_center_iff.1 hzK ⟨k, hk⟩
    have := congrArg (fun x : ↥K => (((x : ↥K) : P) : S)) hc
    have hκ : ∀ x : ↥K, ((κ x : Mi) : S) = (((x : ↥K) : P) : S) := fun x => rfl
    rw [hκ]
    simpa using this
  have ha : orderOf ((κ (z : ↥K) : Mi) : S) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact hz2
  let φ₀ : ↥Mi →* C :=
    (eQ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K))).comp κ.symm.toMonoidHom
  have hφ₀ : Function.Surjective φ₀ :=
    (eQ.surjective.comp (QuotientGroup.mk'_surjective _)).comp κ.symm.surjective
  have hk : φ₀.ker ≤ Subgroup.center ↥Mi := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 : κ.symm x ∈ Subgroup.center ↥K := by
      have h0 : (QuotientGroup.mk' (Subgroup.center ↥K)) (κ.symm x) = 1 :=
        eQ.injective (by simpa [φ₀] using hx)
      exact (QuotientGroup.eq_one_iff _).1 h0
    rw [Subgroup.mem_center_iff]
    intro g
    have h2 := congrArg κ (Subgroup.mem_center_iff.1 h1 (κ.symm g))
    simpa using h2
  exact K37RCoverRankFour.of_centralizer hcov hperf (a := ((κ (z : ↥K) : Mi) : S)) ha (M := Mi) hMa
    φ₀ hφ₀ hk

theorem k37R_coverRankFour_Sbp
    : K37RCoverRankFour CFSG.Monster.B.Sbp := by
  obtain ⟨s, K, hq, hz, ⟨eQ⟩⟩ := bMonsterData_Sbp
  refine K37RCoverRankFour.of_quasisimple_in_centralizer hq hz eQ ?_
  intro Y _ _ f hf hk
  obtain ⟨V, hV, hVc⟩ := central_cover_of_levi stdLeviIn stdLeviEquiv Y f hf hk
  exact ⟨V, (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 V).mp hV, hVc⟩

theorem k37R_coverRankFour_B
    : K37RCoverRankFour CFSG.Blueprint.NativeSporadic.B :=
  k37R_coverRankFour_Sbp.of_mulEquiv CFSG.Monster.B.CTIB.iotaEquiv

end CFSG.LocalAnalysis.RankThreeUC.S15.K37H
