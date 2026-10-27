module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieI5LowCyc
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieI5LowTw
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6TwMain
public import CFSG.HardMathSupport.Lang.E6Descent.RankE6
public import CFSG.Adapters.TauCetiLieModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.HardMathSupport.Lang.E6Descent (exists_elemAbelian_243_E6 exists_elemAbelian_of_mulEquiv)


theorem pRank_ge_of_isElemAbelian {G : Type} [Group G] [Finite G] {p k : ℕ} (hp : p.Prime)
    {E : Subgroup G} (hE : CFSG.Open.IsElemAbelian p E) (hk : p ^ k ≤ Nat.card E) :
    k ≤ CFSG.Open.pRank p (⊤ : Subgroup G) := by
  have : Fact p.Prime := ⟨hp⟩
  have hP : IsPGroup p E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 (x : G) x.2)⟩
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card).1 hP
  have hkj : k ≤ j := (Nat.pow_le_pow_iff_right hp.one_lt).1 (hj ▸ hk)
  exact le_trans hkj (CFSG.SectionRank.le_pRank hp.one_lt le_top hE hj)

theorem pRank_eq_zero_of_not_dvd {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (H : Subgroup G) (hH : ¬ p ∣ Nat.card H) : CFSG.Open.pRank p H = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  refine Nat.le_zero.1 (CFSG.SectionRank.pRank_le hp.one_lt (k := 0) fun E hEH hE => ?_)
  rw [pow_zero]
  have hbot : E = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    by_contra hx1
    have hord : orderOf x = p := orderOf_eq_prime (by simpa using hE.2 x hx) hx1
    have h1 : p ∣ Nat.card E := by
      have := orderOf_dvd_natCard (⟨x, hx⟩ : E)
      rwa [Subgroup.orderOf_mk, hord] at this
    exact hH (h1.trans (Subgroup.card_dvd_of_le hEH))
  rw [hbot, Subgroup.card_bot]

theorem three_ne_char {q : TauCeti.PrimePower} (h : 3 ∣ q.card - 1 ∨ 3 ∣ q.card + 1) :
    3 ≠ q.p := by
  intro h3p
  have hf : 0 < q.exponent := q.exponent_pos
  have hcard : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  rw [← h3p] at hcard
  rw [hcard] at h
  have hN : 0 < 3 ^ q.exponent := by positivity
  have h3f : 3 ∣ 3 ^ q.exponent := dvd_pow_self 3 hf.ne'
  generalize 3 ^ q.exponent = N at h h3f hN
  rcases h with h | h <;> omega

theorem five_le_pRank_E6 {K : Type} [Group K] [Finite K] {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.E6 q).Valid) (h3 : 3 ∣ q.card - 1)
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie ⟨.E6 q, hv⟩).Group) :
    5 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (K ⧸ Subgroup.center K)) := by
  obtain ⟨E, hE, hcard⟩ := exists_elemAbelian_243_E6 q hv h3
  obtain ⟨E', hE', hcard'⟩ := exists_elemAbelian_of_mulEquiv e E hE
  exact pRank_ge_of_isElemAbelian Nat.prime_three hE' (k := 5) (by rw [hcard']; norm_num; omega)

theorem five_le_pRank_twistedE6 {K : Type} [Group K] [Finite K] {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid) (h3 : 3 ∣ q.card + 1)
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group) :
    5 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (K ⧸ Subgroup.center K)) := by
  obtain ⟨E, hE, hcard⟩ := exists_elemAbelian_243_twistedE6 q hv h3
  obtain ⟨E', hE', hcard'⟩ := exists_elemAbelian_of_mulEquiv e E hE
  exact pRank_ge_of_isElemAbelian Nat.prime_three hE' (k := 5) (by rw [hcard']; norm_num; omega)

theorem bound_E6 (hGA : CFSG.Open.GriessAllModelsStatement) {K : Type} [Group K] [Finite K]
    (hK : CFSG.Open.IsQuasisimple K) {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.E6 q).Valid) (h3 : 3 ∣ q.card - 1)
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie ⟨.E6 q, hv⟩).Group) :
    5 + CFSG.Open.pRank 3 (Subgroup.center K) ≤ CFSG.Open.pRank 3 (⊤ : Subgroup K) := by
  have hne : 3 ≠ q.p := three_ne_char (Or.inl h3)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  by_cases hZ : 3 ∣ Nat.card (Subgroup.center K)
  · have hX : CFSG.Models.LieModel (TauCeti.CFSGIndex.lie ⟨.E6 q, hv⟩).Group .E6 0 q.p q.exponent :=
      CFSG.Models.lieModel_of_namesTag (t := .E6) (p := q.p) (f := q.exponent)
        ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.E6 q, hv⟩ ⟨rfl, rfl⟩ (MulEquiv.refl _)
    have hm : CFSG.Models.LieModel (K ⧸ Subgroup.center K) .E6 0 q.p q.exponent :=
      CFSG.Models.lieModel_of_namesTag (t := .E6) (p := q.p) (f := q.exponent)
        ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.E6 q, hv⟩ ⟨rfl, rfl⟩ e
    have hZ1 := pRank_center_le_one hGA hK e hX (Or.inr (Or.inr (Or.inl rfl)))
      Nat.prime_three (by norm_num) hne
    have hBP := CFSG.HardMathSupport.Timmesfeld.Tables.T1b.blueprintLieModel_of_models hm
    have h3' : 3 ∣ q.p ^ q.exponent - 1 := by rw [← hcard]; exact h3
    have h6 := (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.e6RankLowerUntw K 0 q.p q.exponent
      hBP h3').1 hZ
    omega
  · have hZ0 := pRank_eq_zero_of_not_dvd Nat.prime_three (Subgroup.center K) hZ
    have h5 := five_le_pRank_E6 hv h3 e
    rw [CFSG.SectionRank.pRank_quotient_eq (Subgroup.center K) hZ] at h5
    omega

theorem bound_twistedE6 (hGA : CFSG.Open.GriessAllModelsStatement) {K : Type} [Group K]
    [Finite K] (hK : CFSG.Open.IsQuasisimple K) {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid) (h3 : 3 ∣ q.card + 1)
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group) :
    5 + CFSG.Open.pRank 3 (Subgroup.center K) ≤ CFSG.Open.pRank 3 (⊤ : Subgroup K) := by
  have hne : 3 ≠ q.p := three_ne_char (Or.inr h3)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  by_cases hZ : 3 ∣ Nat.card (Subgroup.center K)
  · have hX : CFSG.Models.LieModel (TauCeti.CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group .twistedE6 0
        q.p q.exponent :=
      CFSG.Models.lieModel_of_namesTag (t := .twistedE6) (p := q.p) (f := q.exponent)
        ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.twistedE6 q, hv⟩ ⟨rfl, rfl⟩ (MulEquiv.refl _)
    have hm : CFSG.Models.LieModel (K ⧸ Subgroup.center K) .twistedE6 0 q.p q.exponent :=
      CFSG.Models.lieModel_of_namesTag (t := .twistedE6) (p := q.p) (f := q.exponent)
        ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.twistedE6 q, hv⟩ ⟨rfl, rfl⟩ e
    have hZ1 := pRank_center_le_one hGA hK e hX (Or.inr (Or.inr (Or.inr rfl)))
      Nat.prime_three (by norm_num) hne
    have hBP := CFSG.HardMathSupport.Timmesfeld.Tables.T1b.blueprintLieModel_of_models hm
    have h3' : 3 ∣ q.p ^ q.exponent + 1 := by rw [← hcard]; exact h3
    have h6 := (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.e6RankLowerTw K 0 q.p q.exponent
      hBP h3').1 hZ
    omega
  · have hZ0 := pRank_eq_zero_of_not_dvd Nat.prime_three (Subgroup.center K) hZ
    have h5 := five_le_pRank_twistedE6 hv h3 e
    rw [CFSG.SectionRank.pRank_quotient_eq (Subgroup.center K) hZ] at h5
    omega

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
