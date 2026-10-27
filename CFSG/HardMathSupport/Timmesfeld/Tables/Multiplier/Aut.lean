module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner centerQuotientOuterHom
  centerQuotient_outer_injective)
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom
  centerQuotientHom_injective)

theorem isInner_of_pElement {J : Type} [Group J] [Finite J] [Group.IsPerfect J] {p : ℕ}
    (hp : p.Prime)
    {φ : MulAut J} (hφ : IsPGroup p (Subgroup.zpowers φ))
    (hN : ¬ p ∣ Nat.card (Outer (J ⧸ Subgroup.center J))) : φ ∈ inner J := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hφ.exists_card_eq
  rw [Nat.card_zpowers] at hk
  let q : Outer J := QuotientGroup.mk' (inner J) φ
  have h1 : orderOf q ∣ p ^ k := hk ▸ orderOf_map_dvd (QuotientGroup.mk' (inner J)) φ
  have h2 : orderOf q ∣ Nat.card (Outer (J ⧸ Subgroup.center J)) := by
    rw [← orderOf_injective (centerQuotientOuterHom J) (centerQuotient_outer_injective J) q]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (p ^ k) (Nat.card (Outer (J ⧸ Subgroup.center J))) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hN)
  have h3 : orderOf q = 1 := Nat.eq_one_of_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd h1 h2)
  exact (QuotientGroup.eq_one_iff φ).1 (orderOf_eq_one_iff.1 h3)

theorem pRank_top_le_factorization {A : Type*} [Group A] [Finite A] {p : ℕ} (hp : p.Prime) :
    CFSG.Open.pRank p (⊤ : Subgroup A) ≤ (Nat.card A).factorization p := by
  obtain ⟨E, -, -, hE⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (⊤ : Subgroup A)
  have hd : p ^ CFSG.Open.pRank p (⊤ : Subgroup A) ∣ Nat.card A := by
    rw [← hE]
    exact Subgroup.card_subgroup_dvd_card E
  exact (hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 hd

theorem pRank_mulAut_le {J : Type} [Group J] [Finite J] [Group.IsPerfect J] {p : ℕ}
    (hp : p.Prime) :
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut J)) ≤
      CFSG.Open.pRank p (⊤ : Subgroup (MulAut (J ⧸ Subgroup.center J))) :=
  CFSG.SectionRank.pRank_top_le_of_injective hp.one_lt (centerQuotientHom J)
    (centerQuotientHom_injective J)

end CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier
