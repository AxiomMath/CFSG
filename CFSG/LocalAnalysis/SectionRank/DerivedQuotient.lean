module

public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LieType.BorelTits.DerivedQuotient

public section

namespace CFSG.SectionRank

open CFSG.Open CFSG.Blueprint CFSG.LieType.BorelTits

variable {G : Type*} [Group G] [Finite G] {p : ℕ}

theorem exists_isElemAbelian_card_of_le_pRank [hp : Fact p.Prime] {H : Subgroup G} {k : ℕ}
    (hk : k ≤ pRank p H) : ∃ E : Subgroup G, E ≤ H ∧ IsElemAbelian p E ∧ Nat.card E = p ^ k := by
  obtain ⟨E, hEH, hE, hcard⟩ := exists_pRank hp.out.one_lt H
  obtain ⟨F, hF⟩ := Sylow.exists_subgroup_card_pow_prime (G := E) p
    (hcard ▸ pow_dvd_pow p hk)
  have := hE.1
  have hF' : IsElemAbelian p F := ⟨⟨⟨fun a b => Subtype.ext (mul_comm' (a : E) b)⟩⟩,
    fun x _ => Subtype.ext (by rw [Subgroup.coe_pow, hE.2 x x.2, Subgroup.coe_one])⟩
  refine ⟨F.map E.subtype, (Subgroup.map_subtype_le F).trans hEH, isElemAbelian_map hF' _, ?_⟩
  rw [Subgroup.card_map_of_injective Subtype.val_injective, hF]

theorem pRank_derivedCentralQuotient_eq {M Γ : Type} [Group M] [Group Γ] [Finite Γ]
    (H : Subgroup M) [Finite (DerivedCentralQuotient H)] (e : H ≃* Γ) [hp : Fact p.Prime]
    (h : Holds Γ p) (S : Sylow p Γ) (hS : (S : Subgroup Γ) ≤ commutator Γ) :
    pRank p (⊤ : Subgroup (DerivedCentralQuotient H)) =
      pRank p (⊤ : Subgroup (commutator Γ)) := by
  have hc := (h.of_normal_of_coprime_index (coprime_index_commutator S hS)).coprime_card_center
  rw [pRank_top_eq_of_mulEquiv hp.out.one_lt (derivedCentralQuotientEquiv H e),
    pRank_quotient_eq _ fun hdvd => hp.out.one_lt.ne'
      ((Nat.coprime_self p).1 (Nat.Coprime.coprime_dvd_left hdvd hc))]

end CFSG.SectionRank
