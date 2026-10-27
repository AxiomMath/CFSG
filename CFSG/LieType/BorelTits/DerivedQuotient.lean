module

public import CFSG.LieType.BorelTits.TitsClause
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.LieType.BorelTits

open CFSG.Blueprint

variable {M Γ : Type} [Group M] [Group Γ]

@[expose] noncomputable def commutatorSubgroupEquiv (H : Subgroup M) :
    ↥(⁅H, H⁆ : Subgroup M) ≃* commutator H :=
  ((Subgroup.equivMapOfInjective (commutator H) H.subtype Subtype.val_injective).trans
    (MulEquiv.subgroupCongr (by rw [map_commutator_eq, Subgroup.range_subtype]))).symm

@[expose] noncomputable def commutatorEquiv {H : Type} [Group H] (e : H ≃* Γ) :
    commutator H ≃* commutator Γ :=
  (e.subgroupMap (commutator H)).trans (MulEquiv.subgroupCongr (by
    rw [map_commutator_eq, commutator_def, MonoidHom.range_eq_top.2 e.surjective]))

@[expose] noncomputable def derivedCentralQuotientEquiv (H : Subgroup M) (e : H ≃* Γ) :
    DerivedCentralQuotient H ≃* commutator Γ ⧸ Subgroup.center (commutator Γ) :=
  QuotientGroup.congr _ _ ((commutatorSubgroupEquiv H).trans (commutatorEquiv e))
    (Subgroup.map_center_eq _)

theorem coprime_index_commutator [Finite Γ] {p : ℕ} [Fact p.Prime] (S : Sylow p Γ)
    (hS : (S : Subgroup Γ) ≤ commutator Γ) : Nat.Coprime (commutator Γ).index p := by
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Fact.out]
  intro hdvd
  exact S.not_dvd_index (hdvd.trans (Subgroup.index_dvd_of_le hS))

theorem holds_derivedCentralQuotient [Finite Γ] (H : Subgroup M) (e : H ≃* Γ) {p : ℕ}
    [Fact p.Prime] (h : Holds Γ p) (S : Sylow p Γ) (hS : (S : Subgroup Γ) ≤ commutator Γ) :
    Holds (DerivedCentralQuotient H) p := by
  have hY : Holds (commutator Γ) p :=
    h.of_normal_of_coprime_index (coprime_index_commutator S hS)
  exact (Holds.center_quotient hY).of_mulEquiv (derivedCentralQuotientEquiv H e).symm

theorem holdsTits_derivedCentralQuotient [Finite Γ] (H : Subgroup M) (e : H ≃* Γ) {p : ℕ}
    [Fact p.Prime] (h : Holds Γ p) (hq : IsPGroup p (Γ ⧸ commutator Γ)) :
    HoldsTits (DerivedCentralQuotient H) p := by
  have hY : HoldsTits (commutator Γ) p := holdsTits_of_normal_of_isPGroup_quotient hq h
  exact (HoldsTits.center_quotient hY).of_mulEquiv (derivedCentralQuotientEquiv H e).symm

end CFSG.LieType.BorelTits
