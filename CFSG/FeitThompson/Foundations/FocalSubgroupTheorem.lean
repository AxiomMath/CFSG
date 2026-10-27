module

public import CFSG.FeitThompson.Foundations.FocalGeneratorSet
import CFSG.FeitThompson.Foundations.TransferFocalPowerMap

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup QuotientGroup
open scoped IsMulCommutative

variable {G : Type*} [Group G] {p : ℕ}

theorem focalSubgroup_le_inf_commutator (P : Subgroup G) :
    focalSubgroup P ≤ P ⊓ _root_.commutator G :=
  le_inf (focalSubgroup_le P) (focalSubgroup_le_commutator P)

theorem inf_commutator_le_focalSubgroup [Fact p.Prime] [Finite G] {P : Subgroup G}
    (hP : Nat.card P = p ^ (Nat.card G).factorization p) :
    P ⊓ _root_.commutator G ≤ focalSubgroup P := by
  obtain ⟨T, hT, -⟩ := P.exists_isComplement_right 1
  have hfin : Finite T := finite_of_isComplement_coe hT
  have hnd : ¬ p ∣ P.index := by
    have h := (Sylow.ofCard P hP).not_dvd_index
    rwa [Sylow.coe_ofCard] at h
  obtain ⟨n, hn⟩ := ((IsPGroup.of_card hP).to_quotient (focalSubgroupOf P)).exists_card_eq
  have hcop : (Nat.card (P ⧸ focalSubgroupOf P)).Coprime P.index :=
    hn ▸ Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hnd)
  rintro u ⟨huP, huG⟩
  have hker : transversalTransferHom hT (mk' (focalSubgroupOf P)) u = 1 :=
    MonoidHom.mem_ker.1 (Abelianization.commutator_subset_ker _ huG)
  have hpow := transversalTransferHom_focalSubgroupOf_apply_eq_pow hT ⟨u, huP⟩
  rw [hker] at hpow
  have h1 : mk' (focalSubgroupOf P) ⟨u, huP⟩ = 1 :=
    (powCoprime hcop).injective (by rw [powCoprime_apply, powCoprime_one, ← hpow])
  have h2 := (QuotientGroup.eq_one_iff _).1 h1
  rwa [focalSubgroupOf_def, mem_subgroupOf] at h2

theorem inf_commutator_eq_focalSubgroup [Fact p.Prime] [Finite G] {P : Subgroup G}
    (hP : Nat.card P = p ^ (Nat.card G).factorization p) :
    P ⊓ _root_.commutator G = focalSubgroup P :=
  le_antisymm (inf_commutator_le_focalSubgroup hP) (focalSubgroup_le_inf_commutator P)

theorem inf_commutator_eq_closure_focalGeneratorSet [Fact p.Prime] [Finite G] {P : Subgroup G}
    (hP : Nat.card P = p ^ (Nat.card G).factorization p) :
    P ⊓ _root_.commutator G = closure (focalGeneratorSet P) := by
  rw [closure_focalGeneratorSet, inf_commutator_eq_focalSubgroup hP]

theorem sylow_inf_commutator_eq_focalSubgroup [Fact p.Prime] [Finite G] (P : Sylow p G) :
    (P : Subgroup G) ⊓ _root_.commutator G = focalSubgroup (P : Subgroup G) :=
  inf_commutator_eq_focalSubgroup P.card_eq_multiplicity

theorem inf_commutator_subgroupOf_eq_focalSubgroupOf [Fact p.Prime] [Finite G] {P : Subgroup G}
    (hP : Nat.card P = p ^ (Nat.card G).factorization p) :
    (P ⊓ _root_.commutator G).subgroupOf P = focalSubgroupOf P := by
  rw [inf_commutator_eq_focalSubgroup hP, focalSubgroupOf_def]

theorem index_inf_commutator_eq_natCard_quotient_focalSubgroupOf [Fact p.Prime] [Finite G]
    {P : Subgroup G} (hP : Nat.card P = p ^ (Nat.card G).factorization p) :
    (P ⊓ _root_.commutator G).relIndex P = Nat.card (P ⧸ focalSubgroupOf P) := by
  rw [Subgroup.relIndex, inf_commutator_subgroupOf_eq_focalSubgroupOf hP, Subgroup.index]

end CFSG.FeitThompson
