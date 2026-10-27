module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.JointQuotientAction
public import CFSG.LocalAnalysis.RankThreeUC.ProofSupport.CoprimeQuotientFaithfulness.CoprimeQuotientFaithfulness
public import CFSG.LocalAnalysis.RankThreeUC.Section5.SstarCoprimeStructure
public import CFSG.LocalAnalysis.RankThreeUC.Section5.Context
import all CFSG.LocalAnalysis.RankThreeUC.Section5.Context
public import CFSG.GroupTheory.CoprimeActionSupport.NormalizingJoinCardDividesProduct

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.JointFaithful

open CFSG.LocalAnalysis.RankThreeUC.Section5 CFSG.LocalAnalysis.RankThreeUC.Section5.JointQuotientAction

theorem solvable_sup {M : Type*} [Group M] (N B : Subgroup M)
    (hB : B ≤ Subgroup.normalizer (N : Set M)) [Group.IsSolvable N] (hc : IsMulCommutative B) :
    Group.IsSolvable ↥(N ⊔ B) := by
  haveI : (N.subgroupOf (N ⊔ B)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
    exact sup_le Subgroup.le_normalizer hB
  haveI : Group.IsSolvable (N.subgroupOf (N ⊔ B)) :=
    solvable_of_solvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe (le_sup_left : N ≤ N ⊔ B)).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe (le_sup_left : N ≤ N ⊔ B)).injective
  have hQ : Group.IsSolvable ((N ⊔ B : Subgroup M) ⧸ N.subgroupOf (N ⊔ B)) := by
    apply isSolvable_of_comm
    have key : ∀ x : ↥(N ⊔ B), ∃ b : B, (QuotientGroup.mk x : (N ⊔ B : Subgroup M) ⧸
        N.subgroupOf (N ⊔ B)) = QuotientGroup.mk ⟨b.1, (le_sup_right : B ≤ N ⊔ B) b.2⟩ := by
      intro x
      have hx := x.2
      rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left N B hB] at hx
      obtain ⟨n, hn, b, hb, hnb⟩ := hx
      refine ⟨⟨b, hb⟩, ?_⟩
      rw [QuotientGroup.eq]
      show _ ∈ N
      have : (x : M) = n * b := hnb.symm
      show ((x⁻¹ * ⟨b, _⟩ : ↥(N ⊔ B)) : M) ∈ N
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
      rw [this]
      simpa [mul_assoc] using (Subgroup.mem_normalizer_iff''.mp (hB hb) n⁻¹).mp (N.inv_mem hn)
    intro a c
    induction a using QuotientGroup.induction_on with | _ a => ?_
    induction c using QuotientGroup.induction_on with | _ c => ?_
    obtain ⟨b1, e1⟩ := key a
    obtain ⟨b2, e2⟩ := key c
    rw [e1, e2, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact congrArg (fun z : B => (⟨z.1, (le_sup_right : B ≤ N ⊔ B) z.2⟩ : ↥(N ⊔ B)))
      (hc.is_comm.comm b1 b2)
  exact solvable_of_ker_le_range (N.subgroupOf (N ⊔ B)).subtype
    (QuotientGroup.mk' (N.subgroupOf (N ⊔ B))) (by
      intro x hx
      rw [QuotientGroup.ker_mk'] at hx
      exact ⟨⟨x, hx⟩, rfl⟩)

variable {G : Type} [Group G] [Finite G]

theorem solvable {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (h : ExtraspecialBinaryActionCounterexample G p P T B e ρ) : Group.IsSolvable (joint P T B) := by
  haveI := IsPGroup.isNilpotent (SstarQuotientFaithful.isPGroup h)
  haveI : Group.IsSolvable (Sstar P T B) := inferInstance
  refine solvable_sup _ _ (SstarCoprimeStructure.normalizes h) ?_
  rw [BstarFaithful.range_eq h.oddPrimeClassTwoAction]
  refine ⟨⟨?_⟩⟩
  rintro ⟨_, ⟨x, rfl⟩⟩ ⟨_, ⟨y, rfl⟩⟩
  have := h.oddPrimeClassTwoAction.setting.abelian.is_comm.comm x y
  exact Subtype.ext (by simp [← map_mul, this])

theorem kGroup {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (h : ExtraspecialBinaryActionCounterexample G p P T B e ρ) : CFSG.Open.IsKGroup (joint P T B) := by
  haveI := solvable h
  intro K L hLK hN hsimp ⟨a, b, hab⟩
  exfalso
  haveI : Group.IsSolvable (K ⧸ L.subgroupOf K) := inferInstance
  exact hab ((IsSimpleGroup.comm_iff_isSolvable (G := K ⧸ L.subgroupOf K)).2 inferInstance a b)

theorem faithful {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    [Fact p.Prime] [Fact (⁅⁅P, P⁆, P⁆ = ⊥)] [Fact (Monoid.exponent ↥P = p)]
    (h : ExtraspecialBinaryActionCounterexample G p P T B e ρ) (hpi : p ∉ piOf B) :
    Nat.Coprime (Nat.card (joint P T B)) p ∧ Function.Injective (rep p (joint P T B)) := by
  have hp : p.Prime := h.oddPrimeClassTwoAction.setting.prime
  have hcop : Nat.Coprime (Nat.card (joint P T B)) p := by
    have hd := CFSG.GroupTheory.CoprimeActionSupport.NormalizingJoinCardDividesProduct.card_dvd_product
      (Sstar P T B) (Bstar P B) (SstarCoprimeStructure.normalizes h)
    refine Nat.Coprime.coprime_dvd_left hd (Nat.Coprime.mul_left ?_ ?_)
    · obtain ⟨n, hn⟩ := (SstarQuotientFaithful.isPGroup h).exists_card_eq
      rw [hn]
      refine Nat.Coprime.pow_left _ ?_
      have := h.oddPrimeClassTwoAction.setting.odd
      exact (Nat.coprime_primes Nat.prime_two hp).2 (by rintro rfl; exact absurd this (by decide))
    · rw [BstarFaithful.card_eq h.oddPrimeClassTwoAction h.faithfulBinaryIrreducibleAction]
      exact ((Nat.Prime.coprime_iff_not_dvd hp).2 fun hd => hpi (by simp only [piOf, Set.mem_setOf_eq]; exact ⟨hp, hd⟩)).symm
  refine ⟨hcop, rep_injective_of_quotientHom p _ ?_⟩
  exact CFSG.LocalAnalysis.RankThreeUC.ProofSupport.CoprimeQuotientFaithfulness.injective hp h.extraspecial
    h.oddPrimeClassTwoAction.setting.exponent _ hcop

end CFSG.LocalAnalysis.RankThreeUC.Section5.JointFaithful
