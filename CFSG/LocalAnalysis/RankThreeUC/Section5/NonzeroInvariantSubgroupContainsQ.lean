module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.DeltaTransitivity
public import CFSG.LocalAnalysis.RankThreeUC.Section5.Context
import all CFSG.LocalAnalysis.RankThreeUC.Section5.Context

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.NonzeroInvariantSubgroupContainsQ

open CFSG.LocalAnalysis.RankThreeUC.Section5

variable {G : Type} [Group G] [Finite G]

theorem contains {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (hc : BinaryActionRankCounterexample G p P T B e ρ) {P0 : Subgroup G} (hP0 : P0 ≤ P)
    (hS : twoCoreCommutator T B ≤ Subgroup.normalizer (P0 : Set G))
    (hB : B ≤ Subgroup.normalizer (P0 : Set G)) (hne : P0 ≠ ⊥) :
    P ⊓ Subgroup.centralizer (B : Set G) ≤ P0 := by
  classical
  have hSet := hc.oddPrimeClassTwoAction.setting
  have hel := isElemAbelian_of_binary_rank_counterexample hc
  have hcomm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hel.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hexp : ∀ x ∈ P, x ^ p = 1 := fun x hx => by
    have := Monoid.pow_exponent_eq_one (⟨x, hx⟩ : P)
    rw [hSet.exponent] at this
    exact congrArg Subtype.val this
  have hcop : (Nat.card B).Coprime p := by
    have h19 := (three_lt_pRank_and_prime_not_dvd_card_actor hc).2
    by_contra h
    apply h19
    refine ⟨hSet.prime, ?_⟩
    by_contra hd
    exact h ((Nat.Prime.coprime_iff_not_dvd hSet.prime).2 hd).symm
  have hBP : B ≤ Subgroup.normalizer (P : Set G) := hSet.normB
  obtain ⟨hD0, ⟨hCne, hCb⟩, -⟩ := CanonicalBFixedHyperplane.canonical hc
  have hmeet : P ⊓ Subgroup.centralizer (B : Set G) ⊓ P0 ≠ ⊥ := by
    intro hCE
    have h1 : P0 ≤ ⁅B, P⁆ :=
      CanonicalBFixedHyperplane.le_commutator hSet.prime hcomm hexp hcop hBP hP0 hB hCE
    have hall : ∀ D ∈ Delta p P ρ, P0 ≤ D := by
      intro D hD
      obtain ⟨s, hs, hsD⟩ :=
        DeltaTransitivity.transitive hc _ hD0 D hD
      have hs' := hS hs
      intro x hx
      have hx' : s⁻¹ * x * s⁻¹⁻¹ ∈ P0 :=
        (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hs') x).1 hx
      rw [hsD]
      exact ⟨_, h1 hx', by simp [MulAut.conj_apply]; group⟩
    have htriv : ∀ x ∈ P0, ρ x = 1 := by
      intro x hx
      have htop := (isInternal_hyperplane_fixedSubmodule_of_binary_rank_counterexample hc).submodule_iSup_eq_top
      have : ∀ v ∈ (⊤ : Submodule (ZMod 2) V), ρ x v = v := by
        rw [← htop]
        intro v hv
        refine Submodule.iSup_induction _ (motive := fun v => ρ x v = v) hv ?_ ?_ ?_
        · intro D v hv
          exact (Representation.mem_invariants _ _).1 hv ⟨x, hall D.1 D.2 hx⟩
        · simp
        · intro a b ha hb; simp [ha, hb]
      ext v
      simpa using this v trivial
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have : ρ x = ρ 1 := by rw [htriv x hx, map_one]
    exact (hc.faithfulBinaryIrreducibleAction.faithful this) ▸ Subgroup.one_mem _
  obtain ⟨b0, hb0, hb01⟩ : ∃ b ∈ B, b ≠ 1 := by
    obtain ⟨b, hb⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hc.oddPrimeClassTwoAction.actor_ne_bot
    exact ⟨b, b.2, fun h => hb (Subtype.ext h)⟩
  have hcyc := hc.oddPrimeClassTwoAction.cyclic_centralizer b0 hb0 hb01
  rw [hCb b0 hb0 hb01] at hcyc
  have hcard : Nat.card ↥(P ⊓ Subgroup.centralizer (B : Set G)) ≤ p := by
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
    refine Nat.le_of_dvd hSet.prime.pos (orderOf_dvd_of_pow_eq_one ?_)
    apply Subtype.ext
    exact hexp g.1 (Subgroup.mem_inf.1 g.2).1
  obtain ⟨y, hy⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hmeet
  have hyC : (y : G) ∈ P ⊓ Subgroup.centralizer (B : Set G) := (Subgroup.mem_inf.1 y.2).1
  have hyP0 : (y : G) ∈ P0 := (Subgroup.mem_inf.1 y.2).2
  have hy1 : (y : G) ≠ 1 := fun h => hy (Subtype.ext h)
  have hyp : orderOf (y : G) = p := by
    have hd : orderOf (y : G) ∣ p := orderOf_dvd_of_pow_eq_one (hexp y (Subgroup.mem_inf.1 hyC).1)
    rcases (Nat.dvd_prime hSet.prime).1 hd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hy1
    · exact h
  have hZle : Subgroup.zpowers (y : G) ≤ P ⊓ Subgroup.centralizer (B : Set G) := by
    rw [Subgroup.zpowers_le]; exact hyC
  have hZcard : Nat.card (Subgroup.zpowers (y : G)) = p := by
    rw [Nat.card_zpowers, hyp]
  have heq : Subgroup.zpowers (y : G) = P ⊓ Subgroup.centralizer (B : Set G) :=
    Subgroup.eq_of_le_of_card_ge hZle (by
      haveI : Finite ↥(P ⊓ Subgroup.centralizer (B : Set G)) := inferInstance
      rw [hZcard]; exact hcard)
  rw [← heq, Subgroup.zpowers_le]
  exact hyP0

end CFSG.LocalAnalysis.RankThreeUC.Section5.NonzeroInvariantSubgroupContainsQ
end
