module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.JointFaithful
public import CFSG.LocalAnalysis.RankThreeUC.Section5.FixedKernel
public import CFSG.LocalAnalysis.RankThreeUC.ProofSupport.SquarefreeAbelianCentrality.SquarefreeAbelianCentrality
public import CFSG.GroupTheory.CoprimeActionSupport.FiniteCyclicPrimeSylowsComplement
public import CFSG.LocalAnalysis.RankThreeUC.Section5.CentralizerEqCenterAndActorCyclicAndPrimeCoreCyclic
public import CFSG.LocalAnalysis.RankThreeUC.Section5.Context
import all CFSG.LocalAnalysis.RankThreeUC.Section5.Context

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.AbelianCentrality

open CFSG.LocalAnalysis.RankThreeUC.Section5 CFSG.LocalAnalysis.RankThreeUC.Section5.JointQuotientAction

variable {G : Type} [Group G] [Finite G]

theorem centralizes {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    [Fact p.Prime] [Fact (⁅⁅P, P⁆, P⁆ = ⊥)] [Fact (Monoid.exponent ↥P = p)]
    (h : ExtraspecialBinaryActionCounterexample G p P T B e ρ) (hpi : p ∉ piOf B)
    (U : Subgroup (MulAut ↥P)) [IsMulCommutative U] (hUS : U ≤ Sstar P T B)
    (hN : Bstar P B ≤ Subgroup.normalizer (U : Set (MulAut ↥P))) :
    Bstar P B ≤ Subgroup.centralizer (U : Set (MulAut ↥P)) := by
  classical
  have hp : p.Prime := h.oddPrimeClassTwoAction.setting.prime
  have hcycB : IsCyclic B := (centralizer_eq_center_and_actor_cyclic_and_primeCore_cyclic h).2.1
  have hsfB : Squarefree (Nat.card B) := by
    refine CFSG.GroupTheory.CoprimeActionSupport.FiniteCyclicPrimeSylowsComplement.squarefree_card (E := B) ?_
    intro q hq hqd
    have hqpi : q ∈ piOf B := ⟨hq, hqd⟩
    have h1 := h.oddPrimeClassTwoAction.exponent_Or q hqpi
    unfold CFSG.Open.pCoreOf at h1
    exact (Monoid.exponent_eq_of_mulEquiv
      (Subgroup.equivMapOfInjective (CFSG.Open.pCore q B) B.subtype B.subtype_injective)).trans h1
  have hcardBs : Nat.card (Bstar P B) = Nat.card B := BstarFaithful.card_eq h.oddPrimeClassTwoAction h.faithfulBinaryIrreducibleAction
  have hcycBs : IsCyclic (Bstar P B) := by
    have : IsCyclic (BstarFaithful.bAction h.oddPrimeClassTwoAction).range :=
      isCyclic_of_surjective (BstarFaithful.bAction h.oddPrimeClassTwoAction).rangeRestrict
        (MonoidHom.rangeRestrict_surjective _)
    rwa [← BstarFaithful.range_eq h.oddPrimeClassTwoAction] at this
  set H := joint P T B with hH
  set C : Subgroup H := (Bstar P B).subgroupOf H with hC
  set E : Subgroup H := U.subgroupOf H with hE
  have hBH : Bstar P B ≤ H := Bstar_le_joint P T B
  have hUH : U ≤ H := hUS.trans (Sstar_le_joint P T B)
  have hCeq : Nat.card C = Nat.card B := by
    rw [← hcardBs]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBH).toEquiv
  have hcycC : IsCyclic C := by
    haveI := hcycBs
    exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hBH).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hBH).symm.surjective
  have hcomm : IsMulCommutative E := ⟨⟨fun a b => by
    have := (inferInstance : IsMulCommutative U).is_comm.comm ⟨a.1.1, a.2⟩ ⟨b.1.1, b.2⟩
    apply Subtype.ext; apply Subtype.ext
    simpa using congrArg Subtype.val this⟩⟩
  have hfix : ∀ c ∈ C, c ≠ 1 → LinearMap.ker (rep p H c - LinearMap.id) = (⊥ : Submodule (ZMod p) _) := by
    intro c hc hc1
    have hc' : (c : MulAut ↥P) ∈ Bstar P B := hc
    rw [BstarFaithful.range_eq h.oddPrimeClassTwoAction] at hc'
    obtain ⟨b, hb⟩ := hc'
    have hbc : bToJoint h.oddPrimeClassTwoAction b = c := Subtype.ext (by rw [bToJoint_apply]; exact hb)
    have hb1 : b ≠ 1 := by
      rintro rfl
      exact hc1 (by rw [← hbc, map_one])
    rw [← hbc]
    exact FixedKernel.kernel_eq_bot h hpi b hb1
  have hCE : C ≤ Subgroup.normalizer (E : Set H) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have := (Subgroup.mem_normalizer_iff.mp (hN hc)) (x : MulAut ↥P)
    exact this
  have hEF : (Nat.card E : ZMod p) ≠ 0 := by
    have hU2 : IsPGroup 2 U := (SstarQuotientFaithful.isPGroup h).of_injective
      (Subgroup.inclusion hUS) (Subgroup.inclusion_injective hUS)
    have hE2 : IsPGroup 2 E := hU2.of_equiv (Subgroup.subgroupOfEquivOfLe hUH).symm
    obtain ⟨n, hn⟩ := hE2.exists_card_eq
    rw [hn, Nat.cast_pow]
    refine pow_ne_zero _ ?_
    intro h0
    have : p ∣ 2 := by
      have := (ZMod.natCast_eq_zero_iff 2 p).1 (by exact_mod_cast h0)
      exact this
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this
    exact absurd h.oddPrimeClassTwoAction.setting.odd (by rw [this]; decide)
  have hCF : (Nat.card C : ZMod p) ≠ 0 := by
    rw [hCeq]
    intro h0
    exact hpi ⟨hp, (ZMod.natCast_eq_zero_iff _ p).1 h0⟩
  have key := CFSG.LocalAnalysis.RankThreeUC.ProofSupport.SquarefreeAbelianCentrality.centralizes
    (rep p H) (JointFaithful.faithful h hpi).2 C (hCeq ▸ hsfB) hfix E hCE hEF hCF
  intro x hx u hu
  have := Subgroup.mem_centralizer_iff.mp
    (key (show (⟨x, hBH hx⟩ : H) ∈ C from hx)) ⟨u, hUH hu⟩ (show (⟨u, hUH hu⟩ : H) ∈ E from hu)
  simpa using congrArg Subtype.val this

end CFSG.LocalAnalysis.RankThreeUC.Section5.AbelianCentrality
