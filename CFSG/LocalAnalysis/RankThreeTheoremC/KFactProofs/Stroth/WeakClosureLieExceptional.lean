module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureCases
public import CFSG.RankThree.PartOne.CTP.StrongPG2
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureVacuous

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.StrongP
open scoped commutatorElement

section Transport

variable {K : Type} [Group K] [Finite K] {p f : ℕ}

theorem wcE_wcOn_of_untwisted [Fact p.Prime] {τ : Tag}
    (hnc : ∀ (F : Type) [Field F] [Finite F] [CharP F p], HasNoncommPair p (AdjointQuotient τ F))
    (h : UntwistedChevalleyModel K τ (p ^ f)) : WCOn p K := by
  obtain ⟨F, hF, hFin, hcard, ⟨e⟩⟩ := h
  have hchar : CharP F p := by
    have := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hcard])
  haveI : Finite (AdjointQuotient τ F) := Finite.of_equiv K e.toEquiv
  exact WCOn.of_mulEquiv e (WCOn.of_hasNoncommPair (hnc F))

end Transport


section A2Pair

variable {τ : Tag} {K : Type} [Field K]

theorem wcE_xUnit_not_commute (h2 : (2 : K) ≠ 0) {i j : Fin τ.rank}
    (hij : τ.cartan i j = -1) (hji : τ.cartan j i = -1) :
    ¬ Commute (xUnit τ K i 1) (xUnit τ K j 1) := by
  intro hc
  have h1 := (a2_simple_root_commutatorElement K hij hji 1 1).1
  rw [commutatorElement_eq_one_iff_commute.2 hc, mul_one, eq_comm, mul_inv_eq_one,
    mul_eq_left] at h1
  have hv := congrArg (fun g : (Module.End K (RootModule τ K))ˣ =>
    (g : Module.End K (RootModule τ K)) (hVec τ K j)) h1
  simp only [coe_xUnit, Units.val_one, Module.End.one_apply] at hv
  rw [CFSG.TauCetiBridge.Minuscule.xOp_hVec' K j j 1] at hv
  have key := congrArg (fun v : RootModule τ K => v (Sum.inr ⟨Pi.single j 1, IsRoot.basis j⟩)) hv
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, hVec_coeff, rootVec_coeff,
    if_true, zero_add, Tag.cartan_self] at key
  norm_num at key
  exact h2 key

variable [Finite K] {p : ℕ} [CharP K p]

theorem wcE_hasNoncommPair_adjointGroup (h2 : (2 : K) ≠ 0) {i j : Fin τ.rank}
    (hij : τ.cartan i j = -1) (hji : τ.cartan j i = -1) :
    HasNoncommPair p (adjointGroup τ K) := by
  refine ⟨⟨xUnit τ K i 1, xUnit_mem_adjointGroup i 1⟩, ⟨xUnit τ K j 1, xUnit_mem_adjointGroup j 1⟩,
    ?_, ?_, ?_, isPGroup_closure_xUnit τ i j⟩
  · exact Subtype.ext (by simpa using xUnit_pow_char (K := K) (p := p) τ i)
  · exact Subtype.ext (by simpa using xUnit_pow_char (K := K) (p := p) τ j)
  · intro h
    exact wcE_xUnit_not_commute h2 hij hji (congrArg Subtype.val h)

theorem wcE_hasNoncommPair_adjointQuotient (hp : p.Prime) (hp2 : p ≠ 2) {i j : Fin τ.rank}
    (hij : τ.cartan i j = -1) (hji : τ.cartan j i = -1) :
    HasNoncommPair p (AdjointQuotient τ K) := by
  have h2 : (2 : K) ≠ 0 := by
    haveI : Fact p.Prime := ⟨hp⟩
    exact Ring.two_ne_zero (by rw [ringChar.eq K p]; exact hp2)
  refine HasNoncommPair.map (QuotientGroup.mk' (Subgroup.center ↥(adjointGroup τ K)))
    ((MonoidHom.ker_eq_bot_iff _).1 ?_) (wcE_hasNoncommPair_adjointGroup h2 hij hji)
  rw [QuotientGroup.ker_mk', center_adjointGroup_eq_bot]

end A2Pair

theorem wcOn_chevalley_untwisted {K : Type} [Group K] [Finite K]
    {t : CFSG.Open.StatedLieTag} {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (ht : t = .G2 ∨ t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8)
    (h : CFSG.Blueprint.ChevalleyExceptionalModel K t p f) : WCOn p K := by
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · exact wcE_wcOn_of_untwisted (τ := .G2) (fun F _ _ _ => hasNoncommPair_adjointQuotient_G2) h.2
  · exact wcE_wcOn_of_untwisted (τ := .F4)
      (fun F _ _ _ => wcE_hasNoncommPair_adjointQuotient (i := ⟨0, by decide⟩) (j := ⟨1, by decide⟩)
        Fact.out hp2 (by decide) (by decide)) h.2
  · exact wcE_wcOn_of_untwisted (τ := .E6)
      (fun F _ _ _ => wcE_hasNoncommPair_adjointQuotient (i := ⟨0, by decide⟩) (j := ⟨2, by decide⟩)
        Fact.out hp2 (by decide) (by decide)) h.2
  · exact wcE_wcOn_of_untwisted (τ := .E7)
      (fun F _ _ _ => wcE_hasNoncommPair_adjointQuotient (i := ⟨0, by decide⟩) (j := ⟨2, by decide⟩)
        Fact.out hp2 (by decide) (by decide)) h.2
  · exact wcE_wcOn_of_untwisted (τ := .E8)
      (fun F _ _ _ => wcE_hasNoncommPair_adjointQuotient (i := ⟨0, by decide⟩) (j := ⟨2, by decide⟩)
        Fact.out hp2 (by decide) (by decide)) h.2

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
