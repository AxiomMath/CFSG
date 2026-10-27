module


public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.GroupTheory.CoprimeActionSupport.FiniteCyclicPrimeSylowsComplement

variable {E : Type} [Group E] [Finite E]

theorem squarefree_card [IsCyclic E]
    (hpc : ∀ q : ℕ, q.Prime → q ∣ Nat.card E → Monoid.exponent (CFSG.Open.pCore q E) = q) :
    Squarefree (Nat.card E) := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro q hq hqq
  haveI : Fact q.Prime := ⟨hq⟩
  have hdvd : q ∣ Nat.card E := (dvd_mul_right q q).trans hqq
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow q E))
  have hnorm : (Q : Subgroup E).Normal := Subgroup.normal_of_comm _
  have hQp : IsPGroup q (Q : Subgroup E) := Q.isPGroup'
  have hle : (Q : Subgroup E) ≤ CFSG.Open.pCore q E :=
    CFSG.LieType.BorelTits.le_pCore q hnorm hQp
  have hQc : IsCyclic (Q : Subgroup E) := inferInstance
  obtain ⟨g, hg⟩ := hQc.exists_generator
  have h1 : orderOf g = Nat.card (Q : Subgroup E) := orderOf_eq_card_of_forall_mem_zpowers hg
  have hexp := hpc q hq hdvd
  have h3 : ((g : E)) ^ q = 1 := by
    have hm : (g : E) ∈ CFSG.Open.pCore q E := hle g.2
    have := Monoid.pow_exponent_eq_one (⟨(g : E), hm⟩ : CFSG.Open.pCore q E)
    rw [hexp] at this
    exact congrArg Subtype.val this
  have h2 : orderOf g ∣ q := orderOf_dvd_of_pow_eq_one (Subtype.ext h3)
  rw [h1, Sylow.card_eq_multiplicity] at h2
  have hpos : 0 < (Nat.card E).factorization q := (Nat.Prime.factorization_pos_of_dvd hq
    Nat.card_pos.ne' hdvd)
  have hfac : (Nat.card E).factorization q ≤ 1 := by
    have : q ^ (Nat.card E).factorization q ∣ q ^ 1 := by simpa using h2
    exact (Nat.pow_dvd_pow_iff_le_right hq.one_lt).mp this
  have hge : 2 ≤ (Nat.card E).factorization q := by
    have : q ^ 2 ∣ Nat.card E := by simpa [sq] using hqq
    exact (hq.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp this
  omega

end CFSG.GroupTheory.CoprimeActionSupport.FiniteCyclicPrimeSylowsComplement
