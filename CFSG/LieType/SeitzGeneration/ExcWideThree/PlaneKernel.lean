module

public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.OutRank
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Escape

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.ExcOuterLeOne
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Lang.E6Descent

section PlaneKernel


theorem exists_ne_one_mem_ker_of_plane (τ : Tag) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type}
    [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (Θ : MulAut (adjointGroup τ K) →* RingAut K × Multiplicative (ZMod (exactE τ)))
    (E : Subgroup (MulAut ↥(adjointGroup τ K))) [hE : CFSG.IsElementaryAbelian p ↥E]
    (hEc : Nat.card ↥E = p ^ 2) : ∃ ι ∈ E, ι ≠ 1 ∧ ι ∈ Θ.ker := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  obtain ⟨-, hcyc⟩ := CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hℓ K hK
  have : Finite (RingAut K) := Finite.of_injective (fun σ : RingAut K => (σ : K → K))
    DFunLike.coe_injective
  obtain ⟨hfin, hε2⟩ := exactE_facts τ hτ
  have : Finite (Multiplicative (ZMod (exactE τ))) := hfin
  have hε : ∀ e : Multiplicative (ZMod (exactE τ)), e ^ p = 1 → e = 1 := by
    intro e hep
    have h2 : orderOf e ∣ Nat.gcd p 2 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hep) (orderOf_dvd_of_pow_eq_one (hε2 e))
    rw [(Nat.coprime_primes hp Nat.prime_two).2 hp2] at h2
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h2)
  have hH : Nat.card {h : RingAut K × Multiplicative (ZMod (exactE τ)) // h ^ p = 1} ≤ p := by
    have := Fintype.ofFinite (RingAut K)
    have hinj : Function.Injective
        (fun h : {h : RingAut K × Multiplicative (ZMod (exactE τ)) // h ^ p = 1} =>
          (⟨h.1.1, by
            have := congrArg Prod.fst h.2
            simpa using this⟩ : {σ : RingAut K // σ ^ p = 1})) := by
      intro h h' hh
      have h1 : h.1.1 = h'.1.1 := congrArg Subtype.val hh
      have e2 := hε h.1.2 (by have := congrArg Prod.snd h.2; simpa using this)
      have e2' := hε h'.1.2 (by have := congrArg Prod.snd h'.2; simpa using this)
      exact Subtype.ext (Prod.ext h1 (e2.trans e2'.symm))
    refine (Nat.card_le_card_of_injective _ hinj).trans ?_
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact IsCyclic.card_pow_eq_one_le hp.pos
  have : Finite {h : RingAut K × Multiplicative (ZMod (exactE τ)) // h ^ p = 1} :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact exists_ne_one_mem_ker_of_card_le hp Θ hH E hEc

end PlaneKernel

end CFSG.LieType.SeitzGeneration.ExcWideThree
