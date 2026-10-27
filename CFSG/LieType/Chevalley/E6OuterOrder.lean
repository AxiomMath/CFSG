module

public import CFSG.LieType.Chevalley.OrdinaryEOuterOrder
import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6Three
import CFSG.RankThree.PartTwo.Sec13.K135GL12Out

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem card_outer_adjointGroup_E6_dvd
    {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = p ^ f) :
    Nat.card (Outer (adjointGroup .E6 K)) ∣ 2 * Nat.gcd 3 (p ^ f - 1) * f := by
  by_cases h3 : 3 ∣ p ^ f - 1
  · have hg : Nat.gcd 3 (p ^ f - 1) = 3 := Nat.gcd_eq_left h3
    have hmain := (ordinary_E_outer_order_Cartan_divisor .E6 (Or.inl rfl) hp hf K hK 3 2
      (Or.inl ⟨rfl, rfl, rfl⟩)).1
    rw [hg]
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmain
  · have hndK : ¬ 3 ∣ Nat.card K - 1 := by
      rwa [hK]
    obtain ⟨Φ, hsurj, hkerΦ, hdvd⟩ :=
      exists_outer_hom_E (K := K) (τ := .E6) (Or.inl rfl)
    have hbot : Φ.ker = ⊥ := by
      rw [hkerΦ, eq_bot_iff]
      rintro _ ⟨a, rfl⟩
      rw [Subgroup.mem_bot]
      exact (QuotientGroup.eq_one_iff _).2
        (CFSG.HardMathSupport.Timmesfeld.CrossChar.rootDiagAut_mem_innerAut_of_not_dvd
          K hndK a)
    let Ψ : MulAut (adjointGroup .E6 K) →*
        RingAut K × Multiplicative (ZMod (exactE .E6)) :=
      Φ.comp (QuotientGroup.mk' (inner (adjointGroup .E6 K)))
    have hkerΨ : Ψ.ker =
        (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range := by
      change Ψ.ker = inner (adjointGroup .E6 K)
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hbot,
        Subgroup.mem_bot]
      exact QuotientGroup.eq_one_iff x
    have hdvdOut := CFSG.RankThree.PartTwo.Sec13.K135GL12.gl12kE_card_outer_dvd Ψ hkerΨ
    have hQcard : Nat.card (RingAut K × Multiplicative (ZMod (exactE .E6))) = 2 * f := by
      rw [Nat.card_prod, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
      rw [(CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hp K hK).1]
      rw [show exactE .E6 = 2 from rfl]
      exact Nat.mul_comm f 2
    rw [hQcard] at hdvdOut
    have hcop : Nat.Coprime 3 (p ^ f - 1) :=
      (Nat.prime_three.coprime_iff_not_dvd).mpr h3
    have hg : Nat.gcd 3 (p ^ f - 1) = 1 := hcop.gcd_eq_one
    rw [hg, Nat.mul_one]
    simpa using hdvdOut

end CFSG.LieType.Chevalley

end
