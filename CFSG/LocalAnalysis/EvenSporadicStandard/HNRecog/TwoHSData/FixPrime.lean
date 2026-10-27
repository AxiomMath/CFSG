module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.FixSpec
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.SylowCover
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.Elems

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.EvenSporadicStandard.TwoHS

local notation "𝒞" => CFSG.Sporadic.SmallOddCore.conjClass

theorem isConj_of_fixPrimeOK {p : ℕ} [Fact p.Prime] {ds : List FixData} {sw : List (List ℕ)}
    (hS : Nat.card ↥(closure (elemW '' {w | w ∈ sw})) =
      p ^ (Nat.card ↥P1408).factorization p)
    (hcov : ∀ y ∈ closure (elemW '' {w | w ∈ sw}),
      y = 1 ∨ ∃ d ∈ ds, y ∈ 𝒞 P1408 (elemW d.rep))
    {t : ↥P1408} (ht : orderOf t = p) :
    ∃ d ∈ ds, IsConj (⟨elemW d.rep, elemW_mem _⟩ : ↥P1408) t := by
  obtain ⟨c, hcP, hcS⟩ := TwoHSData.exists_conj_mem_of_orderOf_eq_prime
    (closure_elemW_le sw) hS (M := Equiv.Perm (Fin 1408)) (t := (t : Equiv.Perm (Fin 1408)))
    t.2 (by rw [Subgroup.orderOf_coe]; exact ht)
  have hne : c⁻¹ * (t : Equiv.Perm (Fin 1408)) * c ≠ 1 := by
    intro h1
    have h2 : (t : Equiv.Perm (Fin 1408)) = 1 := by
      have : (t : Equiv.Perm (Fin 1408)) = c * (c⁻¹ * (t : Equiv.Perm (Fin 1408)) * c) * c⁻¹ := by
        group
      rw [this, h1]
      group
    have h3 : t = 1 := Subtype.ext h2
    rw [h3, orderOf_one] at ht
    exact (Fact.out : p.Prime).one_lt.ne ht
  rcases hcov _ hcS with h1 | ⟨d, hd, g, hg, hgd⟩
  · exact absurd h1 hne
  · refine ⟨d, hd, ?_⟩
    rw [isConj_iff_mem_conjClass]
    refine ⟨c * g, P1408.mul_mem hcP hg, ?_⟩
    have e1 : c⁻¹ * (t : Equiv.Perm (Fin 1408)) * c = g * elemW d.rep * g⁻¹ := hgd
    calc (t : Equiv.Perm (Fin 1408)) = c * (c⁻¹ * (t : Equiv.Perm (Fin 1408)) * c) * c⁻¹ := by
          group
      _ = c * (g * elemW d.rep * g⁻¹) * c⁻¹ := by rw [e1]
      _ = (c * g) * elemW d.rep * (c * g)⁻¹ := by group

end CFSG.EvenSporadicStandard.HNRecog
