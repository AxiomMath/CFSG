module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.M24
public import Certificates.Certificate24867
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M24TCheck

public section

namespace CFSG.EvenSporadicStandard.M24Std.Sym6

open CFSG.Sporadic.Schreier CFSG.QuasithinUnique.Setup.X1 CFSG.Blueprint

theorem exists_conj_mem_m24E1l
    {y : S24} (hy : y * y = 1) : ∃ c : S24, c * y * c⁻¹ ∈ m24E1l := by
  by_cases h1 : y = 1
  · refine ⟨1, ?_⟩
    simp only [h1, inv_one, mul_one]
    exact m24_e1_check.2.2.1
  have hord : orderOf (y : Equiv.Perm (Fin 24)) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime ?_ ?_
    · rw [sq, ← Subgroup.coe_mul, hy, Subgroup.coe_one]
    · exact fun h => h1 (Subtype.ext h)
  obtain ⟨r, hr, c, hc, hyc⟩ := HypOne.M24.involution_cover.1 (y : Equiv.Perm (Fin 24))
    (by rw [inv_one, one_mul]; exact y.2) hord
  obtain ⟨⟨x1, hx1, h1'⟩, ⟨x2, hx2, h2'⟩⟩ := Certificates.certificate24867
  have key : ∃ d : S24, ∃ x ∈ m24E1l, (d : Equiv.Perm (Fin 24)) * r *
      (d : Equiv.Perm (Fin 24))⁻¹ = (x : Equiv.Perm (Fin 24)) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨m24Cj wordSxC1, x1, hx1, h1'⟩
    · exact ⟨m24Cj wordSxC2, x2, hx2, h2'⟩
  obtain ⟨d, x, hx, hdx⟩ := key
  refine ⟨d * (⟨c, hc⟩ : S24)⁻¹, ?_⟩
  have e : d * (⟨c, hc⟩ : S24)⁻¹ * y * (d * (⟨c, hc⟩ : S24)⁻¹)⁻¹ = x := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hyc, ← hdx]
    group
  rw [e]
  exact hx

end CFSG.EvenSporadicStandard.M24Std.Sym6

namespace CFSG.EvenSporadicStandard.M24Std

open Sym6

variable {G : Type} [Group G]

theorem exists_conj_mem_of_involution_of_type
    {L A : Subgroup G} (h : SextetType L A) :
    ∀ x ∈ L, x * x = 1 → ∃ l ∈ L, l * x * l⁻¹ ∈ A := by
  obtain ⟨-, e, hA⟩ := h
  intro x hx hxx
  have hy : e ⟨x, hx⟩ * e ⟨x, hx⟩ = 1 := by
    rw [← map_mul, show (⟨x, hx⟩ : L) * ⟨x, hx⟩ = 1 from Subtype.ext hxx, map_one]
  obtain ⟨c, hc⟩ := exists_conj_mem_m24E1l hy
  refine ⟨qdIota e c, qdIota_mem e c, ?_⟩
  rw [show x = qdIota e (e ⟨x, hx⟩) from (qdIota_apply e ⟨x, hx⟩).symm, qdIota_conj]
  exact (qdIota_mem_A e hA _).2 hc

end CFSG.EvenSporadicStandard.M24Std
