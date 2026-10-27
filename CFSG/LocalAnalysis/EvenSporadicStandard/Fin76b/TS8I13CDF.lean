module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8I13CD2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8I13U1
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8I13Par

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Equiv Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace OI13Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {β : G} {B S : Subgroup G} {α σ : G}
  (c : OI13Ctx L z t T E B β S α σ)

theorem caseDelta_false' [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    {π : MulAut ↥E →* Equiv.Perm (Fin 5)} (hπ : EPi E π)
    (hD : ∀ a b : MulAut ↥E, (a, b) ∈ c.rho.range ↔ π a = π b)
    (hEA : ∀ A : Subgroup (MulAut ↥E), (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      (∀ a ∈ A, a * a = 1) → Nat.card ↥A ≤ 16)
    {Rs : Subgroup G} (hR : c.IsRs Rs)
    (hZQ : ∀ q ∈ c.Qs, q * q = 1 → ¬ ∃ g : G, q = g * z * g⁻¹)
    (hEven : ∀ (y : G) (hy : y ∈ Rs ⊓ c.N1), y * y = 1 → y ∉ c.Qs →
      Perm.sign (π (c.rho ⟨y, hy.2⟩).1) = 1 → ¬ ∃ g : G, y = g * z * g⁻¹)
    (h119 : ∀ y : G, y ∈ c.Nc → y ∉ c.N1 → y * y = 1 → (∃ g : G, g * z * g⁻¹ = y) →
      ∃ g ∈ c.Nc, g * z * g⁻¹ = y) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsig : ∀ a b : MulAut ↥E, (a, b) ∈ c.rho.range → Perm.sign (π a) = Perm.sign (π b) :=
    fun a b h => by rw [(hD a b).1 h]
  have hsyl := hR.isSylow hπ hD hEA
  let SS : Sylow 2 G := ⟨Rs, hR.pgroup, fun hQ hle => hsyl _ hQ hle⟩
  have hodd : ¬ 2 ∣ Rs.index := SS.not_dvd_index
  have hz2 : orderOf z = 2 := c.h.oe.cfg.z_order
  obtain ⟨g, hg⟩ := exists_conj_mem_complement hnonab hR.pgroup hodd (c.U1_le hsig hR)
    (c.U1_relIndex hsig hR) hR.z_mem (c.z_not_mem_U1 hsig hR) hz2
  have hyU : g⁻¹ * z * g ∈ c.U1 hsig hR := hg
  have hyRs : g⁻¹ * z * g ∈ Rs := c.U1_le hsig hR hyU
  have hy2 : (g⁻¹ * z * g) * (g⁻¹ * z * g) = 1 := by
    calc (g⁻¹ * z * g) * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
      _ = 1 := by rw [c.h.z_sq]; group
  have hyz : ∃ g' : G, g⁻¹ * z * g = g' * z * g'⁻¹ := ⟨g⁻¹, by rw [inv_inv]⟩
  by_cases hyN : g⁻¹ * z * g ∈ c.N1
  ·
    have hlam := (c.mem_U1_of_mem_N1 hsig hR hyRs hyN).1 hyU
    by_cases hyQ : g⁻¹ * z * g ∈ c.Qs
    · exact hZQ _ hyQ hy2 hyz
    · exact hEven _ ⟨hyRs, hyN⟩ hy2 hyQ hlam hyz
  ·
    have hyz' : g⁻¹ * z * g * z ∈ c.N1 := hR.not_mem_N1_mul_z hyRs hyN
    have hlam := (c.mem_U1_of_not_mem_N1 hsig hR hyRs hyN hyz').1 hyU
    have hyNc : g⁻¹ * z * g ∈ c.Nc := hR.le_Nc hyRs
    obtain ⟨g', hg'N, hg'⟩ := h119 _ hyNc hyN hy2 ⟨g⁻¹, by rw [inv_inv]⟩
    obtain ⟨n, hn, hny⟩ := c.exists_N1_conj hg'N
    rw [hg'] at hny
    obtain ⟨hmem, hlam1⟩ := c.lam_of_conj_z hsig hn hny
    exact absurd (hlam.symm.trans hlam1) (by decide)

end OI13Ctx

end CFSG.EvenSporadicStandard.Fin76b
