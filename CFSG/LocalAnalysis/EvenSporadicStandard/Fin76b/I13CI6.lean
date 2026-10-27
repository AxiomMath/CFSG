module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13CI5

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace I13Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T₀ E : Subgroup G}
  {Q : Sylow 2 G} {x β : G} {B S : Subgroup G} {α : G}
  {c : I13Ctx L z t T₀ E Q x β B S α} {π : MulAut ↥E →* Equiv.Perm (Fin 5)}
  {Rs : Subgroup G}

namespace IsRs

variable (hR : c.IsRs Rs) (hπ : EPi E π)
  (hI : ∀ a b : MulAut ↥E, (a, b) ∈ c.rho.range ↔
    π a ∈ alternatingGroup (Fin 5) ∧ π b = π a)

include hR hπ hI

theorem pi_ne_one_of_not_mem_Qs {y : G} (hy : y ∈ Rs ⊓ c.N1) (hyQ : y ∉ c.Qs) :
    π (c.rho ⟨y, hy.2⟩).1 ≠ 1 := by
  intro h1
  have hmem : ((c.rho ⟨y, hy.2⟩).1, (c.rho ⟨y, hy.2⟩).2) ∈ c.rho.range := ⟨⟨y, hy.2⟩, rfl⟩
  have h2 : π (c.rho ⟨y, hy.2⟩).2 = 1 := by
    rw [((hI _ _).1 hmem).2, h1]
  obtain ⟨e₁, he₁⟩ := ((hπ.ker _).1 h1 : (c.rho ⟨y, hy.2⟩).1 ∈ innAutE E)
  obtain ⟨e₂, he₂⟩ := ((hπ.ker _).1 h2 : (c.rho ⟨y, hy.2⟩).2 ∈ innAutE E)
  obtain ⟨q, hq, hρq⟩ := c.exists_rho_Qs e₁ e₂
  have hqR : q ∈ Rs ⊓ c.N1 := ⟨hR.Qs_le hq, c.Qs_le_N1 hq⟩
  have hk : q⁻¹ * y ∈ Rs ⊓ c.N1 := mul_mem (inv_mem hqR) hy
  have hρk : c.rho ⟨q⁻¹ * y, hk.2⟩ = 1 := by
    have e : (⟨q⁻¹ * y, hk.2⟩ : ↥c.N1) = ⟨q, c.Qs_le_N1 hq⟩⁻¹ * ⟨y, hy.2⟩ := rfl
    rw [e, map_mul, map_inv, hρq]
    have : (MulAut.conj e₁, MulAut.conj e₂) = c.rho ⟨y, hy.2⟩ :=
      Prod.ext he₁ he₂
    rw [this]
    group
  have hkZ : q⁻¹ * y ∈ c.Zs := hR.R_inf_KR_le ⟨hk, c.mem_KR.2 ⟨hk.2, hρk⟩⟩
  apply hyQ
  have : y = q * (q⁻¹ * y) := by group
  rw [this]
  exact mul_mem hq (c.Zs_le_Qs hkZ)

theorem card_Cprime_Qs_le
    (hfix : ∀ φ : MulAut ↥E, BInv E π φ → Nat.card {e : ↥E // φ e = e} = 4)
    {y : G} (hy : y ∈ Rs ⊓ c.N1) (hyQ : y ∉ c.Qs) :
    Nat.card ↥(c.Cprime c.Qs_le_N1 y) ≤ 64 := by
  have hcp := c.card_Cprime_le c.Qs_le_N1 c.Qs_inf_KR_le hy.2
  have hmem : ((c.rho ⟨y, hy.2⟩).1, (c.rho ⟨y, hy.2⟩).2) ∈ c.rho.range := ⟨⟨y, hy.2⟩, rfl⟩
  obtain ⟨hA, hA'⟩ := (hI _ _).1 hmem
  have hne := hR.pi_ne_one_of_not_mem_Qs hπ hI hy hyQ
  obtain ⟨k, hk⟩ := hR.pgroup ⟨y, hy.1⟩
  have hyk : y ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  have hρk : (c.rho ⟨y, hy.2⟩) ^ (2 ^ k) = 1 := by
    rw [← map_pow]
    have : (⟨y, hy.2⟩ : ↥c.N1) ^ (2 ^ k) = 1 := Subtype.ext hyk
    rw [this, map_one]
  have hπk : π (c.rho ⟨y, hy.2⟩).1 ^ (2 ^ k) = 1 := by
    rw [← map_pow, ← Prod.pow_fst, hρk]
    simp
  have h2 : π (c.rho ⟨y, hy.2⟩).1 * π (c.rho ⟨y, hy.2⟩).1 = 1 := a5_two_element hA hπk
  have b1 := c.card_cent_inn_le' hπ hfix hA hne h2
  have b2 := c.card_cent_inn_le' hπ hfix (hA' ▸ hA) (hA' ▸ hne) (hA' ▸ h2)
  have b3 := c.card_cent_Qhat_le (c.rho ⟨y, hy.2⟩).1 (c.rho ⟨y, hy.2⟩).2
  have : Nat.card ↥(c.Rhat c.Qs ⊓ centralizer ({c.rho ⟨y, hy.2⟩} : Set (MulAut ↥E × MulAut ↥E)))
      ≤ 16 := b3.trans (by nlinarith)
  omega

end IsRs

end I13Ctx

end CFSG.EvenSporadicStandard.Fin76b
