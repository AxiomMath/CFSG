module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8I13CA2

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Equiv Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace OI13Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {β : G} {B S : Subgroup G} {α σ : G}
  (c : OI13Ctx L z t T E B β S α σ)

include c in
theorem exists_N1_conj {g : G} (hg : g ∈ c.Nc) :
    ∃ n ∈ c.N1, n * z * n⁻¹ = g * z * g⁻¹ := by
  rcases c.Nc_xor hg with ⟨h1, -⟩ | ⟨h2, -⟩
  · refine ⟨g * z, h1, ?_⟩
    group
  · exact ⟨g, h2, rfl⟩

variable {π : MulAut ↥E →* Equiv.Perm (Fin 5)} (hπ : EPi E π)

include hπ in
theorem not_conj_zsigma_Nc
    (hsig : ∀ a b : MulAut ↥E, (a, b) ∈ c.rho.range → Perm.sign (π a) = Perm.sign (π b)) :
    ¬ ∃ g ∈ c.Nc, g * z * g⁻¹ = z * σ := by
  rintro ⟨g, hg, hgz⟩
  obtain ⟨n, hn, hnz⟩ := c.exists_N1_conj hg
  rw [hgz] at hnz
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right c.h.z_sq
  have hprod : (⟨n, hn⟩ : ↥c.N1) * (c.zconjN1 ⟨n, hn⟩)⁻¹ = ⟨σ, c.sigma_mem_N1⟩ := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_inv, zconjN1_coe]
    show n * (z * n * z⁻¹)⁻¹ = σ
    calc n * (z * n * z⁻¹)⁻¹ = (n * z * n⁻¹) * z⁻¹ := by group
      _ = z * σ * z⁻¹ := by rw [hnz]
      _ = σ * z * z⁻¹ := by rw [c.hσ.comm_z]
      _ = σ := by group
  have hρ := congrArg c.rho hprod
  rw [map_mul, map_inv, rho_zconj, c.rho_sigma] at hρ
  set a := (c.rho ⟨n, hn⟩).1 with ha
  set b := (c.rho ⟨n, hn⟩).2 with hb
  have hab : a * b⁻¹ = convN (⟨σ, c.hσ.norm_E⟩ : normalizer (E : Set G)) :=
    congrArg Prod.fst (by simpa using hρ)
  have hs : Perm.sign (π a) = Perm.sign (π b) := hsig a b ⟨⟨n, hn⟩, rfl⟩
  have hodd := c.pi_sigma_odd hπ
  apply hodd
  rw [← hab, Perm.mem_alternatingGroup, map_mul, map_inv, map_mul, map_inv, hs]
  rcases Int.units_eq_one_or (Perm.sign (π b)) with h | h <;> rw [h] <;> decide

include hπ in
theorem caseA_total
    (hA : ∀ a b : MulAut ↥E, (a, b) ∈ c.rho.range ↔ Perm.sign (π a) = Perm.sign (π b))
    (hE : EFacts614 E t) (hT : Nat.card T ≤ 512)
    (h119 : (∃ g : G, g * z * g⁻¹ = z * σ) → ∃ g ∈ c.Nc, g * z * g⁻¹ = z * σ) :
    ∃ Rs R : Subgroup G, IsPGroup 2 Rs ∧ R ≤ Rs ∧ R.relIndex Rs = 2 ∧ z ∈ Rs ∧ z ∉ R ∧
      (∀ g : G, g * z * g⁻¹ ∈ Rs → ∃ r ∈ Rs, g * z * g⁻¹ = r * z * r⁻¹) ∧
      ¬ 2 ∣ Rs.relIndex (centralizer ({z} : Set G)) :=
  c.caseA_final hπ hA hE hT fun hX =>
    c.not_conj_zsigma_Nc hπ (fun a b h => (hA a b).1 h) (h119 hX)

end OI13Ctx

end CFSG.EvenSporadicStandard.Fin76b
