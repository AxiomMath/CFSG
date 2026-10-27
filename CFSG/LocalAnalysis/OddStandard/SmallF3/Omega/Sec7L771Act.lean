module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L771Fix
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L78Act

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem sec7l771_range_dvd [Finite G] {N B P : Subgroup G} {φ : (Fin 5 → ZMod 2) → G}
    (h : Sec7E16Act N B φ) (hP : IsSylow2Of P N) :
    8 ∣ Nat.card (h.rho.comp (Subgroup.inclusion hP.1)).range := by
  let ψ : ↥P →* Equiv.Perm (Fin 5) := h.rho.comp (Subgroup.inclusion hP.1)
  change 8 ∣ Nat.card ψ.range
  have hker : Nat.card ψ.ker ∣ 16 := by
    have hle : ψ.ker.map P.subtype ≤ B := by
      rintro _ ⟨x, hx, rfl⟩
      exact (h.mem_ker_rho (Subgroup.inclusion hP.1 x)).mp hx
    have h1 : Nat.card (ψ.ker.map P.subtype) = Nat.card ψ.ker :=
      Nat.card_congr (Subgroup.equivMapOfInjective _ _ P.subtype_injective).toEquiv.symm
    have h2 := Subgroup.card_dvd_of_le hle
    rw [h1, h.elem.2] at h2
    simpa using h2
  have hidx := Subgroup.index_mul_card ψ.ker
  rw [Subgroup.index_ker, h.card_sylow hP] at hidx
  obtain ⟨e, he⟩ := hker
  have hpos : 0 < Nat.card ψ.ker := Nat.card_pos
  have h3 : Nat.card ψ.range * Nat.card ψ.ker = (8 * e) * Nat.card ψ.ker := by
    rw [hidx]
    calc 2 ^ 7 = 8 * 16 := by norm_num
      _ = 8 * (Nat.card ψ.ker * e) := by rw [he]
      _ = (8 * e) * Nat.card ψ.ker := by ring
  exact ⟨e, Nat.eq_of_mul_eq_mul_right hpos h3⟩

theorem sec7l771_centralB [Finite G] {N B P : Subgroup G} {φ : (Fin 5 → ZMod 2) → G}
    (h : Sec7E16Act N B φ) (hP : IsSylow2Of P N) {z : G} (hz : z ∈ B) (hz1 : z ≠ 1)
    (hPz : ∀ x ∈ P, x * z = z * x) :
    (∃ w, IsEvenVec w ∧ vecWeight w = 4 ∧ φ w = z) ∧
      ∀ b ∈ B, (∀ x ∈ P, x * b = b * x) → b = 1 ∨ b = z := by
  obtain ⟨w₀, hw₀, hw₀z⟩ := (h.mem_iff z).mp hz
  have hw₀0 : w₀ ≠ 0 := fun h0 => hz1 (by rw [← hw₀z, h0, h.phi_zero])
  let ψ : ↥P →* Equiv.Perm (Fin 5) := h.rho.comp (Subgroup.inclusion hP.1)
  have h8 : 8 ∣ Nat.card ψ.range := sec7l771_range_dvd h hP
  have hfix : ∀ {v : Fin 5 → ZMod 2}, IsEvenVec v →
      (∀ x ∈ P, x * φ v = φ v * x) → ∀ σ ∈ ψ.range, permVec σ v = v := by
    intro v hv hcv σ hσ
    obtain ⟨y, rfl⟩ := hσ
    have h1 := h.rho_spec (Subgroup.inclusion hP.1 y) hv
    have h2 : ((Subgroup.inclusion hP.1 y : ↥N) : G) * φ v *
        ((Subgroup.inclusion hP.1 y : ↥N) : G)⁻¹ = φ v := by
      have hy : ((Subgroup.inclusion hP.1 y : ↥N) : G) ∈ P := y.2
      rw [hcv _ hy]
      group
    exact h.inj (sec7l77_even_permVec (ψ y) hv) hv (h1.symm.trans h2)
  have hcvw : ∀ x ∈ P, x * φ w₀ = φ w₀ * x := by
    intro x hx
    rw [hw₀z]
    exact hPz x hx
  have hfixw : ∀ σ ∈ ψ.range, permVec σ w₀ = w₀ := hfix hw₀ hcvw
  have hwt4 : vecWeight w₀ = 4 :=
    (sec7l771_fix_even ψ.range h8 hw₀ hw₀ hw₀0 hw₀0 hfixw hfixw).1
  refine ⟨⟨w₀, hw₀, hwt4, hw₀z⟩, ?_⟩
  intro b hb hcb
  obtain ⟨v, hv, hvb⟩ := (h.mem_iff b).mp hb
  have hcvv : ∀ x ∈ P, x * φ v = φ v * x := by
    intro x hx
    rw [hvb]
    exact hcb x hx
  have hfixv : ∀ σ ∈ ψ.range, permVec σ v = v := hfix hv hcvv
  by_cases hv0 : v = 0
  · left
    rw [← hvb, hv0, h.phi_zero]
  · right
    have hvz : v = w₀ :=
      (sec7l771_fix_even ψ.range h8 hv hw₀ hv0 hw₀0 hfixv hfixw).2
    rw [← hvb, hvz, hw₀z]

end CFSG.OddStandard.SmallF3.Omega
