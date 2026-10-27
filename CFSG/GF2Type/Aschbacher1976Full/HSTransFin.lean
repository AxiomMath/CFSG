module

public import CFSG.GF2Type.Aschbacher1976Full.HSTransInterfaces
public import CFSG.GF2Type.Aschbacher1976Full.HSTransFinClass
public import CFSG.GF2Type.Aschbacher1976Full.HSTransFinGroup
public import CFSG.GF2Type.Aschbacher1976Full.HSTransFinTop

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS

open Equiv CFSG.GF2Type.Aschbacher1976Full.HS.TransFin

theorem finStmt_holds : FinStmt := by
  intro Q _ _ ι hι hO2 Y hYc hYsq hcard a haY ha1
  obtain ⟨σ, L, hL, hcen, hsurj⟩ := exists_conj_Y ι hι Y hYc hYsq hcard
  let ι' : Q →* Perm (Fin 6) := (MulAut.conj σ).toMonoidHom.comp ι
  have hι'apply : ∀ q, ι' q = σ * ι q * σ⁻¹ := fun q => rfl
  have hι' : Function.Injective ι' := (MulAut.conj σ).injective.comp hι
  have hiso : ∀ x y : Fin 6, x ≠ y → swap x y ∈ ι'.range → ∃ u v : Fin 6, u ≠ v ∧
      swap u v ∈ ι'.range ∧ swap u v * swap x y ≠ swap x y * swap u v := by
    rintro x y hxy ⟨t, ht⟩
    obtain ⟨s, ⟨u, v, huv, hsuv⟩, hst⟩ :=
      exists_noncomm_swap ι' hι' hO2 (t := t) ⟨x, y, hxy, ht⟩
    refine ⟨u, v, huv, ⟨s, hsuv⟩, ?_⟩
    rw [← hsuv, ← ht, ← map_mul, ← map_mul]
    exact fun h => hst (hι' h)
  have hY' : ∀ π ∈ L, π ∈ ι'.range := fun π hπ => by
    obtain ⟨y, hy, rfl⟩ := hsurj π hπ
    exact ⟨y, rfl⟩
  have htop : ι'.range = ⊤ := by
    rcases hL with rfl | rfl
    · exact top_of_Y1 hY' hiso
    · exact top_of_Y2 hY' hiso
  have hsurj' : ∀ g : Perm (Fin 6), ∃ q, ι' q = g := fun g =>
    MonoidHom.mem_range.1 (htop ▸ Subgroup.mem_top g)
  have ha' : σ * ι a * σ⁻¹ ∈ L := hcen a haY
  have ha1' : σ * ι a * σ⁻¹ ≠ 1 := fun h => ha1 (hι' (by rw [hι'apply, h, map_one]))
  obtain ⟨g, hg2, hg4, x₀, hx₀, hgx₀⟩ : ∃ g : Perm (Fin 6), g * g = 1 ∧
      (σ * ι a * σ⁻¹ * g) ^ 4 = 1 ∧ ∃ x₀ ∈ L, g * x₀ * g⁻¹ ∉ L := by
    rcases hL with rfl | rfl
    · exact witness_of_tables Y1L witA ha' ha1'
    · exact witness_of_tables Y2L witB ha' ha1'
  obtain ⟨q, hq⟩ := hsurj' g
  have hqq : q * q = 1 := hι' (by rw [map_mul, hq, hg2, map_one])
  have haq : (a * q) ^ 4 = 1 := hι' (by rw [map_pow, map_mul, hq, hι'apply, hg4, map_one])
  refine ⟨Subgroup.closure {a, q}, isPGroup_closure_pair (hYsq a haY) hqq haq,
    Subgroup.subset_closure (by simp), fun hle => ?_⟩
  have hqP : q ∈ Subgroup.closure {a, q} := Subgroup.subset_closure (by simp)
  have hqN := Subgroup.mem_normalizer_iff.1 (hle hqP)
  obtain ⟨y₀, hy₀, hy₀x⟩ := hsurj x₀ hx₀
  have h1 := (hqN y₀).1 hy₀
  apply hgx₀
  have h2 := hcen _ h1
  have e : σ * ι (q * y₀ * q⁻¹) * σ⁻¹ = g * x₀ * g⁻¹ := by
    have := hι'apply (q * y₀ * q⁻¹)
    rw [← this, map_mul, map_mul, map_inv, hq, hι'apply y₀, hy₀x]
  rwa [e] at h2

end CFSG.GF2Type.Aschbacher1976Full.HS
