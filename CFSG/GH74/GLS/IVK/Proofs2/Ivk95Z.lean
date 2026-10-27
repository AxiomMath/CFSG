module

public import CFSG.GH74.Generic.S1.SL2Facts
public import CFSG.GH74.GLS.IVK.Statements.Sec4
public import CFSG.GH74.GLS.LU.Local.KStepY
public import CFSG.GH74.KGroups.L3EpsOuterLin

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.LU.Local

theorem Ez_le_centralizer {J : Type} [Group J] (z : J) : Ez z ≤ centralizer ({z} : Set J) := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

theorem ivk95_z_facts {J : Type} [Group J] [Finite J] {z : J} (hz : orderOf z = 2) {q : ℕ} (hodd : Odd q)
    (hsl : HasSL2Model ↥(Ez z) (fun r => r = q))
    (hcyc : ∀ S : Sylow 2 ↥(centralizer ((Ez z : Subgroup J) : Set J)), IsCyclic ↥S) :
    z ∈ Ez z ∧ (∀ v ∈ Ez z, v * v = 1 → v = 1 ∨ v = z) ∧ (∀ k ∈ Ez z, k * z = z * k) := by
  obtain ⟨t, htK, ht2, htinv, -⟩ := CFSG.GH74.Generic.S1.sl2_involution_facts hodd hsl
  have hKz : ∀ k ∈ Ez z, k * z = z * k := fun k hk =>
    (mem_centralizer_singleton_iff.mp (Ez_le_centralizer z hk))
  have htc : ∀ g ∈ Ez z, g * t = t * g := by
    intro g hg
    have hconj : g * t * g⁻¹ ∈ Ez z := (Ez z).mul_mem ((Ez z).mul_mem hg htK) ((Ez z).inv_mem hg)
    have hsq : (g * t * g⁻¹) * (g * t * g⁻¹) = 1 := by
      have h1 : t * t = 1 := by
        have := pow_orderOf_eq_one t
        rwa [ht2, pow_two] at this
      calc (g * t * g⁻¹) * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
        _ = 1 := by rw [h1]; group
    rcases htinv _ hconj hsq with h | h
    · exfalso
      have h1 : t = 1 := by
        have := congrArg (fun x => g⁻¹ * x * g) h
        simpa [mul_assoc] using this
      rw [h1, orderOf_one] at ht2
      omega
    · calc g * t = (g * t * g⁻¹) * g := by group
        _ = t * g := by rw [h]
  have hztc : z = t := by
    refine involution_eq_of_cyclic_sylow (C := centralizer ((Ez z : Subgroup J) : Set J)) ?_ ?_ ht2
      hz ?_ hcyc
    · exact mem_centralizer_iff.mpr fun k hk => htc k hk
    · exact mem_centralizer_iff.mpr fun k hk => hKz k hk
    · intro x hx
      exact ((mem_centralizer_iff.mp hx) t htK).symm
  subst hztc
  exact ⟨htK, htinv, htc⟩

end CFSG.GH74.GLS.IVK.Proofs2
