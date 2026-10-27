module

public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizers

public section

namespace CFSG.GH74.KGroups.M12

open Subgroup CFSG.Blueprint CFSG.ComponentClassification CFSG.ComponentClassification.M12Cover
open CFSG.ComponentClassification.OuterAutomorphisms

theorem oddCore_eq_pPrimeCore_two (H : Type*) [Group H] : CFSG.oddCore H = CFSG.pPrimeCore 2 H := by
  unfold CFSG.oddCore CFSG.pPrimeCore
  congr 1
  ext N
  simp only [Set.mem_ofPred_eq, Nat.coprime_two_left]

theorem locBal2_M12
    (X : Type) [Group X] [Finite X] (N : Subgroup X) (hN : N.Normal)
    (hS : NativeSporadic.IsSporadic ↥N .M12) (hC : centralizer (N : Set X) = ⊥) (e : X)
    (he : orderOf e = 2) : CFSG.pPrimeCore 2 ↥(centralizer ({e} : Set X)) = ⊥ := by
  obtain ⟨eN⟩ := hS
  let eN' : ↥N ≃* NativeSporadic.M12 := eN
  let θ : X →* MulAut NativeSporadic.M12 :=
    (MulAut.congr eN').toMonoidHom.comp (MulAut.conjNormal (H := N))
  have hθ : ∀ (x : X) (n : N), θ x (eN' n) = eN' (MulAut.conjNormal (H := N) x n) := fun x n => by
    simp [θ, MulAut.congr_apply]
  have hθinj : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : ∀ n : N, x * (n : X) * x⁻¹ = n := fun n => by
      have h1 := hθ x n
      rw [hx, MulAut.one_apply] at h1
      have h2 := eN'.injective h1.symm
      have h3 := congrArg Subtype.val h2
      simpa using h3
    have hxC : x ∈ centralizer (N : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro n hn
      have := hx' ⟨n, hn⟩
      calc n * x = (x * n * x⁻¹) * x := by rw [this]
        _ = x * n := by group
    rw [hC, Subgroup.mem_bot] at hxC
    exact hxC
  let J : Subgroup (MulAut NativeSporadic.M12) := θ.range
  have hJ : inner NativeSporadic.M12 ≤ J := by
    rintro _ ⟨g, rfl⟩
    obtain ⟨n, rfl⟩ := eN'.surjective g
    refine ⟨(n : X), ?_⟩
    ext m
    obtain ⟨n', rfl⟩ := eN'.surjective m
    rw [hθ, MulAut.conj_apply]
    have : (MulAut.conjNormal (H := N) (n : X)) n' = n * n' * n⁻¹ := by
      apply Subtype.ext
      simp
    rw [this]
    simp
  let eJ : X ≃* J := MonoidHom.ofInjective hθinj
  have hu : orderOf (eJ e) = 2 := by rw [MulEquiv.orderOf_eq]; exact he
  have hodd := oddCore_centralizer J hJ (eJ e) hu
  let f := centralizerEquiv eJ e
  have hmap := CFSG.pPrimeCore_map_iso 2 f
  have h2 : CFSG.pPrimeCore 2 ↥(centralizer ({eJ e} : Set J)) = ⊥ := by
    rw [← oddCore_eq_pPrimeCore_two]
    exact hodd
  rw [h2] at hmap
  exact (Subgroup.map_eq_bot_iff_of_injective _ f.injective).1 hmap

end CFSG.GH74.KGroups.M12
