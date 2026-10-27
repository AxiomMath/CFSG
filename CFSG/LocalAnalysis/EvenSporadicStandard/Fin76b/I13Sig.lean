module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13Pi

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace I13Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T₀ E : Subgroup G}
  {Q : Sylow 2 G} {x β : G} {B S : Subgroup G} {α : G}
  (c : I13Ctx L z t T₀ E Q x β B S α)

include c

theorem exists_klein_B : ∃ b₁ ∈ B, ∃ b₂ ∈ B, b₁ * b₁ = 1 ∧ b₂ * b₂ = 1 ∧ b₁ * b₂ = b₂ * b₁ ∧
    b₁ ≠ 1 ∧ b₂ ≠ 1 ∧ b₁ ≠ b₂ := by
  obtain ⟨eB⟩ := c.h.conf.B_iso
  let u₁ : alternatingGroup (Fin 5) :=
    ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by
      rw [Equiv.Perm.mem_alternatingGroup, map_mul, Equiv.Perm.sign_swap (by decide),
        Equiv.Perm.sign_swap (by decide)]; decide⟩
  let u₂ : alternatingGroup (Fin 5) :=
    ⟨Equiv.swap 0 2 * Equiv.swap 1 3, by
      rw [Equiv.Perm.mem_alternatingGroup, map_mul, Equiv.Perm.sign_swap (by decide),
        Equiv.Perm.sign_swap (by decide)]; decide⟩
  have h11 : u₁ * u₁ = 1 := Subtype.ext (by decide)
  have h22 : u₂ * u₂ = 1 := Subtype.ext (by decide)
  have h12 : u₁ * u₂ = u₂ * u₁ := Subtype.ext (by decide)
  have h1 : u₁ ≠ 1 := fun h => by
    have := congrArg Subtype.val h
    revert this; decide
  have h2 : u₂ ≠ 1 := fun h => by
    have := congrArg Subtype.val h
    revert this; decide
  have h3 : u₁ ≠ u₂ := fun h => by
    have := congrArg Subtype.val h
    revert this; decide
  refine ⟨(eB.symm u₁ : ↥B), (eB.symm u₁).2, (eB.symm u₂ : ↥B), (eB.symm u₂).2, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · have := congrArg (fun u => ((eB.symm u : ↥B) : G)) h11
    simpa [map_mul] using this
  · have := congrArg (fun u => ((eB.symm u : ↥B) : G)) h22
    simpa [map_mul] using this
  · have := congrArg (fun u => ((eB.symm u : ↥B) : G)) h12
    simpa [map_mul] using this
  · intro h
    apply h1
    have : eB.symm u₁ = 1 := Subtype.ext (by simpa using h)
    simpa using congrArg eB this
  · intro h
    apply h2
    have : eB.symm u₂ = 1 := Subtype.ext (by simpa using h)
    simpa using congrArg eB this
  · intro h
    apply h3
    have : eB.symm u₁ = eB.symm u₂ := Subtype.ext h
    exact eB.symm.injective this

variable {π : MulAut ↥E →* Equiv.Perm (Fin 5)} (hπ : EPi E π)

include hπ

omit hπ in
theorem klein_kappa {b₁ b₂ : G} (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B) (h11 : b₁ * b₁ = 1)
    (h22 : b₂ * b₂ = 1) (h12 : b₁ * b₂ = b₂ * b₁) (h1 : b₁ ≠ 1) (h2 : b₂ ≠ 1) (h3 : b₁ ≠ b₂) :
    BInv E π (c.kappa ⟨b₁, hb₁⟩) ∧ BInv E π (c.kappa ⟨b₂, hb₂⟩) ∧
      c.kappa ⟨b₁, hb₁⟩ * c.kappa ⟨b₂, hb₂⟩ = c.kappa ⟨b₂, hb₂⟩ * c.kappa ⟨b₁, hb₁⟩ ∧
      c.kappa ⟨b₁, hb₁⟩ ≠ c.kappa ⟨b₂, hb₂⟩ ∧
      c.kappa ⟨b₁, hb₁⟩ * c.kappa ⟨b₂, hb₂⟩ ∉ innAutE E := by
  have hsq : ∀ (b : G) (hb : b ∈ B), b * b = 1 → c.kappa ⟨b, hb⟩ * c.kappa ⟨b, hb⟩ = 1 := by
    intro b hb hbb
    rw [← map_mul, ← map_one c.kappa]
    congr 1
    exact Subtype.ext hbb
  have hinn : ∀ (b : G) (hb : b ∈ B), b ≠ 1 → c.kappa ⟨b, hb⟩ ∉ innAutE E := by
    intro b hb hb1 hin
    exact hb1 (congrArg Subtype.val (c.eq_one_of_kappa_mem_inn (b := ⟨b, hb⟩) hin))
  refine ⟨⟨hsq b₁ hb₁ h11, c.pi_kappa_mem ⟨b₁, hb₁⟩, hinn b₁ hb₁ h1⟩,
    ⟨hsq b₂ hb₂ h22, c.pi_kappa_mem ⟨b₂, hb₂⟩, hinn b₂ hb₂ h2⟩, ?_, ?_, ?_⟩
  · rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext h12
  · intro h
    exact h3 (congrArg Subtype.val (c.kappa_injective h))
  · intro hin
    rw [← map_mul] at hin
    have := congrArg Subtype.val (c.eq_one_of_kappa_mem_inn (b := ⟨b₁, hb₁⟩ * ⟨b₂, hb₂⟩) hin)
    have h4 : b₁ * b₂ = 1 := this
    apply h3
    calc b₁ = b₁ * (b₂ * b₂) := by rw [h22, mul_one]
      _ = (b₁ * b₂) * b₂ := by group
      _ = b₂ := by rw [h4, one_mul]

end I13Ctx

end CFSG.EvenSporadicStandard.Fin76b
