module

public import CFSG.ClassicalInvolution.Generic.Frame

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution.Generic (Commutes)

namespace T7Z

open scoped commutatorElement

variable {U G : Type} [Group U] [Group G]

theorem commutator_center_le_bot (A : Subgroup U) : ⁅Subgroup.center U, A⁆ = ⊥ := by
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro x hx a _
  rw [Subgroup.mem_bot]
  exact commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hx a).symm

theorem commutes_of_map_commutes (ψ : U →* G) (hker : ψ.ker ≤ Subgroup.center U)
    {A B : Subgroup U} (hA : A ≤ ⁅A, A⁆) (h : Commutes (A.map ψ) (B.map ψ)) : Commutes A B := by
  have h1 : ⁅A, B⁆ ≤ Subgroup.center U := by
    refine le_trans ?_ hker
    rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (h _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩)
  have h2 : ⁅B, A⁆ ≤ Subgroup.center U := by
    rw [Subgroup.commutator_comm]
    exact h1
  have hAB : ⁅⁅A, B⁆, A⁆ = ⊥ :=
    le_bot_iff.mp ((Subgroup.commutator_mono h1 le_rfl).trans (commutator_center_le_bot A).le)
  have hBA : ⁅⁅B, A⁆, A⁆ = ⊥ :=
    le_bot_iff.mp ((Subgroup.commutator_mono h2 le_rfl).trans (commutator_center_le_bot A).le)
  have h3 : ⁅⁅A, A⁆, B⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := A) (H₂ := A) (H₃ := B) hAB hBA
  have h4 : ⁅A, B⁆ = ⊥ :=
    le_bot_iff.mp ((Subgroup.commutator_mono hA le_rfl).trans h3.le)
  intro x hx y hy
  have : ⁅x, y⁆ ∈ ⁅A, B⁆ := Subgroup.commutator_mem_commutator hx hy
  rw [h4, Subgroup.mem_bot] at this
  exact commutatorElement_eq_one_iff_mul_comm.mp this

theorem exists_central_lift (ψ : U →* G) (hker : ψ.ker ≤ Subgroup.center U)
    (hU : (⊤ : Subgroup U) ≤ ⁅(⊤ : Subgroup U), (⊤ : Subgroup U)⁆) {x : G} (hx : x ∈ ψ.range)
    (hcomm : ∀ y ∈ ψ.range, x * y = y * x) : ∃ ε ∈ Subgroup.center U, ψ ε = x := by
  obtain ⟨ε, rfl⟩ := hx
  refine ⟨ε, ?_, rfl⟩
  have h : Commutes ((⊤ : Subgroup U).map ψ) ((Subgroup.zpowers ε).map ψ) := by
    rintro _ ⟨a, -, rfl⟩ _ ⟨b, hb, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hc : Commute (ψ ε) (ψ a) := hcomm (ψ a) ⟨a, rfl⟩
    rw [map_zpow]
    exact (Commute.zpow_right hc.symm k).eq
  have := commutes_of_map_commutes ψ hker hU h
  rw [Subgroup.mem_center_iff]
  intro y
  exact this y trivial ε (Subgroup.mem_zpowers ε)

theorem eq_one_of_map_eq_one_of_card_eq [Finite U] (ψ : U →* G) {R : Subgroup U}
    (hc : Nat.card ↥(R.map ψ) = Nat.card ↥R) {x : U} (hx : x ∈ R) (h : ψ x = 1) : x = 1 := by
  let φ : ↥R → ↥(R.map ψ) := fun r => ⟨ψ r, ⟨r, r.2, rfl⟩⟩
  have hs : Function.Surjective φ := by
    rintro ⟨_, r, hr, rfl⟩
    exact ⟨⟨r, hr⟩, rfl⟩
  have hb : Function.Bijective φ := hs.bijective_of_nat_card_le hc.symm.le
  have h1 : φ ⟨x, hx⟩ = φ 1 := by
    apply Subtype.ext
    simp [φ, h]
  have := hb.1 h1
  exact congrArg Subtype.val this

end T7Z

end CFSG.ClassicalInvolution.Asc77
