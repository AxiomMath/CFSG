module

public import CFSG.Fischer.Aut.TwoPower

public section

namespace CFSG.Fischer

variable {G : Type*} [Group G]

theorem mul_conj_mul_inv (γ : MulAut G) (g : G) : γ * MulAut.conj g * γ⁻¹ = MulAut.conj (γ g) := by
  ext x
  simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply, map_mul, map_inv,
    MulEquiv.apply_symm_apply]

theorem eq_one_of_commute_innerAut (hZ : Subgroup.center G = ⊥) {γ : MulAut G}
    (h : ∀ g : G, γ * MulAut.conj g = MulAut.conj g * γ) : γ = 1 := by
  ext g
  have h1 : MulAut.conj (γ g) = MulAut.conj g := by
    rw [← mul_conj_mul_inv, h g, mul_inv_cancel_right]
  have h2 : g⁻¹ * γ g ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro x
    have := congrArg (fun β : MulAut G => β x) h1
    simp only [MulAut.conj_apply] at this
    have e : γ g * x = g * x * g⁻¹ * γ g := by rw [← this]; group
    calc x * (g⁻¹ * γ g) = g⁻¹ * (g * x * g⁻¹ * γ g) := by group
      _ = g⁻¹ * γ g * x := by rw [← e]; group
  rw [hZ, Subgroup.mem_bot, inv_mul_eq_one] at h2
  exact h2.symm

theorem center_mulAut_eq_bot (hZ : Subgroup.center G = ⊥) : Subgroup.center (MulAut G) = ⊥ := by
  rw [eq_bot_iff]
  intro γ hγ
  rw [Subgroup.mem_bot]
  exact eq_one_of_commute_innerAut hZ fun g => (Subgroup.mem_center_iff.1 hγ _).symm

theorem normalizer_eq_of_complete (hZ : Subgroup.center G = ⊥) {R : Subgroup (MulAut G)}
    (hR : innerAut G ≤ R) (hcomp : ∀ φ : MulAut R, ∃ r : R, φ = MulAut.conj r) :
    Subgroup.normalizer (R : Set (MulAut G)) = R := by
  apply le_antisymm _ Subgroup.le_normalizer
  intro β hβ
  rw [Subgroup.mem_normalizer_iff] at hβ
  let φ : MulAut R :=
    { toFun := fun r => ⟨β * r * β⁻¹, (hβ r).1 r.2⟩
      invFun := fun r => ⟨β⁻¹ * r * β, by
        have := (hβ (β⁻¹ * r * β)).2
        apply this
        simp [mul_assoc]⟩
      left_inv := fun r => Subtype.ext (by simp [mul_assoc])
      right_inv := fun r => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun r s => Subtype.ext (by simp [mul_assoc]) }
  obtain ⟨r₀, hr₀⟩ := hcomp φ
  have key : ∀ r : R, β * r * β⁻¹ = (r₀ : MulAut G) * r * (r₀ : MulAut G)⁻¹ := by
    intro r
    have := congrArg (fun ψ : MulAut R => ((ψ r : R) : MulAut G)) hr₀
    simpa [φ, MulAut.conj_apply] using this
  have h1 : (r₀ : MulAut G)⁻¹ * β = 1 := by
    apply eq_one_of_commute_innerAut hZ
    intro g
    have := key ⟨MulAut.conj g, hR ⟨g, rfl⟩⟩
    simp only at this
    calc (r₀ : MulAut G)⁻¹ * β * MulAut.conj g =
        (r₀ : MulAut G)⁻¹ * (β * MulAut.conj g * β⁻¹) * β := by group
      _ = MulAut.conj g * ((r₀ : MulAut G)⁻¹ * β) := by rw [this]; group
  rw [inv_mul_eq_one] at h1
  rw [← h1]
  exact r₀.2

theorem eq_top_of_complete [Finite G] (hZ : Subgroup.center G = ⊥) {R : Subgroup (MulAut G)}
    (hR : innerAut G ≤ R) (hcomp : ∀ φ : MulAut R, ∃ r : R, φ = MulAut.conj r)
    (hout : ∀ α : MulAut G, ∃ k : ℕ, α ^ (2 ^ k) ∈ innerAut G) : R = ⊤ :=
  eq_top_of_outTwo hout hR (normalizer_eq_of_complete hZ hR hcomp)

theorem commutator_le_of_index_two {A : Type*} [Group A] {H : Subgroup A} (h : H.index = 2) :
    commutator A ≤ H := by
  rw [commutator_def, Subgroup.commutator_le]
  intro g₁ _ g₂ _
  rw [commutatorElement_def, Subgroup.mul_mem_iff_of_index_two h,
    Subgroup.mul_mem_iff_of_index_two h, Subgroup.mul_mem_iff_of_index_two h, inv_mem_iff,
    inv_mem_iff]
  tauto

theorem mulAutConj_injective (hZ : Subgroup.center G = ⊥) :
    Function.Injective (MulAut.conj : G →* MulAut G) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  rw [← hZ, Subgroup.mem_center_iff]
  intro x
  have := congrArg (fun β : MulAut G => β x) hg
  simp only [MulAut.conj_apply, MulAut.one_apply] at this
  calc x * g = g * x * g⁻¹ * g := by rw [this]
    _ = g * x := by group

theorem commutator_mulAut_eq (hperf : commutator G = ⊤) (hidx : (innerAut G).index = 2) :
    commutator (MulAut G) = innerAut G := by
  apply le_antisymm (commutator_le_of_index_two hidx)
  rw [innerAut, MonoidHom.range_eq_map, ← hperf, commutator_def, Subgroup.map_commutator,
    commutator_def]
  exact Subgroup.commutator_mono le_top le_top

@[expose] noncomputable def innerAutEquiv (hZ : Subgroup.center G = ⊥) : G ≃* innerAut G :=
  MonoidHom.ofInjective (mulAutConj_injective hZ)

theorem isSimpleGroup_commutator_mulAut [IsSimpleGroup G] (hZ : Subgroup.center G = ⊥)
    (hperf : commutator G = ⊤) (hidx : (innerAut G).index = 2) :
    IsSimpleGroup (commutator (MulAut G)) :=
  ((MulEquiv.subgroupCongr (commutator_mulAut_eq hperf hidx)).trans
    (innerAutEquiv hZ).symm).isSimpleGroup

end CFSG.Fischer
