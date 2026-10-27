module

public import CFSG.ClassicalInvolution.Asc77.WP1Section7
public import CFSG.ClassicalInvolution.Asc77.WP2Thompson
public import CFSG.ClassicalInvolution.AschTight.Sec7L713C

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G]

@[expose] def L71On (Ω : Set (Subgroup G)) : Prop :=
  ∀ W ∈ WSet Ω, ∀ R ∈ DSet Ω W, ∀ T ∈ DSet Ω W, ∀ u r v t : G,
    Subgroup.zpowers u = R ⊓ W → R = Subgroup.closure {u, r} →
    Subgroup.zpowers v = T ⊓ W → T = Subgroup.closure {v, t} →
      ((∃ J ∈ Ω, R ≤ J ∧ T ≤ J) ∨
        (∃ J ∈ Ω, ∃ J' ∈ Ω, R ≤ J ∧ T ≤ J' ∧ J' ∈ omegaNbr Ω J ∧
          ∀ a ∈ R, ∀ b ∈ T, a * b * a⁻¹ * b⁻¹ ∈ OCW W) ∨
        (∃ J ∈ Ω, ∃ J' ∈ Ω, R ≤ J ∧ T ≤ J' ∧ J' ∈ omegaStarNbr Ω J ∧
          J' ∉ omegaNbr Ω J ∧
          ∃ v' : G, Subgroup.zpowers v' = Subgroup.zpowers v ∧
            t⁻¹ * u * t * (u * v')⁻¹ ∈ OCW W ∧ r⁻¹ * v' * r * (v' * u)⁻¹ ∈ OCW W))

variable {p f : ℕ} [Fact p.Prime]

theorem l71On_of (h71 : L7_1 p f) [Finite G] {Ω : Set (Subgroup G)} (hΩ : PartIHyp p f Ω) :
    L71On Ω := fun W hW R hR T hT u r v t hu hr hv ht =>
  (h71 hΩ.1 hΩ.2.1 G Ω hΩ.2.2.1 hΩ.2.2.2 W hW R hR T hT u r v t hu hr hv ht).2

theorem exists_zpowers_eq {A : Subgroup G} (hA : IsCyclic ↥A) :
    ∃ u : G, Subgroup.zpowers u = A := by
  obtain ⟨g, hg⟩ := hA.exists_generator
  refine ⟨g, le_antisymm (Subgroup.zpowers_le.mpr g.2) fun x hx => ?_⟩
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
  exact Subgroup.mem_zpowers_iff.mpr ⟨n, by rw [← Subgroup.coe_zpow, hn]⟩

theorem eq_closure_of_index_two {A R : Subgroup G} (h2 : A.relIndex R = 2) (hAR : A ≤ R)
    {u r : G} (hu : Subgroup.zpowers u = A) (hrR : r ∈ R) (hrA : r ∉ A) :
    R = Subgroup.closure {u, r} := by
  have huc : u ∈ Subgroup.closure ({u, r} : Set G) := Subgroup.subset_closure (by simp)
  have hrc : r ∈ Subgroup.closure ({u, r} : Set G) := Subgroup.subset_closure (by simp)
  have hAc : A ≤ Subgroup.closure {u, r} := hu ▸ Subgroup.zpowers_le.mpr huc
  refine le_antisymm (fun ρ hρ => ?_) ((Subgroup.closure_le _).mpr ?_)
  · rcases mem_or_mul_inv_mem_of_relIndex_two h2 hrR hrA hρ with h | h
    · exact hAc h
    · have e : ρ = ρ * r⁻¹ * r := by group
      rw [e]
      exact Subgroup.mul_mem _ (hAc h) hrc
  · intro x hx
    rcases hx with rfl | rfl
    · exact hAR (hu ▸ Subgroup.mem_zpowers x)
    · exact hrR

theorem eq_of_mul_inv_mem_OCW [Finite G] {W : Subgroup G} (hW2 : IsPGroup 2 W) {x y : G}
    (hx : x ∈ W) (hy : y ∈ W) (h : x * y⁻¹ ∈ OCW W) : x = y := by
  have h2 : IsPGroup 2 (Subgroup.zpowers (x * y⁻¹)) :=
    hW2.to_le (Subgroup.zpowers_le.mpr (W.mul_mem hx (W.inv_mem hy)))
  have h1 := eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard _) h h2
  exact mul_inv_eq_one.mp h1

theorem braid_of_order_three {Q : Type*} [Group Q] {x y : Q} (hx : x * x = 1) (hy : y * y = 1)
    (hxy : (x * y) ^ 3 = 1) : y * x * y = x * y * x := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have h1 : x * y * x * (y * x * y) = 1 := by
    rw [pow_three] at hxy
    calc x * y * x * (y * x * y) = x * y * (x * y * (x * y)) := by group
      _ = 1 := hxy
  calc y * x * y = (x * y * x)⁻¹ * (x * y * x * (y * x * y)) := by group
    _ = (x * y * x)⁻¹ := by rw [h1, mul_one]
    _ = x⁻¹ * y⁻¹ * x⁻¹ := by group
    _ = x * y * x := by rw [hxi, hyi]

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7
