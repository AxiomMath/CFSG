module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.OrbitCount
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.PlaneAction

public section

open scoped Pointwise

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model

open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three

@[expose] noncomputable def Q0 : Subgroup Q3 :=
  L0 ⊓ MulAction.stabilizer Q3 x2

@[expose] noncomputable def D0 : Subgroup Q3 := Q0 ⊓ Zq

section Membership


theorem mem_Q0_iff {g : Q3} : g ∈ Q0 ↔ g ∈ L0 ∧ g • x2 = x2 := by
  simp [Q0, MulAction.mem_stabilizer_iff]

theorem mem_D0_iff {g : Q3} : g ∈ D0 ↔ g ∈ Q0 ∧ g ∈ Zq := Subgroup.mem_inf

theorem Q0_le_L0 : Q0 ≤ L0 := inf_le_left

theorem D0_le_Q0 : D0 ≤ Q0 := inf_le_left

theorem D0_le_Zq : D0 ≤ Zq := inf_le_right

theorem mem_Q0_iff_of_fix {g : Q3} :
    g ∈ Q0 ↔ g • x0 = x0 ∧ g • x1 = x1 ∧ g • x2 = x2 := by
  rw [mem_Q0_iff, mem_L0_iff, Zp_eq_stabilizer, MulAction.mem_stabilizer_iff, and_assoc]

theorem mem_D0_iff_of_fix {g : Q3} :
    g ∈ D0 ↔ g ∈ Zq ∧ g • x0 = x0 ∧ g • x1 = x1 ∧ g • x2 = x2 := by
  rw [mem_D0_iff, mem_Q0_iff_of_fix, and_comm]

end Membership

section Plane


theorem Zq_smul_plane {g : Q3} (hg : g ∈ Zq) : g • plane = plane := by
  have hsub : g • plane ⊆ plane := by
    intro y hy
    obtain ⟨p, hp, rfl⟩ := Finset.mem_smul_finset.1 hy
    exact Zq_preserves_plane hg hp
  have hcard : (g • plane).card = plane.card := Finset.card_smul_finset g plane
  exact Finset.eq_of_subset_of_card_le hsub hcard.ge

theorem D0_smul_plane {g : Q3} (hg : g ∈ D0) : g • plane = plane :=
  Zq_smul_plane (D0_le_Zq hg)

end Plane

section Card


private noncomputable def planeTriples : Finset (Ω × Ω × Ω) :=
  ((Finset.univ : Finset (Fin 24 × Fin 24 × Fin 24)).filter
    fun t => t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2).image
    fun t => (planePt t.1, planePt t.2.1, planePt t.2.2)

private theorem card_planeTriples : planeTriples.card = 12144 := by
  have hinj : Function.Injective
      (fun t : Fin 24 × Fin 24 × Fin 24 => (planePt t.1, planePt t.2.1, planePt t.2.2)) := by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    rw [planePt_injective h1, planePt_injective h2, planePt_injective h3]
  rw [planeTriples, Finset.card_image_of_injective _ hinj]
  decide +kernel

private theorem orbit_subset_planeTriples :
    MulAction.orbit ↥Zq ((x0, x1, x2) : Ω × Ω × Ω) ⊆ ↑planeTriples := by
  rintro _ ⟨g, rfl⟩
  have h0 := Zq_preserves_plane g.2 x0_mem_plane
  have h1 := Zq_preserves_plane g.2 x1_mem_plane
  have h2 := Zq_preserves_plane g.2 x2_mem_plane
  obtain ⟨i, hi⟩ := mem_plane_iff.1 h0
  obtain ⟨j, hj⟩ := mem_plane_iff.1 h1
  obtain ⟨k, hk⟩ := mem_plane_iff.1 h2
  have e : g • ((x0, x1, x2) : Ω × Ω × Ω) = ((g : Q3) • x0, (g : Q3) • x1, (g : Q3) • x2) := rfl
  change g • ((x0, x1, x2) : Ω × Ω × Ω) ∈ (planeTriples : Set (Ω × Ω × Ω))
  rw [e, Finset.mem_coe, planeTriples, Finset.mem_image]
  refine ⟨(i, j, k), ?_, by simp [hi, hj, hk]⟩
  have hne : ∀ {p q : Ω}, p ≠ q → (g : Q3) • p ≠ (g : Q3) • q :=
    fun h h' => h (smul_left_cancel _ h')
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨fun h => hne x0_ne_x1 ?_, fun h => hne x0_ne_x2 ?_, fun h => hne x1_ne_x2 ?_⟩
  · rw [← hi, ← hj, h]
  · rw [← hi, ← hk, h]
  · rw [← hj, ← hk, h]

private theorem stabilizer_triple_eq :
    MulAction.stabilizer ↥Zq ((x0, x1, x2) : Ω × Ω × Ω) = D0.subgroupOf Zq := by
  ext g
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, mem_D0_iff_of_fix]
  have e : g • ((x0, x1, x2) : Ω × Ω × Ω) = ((g : Q3) • x0, (g : Q3) • x1, (g : Q3) • x2) := rfl
  rw [e, Prod.mk.injEq, Prod.mk.injEq]
  exact ⟨fun h => ⟨g.2, h.1, h.2.1, h.2.2⟩, fun h => ⟨h.2.1, h.2.2.1, h.2.2.2⟩⟩

theorem card_D0_ge : Nat.card Zq ≤ 12144 * Nat.card D0 := by
  have h := card_le_mul_card_stabilizer (G := ↥Zq) planeTriples.finite_toSet
    orbit_subset_planeTriples
  rw [Set.ncard_coe_finset, card_planeTriples, stabilizer_triple_eq,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe D0_le_Zq).toEquiv] at h
  exact h

end Card

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
