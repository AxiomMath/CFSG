module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PerfectResiduals

public section

namespace CFSG.OddStandard.Seitz77.CaseB45

open Subgroup CFSG.RankThreeCoreUniqueness.Helpers

section Conj

variable {G : Type*} [Group G]

@[expose] def cs (g : G) (H : Subgroup G) : Subgroup G :=
  H.map (MulAut.conj g).toMonoidHom

theorem mem_cs {g x : G} {H : Subgroup G} : x ∈ cs g H ↔ g⁻¹ * x * g ∈ H := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    have e : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    simpa [e] using hy
  · intro h
    exact ⟨g⁻¹ * x * g, h, by simp [mul_assoc]⟩

theorem mem_cs_iff {g x : G} {H : Subgroup G} : g * x * g⁻¹ ∈ cs g H ↔ x ∈ H := by
  rw [mem_cs]
  simp [mul_assoc]

theorem cs_one (H : Subgroup G) : cs (1 : G) H = H := by
  ext x
  simp [mem_cs]

theorem cs_mul (g h : G) (H : Subgroup G) : cs (g * h) H = cs g (cs h H) := by
  ext x
  simp [mem_cs, mul_assoc]

theorem cs_inv_cs (g : G) (H : Subgroup G) : cs g⁻¹ (cs g H) = H := by
  rw [← cs_mul, inv_mul_cancel, cs_one]

theorem cs_cs_inv (g : G) (H : Subgroup G) : cs g (cs g⁻¹ H) = H := by
  rw [← cs_mul, mul_inv_cancel, cs_one]

theorem cs_mono (g : G) {H K : Subgroup G} (h : H ≤ K) : cs g H ≤ cs g K := fun _ hx =>
  mem_cs.2 (h (mem_cs.1 hx))

theorem cs_commutator (g : G) (H K : Subgroup G) : cs g ⁅H, K⁆ = ⁅cs g H, cs g K⁆ := by
  unfold cs
  rw [Subgroup.map_commutator]

theorem cs_sup (g : G) (H K : Subgroup G) : cs g (H ⊔ K) = cs g H ⊔ cs g K := by
  unfold cs
  rw [Subgroup.map_sup]

theorem cs_inf (g : G) (H K : Subgroup G) : cs g (H ⊓ K) = cs g H ⊓ cs g K := by
  ext x
  simp [mem_cs]

theorem nat_card_cs (g : G) (H : Subgroup G) : Nat.card (cs g H) = Nat.card H := by
  unfold cs
  exact Nat.card_congr (Subgroup.equivMapOfInjective H (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).toEquiv.symm

theorem cs_normalizer (g : G) (H : Subgroup G) :
    cs g (normalizer (H : Set G)) = normalizer ((cs g H : Subgroup G) : Set G) := by
  ext x
  rw [mem_cs, mem_normalizer_iff, mem_normalizer_iff]
  constructor
  · intro h y
    have h1 := h (g⁻¹ * y * g)
    have e : g⁻¹ * x * g * (g⁻¹ * y * g) * (g⁻¹ * x * g)⁻¹ = g⁻¹ * (x * y * x⁻¹) * g := by group
    rw [e] at h1
    rw [mem_cs, mem_cs]
    exact h1
  · intro h y
    have h1 := h (g * y * g⁻¹)
    rw [mem_cs, mem_cs] at h1
    have e1 : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    have e2 : g⁻¹ * (x * (g * y * g⁻¹) * x⁻¹) * g =
        g⁻¹ * x * g * y * (g⁻¹ * x * g)⁻¹ := by group
    rw [e1, e2] at h1
    exact h1

end Conj

section Residual

variable {G : Type*} [Group G]

theorem perfectResidualOf_le' (H : Subgroup G) : perfectResidualOf H ≤ H :=
  Subgroup.map_subtype_le _

theorem perfectResidualOf_perfect [Finite G] (H : Subgroup G) :
    ⁅perfectResidualOf H, perfectResidualOf H⁆ = perfectResidualOf H :=
  Subgroup.isPerfect_iff.1 (finite_perfectResidualOf_isPerfect H)

theorem le_perfectResidualOf_of_perfect {H Q : Subgroup G} (hQH : Q ≤ H) (hQ : ⁅Q, Q⁆ = Q) :
    Q ≤ perfectResidualOf H := by
  have hQ' : ⁅Q.subgroupOf H, Q.subgroupOf H⁆ = Q.subgroupOf H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hQH, hQ]
  have key : ∀ n : ℕ, Q.subgroupOf H ≤ derivedSeries H n := by
    intro n
    induction n with
    | zero => exact le_top
    | succ n ih =>
      rw [derivedSeries_succ]
      calc Q.subgroupOf H = ⁅Q.subgroupOf H, Q.subgroupOf H⁆ := hQ'.symm
        _ ≤ ⁅derivedSeries H n, derivedSeries H n⁆ := Subgroup.commutator_mono ih ih
  intro x hx
  refine ⟨⟨x, hQH hx⟩, ?_, rfl⟩
  show (⟨x, hQH hx⟩ : H) ∈ ⨅ index, derivedSeries H index
  rw [Subgroup.mem_iInf]
  intro n
  exact key n (Subgroup.mem_subgroupOf.2 hx)

theorem perfectResidualOf_mono [Finite G] {H K : Subgroup G} (h : H ≤ K) :
    perfectResidualOf H ≤ perfectResidualOf K :=
  le_perfectResidualOf_of_perfect ((perfectResidualOf_le' H).trans h) (perfectResidualOf_perfect H)

theorem perfectResidualOf_cs [Finite G] (g : G) (H : Subgroup G) :
    perfectResidualOf (cs g H) = cs g (perfectResidualOf H) := by
  apply le_antisymm
  · have h1 : cs g⁻¹ (perfectResidualOf (cs g H)) ≤ perfectResidualOf H := by
      apply le_perfectResidualOf_of_perfect
      · calc cs g⁻¹ (perfectResidualOf (cs g H)) ≤ cs g⁻¹ (cs g H) :=
            cs_mono _ (perfectResidualOf_le' _)
          _ = H := cs_inv_cs g H
      · rw [← cs_commutator, perfectResidualOf_perfect]
    have := cs_mono g h1
    rwa [cs_cs_inv] at this
  · apply le_perfectResidualOf_of_perfect
    · exact cs_mono g (perfectResidualOf_le' H)
    · rw [← cs_commutator, perfectResidualOf_perfect]

end Residual

end CFSG.OddStandard.Seitz77.CaseB45
