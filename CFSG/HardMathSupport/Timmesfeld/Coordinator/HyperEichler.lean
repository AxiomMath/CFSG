module

public import CFSG.HardMathSupport.Timmesfeld.Coordinator.HyperAverage
public import CFSG.ClassicalGroups.Orthogonal.RootCenters

public section

namespace CFSG.HardMathSupport.Timmesfeld.Coordinator

open Module QuadraticMap CFSG.RankThree.Classical CFSG.ClassicalGroups.Orthogonal

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {p : ℕ}

@[expose] def subRep (A : Subgroup (V ≃ₗ[K] V)) : A →* Module.End K V :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp A.subtype

variable (Q p) in
@[expose] def hyperEichlerSet (A : Subgroup (V ≃ₗ[K] V)) : Set (V ≃ₗ[K] V) :=
  {g | ∃ F : Subgroup (V ≃ₗ[K] V), F ≤ A ∧ Nat.card A ≤ p * Nat.card F ∧
    ∃ u w : V, (∀ h ∈ F, h u = u) ∧ (∀ h ∈ F, h w = w) ∧ g = eichler Q u w}

theorem closure_hyperEichlerSet_le_orthogonalGroup (A : Subgroup (V ≃ₗ[K] V)) :
    Subgroup.closure (hyperEichlerSet Q p A) ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
  rw [Subgroup.closure_le]
  rintro _ ⟨F, -, -, u, w, -, -, rfl⟩
  exact eichler_mem_orthogonalGroup Q u w

open _root_.Classical in
theorem mem_closure_hyperFixed (hp : p.Prime) (hpK : (p : K) ≠ 0)
    {A : Subgroup (V ≃ₗ[K] V)} [Finite A] (hAO : A ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hexp : ∀ x ∈ A, x ^ p = 1)
    {e : V} (he : ∀ h ∈ A, h e = e) {w : V} (hw : polar Q e w = 0) :
    w ∈ AddSubgroup.closure {x : V | polar Q e x = 0 ∧ ∃ F : Subgroup (V ≃ₗ[K] V), F ≤ A ∧
      Nat.card A ≤ p * Nat.card F ∧ ∀ h ∈ F, h x = x} := by
  let _ : CommGroup A := { (inferInstance : Group A) with
    mul_comm := fun a b => Subtype.ext (hcomm a a.2 b b.2) }
  have : Fintype A := Fintype.ofFinite A
  have hexpA : ∀ a : A, a ^ p = 1 := fun a => Subtype.ext (by
    rw [Subgroup.coe_pow]; exact hexp a a.2)
  set S := {x : V | polar Q e x = 0 ∧ ∃ F : Subgroup (V ≃ₗ[K] V), F ≤ A ∧
      Nat.card A ≤ p * Nat.card F ∧ ∀ h ∈ F, h x = x} with hS
  have hB : ∀ (g : A) (u v : V), polarBilin Q (subRep A g u) (subRep A g v) = polarBilin Q u v :=
    fun g u v => polar_map_of_mem (hAO g.2) u v
  have key : ∀ D : Subgroup A, Nat.card A ≤ p * Nat.card D →
      avgOp (subRep A) D w ∈ S := by
    intro D hD
    refine ⟨?_, D.map A.subtype, fun x hx => ?_, ?_, fun h hh => ?_⟩
    · have h1 := bilin_avgOp (polarBilin Q) hB D e w
      have he' : avgOp (subRep A) D e = e :=
        avgOp_apply_of_fixed (natCast_card_subgroup_ne_zero hp hexpA hpK D)
          (fun d _ => he d d.2)
      rw [polarBilin_apply_apply, polarBilin_apply_apply, he'] at h1
      rw [← h1, hw]
    · obtain ⟨y, -, rfl⟩ := hx
      exact y.2
    · rwa [Subgroup.card_map_of_injective A.subtype_injective]
    · obtain ⟨y, hy, rfl⟩ := hh
      exact apply_avgOp (ρ := subRep A) hy w
  have hdecomp := eq_sum_avgOp_hyper_apply hp hexpA hpK (subRep A) w
  rw [hdecomp]
  refine AddSubgroup.sub_mem _ (AddSubgroup.sum_mem _ fun F _ => ?_) ?_
  · exact AddSubgroup.subset_closure (key F.1 F.2.le)
  · rw [show ((Fintype.card (Hyper p A) : K) - 1) = (((Fintype.card (Hyper p A) : ℤ) - 1 : ℤ) : K)
      by push_cast; ring, Int.cast_smul_eq_zsmul]
    refine AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (key ⊤ ?_)) _
    rw [Subgroup.card_top]
    exact Nat.le_mul_of_pos_left _ hp.pos

theorem isRootCenter_closure_hyperEichlerSet (hp : p.Prime) (hpK : (p : K) ≠ 0)
    {A : Subgroup (V ≃ₗ[K] V)} [Finite A] (hAO : A ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hexp : ∀ x ∈ A, x ^ p = 1)
    {e : V} (he0 : e ≠ 0) (heQ : Q e = 0) (he : ∀ h ∈ A, h e = e) :
    IsRootCenter Q (Subgroup.closure (hyperEichlerSet Q p A)) e := by
  refine IsRootCenter.of_span he0 heQ {x : V | polar Q e x = 0 ∧ ∃ F : Subgroup (V ≃ₗ[K] V),
    F ≤ A ∧ Nat.card A ≤ p * Nat.card F ∧ ∀ h ∈ F, h x = x} ?_ ?_
  · rintro w ⟨hw, F, hFA, hF, hFw⟩
    exact ⟨hw, Subgroup.subset_closure ⟨F, hFA, hF, e, w, fun h hh => he h (hFA hh), hFw, rfl⟩⟩
  · intro w hw
    exact AddSubgroup.closure_mono Set.subset_union_left
      (mem_closure_hyperFixed hp hpK hAO hcomm hexp he hw)

theorem elementaryGroup_le_closure_hyperEichlerSet (hp : p.Prime) (hpK : (p : K) ≠ 0)
    (hQ : (polarBilin Q).Nondegenerate)
    {A : Subgroup (V ≃ₗ[K] V)} [Finite A] (hAO : A ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hexp : ∀ x ∈ A, x ^ p = 1)
    (P : HypPair Q) (he : ∀ h ∈ A, h P.e = P.e) (hf : ∀ h ∈ A, h P.f = P.f) :
    elementaryGroup Q ≤ Subgroup.closure (hyperEichlerSet Q p A) :=
  elementaryGroup_le_of_hypPair hQ (closure_hyperEichlerSet_le_orthogonalGroup A) P
    (isRootCenter_closure_hyperEichlerSet hp hpK hAO hcomm hexp P.e_ne_zero P.Q_e he)
    (isRootCenter_closure_hyperEichlerSet hp hpK hAO hcomm hexp P.f_ne_zero P.Q_f hf)

theorem exists_commute_of_mem_hyperEichlerSet {A : Subgroup (V ≃ₗ[K] V)}
    (hAO : A ≤ TauCeti.QuadraticMap.orthogonalGroup Q) {g : V ≃ₗ[K] V}
    (hg : g ∈ hyperEichlerSet Q p A) :
    ∃ F : Subgroup (V ≃ₗ[K] V), F ≤ A ∧ Nat.card A ≤ p * Nat.card F ∧ ∀ h ∈ F, h * g = g * h := by
  obtain ⟨F, hFA, hF, u, w, hu, hw, rfl⟩ := hg
  refine ⟨F, hFA, hF, fun h hh => ?_⟩
  have hc := eichler_conj (hAO (hFA hh)) u w
  rw [hu h hh, hw h hh] at hc
  calc h * eichler Q u w = h * eichler Q u w * h⁻¹ * h := by group
    _ = eichler Q u w * h := by rw [hc]

theorem eichler_mul_self_of_two_eq_zero (h2 : (2 : K) = 0) (u w : V) :
    eichler Q u w * eichler Q u w = 1 := by
  by_cases hw : polar Q u w = 0
  · rw [eichler_mul hw hw, ← two_smul K w, h2, zero_smul, eichler_zero_right]
  · rw [eichler_of_polar_ne_zero hw, mul_one]

end CFSG.HardMathSupport.Timmesfeld.Coordinator
