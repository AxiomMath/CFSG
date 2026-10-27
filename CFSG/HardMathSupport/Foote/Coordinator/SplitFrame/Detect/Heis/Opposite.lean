module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.QPneg
public import CFSG.Adapters.ProjectiveSpecialLinear

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint CFSG.StandardType.RootCentExc

set_option linter.unusedSectionVars false


variable (τ : Tag) (K : Type) [Field K]

theorem commute_pinnedX_of_commPairs_nil {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (hβ : IsRoot τ β) (hne : α ≠ β) (hne' : α ≠ -β) (h : commPairs τ α β = []) (c d : K) :
    Commute (pinnedX τ K α c) (pinnedX τ K β d) := by
  obtain ⟨-, -, -, -, hF⟩ := root_commutator_formula.{0} τ hα hβ hne hne'
  have h1 := hF K c d
  rw [h, List.map_nil, List.prod_nil, ← pinnedX_neg τ K α c, ← pinnedX_neg τ K β d] at h1
  exact commutatorElement_eq_one_iff_commute.1 (by rw [commutatorElement_def]; exact h1)

theorem not_isRoot_single_neg_highRoot (τ : Tag) : ∀ j : Fin τ.rank, j ≠ iθ τ →
    ∀ p ∈ commCandidates,
      p.1 • (Pi.single j 1 : Fin τ.rank → ℤ) + p.2 • (-highRoot τ) ∉ rootFinset τ ∧
      p.1 • (-Pi.single j 1 : Fin τ.rank → ℤ) + p.2 • (-highRoot τ) ∉ rootFinset τ := by
  cases τ <;> decide +kernel

theorem single_ne_highRoot (τ : Tag) : ∀ j : Fin τ.rank,
    (Pi.single j 1 : Fin τ.rank → ℤ) ≠ highRoot τ ∧ (Pi.single j 1 : Fin τ.rank → ℤ) ≠ -highRoot τ ∧
    (-Pi.single j 1 : Fin τ.rank → ℤ) ≠ highRoot τ ∧ (-Pi.single j 1 : Fin τ.rank → ℤ) ≠ -highRoot τ := by
  cases τ <;> decide +kernel

theorem neg_highRoot_mem (τ : Tag) : -highRoot τ ∈ rootFinset τ := by
  cases τ <;> decide +kernel

theorem isRoot_neg_highRoot : IsRoot τ (-highRoot τ) := mem_rootFinset.1 (neg_highRoot_mem τ)

theorem commPairs_single_neg_highRoot {j : Fin τ.rank} (hj : j ≠ iθ τ) :
    commPairs τ (Pi.single j 1) (-highRoot τ) = [] ∧
      commPairs τ (-Pi.single j 1) (-highRoot τ) = [] := by
  constructor <;> refine List.eq_nil_iff_forall_not_mem.2 fun p hp => ?_ <;>
    rw [mem_commPairs] at hp
  · exact (not_isRoot_single_neg_highRoot τ j hj p hp.1).1 (mem_rootFinset.2 hp.2)
  · exact (not_isRoot_single_neg_highRoot τ j hj p hp.1).2 (mem_rootFinset.2 hp.2)

theorem Lθ_le_normalizer_Uneg :
    Lθ τ K ≤ Subgroup.normalizer (Uneg τ K : Set (ModGL τ K)) := by
  refine sup_le (CFSG.StandardType.RootCentExc.torusGroup_le_normalizer_rootSubgroup
    (isRoot_neg_highRoot τ)) ((Subgroup.closure_le _).2 ?_)
  rintro _ ⟨j, hj, c, rfl | rfl⟩
  · refine mem_normalizer_of_forall_mul_eq fun x hx => ?_
    obtain ⟨d, rfl⟩ := mem_rootSubgroup.1 hx
    rw [← pinnedX_single]
    exact (commute_pinnedX_of_commPairs_nil τ K (isRoot_single τ j) (isRoot_neg_highRoot τ)
      (single_ne_highRoot τ j).2.1 (by simpa using (single_ne_highRoot τ j).1)
      (commPairs_single_neg_highRoot τ hj).1 c d).eq
  · refine mem_normalizer_of_forall_mul_eq fun x hx => ?_
    obtain ⟨d, rfl⟩ := mem_rootSubgroup.1 hx
    rw [← pinnedX_neg_single]
    exact (commute_pinnedX_of_commPairs_nil τ K (isRoot_neg_single τ j) (isRoot_neg_highRoot τ)
      (single_ne_highRoot τ j).2.2.2 (by simpa using (single_ne_highRoot τ j).2.2.1)
      (commPairs_single_neg_highRoot τ hj).2 c d).eq

theorem Lθ_le_Pneg : Lθ τ K ≤ Pneg τ K :=
  le_inf (parabolicLevi_le_adjointGroup τ K _) (Lθ_le_normalizer_Uneg τ K)

theorem Pθ_inf_Pneg_le_Lθ {g : ModGL τ K} (hP : g ∈ Pθ τ K) (hN : g ∈ Pneg τ K) :
    g ∈ Lθ τ K := by
  obtain ⟨-, -, -, -, -, -, hfac, -⟩ := parabolic_root_radical_Levi_factors τ K (Jθ τ)
  obtain ⟨⟨q, l⟩, ⟨hq, hl, hgql⟩, -⟩ := hfac g hP
  have hlN : l ∈ Pneg τ K := Lθ_le_Pneg τ K hl
  have hqN : q ∈ Pneg τ K := by
    have : q = g * l⁻¹ := by rw [hgql]; group
    rw [this]
    exact mul_mem hN (inv_mem hlN)
  have hq1 : q ∈ Qθ τ K ⊓ Pneg τ K := ⟨hq, hqN⟩
  rw [Qθ_inf_Pneg τ K, Subgroup.mem_bot] at hq1
  rw [hgql, hq1, one_mul]
  exact hl

theorem centralizer_Uθ_inf_centralizer_Uneg_le_Lθ {g : ModGL τ K} (hg : g ∈ adjointGroup τ K)
    (hc : ∀ x ∈ Uθ τ K, g * x = x * g) (hc' : ∀ x ∈ Uneg τ K, g * x = x * g) :
    g ∈ Lθ τ K :=
  Pθ_inf_Pneg_le_Lθ τ K (centralizer_Uθ_le_Pθ τ K hg hc)
    ⟨hg, mem_normalizer_of_forall_mul_eq hc'⟩

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
