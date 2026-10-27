module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalE7Check
public import CFSG.LieType.Chevalley.RationalToralSignDiagram

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.Steinberg.Adjoint CFSG.ClassicalInvolution.ModelFacts

section Check

variable {τ : Tag} (C : RootCertificate τ)

@[expose] def connectedCheck (m : ℕ) : Bool :=
  (List.range C.roots.length).any fun k₀ => inKernel C m k₀ &&
    (List.range C.roots.length).all fun k => !inKernel C m k ||
      decide (cpair (C.root k₀) (C.root k) ≠ 0) ||
      (List.range C.roots.length).any fun k' => inKernel C m k' &&
        decide (cpair (C.root k₀) (C.root k') ≠ 0) && decide (cpair (C.root k') (C.root k) ≠ 0)

variable {C}

theorem subsingleton_of_connectedCheck (hC : C.check = true)
    (hS : τ.symmetrizedCartan = τ.cartan) {m : ℕ} (h : connectedCheck C m = true) :
    Subsingleton (KernelComponent (signMaskChar τ m)) := by
  simp only [connectedCheck, List.any_eq_true, List.mem_range, Bool.and_eq_true,
    List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
  obtain ⟨k₀, hk₀, hker₀, hall⟩ := h
  have hr₀ : C.root k₀ ∈ kernelRoots (signMaskChar τ m) :=
    (mem_kernelRoots_iff hC).2 ⟨k₀, hk₀, rfl, hker₀⟩
  have key : ∀ (α : Fin τ.rank → ℤ) (hα : α ∈ kernelRoots (signMaskChar τ m)),
      (⟦⟨α, hα⟩⟧ : KernelComponent (signMaskChar τ m)) = ⟦⟨C.root k₀, hr₀⟩⟧ := by
    intro α hα
    obtain ⟨k, hk, rfl, hker⟩ := (mem_kernelRoots_iff hC).1 hα
    rcases hall k hk with (h1 | h1) | ⟨k', hk', ⟨hker', h2⟩, h3⟩
    · rw [hker] at h1
      exact absurd h1 (by simp)
    · refine mk_eq_of_iform_ne_zero ?_
      change iform (C.root k) (C.root k₀) ≠ 0
      rw [iform_comm, iform_eq_cpair hS]
      exact h1
    · have hk'm : C.root k' ∈ kernelRoots (signMaskChar τ m) :=
        (mem_kernelRoots_iff hC).2 ⟨k', hk', rfl, hker'⟩
      have e1 : (⟦⟨C.root k, hα⟩⟧ : KernelComponent (signMaskChar τ m)) = ⟦⟨C.root k', hk'm⟩⟧ := by
        refine mk_eq_of_iform_ne_zero ?_
        change iform (C.root k) (C.root k') ≠ 0
        rw [iform_comm, iform_eq_cpair hS]
        exact h3
      have e2 : (⟦⟨C.root k', hk'm⟩⟧ : KernelComponent (signMaskChar τ m)) =
          ⟦⟨C.root k₀, hr₀⟩⟧ := by
        refine mk_eq_of_iform_ne_zero ?_
        change iform (C.root k') (C.root k₀) ≠ 0
        rw [iform_comm, iform_eq_cpair hS]
        exact h2
      exact e1.trans e2
  refine ⟨fun a b => ?_⟩
  induction a using Quotient.inductionOn with
  | h a =>
  induction b using Quotient.inductionOn with
  | h b =>
  exact (key a.1 a.2).trans (key b.1 b.2).symm

end Check

theorem e7_connectedCheck_two : connectedCheck e7Certificate 2 = true := by decide +kernel

theorem e7_connectedCheck_three : connectedCheck e7Certificate 3 = true := by decide +kernel

theorem e7_subsingleton_two : Subsingleton (KernelComponent (signMaskChar Tag.E7 2)) :=
  subsingleton_of_connectedCheck e7Certificate_check e7_symmetrizedCartan e7_connectedCheck_two

theorem e7_subsingleton_three : Subsingleton (KernelComponent (signMaskChar Tag.E7 3)) :=
  subsingleton_of_connectedCheck e7Certificate_check e7_symmetrizedCartan e7_connectedCheck_three

theorem e7_word_sq {r : SignRep .E7} (hr : r ∈ e7SignDiagramReps)
    {l : List (Fin Tag.E7.rank)} (hl : l ∈ r.omegaWords) (hl0 : l ≠ []) :
    wordElt Tag.E7 l * wordElt Tag.E7 l = 1 := by
  obtain ⟨h7, -, -⟩ := rational_toral_sign_diagram_arithmetic
  have hcard := h7.card_kernelPosStabilizer r hr
  have hset := h7.coe_kernelPosStabilizer r hr
  have hmem : wordElt Tag.E7 l ∈ kernelPosStabilizer (signMaskChar Tag.E7 r.mask) := by
    have : wordElt Tag.E7 l ∈
        (kernelPosStabilizer (signMaskChar Tag.E7 r.mask) : Set (WeylGroup Tag.E7)) := by
      rw [hset]
      exact ⟨l, hl, rfl⟩
    exact this
  have h2 : r.omegaOrder = 2 := by
    simp only [e7SignDiagramReps, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simp [e7OmegaWords0] at hl
      exact absurd hl hl0
    · simp [e7OmegaWords1] at hl
      exact absurd hl hl0
    · rfl
    · rfl
  have h3 := Subgroup.orderOf_dvd_natCard _ hmem
  rw [hcard, h2] at h3
  rw [← pow_two]
  exact orderOf_dvd_iff_pow_eq_one.mp h3

end CFSG.ClassicalInvolution.Q3
