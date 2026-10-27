module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBHyp

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

@[expose] def ConjFixStatement : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (h : Hyp52 H) (g : H), g ∈ h.W →
    g⁻¹ * h.a * g ∈ h.S → g⁻¹ * h.a * g ∉ h.P →
    h.B = h.P ⊓ centralizer ({g⁻¹ * h.a * g} : Set H) ⊓ coreActionKernel (conjugate h.J g) ∧
      g⁻¹ * h.a * g ∉ closure ((h.D : Set H) ∪ {h.a}) ⊓ centralizer ({h.x} : Set H)

@[expose] def SylowKernelStatement : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (h : Hyp52 H), h.B ≤ coreActionKernel h.V ∧
    ∃ R : Sylow 2 ↥(coreActionKernel h.V),
      (R : Subgroup _) = h.B.subgroupOf (coreActionKernel h.V)

theorem Hyp52.B_le_T {H : Type} [Group H] [Finite H] (h : Hyp52 H) : h.B ≤ h.T := by
  intro y hy
  have h1 := h.B_le hy
  exact mem_inf.mpr ⟨mem_inf.mpr ⟨(mem_inf.mp h1).1, le_normalizer hy⟩, h1⟩

instance Hyp52.B_subgroupOf_T_normal {H : Type} [Group H] [Finite H] (h : Hyp52 H) :
    (h.B.subgroupOf h.T).Normal :=
  (normal_subgroupOf_iff_le_normalizer h.B_le_T).mpr fun _ hy => (mem_inf.mp (mem_inf.mp hy).1).2

@[expose] def EmbedsTQuotStatement : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (h : Hyp59 H),
    ∃ f : ↥h.B →* ↥h.T ⧸ h.B.subgroupOf h.T, Function.Injective f

end CFSG.ComponentClassification.GSThmB
