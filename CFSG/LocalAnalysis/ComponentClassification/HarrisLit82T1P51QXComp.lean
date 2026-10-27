module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcToral
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcTorus

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51Q

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.Foote5.OddLieCore.Exc

variable {τ : Tag} {K : Type} [Field K]

theorem componentRootSpan_le_toralCentralizer
    (hK2 : ringChar K ≠ 2) {c : Fin τ.rank → Kˣ}
    (hc : ∀ i, c i = 1 ∨ c i = -1) (ψ : KernelComponent (maskChar (signTupleBits c))) :
    componentRootSpan K (maskChar (signTupleBits c)) ψ ≤ toralCentralizer τ K c := by
  obtain ⟨-, -, -, hnorm, -, -⟩ :=
    root_character_kernel_orthogonal_central_product τ K (maskChar (signTupleBits c))
  have hle := (hnorm ψ).1
  rw [← rootCharKernel_eq_kernelRoots hK2 hc] at hle
  exact hle.trans (rootSpan_rootCharKernel_le_toralCentralizer c)

theorem isComponent_componentRootSpan_toral
    [Finite K]
    (hK2 : ringChar K ≠ 2) (hK5 : 5 ≤ Nat.card K) {c : Fin τ.rank → Kˣ}
    (hc : ∀ i, c i = 1 ∨ c i = -1) (ψ : KernelComponent (maskChar (signTupleBits c))) :
    IsComponent ((componentRootSpan K (maskChar (signTupleBits c)) ψ).subgroupOf
      (toralCentralizer τ K c)) := by
  have hkerχ : rootCharKernel c = kernelRoots (maskChar (signTupleBits c)) :=
    rootCharKernel_eq_kernelRoots hK2 hc
  obtain ⟨-, -, -, hnorm, -, -⟩ :=
    root_character_kernel_orthogonal_central_product τ K (maskChar (signTupleBits c))
  have hΨS : componentRootSpan K (maskChar (signTupleBits c)) ψ ≤
      rootSpan τ K (rootCharKernel c) := by
    rw [hkerχ]
    exact (hnorm ψ).1
  have hEC := componentRootSpan_le_toralCentralizer hK2 hc ψ
  refine ⟨(isQuasisimple_congr (Subgroup.subgroupOfEquivOfLe hEC)).2
    (componentRootSpan_quasisimple hK2 hK5 _ ψ), ?_⟩
  refine isSubnormal_subgroupOf_of_conj (A := rootSpan τ K (rootCharKernel c)) hΨS
    (fun t ht a ha => (Subgroup.mem_normalizer_iff.1
      (toralCentralizer_le_normalizer_rootSpan c ht) a).1 ha) fun a ha _ e he => ?_
  have ha' : a ∈ rootSpan τ K (kernelRoots (maskChar (signTupleBits c))) := hkerχ ▸ ha
  exact (Subgroup.normal_subgroupOf_iff (hnorm ψ).1).1 (hnorm ψ).2 e a he ha'

theorem commute_pinnedX_of_commute_rootFactors
    (hK2 : ringChar K ≠ 2) {c : Fin τ.rank → Kˣ}
    (hc : ∀ i, c i = 1 ∨ c i = -1) {g : toralCentralizer τ K c}
    (hg : ∀ ψ : KernelComponent (maskChar (signTupleBits c)),
      ∀ s ∈ (componentRootSpan K (maskChar (signTupleBits c)) ψ).subgroupOf
        (toralCentralizer τ K c), s * g = g * s) :
    ∀ β ∈ rootCharKernel c, ∀ t : K,
      (g : ModGL τ K) * pinnedX τ K β t = pinnedX τ K β t * g := by
  intro β hβ t
  have hβχ : β ∈ kernelRoots (maskChar (signTupleBits c)) :=
    rootCharKernel_eq_kernelRoots hK2 hc ▸ hβ
  have hmem : pinnedX τ K β t ∈ componentRootSpan K (maskChar (signTupleBits c))
      ⟦⟨β, hβχ⟩⟧ :=
    pinnedX_mem_rootSpan (S := {α | ∃ h : α ∈ kernelRoots (maskChar (signTupleBits c)),
      (⟦⟨α, h⟩⟧ : KernelComponent (maskChar (signTupleBits c))) = ⟦⟨β, hβχ⟩⟧}) ⟨hβχ, rfl⟩ t
  have hX := componentRootSpan_le_toralCentralizer hK2 hc ⟦⟨β, hβχ⟩⟧ hmem
  have h := hg ⟦⟨β, hβχ⟩⟧ ⟨pinnedX τ K β t, hX⟩ (Subgroup.mem_subgroupOf.2 hmem)
  exact (congrArg Subtype.val h).symm

end CFSG.ComponentClassification.HarrisLit.T1.P51Q
