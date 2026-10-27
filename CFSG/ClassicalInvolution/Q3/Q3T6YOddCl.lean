module

public import CFSG.ClassicalInvolution.Basic
public import CFSG.ClassicalInvolution.Generic.SL2Anticommute
public import CFSG.ClassicalInvolution.Q3.Q3T6BAutCO
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6Y

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3.Q3T6B

variable {F : Type} [Group F] [Finite F]

@[expose] def oddClosure (L : Subgroup F) : Subgroup F :=
  Subgroup.closure {g : F | g ∈ L ∧ Odd (orderOf g)}

theorem oddClosure_le (L : Subgroup F) : oddClosure L ≤ L :=
  (Subgroup.closure_le L).mpr fun _ hg => hg.1

theorem mem_oddClosure_of_odd {L : Subgroup F} {g : F} (hg : g ∈ L) (hodd : Odd (orderOf g)) :
    g ∈ oddClosure L :=
  Subgroup.subset_closure ⟨hg, hodd⟩

theorem oddClosure_le_closure_odd (L : Subgroup F) :
    oddClosure L ≤ Subgroup.closure {g : F | g ∈ oddClosure L ∧ Odd (orderOf g)} :=
  (Subgroup.closure_le _).mpr fun _ hg =>
    Subgroup.subset_closure ⟨mem_oddClosure_of_odd hg.1 hg.2, hg.2⟩

theorem oddClosure_normalized {L : Subgroup F} {n : F} (hn : n ∈ Subgroup.normalizer (L : Set F)) :
    n ∈ Subgroup.normalizer ((oddClosure L : Subgroup F) : Set F) := by
  have key : ∀ m ∈ Subgroup.normalizer (L : Set F), ∀ a ∈ oddClosure L,
      m * a * m⁻¹ ∈ oddClosure L := by
    intro m hm a ha
    have hcl : oddClosure L ≤ (oddClosure L).comap (MulAut.conj m).toMonoidHom := by
      refine (Subgroup.closure_le _).mpr fun g hg => ?_
      show m * g * m⁻¹ ∈ oddClosure L
      refine mem_oddClosure_of_odd ?_ ?_
      · exact (Subgroup.mem_normalizer_iff.mp hm g).mp hg.1
      · rw [orderOf_conj_eq]
        exact hg.2
    exact hcl ha
  rw [Subgroup.mem_normalizer_iff]
  intro a
  refine ⟨fun ha => key n hn a ha, fun ha => ?_⟩
  have := key n⁻¹ (Subgroup.inv_mem _ hn) _ ha
  simpa [mul_assoc] using this

theorem isSubnormal_oddClosure {L M : Subgroup F} (h : IsSubnormal L M) :
    IsSubnormal (oddClosure L) M := by
  induction h with
  | refl H =>
    refine IsSubnormal.step (oddClosure_le H) ?_ (IsSubnormal.refl H)
    rw [Subgroup.normal_subgroupOf_iff (oddClosure_le H)]
    intro k d hk hd
    have := oddClosure_normalized (L := H) (Subgroup.le_normalizer hd)
    exact (Subgroup.mem_normalizer_iff.mp this k).mp hk
  | @step L L₂ M hle hnormal hsub ih =>
    refine IsSubnormal.step ((oddClosure_le L).trans hle) ?_ hsub
    rw [Subgroup.normal_subgroupOf_iff ((oddClosure_le L).trans hle)]
    intro k d hk hd
    have hLn : d ∈ Subgroup.normalizer (L : Set F) := by
      rw [Subgroup.mem_normalizer_iff]
      intro l
      constructor
      · intro hl
        have h2 : (⟨l, hle hl⟩ : L₂) ∈ L.subgroupOf L₂ := Subgroup.mem_subgroupOf.mpr hl
        exact Subgroup.mem_subgroupOf.mp (hnormal.conj_mem _ h2 ⟨d, hd⟩)
      · intro hl
        have h2 : (⟨d * l * d⁻¹, hle hl⟩ : L₂) ∈ L.subgroupOf L₂ := Subgroup.mem_subgroupOf.mpr hl
        have := hnormal.conj_mem _ h2 ⟨d⁻¹, L₂.inv_mem hd⟩
        simpa [mul_assoc] using Subgroup.mem_subgroupOf.mp this
    exact (Subgroup.mem_normalizer_iff.mp (oddClosure_normalized hLn) k).mp hk

end CFSG.ClassicalInvolution.Q3.Q3T6Y
