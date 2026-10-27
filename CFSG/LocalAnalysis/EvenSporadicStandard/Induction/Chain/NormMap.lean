module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.UHered

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup

variable {H : Type} [Group H] {ι : Type*}

abbrev CommFamily (B : ι → Subgroup H) : Prop :=
  Pairwise fun i j => ∀ x y : H, x ∈ B i → y ∈ B j → Commute x y

variable [Fintype ι] [DecidableEq ι]

@[expose] def normHom {A : Type*} [Group A] (B : ι → Subgroup H) (hB : CommFamily B)
    (φ : ∀ i, A →* ↥(B i)) : A →* H :=
  (Subgroup.noncommPiCoprod hB).comp (MonoidHom.pi φ)

omit [DecidableEq ι] in
theorem normHom_mem {A : Type*} [Group A] (B : ι → Subgroup H) (hB : CommFamily B)
    (φ : ∀ i, A →* ↥(B i)) (x : A) : normHom B hB φ x ∈ ⨆ i, B i := by
  rw [← Subgroup.noncommPiCoprod_range (hcomm := hB)]
  exact ⟨MonoidHom.pi φ x, rfl⟩

theorem normHom_factor {A : Type*} [Group A] (B : ι → Subgroup H) (hB : CommFamily B)
    (φ : ∀ i, A →* ↥(B i)) (i₀ : ι) (x : A) :
    ∃ c ∈ centralizer (B i₀ : Set H), c ∈ ⨆ i, B i ∧
      normHom B hB φ x = c * ((φ i₀ x : ↥(B i₀)) : H) := by
  have hcomm : ∀ i ∈ (Finset.univ : Finset ι), ∀ j ∈ (Finset.univ : Finset ι), i ≠ j →
      Commute ((φ i x : ↥(B i)) : H) ((φ j x : ↥(B j)) : H) := fun i _ j _ h =>
    hB h _ _ (φ i x).2 (φ j x).2
  have hap : normHom B hB φ x = Finset.noncommProd Finset.univ (fun i => ((φ i x : ↥(B i)) : H))
      hcomm := by
    show Subgroup.noncommPiCoprod hB (MonoidHom.pi φ x) = _
    rw [Subgroup.noncommPiCoprod_apply]
    rfl
  have herase := Finset.noncommProd_erase_mul Finset.univ (Finset.mem_univ i₀)
    (fun i => ((φ i x : ↥(B i)) : H)) hcomm
  have hcomm' : ∀ i ∈ (Finset.univ.erase i₀ : Finset ι), ∀ j ∈ (Finset.univ.erase i₀ : Finset ι),
      i ≠ j → Commute ((φ i x : ↥(B i)) : H) ((φ j x : ↥(B j)) : H) := fun i hi j hj h =>
    hcomm i (Finset.mem_of_mem_erase hi) j (Finset.mem_of_mem_erase hj) h
  refine ⟨(Finset.univ.erase i₀).noncommProd (fun i => ((φ i x : ↥(B i)) : H)) hcomm', ?_, ?_, ?_⟩
  · refine Subgroup.noncommProd_mem _ hcomm' fun j hj => ?_
    have hne : j ≠ i₀ := Finset.ne_of_mem_erase hj
    refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
    exact (hB hne _ _ (φ j x).2 hy).symm
  · refine Subgroup.noncommProd_mem _ hcomm' fun j _ => ?_
    exact Subgroup.mem_iSup_of_mem j (φ j x).2
  · rw [hap, ← herase]

end CFSG.EvenSporadicStandard.Induction
