module

public import CFSG.HardMathSupport.C14IdxDet
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiagTwisted

public section

namespace CFSG.HardMathSupport.C14IdxDet

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {τ : Tag}

private theorem finite_rootSubtype (τ : Tag) :
    Finite {v : Fin τ.rank → ℤ // IsRoot τ v} := by
  refine Finite.of_surjective
    (fun p : WeylGroup τ × Fin τ.rank =>
      (⟨p.1 • Pi.single p.2 1, isRoot_iff_exists_smul_single.2 ⟨p.1, p.2, rfl⟩⟩ :
        {v : Fin τ.rank → ℤ // IsRoot τ v})) ?_
  rintro ⟨v, hv⟩
  obtain ⟨w, j, rfl⟩ := isRoot_iff_exists_smul_single.1 hv
  exact ⟨(w, j), rfl⟩

private theorem finite_label (τ : Tag) : Finite (Label τ) := by
  haveI : Finite {v : Fin τ.rank → ℤ // IsRoot τ v} := finite_rootSubtype τ
  infer_instance

theorem exists_pos_nsmul_single_mem_closure_latGen (Ψ : Set (Fin τ.rank → ℤ)) :
    ∃ N : ℕ, 0 < N ∧ ∀ i, (N • Pi.single i 1 : Fin τ.rank → ℤ) ∈
      AddSubgroup.closure (latGen (τ := τ) Ψ) := by
  classical
  haveI : Finite (Label τ) := finite_label τ
  let ℓ : Fin τ.rank → Label τ := fun j => Sum.inr ⟨Pi.single j 1, IsRoot.basis j⟩
  let m : Fin τ.rank → ℕ := fun j => Nat.card (wtClass Ψ (ℓ j))
  refine ⟨∏ j, m j, Finset.prod_pos fun j _ => ?_, fun i => ?_⟩
  · haveI : Nonempty (wtClass Ψ (ℓ j)) := ⟨ℓ j, fun lam _ => by simp [WtEquiv]⟩
    exact Nat.card_pos
  · have hgen : (m i : ℤ) • labelWt τ (ℓ i) ∈ AddSubgroup.closure (latGen (τ := τ) Ψ) :=
      AddSubgroup.subset_closure (Or.inr ⟨ℓ i, rfl⟩)
    have hmem : ((Finset.univ.erase i).prod m) • ((m i : ℤ) • labelWt τ (ℓ i)) ∈
        AddSubgroup.closure (latGen (τ := τ) Ψ) :=
      AddSubgroup.nsmul_mem _ hgen _
    rw [← natCast_zsmul]
    have heq : ((∏ j, m j : ℕ) : ℤ) • Pi.single i 1
        = ((Finset.univ.erase i).prod m) • ((m i : ℤ) • labelWt τ (ℓ i)) := by
      have hN : (∏ j, m j : ℕ) = (Finset.univ.erase i).prod m * m i :=
        (Finset.prod_erase_mul Finset.univ m (Finset.mem_univ i)).symm
      rw [hN, Nat.cast_mul, mul_smul, natCast_zsmul]
      simp [labelWt, ℓ]
    rw [heq]
    exact hmem

end CFSG.HardMathSupport.C14IdxDet

namespace CFSG.HardMathSupport.C14Idx

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {τ : Tag} {L : Type} [Field L] {ι : Type}

theorem famZ_mem_adjointGroup_and_comm
    [IsAlgClosed L] (a : ι → Fin τ.rank → Lˣ) :
    ∀ g ∈ famZ a, g ∈ adjointGroup τ L ∧ ∀ m ∈ famM a, g * m = m * g := by
  intro g hg
  constructor
  · have hle : famZ a ≤ adjointGroup τ L := by
      rw [famZ, Subgroup.closure_le]
      rintro _ ⟨lam, c, hlam, rfl⟩
      exact CFSG.HardMathSupport.Timmesfeld.CrossChar.rootDiagUnit_mem_adjointGroup_of_isAlgClosed
        (τ := τ) (L := L) (cochar lam c)
    exact hle hg
  · intro m hm
    exact CFSG.HardMathSupport.C14IdxDet.famZ_comm_famM hg hm

theorem finite_famZ_inter_famS
    [IsAlgClosed L] (a : ι → Fin τ.rank → Lˣ) :
    Finite {g : adjointGroup τ L // (g : ModGL τ L) ∈ famZ a ∧ g ∈ famS a} := by
  obtain ⟨N, hN, hlat⟩ :=
    CFSG.HardMathSupport.C14IdxDet.exists_pos_nsmul_single_mem_closure_latGen
      (τ := τ) (CFSG.HardMathSupport.Timmesfeld.Torality.familyKernel a)
  exact CFSG.HardMathSupport.C14IdxDet.finite_famZ_inf_famS N hN hlat

end CFSG.HardMathSupport.C14Idx
