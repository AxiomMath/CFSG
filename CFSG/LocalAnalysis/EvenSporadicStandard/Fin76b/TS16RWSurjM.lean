module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWSurjThm
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWPhiM
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWLab2

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Fin76b.W16

open scoped Pointwise


variable {M : Type*} [Group M] {D E : Subgroup M} {eD : D ≃* DihedralGroup 4} {t : M}
  {eltE : ℕ → M}

namespace DECtx

variable [hW : (D ⊔ E).Normal] (hctx : DECtx D E eD t eltE)

include hctx

theorem stab0_le_range
    (hΓ0 : ∀ α : MulAut ↥(D ⊔ E),
      (∀ x : ↥(D ⊔ E), (x : M) ∈ D → ((α x : ↥(D ⊔ E)) : M) ∈ D) →
      (∀ x : ↥(D ⊔ E), (x : M) ∈ E → ((α x : ↥(D ⊔ E)) : M) ∈ E) →
      ∃ m : M, MulAut.conjNormal m = α) :
    Stab0 ≤ hctx.Phi.range := by
  intro π hπ
  have hπA : (π : Equiv.Perm (Fin 128)) ∈ AutC := pg_le_autC π.2
  have hπD : π • omegaFin 0 = omegaFin 0 := hπ
  have hDmap : ∀ x : Fin 128, x ∈ omegaFin 0 → (π : Equiv.Perm (Fin 128)) x ∈ omegaFin 0 := by
    intro x hx
    have h1 : π • x ∈ π • omegaFin 0 := Finset.smul_mem_smul_finset hx
    rw [hπD] at h1
    exact h1
  have hDonto : ∀ y : Fin 128, y ∈ omegaFin 0 → ∃ x : Fin 128, x ∈ omegaFin 0 ∧
      (π : Equiv.Perm (Fin 128)) x = y := by
    intro y hy
    rw [← hπD] at hy
    obtain ⟨x, hx, hxy⟩ := Finset.mem_smul_finset.1 hy
    exact ⟨x, hx, hxy⟩
  let α : MulAut ↥(D ⊔ E) := ofPerm hctx.tabLab hltC (π : Equiv.Perm (Fin 128)) hπA
  have hα : ∀ i : Fin 128, ((α (labF hctx.tabLab i) : ↥(D ⊔ E)) : M) =
      labD eD eltE ((π : Equiv.Perm (Fin 128)) i : ℕ) := fun i => by
    have := ofPerm_apply hctx.tabLab hltC (π : Equiv.Perm (Fin 128)) hπA i
    exact congrArg Subtype.val this
  have hDD : ∀ x : ↥(D ⊔ E), (x : M) ∈ D → ((α x : ↥(D ⊔ E)) : M) ∈ D := by
    intro x hx
    obtain ⟨i, rfl⟩ := labF_surjective hctx.tabLab x
    rw [hα]
    have hxi : labD eD eltE (i : ℕ) ∈ D := hx
    have h1 : i ∈ omegaFin 0 := by
      rw [mem_omega0, ← mem_Dlist]
      exact (hctx.lab_mem_D i.2).1 hxi
    have h2 := (mem_omega0 _).1 (hDmap i h1)
    exact (hctx.lab_mem_D (Fin.is_lt _)).2 (mem_Dlist.2 h2)
  have hEE : ∀ x : ↥(D ⊔ E), (x : M) ∈ E → ((α x : ↥(D ⊔ E)) : M) ∈ E := by
    intro x hx
    obtain ⟨i, rfl⟩ := labF_surjective hctx.tabLab x
    rw [hα]
    have hxi : labD eD eltE (i : ℕ) ∈ E := hx
    have hi32 : (i : ℕ) < 32 := (hctx.lab_mem_E i.2).1 hxi
    refine (hctx.lab_mem_E (Fin.is_lt _)).2 (cent_Dset _ (Fin.is_lt _) fun d hd hdD => ?_)
    have hdF : (⟨d, hd⟩ : Fin 128) ∈ omegaFin 0 := by
      rw [mem_omega0, ← mem_Dlist]
      exact hdD
    obtain ⟨x', hx', hxd⟩ := hDonto _ hdF
    have hx'D := mem_Dlist.2 ((mem_omega0 _).1 hx')
    have hcomm : mulC (i : ℕ) (x' : ℕ) = mulC (x' : ℕ) (i : ℕ) := commE_Dset i hi32 x' x'.2 hx'D
    have h1 : (π : Equiv.Perm (Fin 128)) (mulF i x') = mulF ((π : Equiv.Perm (Fin 128)) i)
        ((π : Equiv.Perm (Fin 128)) x') := hπA i x'
    have h2 : (π : Equiv.Perm (Fin 128)) (mulF x' i) = mulF ((π : Equiv.Perm (Fin 128)) x')
        ((π : Equiv.Perm (Fin 128)) i) := hπA x' i
    have hmm : mulF i x' = mulF x' i := Fin.ext (by rw [mulF_val, mulF_val]; exact hcomm)
    rw [hmm, h2] at h1
    have h3 := congrArg Fin.val h1
    rw [mulF_val, mulF_val, hxd] at h3
    exact h3.symm
  obtain ⟨m, hm⟩ := hΓ0 α hDD hEE
  refine ⟨m, Subtype.ext ?_⟩
  rw [hctx.Phi_coe, hm]
  exact toPerm_ofPerm hctx.tabLab hltC _ hπA

theorem surj_of_moves
    (hΓ0 : ∀ α : MulAut ↥(D ⊔ E),
      (∀ x : ↥(D ⊔ E), (x : M) ∈ D → ((α x : ↥(D ⊔ E)) : M) ∈ D) →
      (∀ x : ↥(D ⊔ E), (x : M) ∈ E → ((α x : ↥(D ⊔ E)) : M) ∈ E) →
      ∃ m : M, MulAut.conjNormal m = α)
    {g : M} (hg1 : g * sElt eD 1 * g⁻¹ ≠ sElt eD 1) (hg2 : g * sElt eD 1 * g⁻¹ ≠ (sElt eD 1)⁻¹) :
    ∀ α : MulAut ↥(D ⊔ E), ∃ m : M, MulAut.conjNormal m = α := by
  have hnot : ¬ P32 ((hctx.Phi g : ↥Pg) : Equiv.Perm (Fin 128)) := by
    intro hP
    have hl := hctx.Phi_lab g ⟨32, by norm_num⟩
    rcases hP with hP | hP
    · rw [hP, hctx.lab_32] at hl
      exact hg1 hl.symm
    · rw [hP, hctx.lab_53, hctx.lab_32] at hl
      exact hg2 hl.symm
  have htop := surj_of_gen hctx.Phi.range (hctx.stab0_le_range hΓ0) (hctx.Phi g) ⟨g, rfl⟩ hnot
  intro α
  have hαA : toPerm hctx.tabLab α ∈ AutC := toPerm_mem_autC hctx.tabLab hltC α
  have hmem : (⟨toPerm hctx.tabLab α, pg_eq_autC.symm ▸ hαA⟩ : ↥Pg) ∈ hctx.Phi.range := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨m, hm⟩ := hmem
  refine ⟨m, toPerm_injective hctx.tabLab ?_⟩
  rw [← hctx.Phi_coe, hm]

end DECtx

end CFSG.EvenSporadicStandard.Fin76b.W16
