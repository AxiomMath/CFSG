module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.RegularSolvable

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHigh

open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.SeitzGeneration.ExcHighThree

set_option linter.unusedSectionVars false

section FamilyStab


theorem isSolvable_comap_weylQuotient (τ : Tag) (L : Type) [Field L] (H : Subgroup (WeylGroup τ))
    [Group.IsSolvable ↥H] :
    ∃ ρ : monomialSubgroup τ L →* WeylGroup τ,
      (∀ g : monomialSubgroup τ L, MapsRootLines (g : (Module.End L (RootModule τ L))ˣ) (ρ g)) ∧
        Group.IsSolvable ↥(H.comap ρ) := by
  obtain ⟨-, ⟨ρ, -, hmaps, -, -, hker⟩, -⟩ := Weyl_normalizer_quotient τ L
  refine ⟨ρ, hmaps, ?_⟩
  haveI := isSolvable_torusGroup τ L
  let incl : torusGroup τ L →* monomialSubgroup τ L :=
    Subgroup.inclusion (le_sup_left : torusGroup τ L ≤ monomialSubgroup τ L)
  have hincl : ∀ t, ρ (incl t) = 1 := fun t => by
    have h : incl t ∈ ρ.ker := by
      rw [hker, Subgroup.mem_subgroupOf]
      exact t.2
    exact h
  refine Group.isSolvable_of_ker_le_range
    (incl.codRestrict (H.comap ρ) fun t => by rw [Subgroup.mem_comap, hincl t]; exact H.one_mem)
    ((ρ.comp (H.comap ρ).subtype).codRestrict H fun n => n.2) (fun n hn => ?_)
  have h1 : ρ (n : monomialSubgroup τ L) = 1 := congrArg Subtype.val hn
  have h2 : (n : monomialSubgroup τ L) ∈ ρ.ker := h1
  rw [hker, Subgroup.mem_subgroupOf] at h2
  exact ⟨⟨(n : monomialSubgroup τ L).1, h2⟩, Subtype.ext (Subtype.ext rfl)⟩

theorem isSolvable_centralizer_of_familyStab {τ : Tag} {K : Type} [Field K] [Finite K]
    {E₀ : Subgroup (adjointGroup τ K)} (D : LangPlaneData τ K E₀)
    (hreg : ∀ α, IsRoot τ α → ¬ D.Kills α)
    (hS : ∀ a : E₀ → Fin τ.rank → (AlgebraicClosure K)ˣ,
      (∀ x : E₀, rootDiagUnit τ (a x) = diagMap D x.1) →
        ∃ H : Subgroup (WeylGroup τ), Group.IsSolvable ↥H ∧ familyStabilizer a ⊆ H) :
    Group.IsSolvable ↥(Subgroup.centralizer (E₀ : Set (adjointGroup τ K))) := by
  choose a ha using fun x : E₀ =>
    exists_rootDiagUnit_of_mem_torusGroup (diagMap_mem_torusGroup D x.2)
  obtain ⟨H, hHs, hHle⟩ := hS a ha
  have hker : familyKernel a = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.2 fun α hα => hreg α hα.1 fun x hx => ?_
    exact ⟨a ⟨x, hx⟩, ha ⟨x, hx⟩, hα.2 ⟨x, hx⟩⟩
  have hgroup : familyGroup (K := AlgebraicClosure K) a = torusGroup τ (AlgebraicClosure K) := by
    rw [familyGroup, hker, rootSpan]
    simp
  have hmono : ∀ g : Subgroup.centralizer (E₀ : Set (adjointGroup τ K)),
      ∃ w ∈ H, ∃ m ∈ torusGroup τ (AlgebraicClosure K),
        diagMap D g.1 = m * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w := by
    intro g
    have hgc : diagMap D g.1 ∈ familyCentralizer τ (AlgebraicClosure K) a := by
      refine mem_familyCentralizer.2 ⟨?_, fun x => ?_⟩
      · rw [diagMap_apply]
        refine mul_mem (mul_mem ((adjointGroup _ _).inv_mem D.hg0C)
          (baseChangeGL_mem_adjointGroup' _ (D.c * g.1 * D.c⁻¹).2)) D.hg0C
      · rw [ha x, mul_inv_eq_iff_eq_mul, ← map_mul, ← map_mul]
        congr 1
        exact Subgroup.mem_centralizer_iff.1 g.2 x x.2
    obtain ⟨w, hw, m, hm, hmg⟩ := familyCentralizer_le_mul τ (AlgebraicClosure K) a hgc
    rw [hgroup] at hm
    exact ⟨w, hHle hw, m, hm, hmg⟩
  have hmem : ∀ g : Subgroup.centralizer (E₀ : Set (adjointGroup τ K)),
      diagMap D g.1 ∈ monomialSubgroup τ (AlgebraicClosure K) := by
    intro g
    obtain ⟨w, -, m, hm, hmg⟩ := hmono g
    rw [hmg]
    exact mul_mem (Subgroup.mem_sup_left hm)
      (canonicalRep_mem_monomialSubgroup (AlgebraicClosure K) w)
  let ψ : Subgroup.centralizer (E₀ : Set (adjointGroup τ K)) →*
      monomialSubgroup τ (AlgebraicClosure K) :=
    MonoidHom.codRestrict ((diagMap D).comp (Subgroup.subtype _)) _ hmem
  have hψ : Function.Injective ψ := fun g g' h =>
    Subtype.ext (diagMap_injective D (congrArg Subtype.val h))
  haveI := hHs
  obtain ⟨ρ, hρmaps, hsolv⟩ := isSolvable_comap_weylQuotient τ (AlgebraicClosure K) H
  have hρψ : ∀ g, ρ (ψ g) ∈ H := by
    intro g
    obtain ⟨w, hw, m, hm, hmg⟩ := hmono g
    have h1 : MapsRootLines (ψ g : (Module.End (AlgebraicClosure K)
        (RootModule τ (AlgebraicClosure K)))ˣ) (1 * w) := by
      have e : (ψ g : (Module.End (AlgebraicClosure K)
          (RootModule τ (AlgebraicClosure K)))ˣ) =
          m * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w := hmg
      rw [e]
      exact (mapsRootLines_of_mem_torusGroup hm).mul (mapsRootLines_canonicalRep w)
    rw [(hρmaps (ψ g)).unique h1, one_mul]
    exact hw
  let ψ' : Subgroup.centralizer (E₀ : Set (adjointGroup τ K)) →*
      ↥(H.comap ρ) := ψ.codRestrict (H.comap ρ) hρψ
  haveI := hsolv
  exact Group.isSolvable_of_isSolvable_injective (f := ψ') fun g g' h =>
    hψ (congrArg Subtype.val h)

end FamilyStab

end CFSG.LieType.SeitzGeneration.ExcHigh
