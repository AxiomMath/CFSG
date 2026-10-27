module

public import CFSG.LieType.Chevalley.RootCommutator

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint Matrix

variable {τ : Tag} {M : Type*} [CommGroup M]

@[expose] def kernelRoots (χ : Multiplicative (Fin τ.rank → ℤ) →* M) : Set (Fin τ.rank → ℤ) :=
  {α | IsRoot τ α ∧ χ (Multiplicative.ofAdd α) = 1}

@[expose] def kernelRootSetoid (χ : Multiplicative (Fin τ.rank → ℤ) →* M) :
    Setoid (kernelRoots χ) :=
  Relation.EqvGen.setoid fun α β : kernelRoots χ =>
    (α : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (β : Fin τ.rank → ℤ)) ≠ 0

abbrev KernelComponent (χ : Multiplicative (Fin τ.rank → ℤ) →* M) : Type :=
  Quotient (kernelRootSetoid χ)

@[expose] def componentRootSpan
    (K : Type) [Field K] (χ : Multiplicative (Fin τ.rank → ℤ) →* M)
    (i : KernelComponent χ) : Subgroup (Module.End K (RootModule τ K))ˣ :=
  rootSpan τ K {α | ∃ h : α ∈ kernelRoots χ, (⟦⟨α, h⟩⟧ : KernelComponent χ) = i}

theorem dotProduct_mulVec_eq_iform (u v : Fin τ.rank → ℤ) :
    u ⬝ᵥ (τ.symmetrizedCartan *ᵥ v) = iform u v :=
  dotProduct_mulVec_symmetrizedCartan_eq_sum u v

variable {χ : Multiplicative (Fin τ.rank → ℤ) →* M}

theorem mk_eq_of_iform_ne_zero {α β : kernelRoots χ}
    (h : iform (α : Fin τ.rank → ℤ) β ≠ 0) : (⟦α⟧ : KernelComponent χ) = ⟦β⟧ :=
  Quotient.sound (Relation.EqvGen.rel _ _ (by rwa [dotProduct_mulVec_eq_iform]))

theorem iform_eq_zero_of_mk_ne {α β : kernelRoots χ} (h : (⟦α⟧ : KernelComponent χ) ≠ ⟦β⟧) :
    iform (α : Fin τ.rank → ℤ) β = 0 := by
  by_contra h'
  exact h (mk_eq_of_iform_ne_zero h')

theorem chi_nsmul_add {α β : Fin τ.rank → ℤ} (hα : χ (Multiplicative.ofAdd α) = 1)
    (hβ : χ (Multiplicative.ofAdd β) = 1) (a b : ℕ) :
    χ (Multiplicative.ofAdd (a • α + b • β)) = 1 := by
  rw [ofAdd_add, ofAdd_nsmul, ofAdd_nsmul, map_mul, map_pow, map_pow, hα, hβ, one_pow, one_pow,
    mul_one]

theorem not_isRoot_of_mk_ne
    {α β : kernelRoots χ} (h : (⟦α⟧ : KernelComponent χ) ≠ ⟦β⟧)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    ¬IsRoot τ (a • (α : Fin τ.rank → ℤ) + b • (β : Fin τ.rank → ℤ)) := by
  intro hγ
  set γ : kernelRoots χ := ⟨a • (α : Fin τ.rank → ℤ) + b • (β : Fin τ.rank → ℤ),
    hγ, chi_nsmul_add α.2.2 β.2.2 a b⟩
  have h0 : iform (α : Fin τ.rank → ℤ) β = 0 := iform_eq_zero_of_mk_ne h
  have h0' : iform (β : Fin τ.rank → ℤ) α = 0 := by rw [iform_comm]; exact h0
  have hαα := iform_self_pos α.2.1.ne_zero
  have hββ := iform_self_pos β.2.1.ne_zero
  have hγα : iform (γ : Fin τ.rank → ℤ) α ≠ 0 := by
    change iform (a • (α : Fin τ.rank → ℤ) + b • (β : Fin τ.rank → ℤ)) α ≠ 0
    rw [← Nat.cast_smul_eq_nsmul ℤ a, ← Nat.cast_smul_eq_nsmul ℤ b, iform_add_left,
      iform_smul_left, iform_smul_left, h0', mul_zero, add_zero]
    have : (0 : ℤ) < a := by exact_mod_cast ha
    positivity
  have hγβ : iform (γ : Fin τ.rank → ℤ) β ≠ 0 := by
    change iform (a • (α : Fin τ.rank → ℤ) + b • (β : Fin τ.rank → ℤ)) β ≠ 0
    rw [← Nat.cast_smul_eq_nsmul ℤ a, ← Nat.cast_smul_eq_nsmul ℤ b, iform_add_left,
      iform_smul_left, iform_smul_left, h0, mul_zero, zero_add]
    have : (0 : ℤ) < b := by exact_mod_cast hb
    positivity
  exact h ((mk_eq_of_iform_ne_zero hγα).symm.trans (mk_eq_of_iform_ne_zero hγβ))

theorem commute_of_forall_not_isRoot
    {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β)
    (hne : α ≠ β) (hne' : α ≠ -β)
    (h : ∀ a b : ℕ, 0 < a → 0 < b → ¬IsRoot τ (a • α + b • β)) (R : Type) [CommRing R] :
    ∀ x ∈ rootSubgroup τ R α, ∀ y ∈ rootSubgroup τ R β, Commute x y := by
  obtain ⟨-, hmem, -, -, hF⟩ := root_commutator_formula τ hα hβ hne hne'
  have hnil : commPairs τ α β = [] :=
    List.eq_nil_iff_forall_not_mem.2 fun p hp => by
      obtain ⟨h1, h2, h3⟩ := (hmem p).1 hp
      exact h p.1 p.2 h1 h2 h3
  intro x hx y hy
  obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
  obtain ⟨d, rfl⟩ := mem_rootSubgroup.1 hy
  have h0 := hF R c d
  rw [hnil, List.map_nil, List.prod_nil] at h0
  calc pinnedX τ R α c * pinnedX τ R β d =
        (pinnedX τ R α c * pinnedX τ R β d * pinnedX τ R α (-c) * pinnedX τ R β (-d)) *
          (pinnedX τ R β d * pinnedX τ R α c) := by
        rw [← pinnedX_neg, ← pinnedX_neg]
        group
    _ = pinnedX τ R β d * pinnedX τ R α c := by rw [h0, one_mul]

theorem commute_of_mk_ne
    {α β : kernelRoots χ} (h : (⟦α⟧ : KernelComponent χ) ≠ ⟦β⟧)
    (K : Type) [Field K] :
    ∀ x ∈ rootSubgroup τ K α, ∀ y ∈ rootSubgroup τ K β, Commute x y := by
  have hne : (α : Fin τ.rank → ℤ) ≠ β := fun e => h (by rw [Subtype.ext e])
  have hne' : (α : Fin τ.rank → ℤ) ≠ -(β : Fin τ.rank → ℤ) := fun e => by
    have h0 := iform_eq_zero_of_mk_ne h
    rw [e, ← neg_one_smul ℤ (β : Fin τ.rank → ℤ), iform_smul_left] at h0
    have := iform_self_pos β.2.1.ne_zero
    omega
  exact commute_of_forall_not_isRoot α.2.1 β.2.1 hne hne'
    (fun a b ha hb => not_isRoot_of_mk_ne h ha hb) K

variable (K : Type) [Field K]

theorem componentRootSpan_le
    (i : KernelComponent χ) :
    componentRootSpan K χ i ≤ rootSpan τ K (kernelRoots χ) :=
  iSup₂_le fun α ⟨hα, _⟩ => le_iSup₂_of_le (f := fun α (_ : α ∈ kernelRoots χ) =>
    rootSubgroup τ K α) α hα le_rfl

theorem rootSubgroup_le_componentRootSpan
    (α : kernelRoots χ) :
    rootSubgroup τ K α ≤ componentRootSpan K χ ⟦α⟧ :=
  le_iSup₂_of_le (f := fun β (_ : β ∈ {β | ∃ h : β ∈ kernelRoots χ,
    (⟦⟨β, h⟩⟧ : KernelComponent χ) = ⟦α⟧}) => rootSubgroup τ K β) α ⟨α.2, rfl⟩ le_rfl

theorem iSup_componentRootSpan :
    ⨆ i : KernelComponent χ, componentRootSpan K χ i = rootSpan τ K (kernelRoots χ) :=
  le_antisymm (iSup_le fun i => componentRootSpan_le K i)
    (iSup₂_le fun α hα => (rootSubgroup_le_componentRootSpan K ⟨α, hα⟩).trans
      (le_iSup (fun i => componentRootSpan K χ i) _))

theorem componentRootSpan_le_centralizer
    {i j : KernelComponent χ} (hij : i ≠ j) :
    componentRootSpan K χ i ≤ Subgroup.centralizer (componentRootSpan K χ j : Set _) := by
  refine iSup₂_le fun α ⟨hα, hαi⟩ => ?_
  rw [Subgroup.le_centralizer_iff]
  refine iSup₂_le fun β ⟨hβ, hβj⟩ => ?_
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hne : (⟦⟨α, hα⟩⟧ : KernelComponent χ) ≠ ⟦⟨β, hβ⟩⟧ := by rw [hαi, hβj]; exact hij
  exact (commute_of_mk_ne hne K x hx y hy).eq

theorem commutator_componentRootSpan_eq_bot
    {i j : KernelComponent χ} (hij : i ≠ j) :
    ⁅componentRootSpan K χ i, componentRootSpan K χ j⁆ = ⊥ :=
  (Subgroup.commutator_eq_bot_iff_le_centralizer).2 (componentRootSpan_le_centralizer K hij)

theorem rootSpan_le_normalizer
    (i : KernelComponent χ) :
    rootSpan τ K (kernelRoots χ) ≤
      Subgroup.normalizer (componentRootSpan K χ i : Set (Module.End K (RootModule τ K))ˣ) := by
  rw [← iSup_componentRootSpan K]
  refine iSup_le fun j => ?_
  by_cases hij : j = i
  · subst hij
    exact Subgroup.le_normalizer
  · exact (componentRootSpan_le_centralizer K hij).trans (Subgroup.centralizer_le_normalizer _)

open _root_.Classical in
theorem root_character_kernel_orthogonal_central_product
    (τ : Tag) (K : Type) [Field K]
    {M : Type*} [CommGroup M] (χ : Multiplicative (Fin τ.rank → ℤ) →* M) :
    (kernelRoots χ).Finite ∧ Finite (KernelComponent χ) ∧
    (∀ i j : KernelComponent χ, i ≠ j →
      ⁅componentRootSpan K χ i, componentRootSpan K χ j⁆ = ⊥) ∧
    (∀ i : KernelComponent χ, componentRootSpan K χ i ≤ rootSpan τ K (kernelRoots χ) ∧
      ((componentRootSpan K χ i).subgroupOf (rootSpan τ K (kernelRoots χ))).Normal) ∧
    (∃ μ : ((i : KernelComponent χ) → componentRootSpan K χ i) →*
        rootSpan τ K (kernelRoots χ),
      (∀ (i : KernelComponent χ) (x : componentRootSpan K χ i),
        ((μ (Pi.mulSingle i x) : rootSpan τ K (kernelRoots χ)) :
          (Module.End K (RootModule τ K))ˣ) = x) ∧
      Function.Surjective μ ∧
      ∀ s ∈ μ.ker, ∀ i, s i ∈ Subgroup.center (componentRootSpan K χ i)) ∧
    (kernelRoots χ = ∅ →
      rootSpan τ K (kernelRoots χ) = ⊥ ∧ IsEmpty (KernelComponent χ)) := by
  classical
  have hfin : (kernelRoots χ).Finite := (finite_setOf_isRoot τ).subset fun α h => h.1
  have : Finite (kernelRoots χ) := hfin.to_subtype
  have : Fintype (KernelComponent χ) := Fintype.ofFinite _
  have hcomm : Pairwise fun i j : KernelComponent χ => ∀ x y : (Module.End K (RootModule τ K))ˣ,
      x ∈ componentRootSpan K χ i → y ∈ componentRootSpan K χ j → Commute x y :=
    fun i j hij x y hx hy =>
      (Subgroup.mem_centralizer_iff.1 (componentRootSpan_le_centralizer K hij hx) y hy).symm
  set ν := Subgroup.noncommPiCoprod hcomm with hν
  have hrange : ν.range = rootSpan τ K (kernelRoots χ) := by
    rw [hν, Subgroup.noncommPiCoprod_range, iSup_componentRootSpan]
  have hmemν : ∀ s, ν s ∈ rootSpan τ K (kernelRoots χ) := fun s => by
    rw [← hrange]
    exact ⟨s, rfl⟩
  set μ := ν.codRestrict (rootSpan τ K (kernelRoots χ)) hmemν with hμ
  refine ⟨hfin, inferInstance, fun i j hij => commutator_componentRootSpan_eq_bot K hij,
    fun i => ⟨componentRootSpan_le K i, (Subgroup.normal_subgroupOf_iff_le_normalizer
      (componentRootSpan_le K i)).2 (rootSpan_le_normalizer K i)⟩,
    ⟨μ, fun i x => ?_, fun g => ?_, fun s hs i => ?_⟩, fun h => ⟨?_, ?_⟩⟩
  · change ν (Pi.mulSingle i x) = x
    rw [hν, Subgroup.noncommPiCoprod_mulSingle]
  · obtain ⟨s, hs⟩ : (g : (Module.End K (RootModule τ K))ˣ) ∈ ν.range := by
      rw [hrange]
      exact g.2
    exact ⟨s, Subtype.ext hs⟩
  ·
    have h1 : ν s = 1 := congrArg Subtype.val ((MonoidHom.mem_ker).1 hs)
    set P := (Finset.univ.erase i).noncommProd (fun j => ((s j : componentRootSpan K χ j) :
      (Module.End K (RootModule τ K))ˣ)) (fun j _ k _ h => hcomm h _ _ (s j).2 (s k).2) with hP
    have h2 : ((s i : componentRootSpan K χ i) : (Module.End K (RootModule τ K))ˣ) * P =
        ν s := by
      rw [hν, Subgroup.noncommPiCoprod_apply]
      exact Finset.mul_noncommProd_erase Finset.univ (Finset.mem_univ i)
        (fun j => ((s j : componentRootSpan K χ j) : (Module.End K (RootModule τ K))ˣ)) _
    rw [h1] at h2
    have hPC : P ∈ Subgroup.centralizer (componentRootSpan K χ i :
        Set (Module.End K (RootModule τ K))ˣ) :=
      Subgroup.noncommProd_mem _ _ fun j hj =>
        componentRootSpan_le_centralizer K (Finset.ne_of_mem_erase hj) (s j).2
    have hsi : ((s i : componentRootSpan K χ i) : (Module.End K (RootModule τ K))ˣ) = P⁻¹ :=
      eq_inv_of_mul_eq_one_left h2
    rw [Subgroup.mem_center_iff]
    intro g
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul]
    rw [hsi]
    exact ((Subgroup.mem_centralizer_iff.1 (inv_mem hPC)) g g.2)
  · rw [h]
    simp [rootSpan]
  · exact ⟨fun q => Quotient.inductionOn q fun α => Set.notMem_empty _ (h.subset α.2)⟩

end CFSG.LieType.Chevalley
