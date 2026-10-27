module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.WeylCharStab
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerCriterion
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Subnormal
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcLang.Family

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups

private theorem torusGroup_mul_comm_aux
    {τ : Tag} {K : Type} [Field K] {x y : ModGL τ K} (hx : x ∈ torusGroup τ K)
    (hy : y ∈ torusGroup τ K) : x * y = y * x := by
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hx
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hy
  rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]


section Orbits

variable {τ : Tag} {L : Type} [Field L] {χ : Multiplicative (Fin τ.rank → ℤ) →* Lˣ}
  {ρ : Equiv.Perm (Fin τ.rank → ℤ)}

theorem rationalRoots_mapsTo (i : KernelComponent χ) :
    Set.MapsTo (ρ : (Fin τ.rank → ℤ) → _) (rationalRoots ρ χ i) (rationalRoots ρ χ i) := by
  rintro _ ⟨k, δ, hδ, rfl⟩
  exact ⟨k + 1, δ, hδ, by rw [Function.iterate_succ_apply']⟩

theorem rationalRoots_of_apply_mem (hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ)
    (i : KernelComponent χ) {δ : Fin τ.rank → ℤ} (h : ρ δ ∈ rationalRoots ρ χ i) :
    δ ∈ rationalRoots ρ χ i := by
  have hfin : (rationalRoots ρ χ i).Finite :=
    ((finite_setOf_isRoot τ).subset fun α hα => hα.1 : (kernelRoots χ).Finite).subset
      (rationalRoots_subset_kernelRoots hker i)
  have hbij := (hfin.injOn_iff_bijOn_of_mapsTo (rationalRoots_mapsTo i)).1 ρ.injective.injOn
  obtain ⟨γ, hγ, hγδ⟩ := hbij.surjOn h
  exact ρ.injective hγδ ▸ hγ

theorem rationalRoots_of_iterate_mem (hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ)
    (i : KernelComponent χ) (n : ℕ) {δ : Fin τ.rank → ℤ}
    (h : (ρ : (Fin τ.rank → ℤ) → _)^[n] δ ∈ rationalRoots ρ χ i) : δ ∈ rationalRoots ρ χ i := by
  induction n generalizing δ with
  | zero => exact h
  | succ n ih =>
    rw [Function.iterate_succ_apply] at h
    exact rationalRoots_of_apply_mem hker i (ih h)

theorem iterate_mem_rationalRoots (i : KernelComponent χ) (n : ℕ) {γ : Fin τ.rank → ℤ}
    (h : γ ∈ rationalRoots ρ χ i) : (ρ : (Fin τ.rank → ℤ) → _)^[n] γ ∈ rationalRoots ρ χ i := by
  obtain ⟨k, δ, hδ, rfl⟩ := h
  exact ⟨n + k, δ, hδ, by rw [Function.iterate_add_apply]⟩

theorem rationalRoots_subset_of_mem_inter (hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ)
    (hform : ∀ γ δ, CFSG.LieType.Steinberg.Adjoint.iform (ρ γ) (ρ δ) =
      CFSG.LieType.Steinberg.Adjoint.iform γ δ) {i j : KernelComponent χ}
    {δ : Fin τ.rank → ℤ} (hi : δ ∈ rationalRoots ρ χ i) (hj : δ ∈ rationalRoots ρ χ j) :
    rationalRoots ρ χ j ⊆ rationalRoots ρ χ i := by
  obtain ⟨n, δ₂, ⟨hδ₂, hδ₂j⟩, rfl⟩ := hj
  have hδ₂i : δ₂ ∈ rationalRoots ρ χ i := rationalRoots_of_iterate_mem hker i n hi
  rintro _ ⟨l, ε₂, ⟨hε₂, hε₂j⟩, rfl⟩
  exact iterate_mem_rationalRoots i l
    (rationalRoots_closed hker hform i hδ₂i hε₂ (hε₂j.trans hδ₂j.symm))

theorem rationalRoots_eq_of_mem_inter (hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ)
    (hform : ∀ γ δ, CFSG.LieType.Steinberg.Adjoint.iform (ρ γ) (ρ δ) =
      CFSG.LieType.Steinberg.Adjoint.iform γ δ) {i j : KernelComponent χ}
    {δ : Fin τ.rank → ℤ} (hi : δ ∈ rationalRoots ρ χ i) (hj : δ ∈ rationalRoots ρ χ j) :
    rationalRoots ρ χ i = rationalRoots ρ χ j :=
  le_antisymm (rationalRoots_subset_of_mem_inter hker hform hj hi)
    (rationalRoots_subset_of_mem_inter hker hform hi hj)

theorem commute_rootSpan_rationalRoots (hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ)
    (hform : ∀ γ δ, CFSG.LieType.Steinberg.Adjoint.iform (ρ γ) (ρ δ) =
      CFSG.LieType.Steinberg.Adjoint.iform γ δ) {i j : KernelComponent χ}
    (hij : rationalRoots ρ χ i ≠ rationalRoots ρ χ j) :
    ∀ x ∈ rootSpan τ L (rationalRoots ρ χ i), ∀ y ∈ rootSpan τ L (rationalRoots ρ χ j),
      Commute x y := by
  have hle : rootSpan τ L (rationalRoots ρ χ i) ≤
      Subgroup.centralizer (rootSpan τ L (rationalRoots ρ χ j) : Set (ModGL τ L)) := by
    refine iSup₂_le fun γ hγ => ?_
    rw [Subgroup.le_centralizer_iff]
    refine iSup₂_le fun δ hδ => ?_
    rw [Subgroup.le_centralizer_iff]
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hγk := rationalRoots_subset_kernelRoots hker i hγ
    have hδk := rationalRoots_subset_kernelRoots hker j hδ
    have hne : (⟦⟨γ, hγk⟩⟧ : KernelComponent χ) ≠ ⟦⟨δ, hδk⟩⟧ := fun h =>
      hij (rationalRoots_eq_of_mem_inter hker hform
        (rationalRoots_closed hker hform i hγ hδk h.symm) hδ)
    exact (commute_of_mk_ne hne L y hy x hx).eq.symm
  intro x hx y hy
  exact (Subgroup.mem_centralizer_iff.1 (hle hx) y hy).symm

end Orbits

section Toral

theorem perfect_le_rootSpan_kernel {τ : Tag} {K : Type} [Field K] {p : ℕ} (hp : p.Prime)
    (a : Fin τ.rank → Kˣ) (ha : ∀ i, a i ^ p = 1) {P : Subgroup (ModGL τ K)}
    (hP : P ≤ toralCentralizer τ K a) (hperf : ⁅P, P⁆ = P) :
    P ≤ rootSpan τ K (rootCharKernel a) := by
  obtain ⟨hMX, -, -, -, φ, hφ, -⟩ := Chevalley_toral_centralizer_root_generated_quotient τ K a
  have hCN : Group.IsSolvable (↥(toralCentralizer τ K a) ⧸
      (toralRootGroup τ K a).subgroupOf (toralCentralizer τ K a)) := by
    haveI := isSolvable_quotient hp ha
    exact Group.isSolvable_of_surjective hφ
  have hTU : torusGroup τ K ≤
      Subgroup.normalizer (rootSpan τ K (rootCharKernel a) : Set (ModGL τ K)) :=
    torusGroup_le_normalizer_rootSpan fun _ hα => hα.1
  have hUM : rootSpan τ K (rootCharKernel a) ≤ toralRootGroup τ K a := le_sup_right
  haveI hUn : ((rootSpan τ K (rootCharKernel a)).subgroupOf (toralRootGroup τ K a)).Normal :=
    Subgroup.normal_subgroupOf_sup_of_le_normalizer hTU
  have hMU : Group.IsSolvable (↥(toralRootGroup τ K a) ⧸
      (rootSpan τ K (rootCharKernel a)).subgroupOf (toralRootGroup τ K a)) := by
    haveI : ((rootSpan τ K (rootCharKernel a)).subgroupOf
        (torusGroup τ K ⊔ rootSpan τ K (rootCharKernel a))).Normal :=
      Subgroup.normal_subgroupOf_sup_of_le_normalizer hTU
    exact isSolvable_sup_quotient_of_comm (fun _ hx _ hy => torusGroup_mul_comm_aux hx hy) hTU
  exact perfect_le_of_solvable_quotient hUM hMU
    (perfect_le_of_solvable_quotient hMX hCN hP hperf) hperf

end Toral

section Lang

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
  {a : Fin τ.rank → Lˣ}

theorem rho_mem_kernelRoots_of_mem_torus (hT : rootDiagUnit τ a ∈ S.D.torus) :
    ∀ γ ∈ kernelRoots (rootCharHom a), S.ρ γ ∈ kernelRoots (rootCharHom a) := by
  rintro γ ⟨hγ, h⟩
  refine ⟨(S.frob.isRoot_iff γ).2 hγ, ?_⟩
  have h' : rootChar a γ = 1 := h
  show rootChar a (S.ρ γ) = 1
  rw [S.frob.rootChar_eq a hT γ hγ, h', one_pow]

theorem step_mem_rootSpan {T : Set (Fin τ.rank → ℤ)} (hT : ∀ γ ∈ T, IsRoot τ γ)
    (hρ : Set.MapsTo (S.ρ : (Fin τ.rank → ℤ) → _) T T) {x : ModGL τ L}
    (hx : x ∈ rootSpan τ L T) : S.D.step x ∈ rootSpan τ L T := by
  have h1 : S.D.step x ∈ (rootSpan τ L T).map S.D.step := Subgroup.mem_map_of_mem _ hx
  have h2 : (rootSpan τ L T).map S.D.step =
      rootSpan τ L ((S.ρ : (Fin τ.rank → ℤ) → _) '' T) := by
    simp only [rootSpan, Subgroup.map_iSup]
    rw [iSup_image]
    exact iSup_congr fun γ => iSup_congr fun hγ => S.frob.map_rootSubgroup γ (hT γ hγ)
  rw [h2] at h1
  exact rootSpan_mono hρ.image_subset h1

end Lang

theorem perfect_le_glaLayer_langCentralizer_of_prime
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup τ L p₀) (hp : p.Prime) {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (hap : ∀ i, a i ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (hTame : ∀ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∨
        Group.IsSolvable (rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (P : Subgroup (ModGL τ L)) (hP : P ≤ S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a})
    (hperf : ⁅P, P⁆ = P) :
    P ≤ GLALayer (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a}) := by
  classical
  have hker := rho_mem_kernelRoots_of_mem_torus S hT
  have hform := S.frob.iform_eq
  have hΓ : S.Γ ≤ adjointGroup τ L :=
    (Subgroup.commutator_le_self S.D.model).trans inf_le_left
  have hΓfix : ∀ x ∈ S.Γ, S.D.step x = x := fun x hx =>
    ((Subgroup.commutator_le_self S.D.model) hx).2
  have hPX : P ≤ toralCentralizer τ L a := fun x hx =>
    Subgroup.mem_inf.2 ⟨hΓ (Subgroup.mem_inf.1 (hP hx)).1, (Subgroup.mem_inf.1 (hP hx)).2⟩
  have hPU : P ≤ rootSpan τ L (rootCharKernel a) :=
    perfect_le_rootSpan_kernel hp a hap hPX hperf
  haveI : Finite (KernelComponent (rootCharHom a)) :=
    (root_character_kernel_orthogonal_central_product τ L (rootCharHom a)).2.1
  haveI : Finite (Set.range (rationalRoots S.ρ (rootCharHom a))) :=
    (Set.finite_range _).to_subtype
  let A : Set.range (rationalRoots S.ρ (rootCharHom a)) → Subgroup (ModGL τ L) :=
    fun O => rootSpan τ L O.1
  have hc : ∀ O O', O ≠ O' → ∀ x ∈ A O, ∀ y ∈ A O', Commute x y := by
    rintro ⟨_, i, rfl⟩ ⟨_, j, rfl⟩ hne
    exact commute_rootSpan_rationalRoots hker hform (fun h => hne (Subtype.ext h))
  have hF : ∀ O, ∀ x ∈ A O, S.D.step x ∈ A O := by
    rintro ⟨_, i, rfl⟩ x hx
    exact step_mem_rootSpan S (fun γ hγ => (rationalRoots_subset_kernelRoots hker i hγ).1)
      (rationalRoots_mapsTo i) hx
  have hU : ⨆ O, A O = rootSpan τ L (rootCharKernel a) := by
    refine le_antisymm (iSup_le fun O => ?_) ?_
    · obtain ⟨_, i, rfl⟩ := O
      exact rootSpan_mono (rationalRoots_subset_kernelRoots hker i)
    · refine le_trans (iSup_componentRootSpan L (χ := rootCharHom a)).ge (iSup_le fun i => ?_)
      have h : componentRootSpan L (rootCharHom a) i ≤ A ⟨_, i, rfl⟩ :=
        rootSpan_mono fun γ hγ => ⟨0, γ, hγ, rfl⟩
      exact h.trans (le_iSup A ⟨_, i, rfl⟩)
  have hAadj : ∀ O, A O ≤ adjointGroup τ L := fun O => rootSpan_le_adjointGroup L O.1
  have h1 := perfect_le_iSup_inf_fixed S.D.step A hc hF hperf (hPU.trans hU.ge)
    fun x hx => hΓfix x (Subgroup.mem_inf.1 (hP hx)).1
  have hc2 : ∀ O O', O ≠ O' → ∀ x ∈ A O ⊓ S.D.step.eqLocus (MonoidHom.id _),
      ∀ y ∈ A O' ⊓ S.D.step.eqLocus (MonoidHom.id _), Commute x y :=
    fun O O' hne x hx y hy => hc O O' hne x hx.1 y hy.1
  have h2 : P ≤ ⨆ O, A O ⊓ S.Γ := by
    refine (perfect_le_iSup_commutator (fun O => A O ⊓ S.D.step.eqLocus (MonoidHom.id _)) hc2
      hperf h1).trans (iSup_mono fun O => le_inf ?_ ?_)
    · exact (Subgroup.commutator_mono inf_le_left inf_le_left).trans
        (Subgroup.commutator_le_self _)
    · exact Subgroup.commutator_mono (fun x hx => ⟨hAadj O hx.1, hx.2⟩)
        (fun x hx => ⟨hAadj O hx.1, hx.2⟩)
  have hc3 : ∀ O O', O ≠ O' → ∀ x ∈ A O ⊓ S.Γ, ∀ y ∈ A O' ⊓ S.Γ, Commute x y :=
    fun O O' hne x hx y hy => hc O O' hne x hx.1 y hy.1
  have h3 := perfect_le_iSup_commutator (fun O => A O ⊓ S.Γ) hc3 hperf h2
  have hc4 : ∀ O O', O ≠ O' → ∀ x ∈ ⁅A O ⊓ S.Γ, A O ⊓ S.Γ⁆, ∀ y ∈ ⁅A O' ⊓ S.Γ, A O' ⊓ S.Γ⁆,
      Commute x y := fun O O' hne x hx y hy =>
    hc3 O O' hne x (Subgroup.commutator_le_self _ hx) y (Subgroup.commutator_le_self _ hy)
  have h4 := perfect_le_iSup_of_solvable (fun O => ⁅A O ⊓ S.Γ, A O ⊓ S.Γ⁆) hc4
    (fun O => CFSG.IsQuasisimple ↥⁅A O ⊓ S.Γ, A O ⊓ S.Γ⁆)
    (fun O hO => Subgroup.isPerfect_iff.mp hO.1)
    (by
      rintro ⟨_, i, rfl⟩ hO
      exact (hTame i).resolve_left hO)
    hperf h3
  refine h4.trans (iSup_le fun O => iSup_le fun hO => ?_)
  obtain ⟨_, i, rfl⟩ := O
  obtain ⟨hle, hsub⟩ := langSubnormal_of_mem_torus S hT i
  obtain ⟨hperfO, hsimpO, -⟩ := hO
  have hcomp : IsComponentOf (rationalComponent S.ρ S.Γ (rootCharHom a) i)
      (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a}) :=
    ⟨hle, (CFSG.Open.IsSubnormal.iff_subgroupOf hle).2 hsub,
      ⟨hperfO.commutator_eq_top, hsimpO⟩⟩
  exact le_sSup hcomp

theorem perfect_le_glaLayer_langCentralizer
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (hap : ∀ i, a i ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (hTame : ∀ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∨
        Group.IsSolvable (rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (P : Subgroup (ModGL τ L)) (hP : P ≤ S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a})
    (hperf : ⁅P, P⁆ = P) :
    P ≤ GLALayer (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a}) :=
  perfect_le_glaLayer_langCentralizer_of_prime S S.hp hT hap h1 hTame P hP hperf

end CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
