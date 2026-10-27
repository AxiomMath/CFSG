module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcEmb
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcLang.Family
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang
public import CFSG.LargeExtraspecial.S5Comp
public import CFSG.LargeExtraspecial.S5Defs

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
open CFSG.LargeExtraspecial.S5 CFSG.HardMathSupport.Dickson.Sec6.I923
open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.UniquenessMaximal
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.LocalAnalysis.GLTheoremB

namespace Up34Exc

set_option linter.unusedSectionVars false


section Lang

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
  {a : Fin τ.rank → Lˣ}

theorem perfect_le_iSup_rationalComponent {p : ℕ} (hp : p.Prime)
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1)
    (hTame : ∀ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∨
        Group.IsSolvable (rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (P : Subgroup (ModGL τ L)) (hP : P ≤ S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a})
    (hperf : ⁅P, P⁆ = P) :
    P ≤ ⨆ i : KernelComponent (rootCharHom a),
      ⨆ (_ : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)),
        rationalComponent S.ρ S.Γ (rootCharHom a) i := by
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
  exact le_iSup₂_of_le i hO le_rfl

theorem isComponentOf_rationalComponent (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a))
    (hq : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    IsComponentOf (rationalComponent S.ρ S.Γ (rootCharHom a) i)
      (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a}) := by
  obtain ⟨hle, hsub⟩ := langSubnormal_of_mem_torus S hT i
  obtain ⟨hperfO, hsimpO, -⟩ := hq
  exact ⟨hle, (CFSG.Open.IsSubnormal.iff_subgroupOf hle).2 hsub,
    ⟨hperfO.commutator_eq_top, hsimpO⟩⟩

theorem commute_of_isComponentOf_ne_fin {G : Type*} [Group G] {A B K : Subgroup G} [Finite ↥K]
    (hA : IsComponentOf A K) (hB : IsComponentOf B K) (hne : A ≠ B) : ⁅A, B⁆ = ⊥ := by
  have hA' := (isComponentOf_iff_subgroupOf hA.1).mp hA
  have hB' := (isComponentOf_iff_subgroupOf hB.1).mp hB
  have hne' : A.subgroupOf K ≠ B.subgroupOf K := by
    intro h
    have h' := Subgroup.subgroupOf_inj.mp h
    rw [inf_eq_left.mpr hA.1, inf_eq_left.mpr hB.1] at h'
    exact hne h'
  have h := CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ hA' hB' hne'
  have hmap := congrArg (Subgroup.map K.subtype) h
  rwa [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hA.1, Subgroup.map_subgroupOf_eq_of_le hB.1,
    Subgroup.map_bot] at hmap

theorem exists_rationalComponent_eq_of_isComponentOf {p : ℕ} (hp : p.Prime)
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1)
    (hTame : ∀ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∨
        Group.IsSolvable (rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (hfin : Finite S.Γ) {K : Subgroup (ModGL τ L)}
    (hK : IsComponentOf K (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a})) :
    ∃ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∧
        K = rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  classical
  by_contra hcon
  push Not at hcon
  haveI : Finite ↥(S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a}) :=
    Finite.of_injective (Subgroup.inclusion (inf_le_left : S.Γ ⊓ Subgroup.centralizer
      {rootDiagUnit τ a} ≤ S.Γ)) (Subgroup.inclusion_injective _)
  have hKq : CFSG.Open.IsQuasisimple ↥K := hK.2.2
  have hperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.1 ⟨hKq.1⟩
  have hKJ := perfect_le_iSup_rationalComponent S hp hT hap hTame K hK.1 hperf
  have hcomm : ∀ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) →
        ∀ x ∈ K, ∀ y ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i, x * y = y * x := by
    intro i hi x hx y hy
    have h := commute_of_isComponentOf_ne_fin hK (isComponentOf_rationalComponent S hT i hi)
      (hcon i hi)
    have hmem : x * y * x⁻¹ * y⁻¹ ∈ ⁅K, rationalComponent S.ρ S.Γ (rootCharHom a) i⁆ :=
      Subgroup.commutator_mem_commutator hx hy
    rw [h, Subgroup.mem_bot] at hmem
    calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
      _ = y * x := by rw [hmem, one_mul]
  have hKab : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x := by
    intro x hx y hy
    have hyJ := hKJ hy
    refine Subgroup.iSup_induction _ (C := fun y => x * y = y * x) hyJ
      (fun i y hy => ?_) (by simp) (fun y z hy hz => ?_)
    · refine Subgroup.iSup_induction _ (C := fun y => x * y = y * x) hy
        (fun hi y hy => hcomm i hi x hx y hy) (by simp) (fun y z hy hz => ?_)
      rw [← mul_assoc, hy, mul_assoc, hz, mul_assoc]
    · rw [← mul_assoc, hy, mul_assoc, hz, mul_assoc]
  obtain ⟨u, v, huv⟩ := exists_not_comm_of_quasisimple hKq
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective u
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective v
  refine huv ?_
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (hKab u u.2 v v.2)

theorem noL34Layer_of_langSetup {p : ℕ} (hp : p.Prime) {C : Type} [Group C] [Finite C]
    (ι : C →* ModGL τ L) (hι : Function.Injective ι) (hrange : ι.range = S.Γ) (β : MulAut C)
    (hβ : ∀ c, ι (β c) = rootDiagUnit τ a * ι c * (rootDiagUnit τ a)⁻¹)
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (hTame : ∀ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∨
        Group.IsSolvable (rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (hrat : ∀ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) →
        IsLThreeFour (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
          Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) →
        ∃ z : ModGL τ L, z ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i ∧
          (∀ g ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i, g * z = z * g) ∧
          z ^ 3 = 1 ∧ z ≠ 1) :
    Up34Chev2.NoL34Layer β := by
  have hP : PerfectInLayer β :=
    perfectInLayer_of_langSetup_of_prime S hp ι hι hrange β hβ hT hap h1 hTame
  haveI : Finite S.Γ := by
    rw [← hrange]
    exact Finite.of_surjective _ ι.rangeRestrict_surjective
  refine noL34Layer_of_embedding ι hι β (rootDiagUnit τ a) hβ hP fun K hK hKT => ?_
  rw [hrange] at hK
  obtain ⟨i, hi, rfl⟩ := exists_rationalComponent_eq_of_isComponentOf S hp hT hap hTame
    inferInstance hK
  exact hrat i hi hKT

end Lang

end Up34Exc

end CFSG.HardMathSupport.Dickson.Sec6
