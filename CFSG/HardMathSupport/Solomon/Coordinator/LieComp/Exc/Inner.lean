module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcLang
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerEmbed
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Glue
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcLang.Family
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Export
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerBridge

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

set_option linter.unusedSectionVars false


theorem perfect_le_iSup_rationalComponent_of_prime
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup τ L p₀) (hp : p.Prime) {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (hap : ∀ i, a i ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (hTame : ∀ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∨
        Group.IsSolvable (rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (P : Subgroup (ModGL τ L)) (hP : P ≤ S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a})
    (hperf : ⁅P, P⁆ = P) :
    P ≤ ⨆ i : {i : KernelComponent (rootCharHom a) //
        CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)},
      rationalComponent S.ρ S.Γ (rootCharHom a) i.1 := by
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
  exact le_iSup (fun i : {i : KernelComponent (rootCharHom a) //
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)} =>
    rationalComponent S.ρ S.Γ (rootCharHom a) i.1) ⟨i, hO⟩

theorem isComponentOf_comap_of_injective {S G : Type*} [Group S] [Group G] (ι : S →* G)
    (hι : Function.Injective ι) {L K : Subgroup G} (hL : L ≤ ι.range) (hK : K ≤ ι.range)
    (h : IsComponentOf L K) : IsComponentOf (L.comap ι) (K.comap ι) := by
  obtain ⟨hLK, hsub, hq⟩ := h
  have hLmap : (L.comap ι).map ι = L := Subgroup.map_comap_eq_self hL
  have e : ↥(L.comap ι) ≃* ↥L :=
    (Subgroup.equivMapOfInjective (L.comap ι) ι hι).trans (MulEquiv.subgroupCongr hLmap)
  exact ⟨Subgroup.comap_mono hLK, isSubnormal_comap_of_injective ι hι hK hsub,
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e.symm hq⟩

theorem map_fixSubgroup_eq_of_conj {S G : Type*} [Group S] [Group G] (ι : S →* G)
    (hι : Function.Injective ι) (β : MulAut S) (y : G) (hy : ∀ s, ι (β s) = y * ι s * y⁻¹) :
    (fixSubgroup β).map ι = ι.range ⊓ Subgroup.centralizer {y} := by
  apply le_antisymm
  · rintro _ ⟨s, hs, rfl⟩
    have hβs : β s = s := mem_fixSubgroup.1 hs
    have h1 : ι s = y * ι s * y⁻¹ := by rw [← hy s, hβs]
    have hcomm : ι s * y = y * ι s := by
      calc ι s * y = (y * ι s * y⁻¹) * y := by rw [← h1]
        _ = y * ι s := inv_mul_cancel_right _ _
    exact Subgroup.mem_inf.2
      ⟨MonoidHom.mem_range.2 ⟨s, rfl⟩, Subgroup.mem_centralizer_singleton_iff.2 hcomm⟩
  · intro x hx
    obtain ⟨hr, hc⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨s, rfl⟩ := MonoidHom.mem_range.1 hr
    have hcomm : ι s * y = y * ι s := Subgroup.mem_centralizer_singleton_iff.1 hc
    refine Subgroup.mem_map.2 ⟨s, ?_, rfl⟩
    rw [mem_fixSubgroup]
    apply hι
    rw [hy s, ← hcomm, mul_inv_cancel_right]

theorem components_of_langSetup {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup τ L p₀) (hp : p.Prime) {C : Type} [Group C] [Finite C]
    (ι : C →* ModGL τ L) (hι : Function.Injective ι) (hrange : ι.range = S.Γ) (β : MulAut C)
    {a : Fin τ.rank → Lˣ}
    (hβ : ∀ c, ι (β c) = rootDiagUnit τ a * ι c * (rootDiagUnit τ a)⁻¹)
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (hTame : ∀ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∨
        Group.IsSolvable (rationalComponent S.ρ S.Γ (rootCharHom a) i))
    {K : Subgroup C} (hK : IsComponentOf K (fixSubgroup β)) :
    ∃ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∧
        K.map ι = rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  classical
  set d : ModGL τ L := rootDiagUnit τ a with hd
  set R : KernelComponent (rootCharHom a) → Subgroup (ModGL τ L) :=
    fun i => rationalComponent S.ρ S.Γ (rootCharHom a) i with hR
  have hfix : (fixSubgroup β).map ι = S.Γ ⊓ Subgroup.centralizer {d} := by
    rw [map_fixSubgroup_eq_of_conj ι hι β d hβ, hrange]
  have hcomapfix : (S.Γ ⊓ Subgroup.centralizer {d}).comap ι = fixSubgroup β := by
    rw [← hfix]
    exact Subgroup.comap_map_eq_self_of_injective hι _
  have hCdrange : S.Γ ⊓ Subgroup.centralizer {d} ≤ ι.range := fun x hx => by
    rw [hrange]
    exact (Subgroup.mem_inf.1 hx).1
  haveI : Finite (KernelComponent (rootCharHom a)) :=
    (root_character_kernel_orthogonal_central_product τ L (rootCharHom a)).2.1
  let Q := {i : KernelComponent (rootCharHom a) // CFSG.IsQuasisimple (R i)}
  haveI : Finite Q := Subtype.finite
  have hcompR : ∀ i : Q, IsComponentOf (R i.1) (S.Γ ⊓ Subgroup.centralizer {d}) := by
    intro i
    obtain ⟨hle, hsub⟩ := langSubnormal_of_mem_torus S hT i.1
    exact ⟨hle, (CFSG.Open.IsSubnormal.iff_subgroupOf hle).2 hsub, open_isQuasisimple i.2⟩
  have hRrange : ∀ i : Q, R i.1 ≤ ι.range := fun i => (hcompR i).1.trans hCdrange
  let F : Q → Subgroup C := fun i => (R i.1).comap ι
  have hF : ∀ i : Q, IsComponentOf (F i) (fixSubgroup β) := by
    intro i
    have := isComponentOf_comap_of_injective ι hι (hRrange i) hCdrange (hcompR i)
    rwa [hcomapfix] at this
  have hperf : ∀ P : Subgroup C, P ≤ fixSubgroup β → commutator ↥P = ⊤ → P ≤ ⨆ i, F i := by
    intro P hPC hP
    have hPperf : ⁅P, P⁆ = P := Subgroup.isPerfect_iff.1 ⟨hP⟩
    have hPmap : P.map ι ≤ S.Γ ⊓ Subgroup.centralizer {d} := by
      rw [← hfix]
      exact Subgroup.map_mono hPC
    have hperfmap : ⁅P.map ι, P.map ι⁆ = P.map ι := by
      rw [← Subgroup.map_commutator, hPperf]
    have h2 := perfect_le_iSup_rationalComponent_of_prime S hp hT hap h1 hTame (P.map ι) hPmap
      hperfmap
    have hmapF : (⨆ i, F i).map ι = ⨆ i : Q, R i.1 := by
      rw [Subgroup.map_iSup]
      exact iSup_congr fun i => Subgroup.map_comap_eq_self (hRrange i)
    exact (Subgroup.map_le_map_iff_of_injective hι).1 (h2.trans hmapF.ge)
  obtain ⟨i, hi⟩ := component_mem_named_factors F hF hperf hK
  refine ⟨i.1, i.2, ?_⟩
  rw [hi]
  exact Subgroup.map_comap_eq_self (hRrange i)

@[expose] def RationalLieType (ℓ : ℕ) {G : Type} [Group G] (R : Subgroup G) : Prop :=
  CFSG.Yardstones.Md0ec50421ce4.IsChevSimple ℓ (↥R ⧸ Subgroup.center ↥R) ∧
    IsEmpty ((↥R ⧸ Subgroup.center ↥R) ≃* alternatingGroup (Fin 6))

@[expose] def ExcRationalLieTypes : Prop :=
  ∀ (τ : Tag) (L : Type) [Field L] [IsAlgClosed L] (p₀ : ℕ) (S : LangSetup τ L p₀)
    (a : Fin τ.rank → Lˣ), rootDiagUnit τ a ∈ S.D.torus → (∀ i, a i ^ 3 = 1) →
    rootDiagUnit τ a ≠ 1 → ∀ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) →
        RationalLieType (ringChar L) (rationalComponent S.ρ S.Γ (rootCharHom a) i)

theorem lieCompExport_of_langSetup (hres : ExcRationalLieTypes) {τ : Tag} {L : Type} [Field L]
    [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀) {C : Type} [Group C] [Finite C]
    (ι : C →* ModGL τ L) (hι : Function.Injective ι) (hrange : ι.range = S.Γ) (β : MulAut C)
    {a : Fin τ.rank → Lˣ}
    (hβ : ∀ c, ι (β c) = rootDiagUnit τ a * ι c * (rootDiagUnit τ a)⁻¹)
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ 3 = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (hTame : ∀ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∨
        Group.IsSolvable (rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (hlayer : PerfectInLayer β) {ℓ : ℕ} (hℓ : ringChar L = ℓ) : LieCompExport ℓ β := by
  classical
  have hdata : ∀ {K : Subgroup C}, IsComponentOf K (fixSubgroup β) →
      ∃ (R : Subgroup (ModGL τ L)) (eK : ↥K ≃* ↥R), CFSG.IsQuasisimple ↥R ∧ RationalLieType ℓ R := by
    intro K hK
    obtain ⟨i, hq, hKR⟩ := components_of_langSetup S Nat.prime_three ι hι hrange β hβ hT hap h1
      hTame hK
    refine ⟨rationalComponent S.ρ S.Γ (rootCharHom a) i,
      (K.equivMapOfInjective ι hι).trans (MulEquiv.subgroupCongr hKR), hq, ?_⟩
    have := hres τ L p₀ S a hT hap h1 i hq
    rwa [hℓ] at this
  refine ⟨hlayer, fun K hK => ?_, fun ⟨K, hK, ⟨e⟩⟩ => ?_⟩
  · obtain ⟨R, eK, hq, hty⟩ := hdata hK
    haveI : Finite ↥K := Subtype.finite
    haveI : Finite ↥R := Finite.of_equiv _ eK.toEquiv
    refine ⟨↥R, inferInstance, inferInstance, ⟨hq.1.commutator_eq_top, hty.1,
      fun ⟨e'⟩ => (hty.2.false e').elim⟩, eK.symm.toMonoidHom, eK.symm.surjective, ?_⟩
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have : x = 1 := eK.symm.injective (by simpa using hx)
    rw [this]
    exact one_mem _
  · obtain ⟨R, eK, hq, hty⟩ := hdata hK
    let g : (↥K ⧸ Subgroup.center ↥K) ≃* (↥R ⧸ Subgroup.center ↥R) :=
      QuotientGroup.congr _ _ eK (Subgroup.map_center_eq eK)
    exact (hty.2.false (g.symm.trans e)).elim

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
