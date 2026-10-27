module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Component
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcLang.Family

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped commutatorElement

section Embedding

variable {S G : Type*} [Group S] [Group G]

theorem up34_isComponentOf_comap (ι : S →* G) (hι : Function.Injective ι) {F : Subgroup S}
    {L : Subgroup G} (hL : IsComponentOf L (F.map ι)) : IsComponentOf (L.comap ι) F := by
  obtain ⟨hLK, hsub, hq⟩ := hL
  have hFr : F.map ι ≤ ι.range := Subgroup.map_le_range ι F
  have hLr : L ≤ ι.range := hLK.trans hFr
  have hLmap : (L.comap ι).map ι = L := Subgroup.map_comap_eq_self hLr
  have hcomapF : (F.map ι).comap ι = F := Subgroup.comap_map_eq_self_of_injective hι F
  have hLF : L.comap ι ≤ F := by
    have h1 : L.comap ι ≤ (F.map ι).comap ι := Subgroup.comap_mono hLK
    rwa [hcomapF] at h1
  have hsubF : CFSG.Open.IsSubnormal (L.comap ι) F := by
    have h1 := isSubnormal_comap_of_injective ι hι hFr hsub
    rwa [hcomapF] at h1
  have e : ↥(L.comap ι) ≃* ↥L :=
    (Subgroup.equivMapOfInjective (L.comap ι) ι hι).trans (MulEquiv.subgroupCongr hLmap)
  exact ⟨hLF, hsubF, CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e.symm hq⟩

theorem up34_map_fixSubgroup_eq (ι : S →* G) (hι : Function.Injective ι) (β : MulAut S) (y : G)
    (hy : ∀ s, ι (β s) = y * ι s * y⁻¹) :
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

end Embedding

section Rational


theorem perfect_le_iSup_rationalComponent
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup τ L p₀) (hp : p.Prime) {a : Fin τ.rank → Lˣ}
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
  exact le_iSup_of_le i (le_iSup_of_le hO le_rfl)

theorem isComponentOf_rationalComponent
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a))
    (hq : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    IsComponentOf (rationalComponent S.ρ S.Γ (rootCharHom a) i)
      (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a}) := by
  obtain ⟨hle, hsub⟩ := langSubnormal_of_mem_torus S hT i
  obtain ⟨hperfO, hsimpO, -⟩ := hq
  exact ⟨hle, (CFSG.Open.IsSubnormal.iff_subgroupOf hle).2 hsub,
    ⟨hperfO.commutator_eq_top, hsimpO⟩⟩

theorem noL34Layer_of_langSetup
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup τ L p₀) (hp : p.Prime) {C : Type} [Group C] [Finite C]
    (ι : C →* ModGL τ L) (hι : Function.Injective ι) (hrange : ι.range = S.Γ)
    (β : MulAut C) {a : Fin τ.rank → Lˣ}
    (hβ : ∀ c, ι (β c) = rootDiagUnit τ a * ι c * (rootDiagUnit τ a)⁻¹)
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (hTame : ∀ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∨
        Group.IsSolvable (rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (hno : ∀ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) →
        ¬ IsLThreeFour (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
          Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))) :
    NoL34Layer β := by
  classical
  have hPIL : PerfectInLayer β :=
    perfectInLayer_of_langSetup_of_prime S hp ι hι hrange β hβ hT hap h1 hTame
  refine noL34Layer_of_components hPIL ?_
  intro K hK hKT
  have hfix : (fixSubgroup β).map ι =
      S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a} := by
    rw [up34_map_fixSubgroup_eq ι hι β _ hβ, hrange]
  have hRC : ∀ i, rationalComponent S.ρ S.Γ (rootCharHom a) i ≤ ι.range := fun i =>
    hrange ▸ ((langSubnormal_of_mem_torus S hT i).1.trans inf_le_left)
  have hcomp : ∀ i, CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) →
      IsComponentOf ((rationalComponent S.ρ S.Γ (rootCharHom a) i).comap ι)
        (fixSubgroup β) := fun i hi => by
    apply up34_isComponentOf_comap ι hι
    rw [hfix]
    exact isComponentOf_rationalComponent S hT i hi
  have hKd : K.map ι ≤ S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a} := by
    rw [← hfix]
    exact Subgroup.map_mono hK.1
  have hKperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.1 ⟨hK.2.2.1⟩
  have hperf' : ⁅K.map ι, K.map ι⁆ = K.map ι := by rw [← Subgroup.map_commutator, hKperf]
  have hbig := perfect_le_iSup_rationalComponent S hp hT hap hTame (K.map ι) hKd hperf'
  have hKle : K ≤ ⨆ i : KernelComponent (rootCharHom a),
      ⨆ (_ : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)),
        (rationalComponent S.ρ S.Γ (rootCharHom a) i).comap ι := by
    intro x hx
    have hx' : ι x ∈ ⨆ i : KernelComponent (rootCharHom a),
        ⨆ (_ : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)),
          rationalComponent S.ρ S.Γ (rootCharHom a) i := hbig ⟨x, hx, rfl⟩
    have e : (⨆ i : KernelComponent (rootCharHom a),
        ⨆ (_ : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)),
          (rationalComponent S.ρ S.Γ (rootCharHom a) i).comap ι).map ι =
        ⨆ i : KernelComponent (rootCharHom a),
          ⨆ (_ : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)),
            rationalComponent S.ρ S.Γ (rootCharHom a) i := by
      rw [Subgroup.map_iSup]
      refine iSup_congr fun i => ?_
      rw [Subgroup.map_iSup]
      exact iSup_congr fun hi => Subgroup.map_comap_eq_self (hRC i)
    rw [← e] at hx'
    obtain ⟨y, hy, hyx⟩ := hx'
    rwa [← hι hyx]
  have hex : ∃ i, CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∧
      (rationalComponent S.ρ S.Γ (rootCharHom a) i).comap ι ≤ K := by
    by_contra hcon
    push Not at hcon
    have hcomm : ∀ i, CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) →
        ⁅(rationalComponent S.ρ S.Γ (rootCharHom a) i).comap ι, K⁆ = ⊥ := fun i hi =>
      (b3Lie_comp_le_or_comm (hcomp i hi) hK.1 hK.2.1).resolve_left (hcon i hi)
    have hM : (⨆ i : KernelComponent (rootCharHom a),
        ⨆ (_ : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)),
          (rationalComponent S.ρ S.Γ (rootCharHom a) i).comap ι) ≤
        Subgroup.centralizer (K : Set C) :=
      iSup_le fun i => iSup_le fun hi =>
        Subgroup.commutator_eq_bot_iff_le_centralizer.1 (hcomm i hi)
    have hKc : K ≤ Subgroup.centralizer (K : Set C) := hKle.trans hM
    have hab : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a := fun a ha b hb =>
      (Subgroup.mem_centralizer_iff.1 (hKc hb)) a ha
    obtain ⟨-, -, a, b, hab'⟩ := isQuasisimple_of_open_up34 hK.2.2
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    refine hab' ?_
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (hab a a.2 b b.2)
  obtain ⟨i, hQi, hiK⟩ := hex
  have hGsn : IsSubnormal ((rationalComponent S.ρ S.Γ (rootCharHom a) i).comap ι) K :=
    isSubnormal_of_le_of_le (hcomp i hQi).2.1 hiK hK.1
  have hGq : CFSG.Open.IsQuasisimple ↥((rationalComponent S.ρ S.Γ (rootCharHom a) i).comap ι) :=
    (hcomp i hQi).2.2
  have hGp : ⁅(rationalComponent S.ρ S.Γ (rootCharHom a) i).comap ι,
      (rationalComponent S.ρ S.Γ (rootCharHom a) i).comap ι⁆ =
        (rationalComponent S.ρ S.Γ (rootCharHom a) i).comap ι :=
    Subgroup.isPerfect_iff.1 ⟨hGq.1⟩
  have hGne : (rationalComponent S.ρ S.Γ (rootCharHom a) i).comap ι ≠ ⊥ := by
    haveI := CFSG.LocalCores.isQuasisimple_nontrivial (isQuasisimple_of_open_up34 hGq)
    exact (Subgroup.nontrivial_iff_ne_bot _).1 this
  have hGeq : (rationalComponent S.ρ S.Γ (rootCharHom a) i).comap ι = K :=
    Lemma510Ns.eq_of_isSubnormal_of_quasisimple hK.2.2 hGsn hGp hGne
  have hmap : K.map ι = rationalComponent S.ρ S.Γ (rootCharHom a) i := by
    rw [← hGeq]
    exact Subgroup.map_comap_eq_self (hRC i)
  let e : ↥K ≃* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    (Subgroup.equivMapOfInjective K ι hι).trans (MulEquiv.subgroupCongr hmap)
  have hKperf' : Group.IsPerfect ↥K := ⟨hK.2.2.1⟩
  obtain ⟨e'⟩ := CFSG.Goldschmidt.G37.nonempty_centerQuotientEquiv hKperf' e.toMonoidHom
    e.surjective (by
      intro x hx
      have : x = 1 := e.injective (by simpa using hx)
      rw [this]
      exact one_mem _)
  exact hno i hQi (IsLThreeFour.of_mulEquiv e' hKT)

end Rational

end CFSG.HardMathSupport.Dickson.Sec6
