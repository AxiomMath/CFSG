module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenActs
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenAbs
public import CFSG.CGT.PushingUpLit.CGT6X.End4Cover
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentreHom
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenFrame
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenPin
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalLowDimCoverageBasic
public import CFSG.RankThree.PartOne.KE.A1Weyl

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

namespace KSGen

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Classical2
open Matrix
open scoped commutatorElement MatrixGroups

set_option linter.unusedSectionVars false


section Steps

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)

theorem step_mem_torusGroup {r e : ℕ} [Fact r.Prime] [CharP L r] (he : S.D.q = r ^ e)
    {t : ModGL τ L} (ht : t ∈ torusGroup τ L) : S.D.step t ∈ torusGroup τ L := by
  obtain ⟨Q, hQfix, hQnorm, hstep⟩ := exists_step_frobTwist S he
  obtain ⟨σ, hσ⟩ := exists_ringEquiv_frob (L := L) r e
  have hfrobσ : ∀ g, entrywiseFrobGL τ L r e g = frobGL σ g := by
    intro g
    change Units.map (entrywiseHom (iterateFrobenius L r e)) g =
      Units.map (entrywiseHom σ.toRingHom) g
    rw [hσ]
  rw [hstep, frobTwistGL_apply, hfrobσ]
  exact (Subgroup.mem_normalizer_iff.1 hQnorm _).1 (frobGL_mem_torusGroup σ ht)

end Steps

section Acts

variable {L : Type} [Field L] {ν : ℕ}
  {ψ : SL(ν, L) →* ModGL Tag.E6 L} {σ : Fin ν → Fin ν → Fin Tag.E6.rank → ℤ}

theorem torusGroup_le_actsOn (hψ : IsSLFrame ψ σ) (hν : 0 < ν) :
    torusGroup Tag.E6 L ≤ actsOn ψ := by
  intro t ht
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  refine mem_actsOn.2 ⟨diagGLn (fun i => rootChar b (σ i ⟨0, hν⟩)), fun X => ?_⟩
  rw [hψ.torus ⟨0, hν⟩ b X, conjDiagn_eq_conjSLn]

theorem torusSup_le_actsOn {χ : Multiplicative (Fin Tag.E6.rank → ℤ) →* Lˣ}
    (hψ : IsSLFrame ψ σ) (hν : 0 < ν) (i : KernelComponent χ)
    (hΨ : componentRoots χ i = frameRoots σ) :
    torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (kernelRoots χ) ≤ actsOn ψ := by
  refine sup_le (torusGroup_le_actsOn hψ hν) ?_
  rw [← iSup_componentRootSpan L (χ := χ)]
  refine iSup_le fun j => ?_
  by_cases hji : j = i
  · subst hji
    have : componentRootSpan L χ j = ψ.range := by
      rw [hψ.range, ← hΨ]
      rfl
    rw [this]
    exact range_le_actsOn ψ
  · intro g hg
    have h1 := componentRootSpan_le_centralizer L (χ := χ) (Ne.symm hji)
    have h2 : ψ.range ≤ componentRootSpan L χ i := by
      rw [hψ.range, ← hΨ]
      exact le_rfl
    refine mem_actsOn_of_commute fun X => ?_
    have := Subgroup.mem_centralizer_iff.1 (h1 (h2 ⟨X, rfl⟩)) g hg
    exact this

end Acts

section Rat

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
  {a : Fin τ.rank → Lˣ}

theorem rationalRoots_eq_componentRoots (i : KernelComponent (rootCharHom a))
    (hstab : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i) :
    rationalRoots S.ρ (rootCharHom a) i = componentRoots (rootCharHom a) i := by
  ext γ
  constructor
  · rintro ⟨k, δ, hδ, rfl⟩
    induction k with
    | zero => exact hδ
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact hstab _ ih
  · intro hγ
    exact ⟨0, γ, hγ, rfl⟩

theorem map_fix_le_rationalComponent (i : KernelComponent (rootCharHom a))
    (hstab : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    {X : Type*} [Group X] (ψ : X →* ModGL τ L)
    (hψS : ∀ y, ψ y ∈ rootSpan τ L (componentRoots (rootCharHom a) i))
    (hψA : ∀ y, ψ y ∈ adjointGroup τ L) (F' : X →* X)
    (hψF : ∀ y, S.D.step (ψ y) = ψ (F' y)) (K : Subgroup X) (hK : ∀ y ∈ K, F' y = y)
    (hKperf : ⁅K, K⁆ = K) :
    ∀ y ∈ K, ψ y ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  intro y hy
  set P : Subgroup (ModGL τ L) := K.map ψ with hP
  have hPmodel : P ≤ S.D.model := by
    rintro _ ⟨u, hu, rfl⟩
    refine ⟨hψA u, ?_⟩
    change S.D.step (ψ u) = ψ u
    rw [hψF, hK u hu]
  have hPspan : P ≤ rootSpan τ L (componentRoots (rootCharHom a) i) := by
    rintro _ ⟨u, -, rfl⟩
    exact hψS u
  have hPperf : ⁅P, P⁆ = P := by
    rw [hP, ← Subgroup.map_commutator, hKperf]
  have hPΓ : P ≤ S.Γ := by
    rw [← hPperf]
    exact Subgroup.commutator_mono hPmodel hPmodel
  have hPrat : P ≤ rationalSpan S.ρ S.Γ (rootCharHom a) i := by
    intro g hg
    refine Subgroup.mem_inf.2 ⟨?_, hPΓ hg⟩
    rw [rationalRoots_eq_componentRoots S i hstab]
    exact hPspan hg
  have : ⁅P, P⁆ ≤ rationalComponent S.ρ S.Γ (rootCharHom a) i :=
    Subgroup.commutator_mono hPrat hPrat
  rw [hPperf] at this
  exact this ⟨y, hy, rfl⟩

end Rat

section Class


section Fix

variable {L : Type} [Field L] {ν : ℕ}

theorem conjSLn_injective (W : GL (Fin ν) L) : Function.Injective (conjSLn W) := by
  intro X Y h
  have := congrArg (conjSLn W⁻¹) h
  rwa [← conjSLn_mul_apply, ← conjSLn_mul_apply, inv_mul_cancel, conjSLn_one_apply,
    conjSLn_one_apply] at this

theorem commutator_fix_of_conj {F' τ : SL(ν, L) →* SL(ν, L)} (W : GL (Fin ν) L)
    (hW : ∀ X, F' (conjSLn W X) = conjSLn W (τ X)) {C K : Subgroup SL(ν, L)}
    (hC : ∀ X, X ∈ C ↔ τ X = X) (hK : ∀ Y, Y ∈ K ↔ F' Y = Y) (hCperf : ⁅C, C⁆ = C) :
    ⁅K, K⁆ = K := by
  have hKC : K = C.map (conjSLn W) := by
    ext Y
    constructor
    · intro hY
      refine ⟨conjSLn W⁻¹ Y, (hC _).2 ?_, ?_⟩
      · apply conjSLn_injective W
        rw [← hW, ← conjSLn_mul_apply, mul_inv_cancel, conjSLn_one_apply]
        exact (hK Y).1 hY
      · rw [← conjSLn_mul_apply, mul_inv_cancel, conjSLn_one_apply]
    · rintro ⟨Z, hZ, rfl⟩
      rw [hK, hW, (hC Z).1 hZ]
  rw [hKC, ← Subgroup.map_commutator, hCperf]

end Fix

variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup Tag.E6 L p)

theorem unitary_class_peel {ta : Fin Tag.E6.rank → Lˣ} (h3 : ((3 : ℕ) : L) ≠ 0)
    (hT : rootDiagUnit Tag.E6 ta ∈ S.D.torus) (i : KernelComponent (rootCharHom ta))
    {ν : ℕ} (hν : 3 ≤ ν) {ψ : SL(ν, L) →* ModGL Tag.E6 L}
    {σ : Fin ν → Fin ν → Fin Tag.E6.rank → ℤ} (hψ : IsSLFrame ψ σ)
    (hΨ : componentRoots (rootCharHom ta) i = frameRoots σ) (π : Equiv.Perm (Fin ν))
    (hπ : ∀ a b, a ≠ b → S.ρ (σ a b) = σ (π b) (π a))
    {r e : ℕ} (hr : r.Prime) (hchar : CharP L r) (he : 0 < e) (hq : S.D.q = r ^ e)
    (hnq : (ν, r ^ e) ≠ (3, 2)) {Q' : Subgroup (ModGL Tag.E6 L)}
    (hFQ' : ∀ q ∈ Q', S.D.step q ∈ Q')
    (hHQ' : torusGroup Tag.E6 L ≤ Subgroup.normalizer (Q' : Set (ModGL Tag.E6 L)))
    (hQQ' : ∀ a ∈ ψ.range, ∀ b ∈ Q', a * b = b * a)
    {x : ModGL Tag.E6 L} (hx : x ∈ torusGroup Tag.E6 L ⊔ (ψ.range ⊔ Q'))
    (hFx : S.D.step x = x) :
    ∃ r' ∈ rationalComponent S.ρ S.Γ (rootCharHom ta) i, ∃ x' ∈ torusGroup Tag.E6 L ⊔ Q',
      S.D.step x' = x' ∧ x = r' * x' := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : CharP L r := hchar
  haveI : NeZero ν := ⟨by omega⟩
  obtain ⟨σQ, B, d, z, hσc, hB, hstd, hzmem, hz⟩ :=
    exists_unitary_pin S hT i hν hψ hΨ π hπ hr hchar he hq
  have hstab : ∀ γ ∈ componentRoots (rootCharHom ta) i,
      S.ρ γ ∈ componentRoots (rootCharHom ta) i := by
    intro γ hγ
    rw [hΨ] at hγ ⊢
    obtain ⟨x, y, hxy, rfl⟩ := hγ
    exact ⟨π y, π x, fun h => hxy (π.injective h).symm, hπ x y hxy⟩
  have hψS : ∀ y, ψ y ∈ rootSpan Tag.E6 L (componentRoots (rootCharHom ta) i) := fun y => by
    rw [hΨ, ← hψ.range]
    exact ⟨y, rfl⟩
  have hψA : ∀ y, ψ y ∈ adjointGroup Tag.E6 L := fun y => hψ.range_le_adjointGroup ⟨y, rfl⟩
  set τ : SL(ν, L) →* SL(ν, L) := stdUnitary σQ.toRingHom with hτ
  set F' : SL(ν, L) →* SL(ν, L) := conjUni B σQ.toRingHom with hF'
  have hψF : ∀ y, S.D.step (ψ y) = ψ (F' y) := by
    intro y
    have h1 := hstd y
    rw [hF', conjUni_apply, map_mul, map_mul, map_inv, ← h1]
    group
  have hQ2 : 2 ≤ S.D.q := S.hqpow.1.one_lt
  have hLang := lang_diagSL hQ2 σQ.toRingHom (fun c => hσc c) (permDiag_pin d π hB)
  obtain ⟨y, hy, x', hx'mem, hFx', hxeq⟩ := exists_peel_frame S.D.step F' ψ hψF
    (D := diagSL ν L) (fun a ha b hb => torusGroup_comm ha hb)
    (fun t ht => step_mem_torusGroup S hq ht) hFQ'
    (by
      rw [hψ.range]
      exact CFSG.RankThree.PartOne.KE.torusGroup_le_normalizer_rootSpan hψ.frameRoots_isRoot)
    hHQ' hQQ'
    hLang (fun δ hδ => frame_diag_mem_torusGroup h3 (by omega) hψ hδ)
    (fun κ hκ => center_le_diagSL (frame_ker_le_center hν hψ (MonoidHom.mem_ker.2 hκ)))
    (fun κ hκ y => (Subgroup.mem_center_iff.1
      (frame_ker_le_center hν hψ (MonoidHom.mem_ker.2 hκ)) y).symm)
    (fun y hy => frame_hc2 (frame_ker_le_center hν hψ) hy) hx hFx
  refine ⟨ψ y, ?_, x', hx'mem, hFx', hxeq⟩
  obtain ⟨W, hW⟩ := mem_actsOn.1 (torusSup_le_actsOn hψ (by omega) i hΨ hzmem)
  have hdiff : ∀ X, ψ (F' (conjSLn W X)) = ψ (conjSLn W (τ X)) := by
    intro X
    calc ψ (F' (conjSLn W X)) = S.D.step (ψ (conjSLn W X)) := (hψF _).symm
      _ = S.D.step (z * ψ X * z⁻¹) := by rw [hW X]
      _ = S.D.step z * S.D.step (ψ X) * (S.D.step z)⁻¹ := by simp only [map_mul, map_inv]
      _ = z * (ψ B * S.D.step (ψ X) * (ψ B)⁻¹) * z⁻¹ := by rw [hz]; group
      _ = z * ψ (τ X) * z⁻¹ := by rw [hstd X]
      _ = ψ (conjSLn W (τ X)) := hW _
  have hSLperf : Group.IsPerfect SL(ν, L) := (isQuasisimple_specialLinearGroup hν).1
  have hWτ : ∀ X, F' (conjSLn W X) = conjSLn W (τ X) := by
    haveI := hSLperf
    have h := CFSG.CGT.PushingUpLit.CGT6X.End4.hom_eq_of_central (F'.comp (conjSLn W))
      ((conjSLn W).comp τ)
      (fun X => frame_ker_le_center hν hψ (by
        rw [MonoidHom.mem_ker, map_mul, map_inv, MonoidHom.comp_apply, MonoidHom.comp_apply,
          hdiff X, mul_inv_cancel]))
    exact fun X => DFunLike.congr_fun h X
  have hCperf : ⁅fixSubgroup (stdUnitaryEquiv (ν := ν) σQ),
      fixSubgroup (stdUnitaryEquiv (ν := ν) σQ)⁆ = fixSubgroup (stdUnitaryEquiv (ν := ν) σQ) := by
    have hquasi := (stdUnitary_fixSubgroup hr he σQ (fun c => by rw [hσc, hq]) hν).2.1 hnq
    exact Subgroup.isPerfect_iff.1 hquasi.1
  have hKperf := commutator_fix_of_conj (K := F'.eqLocus (MonoidHom.id _)) W hWτ
    (C := fixSubgroup (stdUnitaryEquiv (ν := ν) σQ))
    (fun X => by rw [mem_fixSubgroup, stdUnitaryEquiv_apply]) (fun Y => Iff.rfl) hCperf
  exact map_fix_le_rationalComponent S i hstab ψ hψS hψA F' hψF (F'.eqLocus (MonoidHom.id _))
    (fun y hy => hy) hKperf y hy

theorem unitary_class_quasisimple {ta : Fin Tag.E6.rank → Lˣ}
    (hT : rootDiagUnit Tag.E6 ta ∈ S.D.torus) (i : KernelComponent (rootCharHom ta))
    {ν : ℕ} (hν : 3 ≤ ν) {ψ : SL(ν, L) →* ModGL Tag.E6 L}
    {σ : Fin ν → Fin ν → Fin Tag.E6.rank → ℤ} (hψ : IsSLFrame ψ σ)
    (hΨ : componentRoots (rootCharHom ta) i = frameRoots σ) (π : Equiv.Perm (Fin ν))
    (hπ : ∀ a b, a ≠ b → S.ρ (σ a b) = σ (π b) (π a))
    (hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i) = 1)
    {r e : ℕ} (hr : r.Prime) (hchar : CharP L r) (he : 0 < e) (hq : S.D.q = r ^ e)
    (hnq : (ν, r ^ e) ≠ (3, 2)) :
    CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom ta) i) := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  have hπ' : ∀ a b, a ≠ b → (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
      (componentRoots (rootCharHom ta) i)] (σ a b) = σ (π b) (π a) := fun a b hab => by
    rw [hs1, Function.iterate_one]
    exact hπ a b hab
  obtain ⟨σQ, hσc, f, hf1, hfker, hf2, -⟩ :=
    KSConn.two_suN_exists_hom_conj S hT i hν hψ hΨ π hπ' hr hchar he hq hs1
  have hσ' : ∀ c, σQ c = c ^ (r ^ e) := fun c => by
    rw [hσc, hs1, Nat.mul_one]
  have hCq := (stdUnitary_fixSubgroup hr he σQ hσ' hν).2.1 hnq
  have hRf : f.range = rationalComponent S.ρ S.Γ (rootCharHom ta) i :=
    le_antisymm (hf2 hCq.1) hf1
  rw [← hRf]
  exact CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_range_of_ker_le_center hCq f hfker

end Class

end KSGen

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
