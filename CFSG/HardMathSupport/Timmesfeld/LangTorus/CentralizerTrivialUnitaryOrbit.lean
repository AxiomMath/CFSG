module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentPerm
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.UnitaryShiftTrace
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.FrameAct
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgExcCore
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24A2CubeShape
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart14

public section
namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.Classical2
open scoped MatrixGroups

theorem exists_order_nine (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] :
    ∃ w : Lˣ, orderOf w = 9 := by
  have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
  have h9 : (9 : L) = 1 := by
    calc (9 : L) = 4 * 2 + 1 := by ring
      _ = 1 := by rw [h2, mul_zero, zero_add]
  letI : NeZero (9 : L) := ⟨by rw [h9]; exact one_ne_zero⟩
  obtain ⟨v, hv⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L 9
  let w : Lˣ := Units.mk0 v (hv.ne_zero (by decide))
  refine ⟨w, ?_⟩
  have ho : orderOf (w : L) = orderOf w := orderOf_units
  rw [← ho]
  exact hv.eq_orderOf.symm


theorem exists_returning_shift_three
    {tau : Tag} {L : Type} [Field L] [IsAlgClosed L] {p0 : ℕ}
    (S : LangSetup tau L p0) {a : Fin tau.rank → Lˣ}
    (hT : rootDiagUnit tau a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hs3 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 3)
    (hcover : ∀ c : KernelComponent (rootCharHom a),
      rationalRoots S.ρ (rootCharHom a) c = rationalRoots S.ρ (rootCharHom a) i)
    {w : WeylGroup tau} (hw : w ∈ rootCharStabilizer a) :
    ∃ k : ℕ, k < 3 ∧
      (fun beta => (S.ρ : (Fin tau.rank → ℤ) → _)^[k] (w • beta)) ''
        componentRoots (rootCharHom a) i = componentRoots (rootCharHom a) i := by
  obtain ⟨j, hj⟩ := exists_weyl_image_component a hw i
  obtain ⟨⟨beta, hbeta⟩, hbj⟩ := Quotient.exists_rep j
  have hb : beta ∈ componentRoots (rootCharHom a) j := ⟨hbeta, hbj⟩
  have hrat : beta ∈ rationalRoots S.ρ (rootCharHom a) i := by
    rw [← hcover j]
    exact ⟨0, beta, hb, rfl⟩
  obtain ⟨t, gamma, hgamma, ht⟩ := hrat
  obtain ⟨c, hc⟩ := outer_iterate_image_component S hT i t
  have hbc : beta ∈ componentRoots (rootCharHom a) c := by
    rw [hc]
    exact ⟨gamma, hgamma, ht.symm⟩
  have hjc : j = c := hb.2.symm.trans hbc.2
  have hper : (S.ρ : (Fin tau.rank → ℤ) → _)^[3] ''
      componentRoots (rootCharHom a) i = componentRoots (rootCharHom a) i := by
    simpa only [hs3] using (outer_componentOrbitLength_spec S hT i).2.1
  let k := (3 - t % 3) % 3
  have hk : k < 3 := Nat.mod_lt _ (by decide)
  have hmod : (k + t) % 3 = 0 := by dsimp only [k]; omega
  refine ⟨k, hk, ?_⟩
  change ((S.ρ : (Fin tau.rank → ℤ) → _)^[k] ∘ (fun beta => w • beta)) '' _ = _
  rw [Set.image_comp, hj, hjc, hc, ← Set.image_comp, ← Function.iterate_add,
    iterate_image_period (S := S) hper (k + t), hmod]
  simp

theorem step_mem_torusGroup
    {tau : Tag} {L : Type} [Field L] [IsAlgClosed L] {p0 : ℕ}
    (S : LangSetup tau L p0) {g : ModGL tau L} (hg : g ∈ torusGroup tau L) :
    S.D.step g ∈ torusGroup tau L := by
  obtain ⟨Fr, hFr, P, hP, hPhi⟩ := S.D.steinberg
  obtain ⟨w, hw⟩ := S.D.n_weyl
  have hn : S.D.n ∈ Subgroup.normalizer (torusGroup tau L : Set _) := by
    rw [hw]
    exact canonicalRep_mem_normalizer (R := L) w
  have hPhiG : S.D.Φ g ∈ torusGroup tau L := by
    obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hg
    rw [hPhi]
    rcases hP with rfl | ⟨t, ht, rfl⟩
    · simp only [one_mul, inv_one, mul_one]
      rw [CFSG.HardMathSupport.Timmesfeld.CrossChar.units_map_entrywiseHom_rootDiagUnit]
      exact rootDiagUnit_mem_torusGroup _
    · subst tau
      change twistHom t L Fr (rootDiagUnit t.tag b) ∈ torusGroup t.tag L
      rw [twistHom_rootDiagUnit_eq]
      exact rootDiagUnit_mem_torusGroup _
  exact (Subgroup.mem_normalizer_iff.mp hn _).1 hPhiG

theorem step_mem_toralRootGroup
    {tau : Tag} {L : Type} [Field L] [IsAlgClosed L] {p0 : ℕ}
    (S : LangSetup tau L p0) {a : Fin tau.rank → Lˣ}
    (hT : rootDiagUnit tau a ∈ S.D.torus) {g : ModGL tau L}
    (hg : g ∈ toralRootGroup tau L a) : S.D.step g ∈ toralRootGroup tau L a := by
  have hK : (rootSpan tau L (kernelRoots (rootCharHom a))).map S.D.step ≤
      rootSpan tau L (kernelRoots (rootCharHom a)) := by
    rw [map_rootSpan_step (S := S) _ (fun beta hbeta => hbeta.1)]
    apply rootSpan_mono
    rintro _ ⟨beta, hbeta, rfl⟩
    exact outer_rho_mem_kernelRoots S hT hbeta
  have hZ : (toralRootGroup tau L a).map S.D.step ≤ toralRootGroup tau L a := by
    rw [toralRootGroup, Subgroup.map_sup]
    apply sup_le
    · rintro _ ⟨x, hx, rfl⟩
      exact Subgroup.mem_sup_left (step_mem_torusGroup S hx)
    · exact hK.trans le_sup_right
  exact hZ (Subgroup.mem_map_of_mem S.D.step hg)

theorem map_componentSpan_iter
    {tau : Tag} {L : Type} [Field L] [IsAlgClosed L] {p0 : ℕ}
    (S : LangSetup tau L p0) {a : Fin tau.rank → Lˣ}
    (i : KernelComponent (rootCharHom a)) (k : ℕ) :
    (rootSpan tau L (componentRoots (rootCharHom a) i)).map (iterHom S.D.step k) =
      rootSpan tau L ((S.ρ : (Fin tau.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom a) i) := by
  induction k with
  | zero => simp [iterHom]
  | succ k ih =>
    change (rootSpan tau L (componentRoots (rootCharHom a) i)).map
      (S.D.step.comp (iterHom S.D.step k)) = _
    rw [← Subgroup.map_map, ih, map_rootSpan_step (S := S) _
      (fun gamma hgamma => outer_isRoot_of_mem_iterate_image S i k hgamma),
      ← Set.image_comp, ← Function.iterate_succ']

theorem normalizer_all_of_single_orbit
    {tau : Tag} {L : Type} [Field L] [IsAlgClosed L] {p0 : ℕ}
    (S : LangSetup tau L p0) {a : Fin tau.rank → Lˣ}
    (hT : rootDiagUnit tau a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hcover : ∀ c : KernelComponent (rootCharHom a),
      rationalRoots S.ρ (rootCharHom a) c = rationalRoots S.ρ (rootCharHom a) i)
    {z : ModGL tau L} (hzF : S.D.step z = z)
    (hzN : z ∈ Subgroup.normalizer (rootSpan tau L (componentRoots (rootCharHom a) i) : Set _)) :
    ∀ c : KernelComponent (rootCharHom a),
      z ∈ Subgroup.normalizer (rootSpan tau L (componentRoots (rootCharHom a) c) : Set _) := by
  have hzIter : ∀ k, iterHom S.D.step k z = z := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [iterHom_succ, ih, hzF]
  intro c
  obtain ⟨⟨beta, hbeta⟩, hbc⟩ := Quotient.exists_rep c
  have hb : beta ∈ componentRoots (rootCharHom a) c := ⟨hbeta, hbc⟩
  have hrat : beta ∈ rationalRoots S.ρ (rootCharHom a) i := by
    rw [← hcover c]
    exact ⟨0, beta, hb, rfl⟩
  obtain ⟨k, gamma, hgamma, hk⟩ := hrat
  obtain ⟨d, hd⟩ := outer_iterate_image_component S hT i k
  have hbd : beta ∈ componentRoots (rootCharHom a) d := by
    rw [hd]
    exact ⟨gamma, hgamma, hk.symm⟩
  have hcd : c = d := hb.2.symm.trans hbd.2
  have hmap := Subgroup.le_normalizer_map
    (H := rootSpan tau L (componentRoots (rootCharHom a) i)) (iterHom S.D.step k)
    (Subgroup.mem_map_of_mem (iterHom S.D.step k) hzN)
  rw [hzIter, map_componentSpan_iter S i k] at hmap
  simpa only [hcd, hd] using hmap

theorem exists_returning_frameAct
    {L : Type} [Field L] [IsAlgClosed L] {p0 : ℕ}
    (S : LangSetup Tag.E6 L p0)
    {a : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a))
    {psi : SL(3, L) →* ModGL Tag.E6 L}
    {sigma : Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ}
    (hpsi : IsSLFrame psi sigma)
    (hPsi : componentRoots (rootCharHom a) i = frameRoots sigma)
    (hnorm : ∀ x y, x ≠ y → iform (sigma x y) (sigma x y) = 2)
    {v xu m : ModGL Tag.E6 L} {w : WeylGroup Tag.E6}
    (hm : m ∈ toralRootGroup Tag.E6 L a)
    (hxu : xu ∈ toralRootGroup Tag.E6 L a)
    (hv : v = m * canonicalRep (coxeterSystem Tag.E6) L w)
    (k : ℕ)
    (hret : (fun beta => (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[k] (w • beta)) ''
      componentRoots (rootCharHom a) i = componentRoots (rootCharHom a) i) :
    ∃ eta : L ≃+* L, (∀ c, eta c = c ^ (S.D.q ^ k)) ∧
      ∃ (B : GL (Fin 3) L) (eps : Bool), ∀ X : SL(3, L),
        xu⁻¹ * iterHom S.D.step k (v * psi X * v⁻¹) * xu =
          psi (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 L B
            (if eps then stdUnitary eta.toRingHom X else Matrix.SpecialLinearGroup.map eta.toRingHom X)) := by
  obtain ⟨eta, heta⟩ := outer_exists_frob S k
  let f : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ) :=
    fun beta => (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[k] (w • beta)
  let phi : ModGL Tag.E6 L →* ModGL Tag.E6 L :=
    (iterHom S.D.step k).comp (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) L w)).toMonoidHom
  have hpin : ∀ x y, x ≠ y → ∃ beta : Lˣ, ∀ c : L,
      phi (pinnedX Tag.E6 L (sigma x y) c) =
        pinnedX Tag.E6 L (f (sigma x y)) ((beta : L) * eta c) := by
    intro x y hxy
    have hr : IsRoot Tag.E6 (sigma x y) := hpsi.isRoot x y hxy
    obtain ⟨eps, heps, hconj⟩ := exists_canonicalRep_mul_pinnedX_mul_inv L w hr
    have heps0 : eps ≠ 0 := by
      intro he
      rw [he, zero_mul] at heps
      exact zero_ne_one heps
    obtain ⟨mu, hmu0, hmu⟩ := iter_step_pinnedX S k (IsRoot.smul hr w)
    refine ⟨Units.mk0 (mu * eps ^ (S.D.q ^ k))
      (mul_ne_zero hmu0 (pow_ne_zero _ heps0)), fun c => ?_⟩
    change iterHom S.D.step k (canonicalRep (coxeterSystem Tag.E6) L w *
      pinnedX Tag.E6 L (sigma x y) c * (canonicalRep (coxeterSystem Tag.E6) L w)⁻¹) = _
    rw [hconj, iterHom_eq_iterate, hmu, mul_pow]
    change pinnedX Tag.E6 L (f (sigma x y)) (mu * (eps ^ (S.D.q ^ k) * c ^ (S.D.q ^ k))) =
      pinnedX Tag.E6 L (f (sigma x y)) ((mu * eps ^ (S.D.q ^ k)) * eta c)
    rw [heta, mul_assoc]
  have hneg : ∀ n beta, (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[n] (-beta) =
      -((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[n] beta) := by
    intro n
    induction n with
    | zero => intro beta; rfl
    | succ n ih =>
      intro beta
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, S.frob.neg_eq]
  obtain ⟨B0, eps, hB0⟩ := exists_frameAct_of_semilinear hpsi one_ne_zero
    (fun x y hxy => by simpa using hnorm x y hxy) phi eta f
    (fun x y hxy => by
      have hr : sigma x y ∈ componentRoots (rootCharHom a) i := by
        rw [hPsi]
        exact ⟨x, y, hxy, rfl⟩
      have h := Set.mem_image_of_mem f hr
      change f (sigma x y) ∈ f '' componentRoots (rootCharHom a) i at h
      rw [hret, hPsi] at h
      exact h)
    (fun beta => by dsimp only [f]; rw [smul_neg, hneg])
    (fun beta gamma => by
      dsimp only [f]
      rw [iform_rho_iterate S k, iform_smul]) hpin
  have hmIter : ∀ n, iterHom S.D.step n m ∈ toralRootGroup Tag.E6 L a := by
    intro n
    induction n with
    | zero => exact hm
    | succ n ih =>
      exact step_mem_toralRootGroup S hT ih
  have hM : xu⁻¹ * iterHom S.D.step k m ∈ toralRootGroup Tag.E6 L a :=
    mul_mem (inv_mem hxu) (hmIter k)
  obtain ⟨B1, hB1⟩ := exists_frameAct_of_mem_toralRootGroup i hpsi hPsi hM
  refine ⟨eta, heta, B1 * B0, eps, fun X => ?_⟩
  have he : xu⁻¹ * iterHom S.D.step k (v * psi X * v⁻¹) * xu =
      (xu⁻¹ * iterHom S.D.step k m) * phi (psi X) *
        (xu⁻¹ * iterHom S.D.step k m)⁻¹ := by
    have hvX : v * psi X * v⁻¹ =
        m * (canonicalRep (coxeterSystem Tag.E6) L w * psi X *
          (canonicalRep (coxeterSystem Tag.E6) L w)⁻¹) * m⁻¹ := by
      rw [hv]
      group
    rw [hvX, map_mul, map_mul, map_inv]
    change xu⁻¹ * (iterHom S.D.step k m * phi (psi X) * (iterHom S.D.step k m)⁻¹) * xu = _
    group
  rw [he, hB0]
  have h := hB1 (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 L B0
    (if eps then stdUnitary eta.toRingHom X else Matrix.SpecialLinearGroup.map eta.toRingHom X))
  change _ = _ at h
  rw [h]
  congr 1
  rw [map_mul]
  rfl


theorem commute_kernelSpan_of_geom_unitary_orbit_three
    {tau : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p0 : ℕ}
    (S : LangSetup tau L p0) (htau : tau = .E6)
    {a : Fin tau.rank → Lˣ} (hT : rootDiagUnit tau a ∈ S.D.torus)
    (hap : ∀ j, a j ^ 3 = 1) (h1 : rootDiagUnit tau a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hSix : (componentRoots (rootCharHom a) i).ncard = 6)
    (hs3 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 3)
    (hq2 : S.D.q = 2)
    (hcover : ∀ c : KernelComponent (rootCharHom a),
      rationalRoots S.ρ (rootCharHom a) c = rationalRoots S.ρ (rootCharHom a) i)
    (z : ModGL tau L) (hzC : z ∈ toralCentralizer tau L a)
    (hzF : S.D.step z = z)
    (hcomm : ∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i, Commute z x) :
    ∀ y ∈ rootSpan tau L (kernelRoots (rootCharHom a)), Commute z y := by
  subst tau
  classical
  have h3 : ((3 : ℕ) : L) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff L 2]
    norm_num
  obtain ⟨psi, sigma, hpsi, hnorm, hPsi⟩ :=
    (CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6UniqAbs.kac_facts h3 hap).frame i hSix
  obtain ⟨pi, hpi⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24.exists_unitary_perm_of_odd_orbit
      S hT hap h1 i hSix hpsi hnorm hPsi (by simpa only [hs3] using (show (3 : ℕ) % 2 = 1 from by decide))
      (by simpa only [hq2] using (show (3 : ℕ) ∣ 2 + 1 from by decide))
  obtain ⟨sigmaQ, xu, hSigmaQ, hXu, hXuN, hStepPsi⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Lie.exists_unitary_untwist_kd264alg (S := S)
      hT i (le_refl 3) hpsi hPsi pi hpi Nat.prime_two (inferInstance : CharP L 2)
      (by decide : 0 < 1) (by rw [hq2]; norm_num)
  have hSigma : ∀ c, sigmaQ c = c ^ (2 ^ 3) := by
    intro c
    simpa only [hs3, one_mul] using hSigmaQ c
  have hFs : ∀ X : SL(3, L), iterHom S.D.step 3 (xu * psi X * xu⁻¹) =
      xu * psi (stdUnitary sigmaQ.toRingHom X) * xu⁻¹ := by
    simpa only [hs3] using hStepPsi
  change xu ∈ toralRootGroup Tag.E6 L a at hXu
  let C := fixSubgroup (stdUnitaryEquiv (ν := 3) sigmaQ)
  have hC : Group.IsPerfect C :=
    ((stdUnitary_fixSubgroup Nat.prime_two (by decide : 1 ≤ 3) sigmaQ hSigma (le_refl 3)).2.1
      (by decide : ((3 : ℕ), 2 ^ 3) ≠ (3, 2))).1
  obtain ⟨_, hPeriod, hMin⟩ := outer_componentOrbitLength_spec S hT i
  rw [hs3] at hPeriod hMin
  let P : CycFamily S.D.step 3 := outerOrbitFamily S hT i hPeriod hMin
  have hP0 : P.S 0 = rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) := by
    rw [outerOrbitFamily_S, ZMod.val_zero]
    simp only [Function.iterate_zero, id_eq, Set.image_id']
  have hPsiMem : ∀ X : SL(3, L), psi X ∈ rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) := by
    intro X
    rw [hPsi, ← hpsi.range]
    exact ⟨X, rfl⟩
  let base : C →* ModGL Tag.E6 L :=
    ((MulAut.conj xu).toMonoidHom.comp psi).comp C.subtype
  have hBase : ∀ X : C, base X ∈ P.S 0 := by
    intro X
    rw [hP0]
    exact (hXuN i _).mp (hPsiMem (X : SL(3, L)))
  let theta : C →* P.S 0 := base.codRestrict (P.S 0) hBase
  have hThetaF : ∀ X : C, iterHom S.D.step 3 (theta X : ModGL Tag.E6 L) = theta X := by
    intro X
    change iterHom S.D.step 3 (xu * psi (X : SL(3, L)) * xu⁻¹) =
      xu * psi (X : SL(3, L)) * xu⁻¹
    rw [hFs]
    have hX : stdUnitary sigmaQ.toRingHom (X : SL(3, L)) = (X : SL(3, L)) := by
      simpa only [C, mem_fixSubgroup, stdUnitaryEquiv_apply] using X.property
    rw [hX]
  have hNorm : ∀ X : C, Commute z (P.norm (theta X)) := by
    intro X
    exact hcomm _ (outer_norm_mem_rationalComponent S hT i hPeriod hMin hC theta hThetaF X)
  let v := z * xu
  have hvC : v ∈ toralCentralizer Tag.E6 L a := mul_mem hzC (toralRootGroup_le a hXu)
  obtain ⟨w, hw, m, hm, hv⟩ := exists_mul_canonicalRep_of_mem_toralCentralizer a hvC
  obtain ⟨k, hk, hRet⟩ := exists_returning_shift_three S hT i hs3 hcover hw
  obtain ⟨c, hc⟩ := exists_weyl_image_component a hw i
  have hMapV : (rootSpan Tag.E6 L (componentRoots (rootCharHom a) i)).map
      (MulAut.conj v).toMonoidHom = rootSpan Tag.E6 L (componentRoots (rootCharHom a) c) := by
    rw [hv]
    exact map_conj_componentRootSpan a hw hm hc
  have hRetC : (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom a) c =
      componentRoots (rootCharHom a) i := by
    rw [← hc, ← Set.image_comp]
    exact hRet
  let Phi : ModGL Tag.E6 L →* ModGL Tag.E6 L :=
    (iterHom S.D.step k).comp (MulAut.conj v).toMonoidHom
  have hMapPhi : (rootSpan Tag.E6 L (componentRoots (rootCharHom a) i)).map Phi =
      rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) := by
    rw [← Subgroup.map_map, hMapV, map_componentSpan_iter S c k, hRetC]
  have hShiftMem : ∀ X : C, iterHom S.D.step k
      (z * (theta X : ModGL Tag.E6 L) * z⁻¹) ∈ P.S 0 := by
    intro X
    change iterHom S.D.step k (z * (xu * psi (X : SL(3, L)) * xu⁻¹) * z⁻¹) ∈ P.S 0
    rw [hP0]
    have he : z * (xu * psi (X : SL(3, L)) * xu⁻¹) * z⁻¹ =
        v * psi (X : SL(3, L)) * v⁻¹ := by dsimp only [v]; group
    rw [he]
    change Phi (psi (X : SL(3, L))) ∈ _
    rw [← hMapPhi]
    exact Subgroup.mem_map_of_mem Phi (hPsiMem _)
  have hEq := P.eq_of_shifted_conj_of_norm hC theta hThetaF hzF hNorm k hShiftMem
  obtain ⟨eta, heta, B, eps, hFrame⟩ := exists_returning_frameAct S hT i hpsi hPsi hnorm hm hXu hv k hRet
  have hFix : ∀ X : SL(3, L), stdUnitary sigmaQ.toRingHom X = X →
      psi (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 L B
        (if eps then stdUnitary eta.toRingHom X else Matrix.SpecialLinearGroup.map eta.toRingHom X)) = psi X := by
    intro X hX
    have hmX : X ∈ C := by simpa only [C, mem_fixSubgroup, stdUnitaryEquiv_apply] using hX
    have hEqX := hEq ⟨X, hmX⟩
    change iterHom S.D.step k (z * (xu * psi X * xu⁻¹) * z⁻¹) = xu * psi X * xu⁻¹ at hEqX
    have he : z * (xu * psi X * xu⁻¹) * z⁻¹ = v * psi X * v⁻¹ := by dsimp only [v]; group
    rw [he] at hEqX
    have h := hFrame X
    rw [hEqX] at h
    have hcanc : xu⁻¹ * (xu * psi X * xu⁻¹) * xu = psi X := by group
    rw [hcanc] at h
    exact h.symm
  have hk0 : k = 0 := by
    by_contra hn
    have hk12 : k = 1 ∨ k = 2 := by omega
    obtain ⟨omega9, hOmega9⟩ := exists_order_nine L
    have hPow : omega9 ^ 9 = 1 := by
      have h := pow_orderOf_eq_one omega9
      simpa only [hOmega9] using h
    have h8 : omega9 ^ 8 = omega9⁻¹ := by
      calc omega9 ^ 8 = (omega9 ^ 8 * omega9) * omega9⁻¹ := by group
        _ = omega9 ^ 9 * omega9⁻¹ :=
          congrArg (fun q : Lˣ => q * omega9⁻¹) (pow_succ omega9 8).symm
        _ = omega9⁻¹ := by rw [hPow, one_mul]
    have hBar : Units.map sigmaQ.toRingHom.toMonoidHom omega9 = omega9⁻¹ := by
      apply Units.ext
      change sigmaQ (omega9 : L) = ((omega9⁻¹ : Lˣ) : L)
      rw [hSigma]
      simpa using congrArg (fun u : Lˣ => (u : L)) h8
    have hEta : ∀ d, eta d = d ^ (2 ^ k) := by intro d; rw [heta, hq2]
    have hKer : psi.ker ≤ Subgroup.center SL(3, L) :=
      CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen.frame_ker_le_center (le_refl 3) hpsi
    exact (not_forall_unitary_frame_conj_frobenius_shift sigmaQ eta omega9 hOmega9 hBar
      k hk12 hEta psi hKer hC B eps) hFix
  have hwFix : (fun beta => w • beta) '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) i := by
    simpa only [hk0, Function.iterate_zero, id_eq] using hRet
  have hvFix : (rootSpan Tag.E6 L (componentRoots (rootCharHom a) i)).map
      (MulAut.conj v).toMonoidHom = rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) := by
    rw [hMapV, ← hc, hwFix]
  have hXuFix : (rootSpan Tag.E6 L (componentRoots (rootCharHom a) i)).map
      (MulAut.conj xu).toMonoidHom = rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) := by
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mp
    exact Subgroup.mem_normalizer_iff.mpr (hXuN i)
  have hVConj : (MulAut.conj v).toMonoidHom =
      (MulAut.conj z).toMonoidHom.comp (MulAut.conj xu).toMonoidHom := by
    ext x
    dsimp only [v, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rw [hVConj, ← Subgroup.map_map, hXuFix] at hvFix
  have hzN : z ∈ Subgroup.normalizer (rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) : Set _) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hvFix
  have hNAll := normalizer_all_of_single_orbit S hT i hcover hzF hzN
  have hQ4 : 4 ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) := by
    rw [hq2, hs3]; norm_num
  have hGeom := commute_rootSpan_of_commute_component_fixed S (by decide : Tag.E6 ≠ .G2)
    hT i hQ4 z hzF hNAll hcomm
  have hSpan : rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ≤
      Subgroup.centralizer ({z} : Set (ModGL Tag.E6 L)) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hGeom y hy).symm.eq
  have hOrbit := CFSG.StandardType.F4ExplicitPos.OrbitKernel.rootSpan_rationalRoots_le_centralizer_of_fixed
    S i hzF hSpan
  have hSub : kernelRoots (rootCharHom a) ⊆ rationalRoots S.ρ (rootCharHom a) i := by
    intro beta hbeta
    let c : KernelComponent (rootCharHom a) := ⟦⟨beta, hbeta⟩⟧
    rw [← hcover c]
    exact ⟨0, beta, ⟨hbeta, rfl⟩, rfl⟩
  have hKernel := (rootSpan_mono hSub).trans hOrbit
  intro y hy
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hKernel hy)).symm



end CFSG.HardMathSupport.Timmesfeld.LangTorus
