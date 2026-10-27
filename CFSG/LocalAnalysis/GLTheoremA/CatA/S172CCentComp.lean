module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentFrame
import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.Commutator
import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.OrthBlocksComp
public import CFSG.HardMathSupport.Dickson.Bal207.OrthSU38Comp

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.S172C.Cent

open Polynomial Module QuadraticMap CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V}

private theorem comp_cases_orthDerived_gen_aux1 {G G' : Type} [Group G] [Group G'] (φ : G →* G')
    (hφ : Function.Injective φ) {L K : Subgroup G} (h : CFSG.Open.IsComponentOf L K) :
    CFSG.Open.IsComponentOf (L.map φ) (K.map φ) :=
  ⟨Subgroup.map_mono h.1, CFSG.Open.IsSubnormal.map φ h.2.1,
    CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.equivMapOfInjective L φ hφ).symm h.2.2⟩

private theorem comp_cases_orthDerived_gen_aux2 {p : ℕ} {x : ↥(orthDerived Q)}
    (hx : OddOrderIsometry Q p (x : V ≃ₗ[F] V)) (hlist : FixedLayerListed Q (x : V ≃ₗ[F] V))
    {I : Subgroup (ProjOrthDerived Q)}
    (hI : CFSG.Open.IsComponentOf I (centralizerImage Q (x : V ≃ₗ[F] V)))
    (hIle : I ≤ fixedComponentImage Q (x : V ≃ₗ[F] V)) :
    ∃ G : Subgroup (V ≃ₗ[F] V), CFSG.IsQuasisimple ↥G ∧
      G ≤ supportedFixedDerived Q (x : V ≃ₗ[F] V) ∧
      (G.subgroupOf (supportedFixedDerived Q (x : V ≃ₗ[F] V))).Normal ∧
      (finrank F (fixedSpace (x : V ≃ₗ[F] V)) ≤ 4 ∨
        G = supportedFixedDerived Q (x : V ≃ₗ[F] V)) ∧
      I = ((G.subgroupOf (orthDerived Q)).map (piOrth Q)) := by
  classical
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (V ≃ₗ[F] V) := Finite.of_injective (fun e : V ≃ₗ[F] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  obtain ⟨n, Fam, hFq, hFsup, hFn0, hFix⟩ :=
    CFSG.HardMathSupport.Dickson.Bal207.OrthFix.exists_fixedFactors' hx
  have hFΩ : ∀ i, Fam i ≤ orthDerived Q := fun i =>
    (hFq i).2.1.trans hx.supportedFixedDerived_le_orthDerived
  let C : Fin n → Subgroup (ProjOrthDerived Q) := fun i =>
    ((Fam i).subgroupOf (orthDerived Q)).map (piOrth Q)
  have hCle : ∀ i, C i ≤ fixedComponentImage Q (x : V ≃ₗ[F] V) := fun i =>
    Subgroup.map_mono fun g hg => Subgroup.mem_subgroupOf.mpr
      ((hFq i).2.1 (Subgroup.mem_subgroupOf.mp hg))
  have hCsup : (⨆ i, C i) = fixedComponentImage Q (x : V ≃ₗ[F] V) := by
    unfold fixedComponentImage
    rw [← hFsup hlist, subgroupOf_iSup_of_le Fam _ hFΩ, Subgroup.map_iSup]
  have hCcomp : ∀ i, CFSG.Open.IsComponentOf (C i)
      (centralizerImage Q (x : V ≃ₗ[F] V)) := by
    intro i
    have hconj := map_conj_mem (piOrth Q) (F := (Fam i).subgroupOf (orthDerived Q))
      (F' := (supportedFixedDerived Q (x : V ≃ₗ[F] V)).subgroupOf (orthDerived Q))
      (fun h k hh hk => by
        have := (Subgroup.normal_subgroupOf_iff (hFq i).2.1).mp (hFq i).2.2
          (h : V ≃ₗ[F] V) (k : V ≃ₗ[F] V)
          (Subgroup.mem_subgroupOf.mp hh) (Subgroup.mem_subgroupOf.mp hk)
        exact Subgroup.mem_subgroupOf.mpr this)
    refine CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.isComponentOf_of_normal_normal
      (hCle i) fixedComponentImage_le_centralizerImage ?_
      hx.normal_fixedComponentImage (isQuasisimple_map_projective (hFΩ i) (hFq i).1)
    rw [Subgroup.normal_subgroupOf_iff (hCle i)]
    intro h k hh hk
    exact hconj _ _ hh hk
  have hle : I ≤ ⨆ i, C i := by rw [hCsup]; exact hIle
  obtain ⟨j, hj⟩ :=
    CFSG.HardMathSupport.Dickson.Sec6.OrthBlocks.exists_eq_of_isComponentOf_le_iSup
      C hCcomp hI hle
  exact ⟨Fam j, (hFq j).1, (hFq j).2.1, (hFq j).2.2, hFix j, hj.symm⟩

private theorem comp_cases_orthDerived_gen_aux3 (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {x : ↥(orthDerived Q)}
    (hx : OddOrderIsometry Q p (x : V ≃ₗ[F] V)) {L : Subgroup (ProjOrthDerived Q)}
    (hL : CFSG.Open.IsComponentOf L (centralizerImage Q (x : V ≃ₗ[F] V))) :
    (∃ h ∈ primaryFactors (x : V ≃ₗ[F] V).toLinearMap, h ≠ X - 1 ∧
        CFSG.IsQuasisimple ↥(specialBlock Q (x : V ≃ₗ[F] V) h) ∧
        L = componentImage Q (x : V ≃ₗ[F] V) h) ∨
      ∃ G : Subgroup (V ≃ₗ[F] V), CFSG.IsQuasisimple ↥G ∧
        G ≤ supportedFixedDerived Q (x : V ≃ₗ[F] V) ∧
        (G.subgroupOf (supportedFixedDerived Q (x : V ≃ₗ[F] V))).Normal ∧
        (finrank F (fixedSpace (x : V ≃ₗ[F] V)) ≤ 4 ∨
          G = supportedFixedDerived Q (x : V ≃ₗ[F] V)) ∧
        L = ((G.subgroupOf (orthDerived Q)).map (piOrth Q)) := by
  obtain ⟨Rep, hRep⟩ := hx.exists_orbitRepresentatives
  rcases CFSG.HardMathSupport.Dickson.Sec6.OrthBlocks.isComponentOf_centralizerImage_cases
      hQ hp hp2 x hx hRep hL with
    ⟨h, hh, hne, hq, hLh⟩ | ⟨hlist, n, C, hCsup, hCq, hCcomm, i, hLi⟩
  · exact Or.inl ⟨h, hRep.1 hh, hne, hq, hLh⟩
  · obtain ⟨G, hGq, hGle, hGn, hGdim, hIG⟩ :=
      comp_cases_orthDerived_gen_aux2 hx hlist
        ⟨(hCq i).2.1, (CFSG.Open.IsSubnormal.iff_subgroupOf (hCq i).2.1).mpr (hCq i).2.2,
          (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open (C i)).mp
            ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native (C i)).mpr
              (hCq i).1)⟩ (hCsup ▸ le_iSup C i)
    exact Or.inr ⟨G, hGq, hGle, hGn, hGdim, hLi.trans hIG⟩

theorem comp_cases_orthDerived_of_prime (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {x : ↥(orthDerived Q)} (hx : orderOf x = p)
    {L : Subgroup ↥(orthDerived Q)}
    (hL : CFSG.Open.IsComponentOf L (Subgroup.centralizer ({x} : Set ↥(orthDerived Q)))) :
    (∃ h ∈ primaryFactors (x : V ≃ₗ[F] V).toLinearMap, h ≠ X - 1 ∧
        CFSG.IsQuasisimple ↥(specialBlock Q (x : V ≃ₗ[F] V) h) ∧
        L = (specialBlock Q (x : V ≃ₗ[F] V) h).subgroupOf (orthDerived Q)) ∨
      ∃ G : Subgroup (V ≃ₗ[F] V), CFSG.IsQuasisimple ↥G ∧
        G ≤ supportedFixedDerived Q (x : V ≃ₗ[F] V) ∧
        (G.subgroupOf (supportedFixedDerived Q (x : V ≃ₗ[F] V))).Normal ∧
        (finrank F (fixedSpace (x : V ≃ₗ[F] V)) ≤ 4 ∨
          G = supportedFixedDerived Q (x : V ≃ₗ[F] V)) ∧
        L = G.subgroupOf (orthDerived Q) := by
  classical
  have hV : Nontrivial V := by
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    haveI := hV
    have h1 : x = 1 := Subtype.ext (LinearEquiv.ext fun v => Subsingleton.elim _ _)
    rw [h1, orderOf_one] at hx
    exact hp.ne_one hx.symm
  haveI := hV
  have hinj : Function.Injective (piOrth Q) := piOrth_injective hQ
  have hpl : p ≠ ringChar F := by rw [ringChar.eq F 2]; exact hp2
  have hxo : OddOrderIsometry Q p (x : V ≃ₗ[F] V) :=
    oddOrderIsometry_of_orthDerived hp hpl hQ x hx
  have hL' : CFSG.Open.IsComponentOf (L.map (piOrth Q))
      (centralizerImage Q (x : V ≃ₗ[F] V)) := by
    have h := comp_cases_orthDerived_gen_aux1 (piOrth Q) hinj hL
    rwa [map_centralizer_eq_centralizerImage x] at h
  rcases comp_cases_orthDerived_gen_aux3 hQ hp hp2 hxo hL' with
    ⟨h, hh, hne, hq, hLh⟩ | ⟨G, hGq, hGle, hGn, hGdim, hLG⟩
  · left
    refine ⟨h, hh, hne, hq, ?_⟩
    refine Subgroup.map_injective hinj ?_
    rw [hLh]
    rfl
  · right
    exact ⟨G, hGq, hGle, hGn, hGdim, Subgroup.map_injective hinj hLG⟩

theorem comp_cases_orthDerived_gen (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (_hpq : p ∣ Nat.card F + 1) {x : ↥(orthDerived Q)} (hx : orderOf x = p)
    {L : Subgroup ↥(orthDerived Q)}
    (hL : CFSG.Open.IsComponentOf L (Subgroup.centralizer ({x} : Set ↥(orthDerived Q)))) :
    (∃ h ∈ primaryFactors (x : V ≃ₗ[F] V).toLinearMap, h ≠ X - 1 ∧
        CFSG.IsQuasisimple ↥(specialBlock Q (x : V ≃ₗ[F] V) h) ∧
        L = (specialBlock Q (x : V ≃ₗ[F] V) h).subgroupOf (orthDerived Q)) ∨
      ∃ G : Subgroup (V ≃ₗ[F] V), CFSG.IsQuasisimple ↥G ∧
        G ≤ supportedFixedDerived Q (x : V ≃ₗ[F] V) ∧
        (G.subgroupOf (supportedFixedDerived Q (x : V ≃ₗ[F] V))).Normal ∧
        (finrank F (fixedSpace (x : V ≃ₗ[F] V)) ≤ 4 ∨
          G = supportedFixedDerived Q (x : V ≃ₗ[F] V)) ∧
        L = G.subgroupOf (orthDerived Q) :=
  comp_cases_orthDerived_of_prime hQ hp hp2 hx hL

theorem apply_eq_of_mem_specialBlock {x g : V ≃ₗ[F] V} {h k : F[X]}
    (hk : k ∈ primaryFactors x.toLinearMap) (hkh : k ≠ h) (hkh' : k ≠ reciprocalPolynomial h)
    (hg : g ∈ specialBlock Q x h) {v : V} (hv : v ∈ primaryComponent x.toLinearMap k) : g v = v := by
  have hg' := (mem_supportedBlock.1 (specialBlock_le_supportedBlock h hg)).2
  exact hg' v (Submodule.mem_iSup_of_mem k (Submodule.mem_iSup_of_mem ⟨hk, hkh, hkh'⟩ hv))

theorem apply_eq_of_mem_supportedFixedDerived {x g : V ≃ₗ[F] V} {k : F[X]}
    (hk : k ∈ primaryFactors x.toLinearMap) (hk1 : k ≠ X - 1) (hg : g ∈ supportedFixedDerived Q x) {v : V}
    (hv : v ∈ primaryComponent x.toLinearMap k) : g v = v := by
  have hg' := (mem_supportedBlock.1 (supportedFixedDerived_le_supportedBlock hg)).2
  refine hg' v (Submodule.mem_iSup_of_mem k (Submodule.mem_iSup_of_mem ⟨hk, hk1, ?_⟩ hv))
  rw [reciprocalPolynomial_X_sub_one]
  exact hk1

theorem commute_of_apply_eq {U : Submodule F V}
    (hU : (QuadraticMap.polarBilin (Q.comp U.subtype)).Nondegenerate) {g e : V ≃ₗ[F] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hgU : ∀ x ∈ U, g x = x)
    (heU : ∀ x ∈ U, e x ∈ U) (heP : ∀ x ∈ polarPerp Q U, e x = x) : g * e = e * g := by
  have hgp : ∀ w ∈ polarPerp Q U, g w ∈ polarPerp Q U := by
    intro w hw
    rw [mem_polarPerp_iff] at hw ⊢
    intro y hy
    have h1 : QuadraticMap.polar Q (g y) (g w) = QuadraticMap.polar Q y w := by
      simp only [QuadraticMap.polar, ← map_add,
        TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hg]
    rw [hgU y hy] at h1
    rw [h1]
    exact hw y hy
  refine LinearEquiv.ext fun x => ?_
  have hx : x ∈ U ⊔ polarPerp Q U := by
    rw [(isCompl_polarPerp hU).sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 hx
  simp only [LinearEquiv.mul_apply, map_add, hgU u hu, heP w hw, hgU _ (heU u hu),
    heP _ (hgp w hw)]

private theorem eq_one_of_commute_orthDerived_aux1 {W : Type} [AddCommGroup W] [Module F W]
    [FiniteDimensional F W] {R : QuadraticForm F W}
    (hQ : (QuadraticMap.polarBilin R).Nondegenerate) (hd : 3 ≤ Module.finrank F W)
    {g : W ≃ₗ[F] W}
    (hc : ∀ u w, R u = 0 → polar R u w = 0 → g * eichler R u w = eichler R u w * g)
    {u : W} (hu0 : u ≠ 0) (hu : R u = 0) : ∃ c : F, g u = c • u := by
  have key : ∀ w, polar R u w = 0 →
      polar R (g u) u • w = (polar R (g u) w + R w * polar R (g u) u) • u := by
    intro w hw
    have h2 := congrArg (fun z => z u) (hc u w hu hw)
    simp only [LinearEquiv.mul_apply, eichler_apply_self] at h2
    have h3 : eichler R u w (g u) = g u := h2.symm
    rw [eichler_apply hu hw] at h3
    linear_combination (norm := module) h3
  by_cases h0 : polar R (g u) u = 0
  · refine CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.exists_smul_of_forall_polar_eq_zero
      hQ fun w hw => ?_
    have := key w hw
    rw [h0, zero_smul, mul_zero, add_zero] at this
    exact (smul_eq_zero.mp this.symm).resolve_right hu0
  · exfalso
    have hker : LinearMap.ker (polarBilin R u) ≤ Submodule.span F {u} := by
      intro w hw
      have hw' : polar R u w = 0 := by
        simpa [QuadraticMap.polarBilin_apply_apply] using hw
      have hk := key w hw'
      rw [Submodule.mem_span_singleton]
      refine ⟨(polar R (g u) u)⁻¹ * (polar R (g u) w + R w * polar R (g u) u), ?_⟩
      have h1 := congrArg (fun z => (polar R (g u) u)⁻¹ • z) hk
      simp only [smul_smul] at h1
      rw [inv_mul_cancel₀ h0, one_smul] at h1
      exact h1.symm
    have h1 : Module.finrank F (LinearMap.ker (polarBilin R u)) ≤ 1 := by
      calc Module.finrank F (LinearMap.ker (polarBilin R u))
          ≤ Module.finrank F (Submodule.span F {u}) := Submodule.finrank_mono hker
        _ = 1 := finrank_span_singleton hu0
    have h2 := LinearMap.finrank_range_add_finrank_ker (polarBilin R u)
    have h3 : Module.finrank F (LinearMap.range (polarBilin R u)) ≤ 1 :=
      (Submodule.finrank_le _).trans (by simp)
    omega

theorem eq_one_of_commute_orthDerived {W : Type} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    {R : QuadraticForm F W} (hR : (QuadraticMap.polarBilin R).Nondegenerate)
    (hT : ∃ T : Submodule F W, Module.finrank F T = 3 ∧ ∀ u ∈ T, R u = 0) {g : W ≃ₗ[F] W}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup R)
    (hc : ∀ h ∈ orthDerived R, g * h = h * g) : g = 1 := by
  obtain ⟨hΩE, -⟩ := CFSG.RankThree.Classical.orthDerived_eq_and_le_closure hR hT
  have hdim : 3 ≤ Module.finrank F W := by
    obtain ⟨T, hT3, -⟩ := hT
    calc 3 = Module.finrank F T := hT3.symm
      _ ≤ Module.finrank F W := Submodule.finrank_le _
  have hfix : ∀ v, v ≠ 0 → R v = 0 → ∃ c : F, g v = c • v := by
    intro u hu0 hu
    refine eq_one_of_commute_orthDerived_aux1 hR hdim (fun a b _ _ => ?_) hu0 hu
    have hmem : eichler R a b ∈ orthDerived R := by
      rw [hΩE]
      exact eichler_mem_elementaryGroup R a b
    exact hc _ hmem
  obtain ⟨P, r, hr, hP, -, -⟩ :=
    CFSG.RankThree.Classical.exists_hypPair_tail_decomposition hR hT
  have hPP' : (P 0).Orth (P 1) := hP 0 1 (by omega) (by omega) (by decide)
  have hsc : g ∈ scalars F W := mem_scalars_of_forall_singular hPP' hg hfix
  obtain ⟨c, hcs⟩ := mem_scalars.mp hsc
  set w : W := (P 0).e + (P 0).f with hw
  have hns : R w = 1 := by
    rw [hw, QuadraticMap.map_add R, (P 0).Q_e, (P 0).Q_f, (P 0).polar_ef]
    ring
  have h1 : R (g w) = R w := TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hg w
  have h2 : g w = c • w := hcs w
  have h3 : c ^ 2 = 1 := by
    rw [h2, map_smul_eq_sq, hns, mul_one] at h1
    exact h1
  have hc1 : c = 1 := CharTwo.sq_inj.mp (by rw [h3, one_pow])
  refine LinearEquiv.ext fun v => ?_
  rw [hcs v, hc1, one_smul]
  rfl

end CFSG.LocalAnalysis.GLTheoremA.S172C.Cent

end
