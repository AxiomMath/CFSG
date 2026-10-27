module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExcE6
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Glue
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.KE6 CFSG.RankThree.PartOne.KD4T
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints frobenius_canonicalRep)

section Eq


theorem l154_rationalComponent_eq_of_layer {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    {p : ℕ} (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (hqs : CFSG.IsQuasisimple ↥(rootSpan τ L (componentRoots (rootCharHom a) i) ⊓ S.D.model)) :
    rationalComponent S.ρ S.Γ (rootCharHom a) i =
      rootSpan τ L (componentRoots (rootCharHom a) i) ⊓ S.D.model := by
  have horbit : rationalRoots S.ρ (rootCharHom a) i = componentRoots (rootCharHom a) i := by
    ext γ
    constructor
    · rintro ⟨k, δ, hδ, rfl⟩
      induction k generalizing δ with
      | zero => exact hδ
      | succ k ih =>
        rw [Function.iterate_succ_apply]
        exact ih _ (hρ δ hδ)
    · intro hγ
      exact ⟨0, γ, hγ, rfl⟩
  set P := rootSpan τ L (componentRoots (rootCharHom a) i) ⊓ S.D.model with hP
  have hPP : ⁅P, P⁆ = P := by
    have h1 := (Group.isPerfect_def.1 hqs.1)
    rw [_root_.commutator_def] at h1
    have h2 := congrArg (Subgroup.map P.subtype) h1
    rwa [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h2
  have hPΓ : P ≤ S.Γ := by
    rw [← hPP]
    exact Subgroup.commutator_mono inf_le_right inf_le_right
  have hspan : rationalSpan S.ρ S.Γ (rootCharHom a) i = P := by
    rw [rationalSpan, horbit]
    refine le_antisymm ?_ ?_
    · exact inf_le_inf_left _ (Subgroup.commutator_le.2 fun x hx y hy => by
        rw [commutatorElement_def]
        exact S.D.model.mul_mem (S.D.model.mul_mem (S.D.model.mul_mem hx hy)
          (S.D.model.inv_mem hx)) (S.D.model.inv_mem hy))
    · exact le_inf inf_le_left hPΓ
  rw [rationalComponent, hspan, hPP]

end Eq

section Layer


theorem l154_layer_data {τ : Tag} [hτ : M27Ok τ] [E6Sub τ] {L : Type} [Field L] [IsAlgClosed L]
    [h2 : CharP L 2] {p : ℕ} (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ}
    (haT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a)) (v : WeylGroup τ)
    (hΨ : componentRoots (rootCharHom a) i =
      (fun α => v • α) '' parabolicRoots τ (e6Nodes τ)) :
    ∃ (f : ℕ) (n₁ g : ModGL τ L) (π : Equiv.Perm (Fin τ.rank)), 1 ≤ f ∧ StdTwist6 n₁ π ∧
      rationalComponent S.ρ S.Γ (rootCharHom a) i =
        (stdLayer τ 2 f n₁).map (MulAut.conj g).toMonoidHom := by
  classical
  have hτ' : ∀ t : TwistTag, t.tag ≠ τ := by
    rcases hτ.isE7E8 with rfl | rfl
    · exact twistTag_tag_ne_E7
    · exact twistTag_tag_ne_E8
  obtain ⟨w, hn⟩ := S.D.n_weyl
  have h6 : 6 ≤ τ.rank := by rcases hτ.isE7E8 with rfl | rfl <;> decide
  have hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i := by
    rcases hτ.isE7E8 with rfl | rfl
    · refine S.rho_mem_componentRootsT haT i v hΨ (N := 0) (fun s hs => ?_)
        ⟨({Pi.single 0 1} : Finset (Fin Tag.E7.rank → ℤ)), fun α hα => ?_, by simp⟩
      · have := card_le_of_orth_e6 h6 [] (fun l hl h => absurd h (orth_e6_E7 l hl)) s hs
        simpa using this
      · rw [Finset.mem_singleton.1 hα]
        exact single_mem_parabolicRoots_e6 _ (by decide)
    · refine S.rho_mem_componentRootsT haT i v hΨ (N := 6) (fun s hs => ?_)
        ⟨({Pi.single 0 1, Pi.single 1 1, Pi.single 2 1, Pi.single 3 1, Pi.single 4 1,
          Pi.single 5 1, Pi.single 0 1 + Pi.single 2 1} : Finset (Fin Tag.E8.rank → ℤ)),
          fun α hα => ?_, by decide⟩
      · exact (card_le_of_orth_e6 h6 _ orth_e6_E8 s hs).trans (by decide)
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hα
        rcases hα with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact single_mem_parabolicRoots_e6 _ (by decide)
        · exact single_mem_parabolicRoots_e6 _ (by decide)
        · exact single_mem_parabolicRoots_e6 _ (by decide)
        · exact single_mem_parabolicRoots_e6 _ (by decide)
        · exact single_mem_parabolicRoots_e6 _ (by decide)
        · exact single_mem_parabolicRoots_e6 _ (by decide)
        · refine ⟨isRoot_iff_mem_artifactRoots.2 (by decide), fun j hj => ?_⟩
          have key : ∀ j : Fin 8, ¬ (j.val ≤ 5) →
              ((Pi.single 0 1 + Pi.single 2 1 : Fin 8 → ℤ)) j = 0 := by decide
          exact key j hj
  have hw : ∀ γ ∈ componentRoots (rootCharHom a) i, w • γ ∈ componentRoots (rootCharHom a) i := by
    intro γ hγ
    rw [← S.rho_eq_smul hτ' hn hγ.1.1]
    exact hρ γ hγ
  obtain ⟨ℓ, f, hℓ, hchar, hf, hq⟩ := S.exists_char_pow
  have hℓ2 : ℓ = 2 := CharP.eq L hchar h2
  subst hℓ2
  obtain ⟨Fr, hFr, hΦ⟩ := S.D.exists_frob_of_untwisted hτ'
  have hFr' : Fr = iterateFrobenius L 2 f := by
    ext c
    rw [hFr, hq, iterateFrobenius_def]
  set nv := canonicalRep (coxeterSystem τ) L v with hnv
  set nw := canonicalRep (coxeterSystem τ) L w with hnw
  have hroots : ∀ α ∈ parabolicRoots τ (e6Nodes τ), IsRoot τ α := fun α hα => hα.1
  set Ψ := componentRoots (rootCharHom a) i with hΨdef
  have hmodel : rootSpan τ L Ψ ⊓ S.D.model = rootSpan τ L Ψ ⊓
      twistedFixedPoints nw (Units.map (entrywiseHom (iterateFrobenius L 2 f))) := by
    ext x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hx, -, hxF⟩
      refine ⟨hx, ?_⟩
      have hxF' : S.D.n * S.D.Φ x * S.D.n⁻¹ = x := hxF
      rw [hn, hΦ, hFr'] at hxF'
      exact hxF'
    · rintro ⟨hx, hxF⟩
      refine ⟨hx, rootSpan_le_adjointGroup L _ hx, ?_⟩
      change S.D.n * S.D.Φ x * S.D.n⁻¹ = x
      rw [hn, hΦ, hFr']
      exact hxF
  have htrans := rootSpan_inf_twistedFixedPoints_smul (iterateFrobenius L 2 f) v nw hroots
  have hnvM := canonicalRep_mem_monomialSubgroup L v
  have hnwM := canonicalRep_mem_monomialSubgroup L w
  have hn'M : nv⁻¹ * nw * nv ∈ monomialSubgroup τ L :=
    mul_mem (mul_mem (inv_mem hnvM) hnwM) hnvM
  have hπ : weylQuotientHom τ L ⟨nv⁻¹ * nw * nv, hn'M⟩ = v⁻¹ * w * v := by
    have e : (⟨nv⁻¹ * nw * nv, hn'M⟩ : monomialSubgroup τ L) =
        (⟨nv, hnvM⟩ : monomialSubgroup τ L)⁻¹ * ⟨nw, hnwM⟩ * ⟨nv, hnvM⟩ := rfl
    rw [e, map_mul, map_mul, map_inv, weylQuotientHom_eq (mapsRootLines_canonicalRep v),
      weylQuotientHom_eq (mapsRootLines_canonicalRep w)]
  have hΨ' : Ψ = (fun α => v • α) '' parabolicRoots τ (e6Nodes τ) := hΨ
  have hmaps : ∀ α ∈ parabolicRoots τ (e6Nodes τ),
      weylQuotientHom τ L ⟨nv⁻¹ * nw * nv, hn'M⟩ • α ∈ parabolicRoots τ (e6Nodes τ) := by
    intro α hα
    rw [hπ]
    have h1 : w • (v • α) ∈ (fun α => v • α) '' parabolicRoots τ (e6Nodes τ) := by
      rw [← hΨ']
      exact hw _ (by rw [hΨ']; exact ⟨α, hα, rfl⟩)
    obtain ⟨β, hβ, hβe⟩ := h1
    rw [mul_smul, mul_smul, ← hβe, inv_smul_smul]
    exact hβ
  have hwJ : MapsJ τ (e6Set τ) (weylQuotientHom τ L ⟨nv⁻¹ * nw * nv, hn'M⟩) := by
    intro α hα
    have := hmaps α (by rwa [e6Nodes_eq_e6Set])
    rwa [e6Nodes_eq_e6Set] at this
  obtain ⟨u, hu, π, hπ12, hact⟩ := exists_action hwJ
  have hπJ : ∀ i ∈ e6Set τ, π i ∈ e6Set τ := by
    rcases hπ12 with rfl | rfl
    · exact fun i hi => hi
    · exact fun i hi => rhoτ_mem hi
  have hπJ' : ∀ i ∈ e6Set τ, π.symm i ∈ e6Set τ := by
    rcases hπ12 with rfl | rfl
    · exact fun i hi => hi
    · exact fun i hi => rhoτ_symm_mem hi
  obtain ⟨n₁, h, hn₁, hh, hgen, hlang⟩ :=
    exists_conj_twistedFixed hf hn'M hπJ hπJ' hu hact
  have hstd : StdTwist6 n₁ π := ⟨hπ12, hgen⟩
  set P₀ := rootSpan τ L (parabolicRoots τ (e6Nodes τ)) ⊓
    twistedFixedPoints (nv⁻¹ * nw * nv) (Units.map (entrywiseHom (iterateFrobenius L 2 f)))
    with hP₀
  have hQeq : rootSpan τ L (parabolicRoots τ (e6Nodes τ)) = subsystemGroup τ L (e6Set τ) := by
    rw [subsystemGroup_eq_rootSpan, e6Nodes_eq_e6Set]
  have hconj : P₀.map (MulAut.conj h).toMonoidHom = stdLayer τ 2 f n₁ := by
    ext g
    constructor
    · rintro ⟨x, ⟨hxQ, hxF⟩, rfl⟩
      rw [hQeq] at hxQ
      refine mem_stdLayer.2 ⟨?_, ?_⟩
      · exact mul_mem (mul_mem hh hxQ) (inv_mem hh)
      · exact (hlang x).1 hxF
    · intro hg
      obtain ⟨hgQ, hgF⟩ := mem_stdLayer.1 hg
      have hx : h⁻¹ * g * h ∈ subsystemGroup τ L (e6Set τ) :=
        mul_mem (mul_mem (inv_mem hh) hgQ) hh
      have hhx : h * (h⁻¹ * g * h) * h⁻¹ = g := by group
      refine ⟨h⁻¹ * g * h, ⟨by rw [hQeq]; exact hx, ?_⟩, hhx⟩
      refine (hlang _).2 ?_
      rw [hhx]
      exact hgF
  have hP : rootSpan τ L Ψ ⊓ S.D.model = P₀.map (MulAut.conj nv).toMonoidHom := by
    rw [hmodel, hΨ']
    exact htrans
  have hqs := (hstd.finite_quasisimple hf).2
  let e1 : ↥(rootSpan τ L Ψ ⊓ S.D.model) ≃* ↥P₀ :=
    (MulEquiv.subgroupCongr hP).trans (P₀.equivMapOfInjective _ (MulAut.conj nv).injective).symm
  let e2 : ↥P₀ ≃* ↥(stdLayer τ 2 f n₁) :=
    (P₀.equivMapOfInjective _ (MulAut.conj h).injective).trans (MulEquiv.subgroupCongr hconj)
  have hqsP : CFSG.IsQuasisimple ↥(rootSpan τ L Ψ ⊓ S.D.model) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (e1.trans e2).symm hqs
  have hR : rationalComponent S.ρ S.Γ (rootCharHom a) i = rootSpan τ L Ψ ⊓ S.D.model :=
    l154_rationalComponent_eq_of_layer S i hρ hqsP
  refine ⟨f, n₁, nv * h⁻¹, π, hf, hstd, ?_⟩
  rw [hR, hP, ← hconj, Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

end Layer

end CFSG.LocalAnalysis.GLTheoremA.K155X

end
