module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxExc
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxExcTw2
public import CFSG.Blueprint.SourceClassicalTransportOrthogonal
import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.ExcTrialityOrient
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPD4Layers
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPTwoDChainO
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPTwoDExport
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPTwoDMain
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwoDFour

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

namespace ExcUntw

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Minuscule MinData.Valid CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.CurtisTits CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.CatLeafProof
  CFSG.Adapters.RankTwoModelTransports CFSG.HardMathSupport.Solomon.Coordinator.LieComp

section TwistedE6Bridge

theorem catalogueOver_of_lieModel_twistedE6 {X : Type} [Group X] {p f : ℕ}
    (h : LieModel (X ⧸ Subgroup.center X) .twistedE6 0 p f) : CatalogueOver p (p ^ f) X := by
  have hadm := h.admissible
  have hp : p.Prime := hadm.1
  have hf : 0 < f := hadm.2.1
  rcases h with ⟨ht, -⟩ | ⟨-, -, hmod⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · simp [classicalTags] at ht
  · obtain ⟨-, K, _, _, hK, σ, hσ, ⟨e⟩⟩ := hmod
    let q : TauCeti.PrimePower := ⟨p, f, hp, hf⟩
    have hv := TauCeti.LieTypeIndex.valid_twistedE6 q
    obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.twistedE6 q hv K
      (by rw [hK, TauCeti.PrimePower.card_def]) σ (fun x => by rw [hσ, TauCeti.PrimePower.card_def])
    exact ⟨.lie ⟨.twistedE6 q, hv⟩, ⟨e.trans b⟩,
      Or.inl ⟨TauCeti.LieTypeIndex.characteristic_twistedE6 q,
        by simp [fieldSize, q, TauCeti.PrimePower.card_def], by simp [suzRee]⟩⟩
  · simp [reeTitsTags] at ht
  · exact absurd ht (by decide)

end TwistedE6Bridge

section Layer

open CFSG.RankThree.PartOne.KE6 CFSG.RankThree.PartOne.KD4T
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints frobenius_canonicalRep)

theorem lieModel_rationalComponent_of_e6_outer {τ : Tag} [hτ : M27Ok τ] [E6Sub τ]
    {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ}
    (haT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a)) (v : WeylGroup τ)
    (hΨ : componentRoots (rootCharHom a) i =
      (fun α => v • α) '' parabolicRoots τ (e6Nodes τ))
    (hout : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    ∃ f : ℕ, 0 < f ∧ ringChar L ^ f = S.D.q ∧
      LieModel (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) .twistedE6 0
        (ringChar L) f := by
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
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨Fr, hFr, hΦ⟩ := S.D.exists_frob_of_untwisted hτ'
  have hFr' : Fr = iterateFrobenius L ℓ f := by
    ext c
    rw [hFr, hq, iterateFrobenius_def]
  set nv := canonicalRep (coxeterSystem τ) L v with hnv
  set nw := canonicalRep (coxeterSystem τ) L w with hnw
  have hroots : ∀ α ∈ parabolicRoots τ (e6Nodes τ), IsRoot τ α := fun α hα => hα.1
  set Ψ := componentRoots (rootCharHom a) i with hΨdef
  have hmodel : rootSpan τ L Ψ ⊓ S.D.model = rootSpan τ L Ψ ⊓
      twistedFixedPoints nw (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) := by
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
  have htrans := rootSpan_inf_twistedFixedPoints_smul (iterateFrobenius L ℓ f) v nw hroots
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
  have hπρ : π = rhoτ τ := by
    rcases hπ12 with h1 | h1
    · exfalso
      apply hout
      subst h1
      set g : WeylGroup τ := v * u * v⁻¹ with hg
      have hgcl : g ∈ Subgroup.closure
          {s : WeylGroup τ | ∃ γ ∈ Ψ, s = rootReflection γ} := by
        have hu2 : u ∈ parabolicWeylGroup τ (e6Nodes τ) := by
          rw [e6Nodes_eq_e6Set]
          exact hu
        exact conj_parabolicWeyl_mem_closure v hΨ' hu2
      have hact1 : ∀ γ ∈ Ψ, S.ρ γ = g • γ := by
        intro γ hγ
        have hγ' := hγ
        rw [hΨ'] at hγ'
        obtain ⟨α, hα, rfl⟩ := hγ'
        have hαJ : ∀ k, k ∉ e6Set τ → α k = 0 := by
          intro k hk
          exact hα.2 k (by rwa [e6Nodes_eq_e6Set])
        have hwα : (v⁻¹ * w * v) • α = u • α := by
          have hα_eq : α = ∑ j ∈ (Finset.univ.filter fun j => j ∈ e6Set τ),
              α j • (Pi.single j 1 : Fin τ.rank → ℤ) := by
            funext k
            simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
            by_cases hk : k ∈ e6Set τ
            · rw [Finset.sum_eq_single k]
              · simp
              · intro b hb hbk
                simp [Pi.single_apply, Ne.symm hbk]
              · intro hk'
                exact absurd (by simpa using hk) hk'
            · rw [hαJ k hk, Finset.sum_eq_zero]
              intro b hb
              have hbk : k ≠ b := fun h => hk (h ▸ (Finset.mem_filter.1 hb).2)
              simp [Pi.single_apply, hbk]
          rw [hα_eq, Finset.smul_sum, Finset.smul_sum]
          refine Finset.sum_congr rfl fun j hj => ?_
          have hjJ : j ∈ e6Set τ := (Finset.mem_filter.1 hj).2
          rw [smul_comm (v⁻¹ * w * v) (α j) _, smul_comm u (α j) _, ← hπ, hact j hjJ]
          rfl
        have hρw : S.ρ (v • α) = w • (v • α) :=
          S.rho_eq_smul hτ' hn (IsRoot.smul hα.1 v)
        have : w • (v • α) = v • ((v⁻¹ * w * v) • α) := by
          rw [mul_smul, mul_smul, smul_inv_smul]
        show S.ρ (v • α) = g • (v • α)
        rw [hρw, this, hwα, hg, mul_smul, mul_smul, inv_smul_smul]
      have hsts : ∀ γ ∈ Ψ, g • γ ∈ Ψ := fun γ hγ => by
        rw [← hact1 γ hγ]
        exact hρ γ hγ
      refine ⟨g ^ componentOrbitLength S.ρ Ψ, Subgroup.pow_mem _ hgcl _, ?_⟩
      have key : ∀ n : ℕ, ∀ γ ∈ Ψ, (S.ρ : (Fin τ.rank → ℤ) → _)^[n] γ = (g ^ n) • γ ∧
          (g ^ n) • γ ∈ Ψ := by
        intro n
        induction n with
        | zero => exact fun γ hγ => ⟨by simp, by simpa using hγ⟩
        | succ n ih =>
          intro γ hγ
          obtain ⟨h1, h2⟩ := ih γ hγ
          refine ⟨?_, ?_⟩
          · rw [Function.iterate_succ_apply', h1, hact1 _ h2, ← mul_smul, ← pow_succ']
          · rw [pow_succ', mul_smul]
            exact hsts _ h2
      exact fun γ hγ => (key _ γ hγ).1
    · exact h1
  obtain ⟨n₁, h, hn₁, hh, hgen, hlang⟩ :=
    exists_conj_twistedFixed hf hn'M hπJ hπJ' hu hact
  have hstd : StdTwist6 n₁ π := ⟨hπ12, hgen⟩
  have hψ : Function.Injective (psi2 τ L ℓ f) := by
    intro x y hxy
    apply Subtype.ext
    have h1 := baseChangeGL_injective _ hxy
    exact (m27Equiv τ (K2 L ℓ f)).symm.injective (Subtype.ext h1)
  have hrange : stdLayer τ ℓ f n₁ = (psi2 τ L ℓ f).range :=
    hstd.stdLayer_eq_range_of_rho hπρ
  set P₀ := rootSpan τ L (parabolicRoots τ (e6Nodes τ)) ⊓
    twistedFixedPoints (nv⁻¹ * nw * nv) (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))
    with hP₀
  have hQeq : rootSpan τ L (parabolicRoots τ (e6Nodes τ)) = subsystemGroup τ L (e6Set τ) := by
    rw [subsystemGroup_eq_rootSpan, e6Nodes_eq_e6Set]
  have hconj : P₀.map (MulAut.conj h).toMonoidHom = stdLayer τ ℓ f n₁ := by
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
  let e1 : ↥(rootSpan τ L Ψ ⊓ S.D.model) ≃* ↥P₀ :=
    (MulEquiv.subgroupCongr hP).trans (P₀.equivMapOfInjective _ (MulAut.conj nv).injective).symm
  let e2 : ↥P₀ ≃* ↥(stdLayer τ ℓ f n₁) :=
    (P₀.equivMapOfInjective _ (MulAut.conj h).injective).trans (MulEquiv.subgroupCongr hconj)
  let e3 : ↥(stdLayer τ ℓ f n₁) ≃* ↥(psi2 τ L ℓ f).range := MulEquiv.subgroupCongr hrange
  let e4 : ↥(psi2 τ L ℓ f).range ≃* ↥(fixedGroup (K2 L ℓ f) (theta2 L ℓ f)) :=
    (MonoidHom.ofInjective hψ).symm
  let e := e1.trans (e2.trans (e3.trans e4))
  haveI : Finite (K2 L ℓ f) := finite_frobeniusFixedField (by omega)
  have hk : Nat.card (K2 L ℓ f) = (ℓ ^ f) ^ 2 := by rw [card_K2 hf, pow_mul']
  have hk4 : 4 ≤ Nat.card (K2 L ℓ f) := by
    rw [hk]
    have h2 : 2 ≤ ℓ ^ f := le_trans hℓ.two_le (Nat.le_self_pow (by omega) ℓ)
    nlinarith
  have hθq : ∀ c, theta2 L ℓ f c = c ^ ℓ ^ f := fun c => iterateFrobenius_def ℓ f c
  have hqsG := fixedGroup_isQuasisimple_of_four_le_card (theta2 L ℓ f) theta2_theta2 hk4
  have hqsP : CFSG.IsQuasisimple ↥(rootSpan τ L Ψ ⊓ S.D.model) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hqsG
  have hR : rationalComponent S.ρ S.Γ (rootCharHom a) i = rootSpan τ L Ψ ⊓ S.D.model :=
    rationalComponent_eq_of_layer S i hρ hqsP
  have hqiso : ↥(rootSpan τ L Ψ ⊓ S.D.model) ⧸ Subgroup.center ↥(rootSpan τ L Ψ ⊓ S.D.model) ≃*
      ↥(fixedGroup (K2 L ℓ f) (theta2 L ℓ f)) ⧸
        Subgroup.center ↥(fixedGroup (K2 L ℓ f) (theta2 L ℓ f)) :=
    QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
  have hlie : LieModel (↥(rootSpan τ L Ψ ⊓ S.D.model) ⧸
      Subgroup.center ↥(rootSpan τ L Ψ ⊓ S.D.model)) .twistedE6 0 ℓ f :=
    LieModel.of_mulEquiv hqiso.symm
      (lieModel_twistedE6_fixed (theta2 L ℓ f) theta2_theta2 hℓ hf hk hθq)
  have hring : ringChar L = ℓ := ringChar.eq L ℓ
  refine ⟨f, hf, ?_, ?_⟩
  · rw [hring, hq]
  · rw [hR, hring]
    exact hlie

end Layer

section OuterE

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.KE CFSG.Timmesfeld CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.RankThree.PartOne.KE6 CFSG.RankThree.PartOne.KD4T CFSG.ComponentClassification.CatLeafProof
  CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.RankThree.Lattice
open scoped MatrixGroups Matrix

theorem lieModel_rationalComponent_of_outer_E7 {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup Tag.E7 L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin Tag.E7.rank → Lˣ} (hTor : rootDiagUnit Tag.E7 a ∈ S.D.torus)
    (hTp : rootDiagUnit Tag.E7 a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (h6 : 6 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      eRootCount (compRank (componentRoots (rootCharHom a) i)))
    (hout : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E7.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    ∃ f : ℕ, 0 < f ∧ ringChar L ^ f = S.D.q ∧
      LieModel (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) .twistedE6 0
        (ringChar L) f := by
  classical
  obtain ⟨v, μ, x, c, -, hc, -, hlen, hroots, hrank, hncard⟩ :=
    exists_cand_of_class kacE7 facts_E7 e7_tree e7_adj e7_check e7_lt e7_card S hp hpL
      hTp i
  have hn' := hn
  rw [hrank] at h6 hn'
  rw [hncard] at hn'
  have hrk : Tag.E7.rank = 7 := rfl
  by_cases hc6 : c.length = 6
  · have h72 : kacCount Tag.E7 kacE7.θ (c.map (idxNode (r := Tag.E7.rank))).toFinset = 72 := by
      rw [hn', hc6]
      rfl
    have hCeq := kacCount_E7_six ((c.map (idxNode (r := Tag.E7.rank))).toFinset)
      (by rw [e7_card c hc, hc6]) h72
    refine lieModel_rationalComponent_of_e6_outer S hTor i v ?_ hout
    rw [hroots, hCeq, rootsOf_eq_parabolicRoots kacE7 facts_E7 (J := e6Nodes Tag.E7)
      (by decide) (fun j => by simp only [e6Nodes, Set.mem_setOf_eq]; revert j; decide)]
  ·
    exfalso
    apply hout
    have hc7 : c.length = 7 := by omega
    refine twistInner_of_shape S hTor i 7 126 (by rw [hrank, hc7]) (by rw [hncard, hn', hc7]; rfl)
      (by omega) (by omega) (by omega) (by omega)

theorem ratCat_of_outer_E7 {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup Tag.E7 L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin Tag.E7.rank → Lˣ} (hTor : rootDiagUnit Tag.E7 a ∈ S.D.torus)
    (hTp : rootDiagUnit Tag.E7 a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (h6 : 6 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      eRootCount (compRank (componentRoots (rootCharHom a) i)))
    (hout : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E7.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    RationalCatalogue S i := by
  obtain ⟨f, hf, hq, hlie⟩ :=
    lieModel_rationalComponent_of_outer_E7 S hp hpL hTor hTp i h6 hn hout
  refine ⟨1, le_rfl, ?_⟩
  rw [pow_one, ← hq]
  exact catalogueOver_of_lieModel_twistedE6 hlie

theorem lieModel_rationalComponent_of_outer_E8 {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup Tag.E8 L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin Tag.E8.rank → Lˣ} (hTor : rootDiagUnit Tag.E8 a ∈ S.D.torus)
    (hTp : rootDiagUnit Tag.E8 a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (h6 : 6 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      eRootCount (compRank (componentRoots (rootCharHom a) i)))
    (hout : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E8.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    ∃ f : ℕ, 0 < f ∧ ringChar L ^ f = S.D.q ∧
      LieModel (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) .twistedE6 0
        (ringChar L) f := by
  classical
  obtain ⟨v, μ, x, c, -, hc, -, hlen, hroots, hrank, hncard⟩ :=
    exists_cand_of_class kacE8 facts_E8 e8_tree e8_adj e8_check e8_lt e8_card S hp hpL
      hTp i
  have hn' := hn
  rw [hrank] at h6 hn'
  rw [hncard] at hn'
  have hrk : Tag.E8.rank = 8 := rfl
  by_cases hc6 : c.length = 6
  · have h72 : kacCount Tag.E8 kacE8.θ (c.map (idxNode (r := Tag.E8.rank))).toFinset = 72 := by
      rw [hn', hc6]
      rfl
    have hCeq := kacCount_E8_six ((c.map (idxNode (r := Tag.E8.rank))).toFinset)
      (by rw [e8_card c hc, hc6]) h72
    refine lieModel_rationalComponent_of_e6_outer S hTor i v ?_ hout
    rw [hroots, hCeq, rootsOf_eq_parabolicRoots kacE8 facts_E8 (J := e6Nodes Tag.E8)
      (by decide) (fun j => by simp only [e6Nodes, Set.mem_setOf_eq]; revert j; decide)]
  ·
    exfalso
    apply hout
    have hc78 : c.length = 7 ∨ c.length = 8 := by omega
    rcases hc78 with hc7 | hc8
    · refine twistInner_of_shape S hTor i 7 126 (by rw [hrank, hc7])
        (by rw [hncard, hn', hc7]; rfl) (by omega) (by omega) (by omega) (by omega)
    · refine twistInner_of_shape S hTor i 8 240 (by rw [hrank, hc8])
        (by rw [hncard, hn', hc8]; rfl) (by omega) (by omega) (by omega) (by omega)

theorem ratCat_of_outer_E8 {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup Tag.E8 L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin Tag.E8.rank → Lˣ} (hTor : rootDiagUnit Tag.E8 a ∈ S.D.torus)
    (hTp : rootDiagUnit Tag.E8 a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (h6 : 6 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      eRootCount (compRank (componentRoots (rootCharHom a) i)))
    (hout : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E8.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    RationalCatalogue S i := by
  obtain ⟨f, hf, hq, hlie⟩ :=
    lieModel_rationalComponent_of_outer_E8 S hp hpL hTor hTp i h6 hn hout
  refine ⟨1, le_rfl, ?_⟩
  rw [pow_one, ← hq]
  exact catalogueOver_of_lieModel_twistedE6 hlie

theorem excUntwOuterECatalogue_holds : ExcUntwOuterECatalogue := by
  intro τ hτ L _ _ p₀ S p hp hp2 a hT hap h1 i h6 hn hout
  have hℓp : ringChar L ≠ p := ringChar_ne_of_pow_eq_one hp hap h1
  have hpL : ((p : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hp hℓp
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  rcases hτ with rfl | rfl
  · exact ratCat_of_outer_E7 S hp hpL hT hTp i h6 hn hout
  · exact ratCat_of_outer_E8 S hp hpL hT hTp i h6 hn hout

end OuterE

section TwoD

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.Lattice CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Models.TwistedPairs
  CFSG.LieType.AlgebraicGroups CFSG.Open CFSG.RankThree.Chevalley CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.Timmesfeld CFSG.Timmesfeld.LevisSpin
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPTwoDDatum
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPTwoDDatumG
open scoped Matrix MatrixGroups

theorem catalogueIdx_statedProj_minus {K : Type} [Field K] [Fintype K] (n : ℕ) (hn : 4 ≤ n)
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∃ i : TauCeti.CFSGIndex,
      Nonempty (StatedProj (StatedOmega (StatedQuadMinus n K b c)) ≃* i.Group) ∧
        IdxOver (ringChar K) (Fintype.card K) i := by
  obtain ⟨f, hp, hcard⟩ := FiniteField.card K (ringChar K)
  let q : TauCeti.PrimePower := ⟨ringChar K, f, hp, f.pos⟩
  have hv : (TauCeti.LieTypeIndex.twistedD n q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨hn, not_false⟩
  obtain ⟨b₀, c₀, hirr₀, ⟨eT⟩⟩ :=
    CFSG.RankThree.PartTwo.Census.Carrier.SpinD.exists_typeTwistedDGroupEquivStatedProj_of_valid
      n q hv
  obtain ⟨φ⟩ := nonempty_ringEquiv_fixedField_excU (K := K) ⟨.twistedD n q, hv⟩ (by
    simp [TauCeti.ValidLieTypeIndex.fieldOrder, q, hcard])
  haveI : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.twistedD n q, hv⟩) :=
    CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  obtain ⟨e2⟩ := CFSG.Blueprint.EvenSource.nonempty_statedOmegaMinus_equiv (n := n) (by omega)
    (CFSG.ClassicalInvolution.Upgrade.irreducible_map φ hirr) hirr₀
  let e1 := statedProjCongr (glCongr φ)
    (CFSG.ClassicalInvolution.Upgrade.map_statedOmega φ
      (CFSG.ClassicalInvolution.Upgrade.statedQuadMinus_comp (n := n) (b := b) (c := c) φ rfl
        rfl))
    (glCongr_statedScalars φ)
  refine ⟨.lie ⟨.twistedD n q, hv⟩, ⟨(e1.trans e2).trans eT.symm⟩,
    Or.inl ⟨TauCeti.LieTypeIndex.characteristic_twistedD n q, ?_, by simp [suzRee]⟩⟩
  simp [fieldSize, q, TauCeti.PrimePower.card_def, hcard]

theorem catalogueOver_of_lieModel_pominus {X : Type} [Group X] {n p f : ℕ}
    (h : LieModel (X ⧸ Subgroup.center X) .POmegaMinus n p f) : CatalogueOver p (p ^ f) X := by
  have hadm := h.admissible
  have hn4 : 4 ≤ n := hadm.2.2
  have hp : p.Prime := hadm.1
  have hf : 0 < f := hadm.2.1
  rcases h with ⟨-, hmod⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · obtain ⟨-, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := hmod
    haveI : Fintype K := Fintype.ofFinite K
    have hring : ringChar K = p := ringChar_eq_of_natCard_eq_pow hp hK hf
    obtain ⟨i, ⟨φ⟩, hi⟩ := catalogueIdx_statedProj_minus (K := K) n hn4 hirr
    refine ⟨i, ⟨e.trans φ⟩, ?_⟩
    rw [hring, ← Nat.card_eq_fintype_card, hK] at hi
    exact hi
  all_goals simp [chevalleyExceptionalTags, reeTitsTags] at ht

theorem lieModel_orbitGroup_of_datum_core_four_of_root_data {τ : Tag}
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {r : ℕ} [Fact r.Prime] {L : Type} [Field L] [CharP L r] [IsAlgClosed L] {M : Type}
    [CommGroup M] (D : GenFixedRootDatum τ r L M) {m : ℕ}
    (hm4 : 4 ≤ m) (hrec : TwoDChainRecog r L D.e m) (b : Fin m → Fin τ.rank → ℤ)
    (hroot : ∀ j, IsRoot τ (b j))
    (hbinj : Function.Injective b)
    (hG : ∀ j k, iform (b j) (b k) = CFSG.LieType.Universal.Spin.cartanD m j k)
    (hsimple : D.simpleRootsJ = Set.range b)
    (hfix : ∀ j : Fin m, j.val + 2 < m → D.θ (toReal (b j)) = toReal (b j))
    (hswap01 : D.θ (toReal (b ⟨m - 2, by omega⟩)) = toReal (b ⟨m - 1, by omega⟩))
    (hswap10 : D.θ (toReal (b ⟨m - 1, by omega⟩)) = toReal (b ⟨m - 2, by omega⟩))
    (horb : GenFixedRootDatum.orbitRoot (thetaOrbit D.θ (b ⟨m - 2, by omega⟩)) =
      b ⟨m - 2, by omega⟩)
    (hframe : ∀ j k : Fin m, CFSG.LieType.Universal.Spin.cartanD m j k = -1 →
      ∃ θ : SL(3, L) →* ModGL τ L, θ.comp (blockSL L 3 2 0 (by omega)) = rootSL2 τ L (b j) ∧
        θ.comp (blockSL L 3 2 1 (by omega)) = rootSL2 τ L (b k)) :
    LieModel (↥D.orbitGroup ⧸ Subgroup.center ↥D.orbitGroup) .POmegaMinus m r D.e := by
  classical
  set a0 : Fin m := ⟨m - 2, by omega⟩ with ha0
  set a1 : Fin m := ⟨m - 1, by omega⟩ with ha1
  set a2 : Fin m := ⟨m - 3, by omega⟩ with ha2
  have hdiag : ∀ j : Fin m, CFSG.LieType.Universal.Spin.cartanD m j j = 2 := fun j => by
    rw [cartanD_apply]; simp
  have hbD : ∀ j, b j ∈ D.simpleRootsJ := fun j => by rw [hsimple]; exact ⟨j, rfl⟩
  have hmemOrb : ∀ j, thetaOrbit D.θ (b j) ∈ D.orbits := fun j => ⟨b j, hbD j, rfl⟩
  have hOfix : ∀ j : Fin m, j.val + 2 < m → thetaOrbit D.θ (b j) = {b j} := fun j hj =>
    thetaOrbit_of_fixed (hfix j hj)
  have hOf : thetaOrbit D.θ (b a0) = {b a0, b a1} := thetaOrbit_of_swap hswap01 hswap10
  have hOf' : thetaOrbit D.θ (b a1) = {b a0, b a1} := by
    rw [thetaOrbit_of_swap hswap10 hswap01, Set.pair_comm]
  have hne01 : b a0 ≠ b a1 := fun h => by
    have := hbinj h
    simp only [ha0, ha1, Fin.mk.injEq] at this
    omega
  have hOcases : ∀ O ∈ D.orbits, (∃ j : Fin m, j.val + 2 < m ∧ O = thetaOrbit D.θ (b j)) ∨
      O = thetaOrbit D.θ (b a0) := by
    rintro O ⟨β, hβ, rfl⟩
    rw [hsimple] at hβ
    obtain ⟨j, rfl⟩ := hβ
    by_cases hj : j.val + 2 < m
    · exact Or.inl ⟨j, hj, rfl⟩
    · right
      have hj' : j = a0 ∨ j = a1 := by
        have : j.val = m - 2 ∨ j.val = m - 1 := by have := j.isLt; omega
        rcases this with h | h
        · exact Or.inl (Fin.ext h)
        · exact Or.inr (Fin.ext h)
      rcases hj' with rfl | rfl
      · rfl
      · rw [hOf', hOf]
  have hcard1 : ∀ j : Fin m, j.val + 2 < m →
      GenFixedRootDatum.orbitCard (thetaOrbit D.θ (b j)) = 1 := fun j hj => by
    rw [hOfix j hj]
    exact Set.ncard_singleton _
  have hcard2 : GenFixedRootDatum.orbitCard (thetaOrbit D.θ (b a0)) = 2 := by
    rw [hOf]
    exact Set.ncard_pair hne01
  have hroot1 : ∀ j : Fin m, j.val + 2 < m →
      GenFixedRootDatum.orbitRoot (thetaOrbit D.θ (b j)) = b j := fun j hj => by
    rw [hOfix j hj]
    exact Set.mem_singleton_iff.1 (lexLeast_mem (Set.finite_singleton _) (Set.singleton_nonempty _))
  have hX : ∀ O ∈ D.orbits, ∀ c : ↥(D.orbitField O), D.orbitX O c ∈ D.orbitGroup ∧
      D.orbitY O c ∈ D.orbitGroup := fun O hO c =>
    ⟨Subgroup.subset_closure ⟨O, hO, c, Or.inl rfl⟩, Subgroup.subset_closure ⟨O, hO, c, Or.inr rfl⟩⟩
  have hmemq : ∀ O : Set (Fin τ.rank → ℤ), ∀ x : L, x ∈ D.orbitField O ↔
      x ^ r ^ (D.e * GenFixedRootDatum.orbitCard O) = x := fun O x => by
    rw [D.mem_orbitField, GenFixedRootDatum.q, pow_mul]
  have hXeq : ∀ j : Fin m, j.val + 2 < m → ∀ c : ↥(D.orbitField (thetaOrbit D.θ (b j))),
      D.orbitX (thetaOrbit D.θ (b j)) c = rootSL2 τ L (b j) (uSL (c : L)) ∧
        D.orbitY (thetaOrbit D.θ (b j)) c = rootSL2 τ L (b j) (vSL (c : L)) := by
    intro j hj c
    refine ⟨?_, ?_⟩
    · rw [GenFixedRootDatum.orbitX, orbitMap_single D (hcard1 j hj), hroot1 j hj, map_uSL']
      rfl
    · rw [GenFixedRootDatum.orbitY, orbitMap_single D (hcard1 j hj), hroot1 j hj, map_vSL']
      rfl
  have hXeqf : ∀ c : ↥(D.orbitField (thetaOrbit D.θ (b a0))),
      D.orbitX (thetaOrbit D.θ (b a0)) c =
        rootSL2 τ L (b a0) (uSL (c : L)) * rootSL2 τ L (b a1) (uSL ((c : L) ^ r ^ D.e)) ∧
      D.orbitY (thetaOrbit D.θ (b a0)) c =
        rootSL2 τ L (b a0) (vSL (c : L)) * rootSL2 τ L (b a1) (vSL ((c : L) ^ r ^ D.e)) := by
    intro c
    refine ⟨?_, ?_⟩
    · rw [GenFixedRootDatum.orbitX, orbitMap_pair D hcard2 horb hswap01]
      simp only [map_uSL', Subfield.coe_subtype, iterateFrobenius_def]
    · rw [GenFixedRootDatum.orbitY, orbitMap_pair D hcard2 horb hswap01]
      simp only [map_vSL', Subfield.coe_subtype, iterateFrobenius_def]
  have hlongmem : ∀ j : Fin m, j.val + 2 < m → ∀ x : L, x ^ r ^ D.e = x →
      rootSL2 τ L (b j) (uSL x) ∈ D.orbitGroup ∧ rootSL2 τ L (b j) (vSL x) ∈ D.orbitGroup := by
    intro j hj x hx
    have hxO : x ∈ D.orbitField (thetaOrbit D.θ (b j)) := by
      rw [hmemq, hcard1 j hj, mul_one]
      exact hx
    obtain ⟨h1, h2⟩ := hX _ (hmemOrb j) ⟨x, hxO⟩
    obtain ⟨e1, e2⟩ := hXeq j hj ⟨x, hxO⟩
    exact ⟨e1 ▸ h1, e2 ▸ h2⟩
  have hforkmem : ∀ x : L, x ^ r ^ (D.e * 2) = x →
      rootSL2 τ L (b a0) (uSL x) * rootSL2 τ L (b a1) (uSL (x ^ r ^ D.e)) ∈ D.orbitGroup ∧
        rootSL2 τ L (b a0) (vSL x) * rootSL2 τ L (b a1) (vSL (x ^ r ^ D.e)) ∈ D.orbitGroup := by
    intro x hx
    have hxO : x ∈ D.orbitField (thetaOrbit D.θ (b a0)) := by
      rw [hmemq, hcard2]
      exact hx
    obtain ⟨h1, h2⟩ := hX _ (hmemOrb a0) ⟨x, hxO⟩
    obtain ⟨e1, e2⟩ := hXeqf ⟨x, hxO⟩
    exact ⟨e1 ▸ h1, e2 ▸ h2⟩
  let bn : ℕ → Fin τ.rank → ℤ := fun i => if h : i < m then b ⟨i, h⟩ else 0
  have hbn : ∀ j : Fin m, bn j.val = b j := fun j => by simp [bn, j.isLt]
  let ρ : ℕ → SL(2, L) →* ModGL τ L := fun i => rootSL2 τ L (bn i)
  have hρi : ∀ j : Fin m, ρ j.val = rootSL2 τ L (b j) := fun j => by simp only [ρ, hbn]
  have hρinj : ∀ i, i < m → Function.Injective (ρ i) := fun i _ => rootSL2_injective_of_field _
  have hcomm : ∀ i j : ℕ, i < m → j < m → i ≠ j → ¬ CompsPTwoDChain.dEdge m i j →
      ¬ CompsPTwoDChain.dEdge m j i → ∀ A B, ρ i A * ρ j B = ρ j B * ρ i A := by
    intro i j hi hj hij h1 h2 A B
    have h0 : iform (b ⟨i, hi⟩) (b ⟨j, hj⟩) = 0 := by
      rw [hG]
      exact (cartanD_of_not_edgeD (n := m) (i := ⟨i, hi⟩) (j := ⟨j, hj⟩)
        (fun h => hij (by simpa using congrArg Fin.val h)) h1 h2).1
    have := (commute_rootSL2_of_iform_eq_zero hτ (hroot ⟨i, hi⟩) (hroot ⟨j, hj⟩) h0 A B).eq
    have e1 := hρi ⟨i, hi⟩
    have e2 := hρi ⟨j, hj⟩
    simp only at e1 e2
    rw [e1, e2]
    exact this
  have hfr : ∀ i : ℕ, i + 3 < m → ∃ θ : SL(3, L) →* ModGL τ L,
      θ.comp (blockSL L 3 2 0 (by omega)) = ρ i ∧
        θ.comp (blockSL L 3 2 1 (by omega)) = ρ (i + 1) := by
    intro i hi
    have hedge : edgeD m ⟨i, by omega⟩ ⟨i + 1, by omega⟩ :=
      Or.inl ⟨rfl, by simp only; omega⟩
    obtain ⟨θ, h0, h1⟩ := hframe ⟨i, by omega⟩ ⟨i + 1, by omega⟩ (cartanD_of_edgeD hedge).1
    exact ⟨θ, h0.trans (hρi ⟨i, by omega⟩).symm, h1.trans (hρi ⟨i + 1, by omega⟩).symm⟩
  have v1 : CFSG.LieType.Universal.Spin.cartanD m a0 a2 = -1 := (cartanD_fork_values hm4).1
  have v2 : CFSG.LieType.Universal.Spin.cartanD m a2 a0 = -1 := (cartanD_fork_values hm4).2.1
  have v3 : CFSG.LieType.Universal.Spin.cartanD m a1 a2 = -1 := (cartanD_fork_values hm4).2.2.1
  have v4 : CFSG.LieType.Universal.Spin.cartanD m a2 a1 = -1 := (cartanD_fork_values hm4).2.2.2.1
  have v5 : CFSG.LieType.Universal.Spin.cartanD m a0 a1 = 0 :=
    (cartanD_fork_values hm4).2.2.2.2.1
  have v6 : CFSG.LieType.Universal.Spin.cartanD m a1 a0 = 0 :=
    (cartanD_fork_values hm4).2.2.2.2.2
  let β3 : Fin 3 → Fin τ.rank → ℤ := ![b a0, b a2, b a1]
  have hβroot : ∀ c, IsRoot τ (β3 c) := fun c => by
    fin_cases c
    · exact hroot a0
    · exact hroot a2
    · exact hroot a1
  have hGβ : ∀ c d, iform (β3 c) (β3 d) = chainGram c d := by
    intro c d
    fin_cases c <;> fin_cases d <;>
      simp [β3, chainGram, hG, hdiag, v1, v2, v3, v4, v5, v6]
  have hθβ : ∀ (c : Fin 3) (h : (c : ℕ) + 1 < 3), ∃ θ : SL(3, L) →* ModGL τ L,
      θ.comp (blockSL L 3 2 0 (by omega)) = rootSL2 τ L (β3 c) ∧
        θ.comp (blockSL L 3 2 1 (by omega)) = rootSL2 τ L (β3 ⟨c + 1, h⟩) := by
    intro c h
    fin_cases c
    · exact hframe a0 a2 v1
    · exact hframe a2 a1 v4
    · exact absurd h (by decide)
  obtain ⟨Φ, hΦ⟩ := exists_chainHom hτ β3 hβroot hGβ hθβ
  have hΦ0 : Φ.comp (blockSL2 L 3 0) = ρ (m - 2) := (hΦ 0).trans (hρi a0).symm
  have hΦ1 : Φ.comp (blockSL2 L 3 1) = ρ (m - 3) := (hΦ 1).trans (hρi a2).symm
  have hΦ2 : Φ.comp (blockSL2 L 3 2) = ρ (m - 1) := (hΦ 2).trans (hρi a1).symm
  set ι : ↥(frobeniusFixedField L r (D.e * 2)) →+* L :=
    (frobeniusFixedField L r (D.e * 2)).subtype with hι
  have hσσ : ∀ x : ↥(frobeniusFixedField L r (D.e * 2)),
      (CompsPTwoDKlein.frobInvol (k := L) (p := r) D.e).toRingHom
        ((CompsPTwoDKlein.frobInvol (k := L) (p := r) D.e).toRingHom x) = x :=
    fun x => CompsPTwoDKlein.frobHom_frobHom D.e x
  let linNode : ℕ → Subgroup (ModGL τ L) := fun i =>
    ((ρ i).comp (Matrix.SpecialLinearGroup.map (ι.comp (algebraMap
      ↥(frobeniusFixedField L r D.e) ↥(frobeniusFixedField L r (D.e * 2)))))).range
  let Vg : Subgroup (ModGL τ L) := ((Φ.comp (Matrix.SpecialLinearGroup.map ι)).comp
    (usbSL (CompsPTwoDKlein.frobInvol (k := L) (p := r) D.e).toRingHom hσσ)).range
  have hlongrange : ∀ j : Fin m, j.val + 2 < m → ∀ x : L, x ^ r ^ D.e = x →
      rootSL2 τ L (b j) (uSL x) ∈ linNode j.val ∧ rootSL2 τ L (b j) (vSL x) ∈ linNode j.val := by
    intro j hj x hx
    have hxF : x ∈ frobeniusFixedField L r D.e :=
      CFSG.LieType.Chevalley.mem_frobeniusFixedField.2 hx
    refine ⟨⟨uSL (⟨x, hxF⟩ : ↥(frobeniusFixedField L r D.e)), ?_⟩,
      ⟨vSL (⟨x, hxF⟩ : ↥(frobeniusFixedField L r D.e)), ?_⟩⟩
    · simp only [MonoidHom.comp_apply, map_uSL', hρi j]
      rfl
    · simp only [MonoidHom.comp_apply, map_vSL', hρi j]
      rfl
  have hρ0 : ρ (m - 2) = rootSL2 τ L (b a0) := hρi a0
  have hρ1 : ρ (m - 1) = rootSL2 τ L (b a1) := hρi a1
  have hforkrange : ∀ x : L, x ^ r ^ (D.e * 2) = x →
      rootSL2 τ L (b a0) (uSL x) * rootSL2 τ L (b a1) (uSL (x ^ r ^ D.e)) ∈ Vg ∧
        rootSL2 τ L (b a0) (vSL x) * rootSL2 τ L (b a1) (vSL (x ^ r ^ D.e)) ∈ Vg := by
    intro x hx
    have hxK : x ∈ frobeniusFixedField L r (D.e * 2) :=
      CFSG.LieType.Chevalley.mem_frobeniusFixedField.2 hx
    refine ⟨⟨uSL (⟨x, hxK⟩ : ↥(frobeniusFixedField L r (D.e * 2))), ?_⟩,
      ⟨vSL (⟨x, hxK⟩ : ↥(frobeniusFixedField L r (D.e * 2))), ?_⟩⟩
    · simp only [MonoidHom.comp_apply]
      rw [CompsPTwoDChain.phi_usbSL ι hσσ Φ hΦ0 hΦ2, map_uSL', map_uSL', hρ0, hρ1]
      rfl
    · simp only [MonoidHom.comp_apply]
      rw [CompsPTwoDChain.phi_usbSL ι hσσ Φ hΦ0 hΦ2, map_vSL', map_vSL', hρ0, hρ1]
      rfl
  have hle_long : ∀ j : Fin m, j.val + 2 < m → linNode j.val ≤
      ⨆ i : Fin (m - 1), if i.val + 2 < m then linNode i.val else Vg := by
    intro j hj
    have hlt : j.val < m - 1 := by omega
    have := le_iSup (fun i : Fin (m - 1) => if i.val + 2 < m then linNode i.val else Vg)
      ⟨j.val, hlt⟩
    simpa only [if_pos (show (⟨j.val, hlt⟩ : Fin (m - 1)).val + 2 < m from hj)] using this
  have hle_fork : Vg ≤ ⨆ i : Fin (m - 1), if i.val + 2 < m then linNode i.val else Vg := by
    have hlt : m - 2 < m - 1 := by omega
    have hcond : ¬ (⟨m - 2, hlt⟩ : Fin (m - 1)).val + 2 < m := by
      show ¬ m - 2 + 2 < m
      omega
    have := le_iSup (fun i : Fin (m - 1) => if i.val + 2 < m then linNode i.val else Vg)
      ⟨m - 2, hlt⟩
    simpa only [if_neg hcond] using this
  have hC : (⨆ i : Fin (m - 1), if i.val + 2 < m then linNode i.val else Vg) =
      D.orbitGroup := by
    refine le_antisymm (iSup_le fun i => ?_) ?_
    · by_cases hi : i.val + 2 < m
      · rw [if_pos hi]
        rintro _ ⟨A, rfl⟩
        refine sl2_hom_mem_of_gens _ D.orbitGroup (fun t => ?_) (fun t => ?_) A
        · have h := (hlongmem ⟨i.val, by omega⟩ hi (t : L)
            (CFSG.LieType.Chevalley.mem_frobeniusFixedField.1 t.2)).1
          rw [← hρi ⟨i.val, by omega⟩] at h
          simp only [MonoidHom.comp_apply, map_uSL']
          exact h
        · have h := (hlongmem ⟨i.val, by omega⟩ hi (t : L)
            (CFSG.LieType.Chevalley.mem_frobeniusFixedField.1 t.2)).2
          rw [← hρi ⟨i.val, by omega⟩] at h
          simp only [MonoidHom.comp_apply, map_vSL']
          exact h
      · rw [if_neg hi]
        rintro _ ⟨B, rfl⟩
        refine sl2_hom_mem_of_gens _ D.orbitGroup (fun t => ?_) (fun t => ?_) B
        · have h := (hforkmem (t : L) (CFSG.LieType.Chevalley.mem_frobeniusFixedField.1 t.2)).1
          rw [← hρi a0, ← hρi a1] at h
          have e := CompsPTwoDChain.phi_usbSL ι hσσ Φ hΦ0 hΦ2 (uSL t)
          simp only [MonoidHom.comp_apply, e, map_uSL']
          exact h
        · have h := (hforkmem (t : L) (CFSG.LieType.Chevalley.mem_frobeniusFixedField.1 t.2)).2
          rw [← hρi a0, ← hρi a1] at h
          have e := CompsPTwoDChain.phi_usbSL ι hσσ Φ hΦ0 hΦ2 (vSL t)
          simp only [MonoidHom.comp_apply, e, map_vSL']
          exact h
    · have hgen : ∀ O ∈ D.orbits, ∀ c : ↥(D.orbitField O),
          D.orbitX O c ∈ (⨆ i : Fin (m - 1), if i.val + 2 < m then linNode i.val else Vg) ∧
          D.orbitY O c ∈ (⨆ i : Fin (m - 1), if i.val + 2 < m then linNode i.val else Vg) := by
        intro O hO c
        rcases hOcases O hO with ⟨j, hj, rfl⟩ | rfl
        · have hx : (c : L) ^ r ^ D.e = c := by
            have := (hmemq _ (c : L)).1 c.2
            rwa [hcard1 j hj, mul_one] at this
          obtain ⟨h1, h2⟩ := hlongrange j hj (c : L) hx
          obtain ⟨e1, e2⟩ := hXeq j hj c
          exact ⟨e1 ▸ hle_long j hj h1, e2 ▸ hle_long j hj h2⟩
        · have hx : (c : L) ^ r ^ (D.e * 2) = c := by
            have := (hmemq _ (c : L)).1 c.2
            rwa [hcard2] at this
          obtain ⟨h1, h2⟩ := hforkrange (c : L) hx
          obtain ⟨e1, e2⟩ := hXeqf c
          exact ⟨e1 ▸ hle_fork h1, e2 ▸ hle_fork h2⟩
      refine (Subgroup.closure_le _).2 ?_
      rintro g ⟨O, hO, c, rfl | rfl⟩
      · exact (hgen O hO c).1
      · exact (hgen O hO c).2
  exact hrec ρ Φ D.orbitGroup hρinj hcomm hfr hΦ0 hΦ1 hΦ2 hC

theorem lieModel_orbitGroup_of_datum_four_of_root_data {τ : Tag}
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {r : ℕ} [Fact r.Prime] {L : Type} [Field L] [CharP L r] [IsAlgClosed L] {M : Type}
    [CommGroup M] (D : GenFixedRootDatum τ r L M) {m : ℕ}
    (hm4 : 4 ≤ m) (hrec : TwoDChainRecog r L D.e m) (b : Fin m → Fin τ.rank → ℤ)
    (hroot : ∀ j, IsRoot τ (b j))
    (hbinj : Function.Injective b)
    (hG : ∀ j k, iform (b j) (b k) = CFSG.LieType.Universal.Spin.cartanD m j k)
    (hsimple : D.simpleRootsJ = Set.range b)
    (hfix : ∀ j : Fin m, j.val + 2 < m → D.θ (toReal (b j)) = toReal (b j))
    (hswap01 : D.θ (toReal (b ⟨m - 2, by omega⟩)) = toReal (b ⟨m - 1, by omega⟩))
    (hswap10 : D.θ (toReal (b ⟨m - 1, by omega⟩)) = toReal (b ⟨m - 2, by omega⟩))
    (hframe : ∀ j k : Fin m, CFSG.LieType.Universal.Spin.cartanD m j k = -1 →
      ∃ θ : SL(3, L) →* ModGL τ L, θ.comp (blockSL L 3 2 0 (by omega)) = rootSL2 τ L (b j) ∧
        θ.comp (blockSL L 3 2 1 (by omega)) = rootSL2 τ L (b k)) :
    LieModel (↥D.orbitGroup ⧸ Subgroup.center ↥D.orbitGroup) .POmegaMinus m r D.e := by
  classical
  have hOf : thetaOrbit D.θ (b ⟨m - 2, by omega⟩) = {b ⟨m - 2, by omega⟩, b ⟨m - 1, by omega⟩} :=
    thetaOrbit_of_swap hswap01 hswap10
  have hOf' : thetaOrbit D.θ (b ⟨m - 1, by omega⟩) =
      {b ⟨m - 2, by omega⟩, b ⟨m - 1, by omega⟩} := by
    rw [thetaOrbit_of_swap hswap10 hswap01, Set.pair_comm]
  by_cases h : GenFixedRootDatum.orbitRoot (thetaOrbit D.θ (b ⟨m - 2, by omega⟩)) =
      b ⟨m - 2, by omega⟩
  · exact lieModel_orbitGroup_of_datum_core_four_of_root_data hτ D hm4 hrec b hroot hbinj hG hsimple hfix hswap01
      hswap10 h hframe
  · have hmem : GenFixedRootDatum.orbitRoot (thetaOrbit D.θ (b ⟨m - 2, by omega⟩)) ∈
        thetaOrbit D.θ (b ⟨m - 2, by omega⟩) :=
      lexLeast_mem (by rw [hOf]; exact Set.toFinite _) ⟨_, self_mem_thetaOrbit _ _⟩
    have h1 : GenFixedRootDatum.orbitRoot (thetaOrbit D.θ (b ⟨m - 2, by omega⟩)) =
        b ⟨m - 1, by omega⟩ := by
      have hmem' : GenFixedRootDatum.orbitRoot (thetaOrbit D.θ (b ⟨m - 2, by omega⟩)) ∈
          ({b ⟨m - 2, by omega⟩, b ⟨m - 1, by omega⟩} : Set (Fin τ.rank → ℤ)) := by
        rw [← hOf]
        exact hmem
      rcases hmem' with h' | h'
      · exact absurd h' h
      · exact h'
    have hsw0 : Equiv.swap (⟨m - 2, by omega⟩ : Fin m) ⟨m - 1, by omega⟩ ⟨m - 2, by omega⟩ =
        ⟨m - 1, by omega⟩ := Equiv.swap_apply_left _ _
    have hsw1 : Equiv.swap (⟨m - 2, by omega⟩ : Fin m) ⟨m - 1, by omega⟩ ⟨m - 1, by omega⟩ =
        ⟨m - 2, by omega⟩ := Equiv.swap_apply_right _ _
    refine lieModel_orbitGroup_of_datum_core_four_of_root_data hτ D hm4 hrec
      (fun j => b (Equiv.swap (⟨m - 2, by omega⟩ : Fin m) ⟨m - 1, by omega⟩ j))
      (fun j => hroot _) (hbinj.comp (Equiv.injective _))
      (fun j k => by rw [hG, cartanD_swap hm4]) ?_ (fun j hj => ?_) ?_ ?_ ?_ (fun j k hjk => ?_)
    · rw [hsimple]
      exact ((Equiv.swap (⟨m - 2, by omega⟩ : Fin m)
        ⟨m - 1, by omega⟩).surjective.range_comp b).symm
    · have e : Equiv.swap (⟨m - 2, by omega⟩ : Fin m) ⟨m - 1, by omega⟩ j = j :=
        Equiv.swap_apply_of_ne_of_ne
          (fun h' => by rw [h'] at hj; simp only [Fin.val_mk] at hj; omega)
          (fun h' => by rw [h'] at hj; simp only [Fin.val_mk] at hj; omega)
      show D.θ (toReal (b (Equiv.swap _ _ j))) = toReal (b (Equiv.swap _ _ j))
      rw [e]
      exact hfix j hj
    · show D.θ (toReal (b (Equiv.swap (⟨m - 2, by omega⟩ : Fin m) ⟨m - 1, by omega⟩
        ⟨m - 2, by omega⟩))) = toReal (b (Equiv.swap (⟨m - 2, by omega⟩ : Fin m)
          ⟨m - 1, by omega⟩ ⟨m - 1, by omega⟩))
      rw [hsw0, hsw1]
      exact hswap10
    · show D.θ (toReal (b (Equiv.swap (⟨m - 2, by omega⟩ : Fin m) ⟨m - 1, by omega⟩
        ⟨m - 1, by omega⟩))) = toReal (b (Equiv.swap (⟨m - 2, by omega⟩ : Fin m)
          ⟨m - 1, by omega⟩ ⟨m - 2, by omega⟩))
      rw [hsw0, hsw1]
      exact hswap01
    · show GenFixedRootDatum.orbitRoot (thetaOrbit D.θ (b (Equiv.swap (⟨m - 2, by omega⟩ : Fin m)
        ⟨m - 1, by omega⟩ ⟨m - 2, by omega⟩))) =
          b (Equiv.swap (⟨m - 2, by omega⟩ : Fin m) ⟨m - 1, by omega⟩ ⟨m - 2, by omega⟩)
      rw [hsw0, hOf', ← hOf, h1]
    · exact hframe _ _ (by rw [cartanD_swap hm4]; exact hjk)

theorem lieModel_orbitGroup_of_datum_four {τ : Tag}
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {r : ℕ} [Fact r.Prime] {L : Type} [Field L] [CharP L r] [IsAlgClosed L] {M : Type}
    [CommGroup M] (D : GenFixedRootDatum τ r L M) {m : ℕ}
    (hm4 : 4 ≤ m) (hrec : TwoDChainRecog r L D.e m) (b : Fin m → Fin τ.rank → ℤ)
    (hroot : ∀ j, IsRoot τ (b j))
    (hbinj : Function.Injective b)
    (hG : ∀ j k, iform (b j) (b k) = CFSG.LieType.Universal.Spin.cartanD m j k)
    (hsimple : D.simpleRootsJ = Set.range b)
    (hfix : ∀ j : Fin m, j.val + 2 < m → D.θ (toReal (b j)) = toReal (b j))
    (hswap01 : D.θ (toReal (b ⟨m - 2, by omega⟩)) = toReal (b ⟨m - 1, by omega⟩))
    (hswap10 : D.θ (toReal (b ⟨m - 1, by omega⟩)) = toReal (b ⟨m - 2, by omega⟩))
    (hframe : ∀ j k : Fin m, CFSG.LieType.Universal.Spin.cartanD m j k = -1 →
      ∃ θ : SL(3, L) →* ModGL τ L, θ.comp (blockSL L 3 2 0 (by omega)) = rootSL2 τ L (b j) ∧
        θ.comp (blockSL L 3 2 1 (by omega)) = rootSL2 τ L (b k)) :
    LieModel (↥D.orbitGroup ⧸ Subgroup.center ↥D.orbitGroup) .POmegaMinus m r D.e :=
  lieModel_orbitGroup_of_datum_four_of_root_data hτ D hm4 hrec b hroot hbinj hG
    hsimple hfix hswap01 hswap10 hframe

theorem catalogueOver_of_datum_four {τ : Tag}
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {r : ℕ} [Fact r.Prime] {L : Type} [Field L] [CharP L r] [IsAlgClosed L] {M : Type}
    [CommGroup M] (D : GenFixedRootDatum τ r L M) {m : ℕ}
    (hm4 : 4 ≤ m) (hrec : TwoDChainRecog r L D.e m) (b : Fin m → Fin τ.rank → ℤ)
    (hroot : ∀ j, IsRoot τ (b j))
    (hbinj : Function.Injective b)
    (hG : ∀ j k, iform (b j) (b k) = CFSG.LieType.Universal.Spin.cartanD m j k)
    (hsimple : D.simpleRootsJ = Set.range b)
    (hfix : ∀ j : Fin m, j.val + 2 < m → D.θ (toReal (b j)) = toReal (b j))
    (hswap01 : D.θ (toReal (b ⟨m - 2, by omega⟩)) = toReal (b ⟨m - 1, by omega⟩))
    (hswap10 : D.θ (toReal (b ⟨m - 1, by omega⟩)) = toReal (b ⟨m - 2, by omega⟩))
    (hframe : ∀ j k : Fin m, CFSG.LieType.Universal.Spin.cartanD m j k = -1 →
      ∃ θ : SL(3, L) →* ModGL τ L, θ.comp (blockSL L 3 2 0 (by omega)) = rootSL2 τ L (b j) ∧
        θ.comp (blockSL L 3 2 1 (by omega)) = rootSL2 τ L (b k)) :
    CatalogueOver r (r ^ D.e) ↥D.orbitGroup :=
  catalogueOver_of_lieModel_pominus
    (lieModel_orbitGroup_of_datum_four hτ D hm4 hrec b hroot hbinj hG hsimple hfix hswap01
      hswap10 hframe)

end TwoD

section TwoDClass

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.KE CFSG.ClassicalInvolution.WeakCT CFSG.Timmesfeld
  CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPTwoDMain
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPTwoDRecog
open scoped MatrixGroups Matrix

variable {τ : Tag}

theorem lieModel_rationalComponent_of_dClassTwistedG (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (K : KacData τ) (hK : K.Facts) {E : List (ℕ × ℕ)} {tp : ℕ → ℕ → List ℕ}
    (hT : IsTreePaths (τ.rank + 1) E tp)
    (hadj : ∀ x y : Option (Fin τ.rank), K.Adj x y ↔ (nodeIdx x, nodeIdx y) ∈ E)
    {cands : List (List ℕ)}
    (hcheck : ((List.range (τ.rank + 1)).sublists.all fun zl =>
      !(fun _ : List ℕ => true) zl ||
        zl.all fun x => cands.any (sameSet (compIdx (τ.rank + 1) tp zl x))) = true)
    (hlt : ∀ c ∈ cands, ∀ w ∈ c, w < τ.rank + 1)
    (hcard : ∀ c ∈ cands, (c.map (idxNode (r := τ.rank))).toFinset.card = c.length)
    {trees : List (List (Option (Fin τ.rank)))}
    (hcount : ∀ c ∈ cands, 4 ≤ c.length →
      kacCount τ K.θ (c.map (idxNode (r := τ.rank))).toFinset = 2 * c.length * (c.length - 1) →
        ∃ P ∈ trees, sameSet c (P.map nodeIdx) = true)
    (htrees : ∀ P ∈ trees, P.Nodup ∧ 4 ≤ P.length ∧
      (∀ c d : Fin P.length, c ≠ d → ¬ edgeD P.length c d → ¬ edgeD P.length d c →
        iform (K.extRoot (P.get c)) (K.extRoot (P.get d)) = 0) ∧
      ∀ c d : Fin P.length, edgeD P.length c d →
        (nodeIdx (P.get c), nodeIdx (P.get d)) ∈ E)
    (hframes : ∀ {F : Type} [Field F] (x y : Option (Fin τ.rank)),
      (nodeIdx x, nodeIdx y) ∈ E →
        ∃ (ρ : SL(3, F) →* ModGL τ F) (σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ),
          CFSG.RankThree.PartOne.KF4.IsA2Frame ρ σ ∧ σ 0 1 = K.extRoot x ∧
            σ 1 2 = K.extRoot y)
    {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime)
    (hpL : (p : L) ≠ 0) {a : Fin τ.rank → Lˣ} (hTor : rootDiagUnit τ a ∈ S.D.torus)
    (hTp : rootDiagUnit τ a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      2 * compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) - 1))
    (hkind : twistKind S.ρ (rootCharHom a) i = .twoD)
    (Q : ℕ → ℕ → Prop) (hrec : TwoDChainRecogAll L Q) (hQ : Q (ringChar L) S.D.q) :
    ∃ m e : ℕ, ringChar L ^ e = S.D.q ∧
      LieModel (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) .POmegaMinus m
        (ringChar L) e := by
  classical
  obtain ⟨r, e, m, hr, hchar, hm5, z, ε, D, hq, he, hDe, hRC, hDs, hCart, hfix, hswap⟩ :=
    CompsPTwoDExport.exists_twoD_export S hτ hTor i hkind h5
  haveI := hr
  haveI := hchar
  have hrc : ringChar L = r := ringChar.eq L r
  have hQ' : Q r (r ^ e) := by
    have h := hQ
    rw [hrc, hq] at h
    exact h
  have hR : CompsPTwoDDatumG.TwoDChainRecog r L D.e m := by
    rw [hDe]
    exact hrec r e m he hm5 hQ'
  have hΨ : IsRootComponent (componentRoots (rootCharHom a) i) := isRootComponent_componentRoots i
  have hsl : ∀ β ∈ componentRoots (rootCharHom a) i, iform β β = 2 := fun β hβ => by
    rw [← dotProduct_mulVec_eq_iform]
    exact rootForm_self hτ (hΨ.isRoot β hβ)
  have hbroot : ∀ j : Fin m, IsRoot τ (ε.symm j : Fin τ.rank → ℤ) := fun j =>
    simpleRoots_isRoot (ε.symm j).2
  have hbinj : Function.Injective (fun j : Fin m => (ε.symm j : Fin τ.rank → ℤ)) :=
    fun j k h => ε.symm.injective (Subtype.ext h)
  have hG : ∀ j k : Fin m, iform (ε.symm j : Fin τ.rank → ℤ) (ε.symm k) =
      CFSG.LieType.Universal.Spin.cartanD m j k := by
    intro j k
    have h := hCart (ε.symm j) (ε.symm k)
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
    rw [← h]
    exact (CompsPTwoDBase.corootPair_eq_iform (hbroot j)
      (hsl _ (simpleRoots_subset (ε.symm j).2)) _).symm
  have hrange : Set.range (fun j : Fin m => (ε.symm j : Fin τ.rank → ℤ)) =
      ((simpleRoots (componentRoots (rootCharHom a) i) : Finset (Fin τ.rank → ℤ)) :
        Set (Fin τ.rank → ℤ)) := by
    ext β
    constructor
    · rintro ⟨j, rfl⟩
      exact (ε.symm j).2
    · intro hβ
      exact ⟨ε ⟨β, hβ⟩, by simp⟩
  have hsw := hswap ⟨m - 2, by omega⟩ ⟨m - 1, by omega⟩ (by simp only [Fin.val_mk]; omega)
    (by simp only [Fin.val_mk]; omega)
  have hlie := lieModel_orbitGroup_of_datum_four hτ D (by omega) hR
    (fun j : Fin m => (ε.symm j : Fin τ.rank → ℤ)) hbroot hbinj hG (hDs.trans hrange.symm) hfix
    hsw.1 hsw.2
    (fun j k hjk => exists_dFrames hτ K hK hT hadj hcheck hlt hcard hcount htrees hframes S hp hpL
      hTp i (by omega) hn ε hCart L j k hjk)
  let eR : ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ≃* ↥D.orbitGroup :=
    ((rationalComponent S.ρ S.Γ (rootCharHom a) i).equivMapOfInjective
      (MulAut.conj z⁻¹).toMonoidHom (MulAut.conj z⁻¹).injective).trans (MulEquiv.subgroupCongr hRC)
  have hqiso : ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ≃*
      ↥D.orbitGroup ⧸ Subgroup.center ↥D.orbitGroup :=
    QuotientGroup.congr _ _ eR (Subgroup.map_center_eq eR)
  have hmodel : LieModel (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
      .POmegaMinus m r D.e :=
    LieModel.of_mulEquiv hqiso.symm hlie
  refine ⟨m, e, ?_, ?_⟩
  · rw [hrc, hq]
  · rw [hrc]
    exact hDe ▸ hmodel

variable {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}

theorem lieModel_rationalComponent_of_dClassTwistedG_E6 (S : LangSetup Tag.E6 L p₀) (hp : p.Prime)
    (hpL : (p : L) ≠ 0) {a : Fin Tag.E6.rank → Lˣ} (hTor : rootDiagUnit Tag.E6 a ∈ S.D.torus)
    (hTp : rootDiagUnit Tag.E6 a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      2 * compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) - 1))
    (hkind : twistKind S.ρ (rootCharHom a) i = .twoD)
    (Q : ℕ → ℕ → Prop) (hrec : TwoDChainRecogAll L Q) (hQ : Q (ringChar L) S.D.q) :
    ∃ m e : ℕ, ringChar L ^ e = S.D.q ∧
      LieModel (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) .POmegaMinus m
        (ringChar L) e :=
  lieModel_rationalComponent_of_dClassTwistedG (Or.inr (Or.inl rfl)) kacE6 facts_E6 e6_tree
    e6_adj e6_check e6_lt e6_card e6_dcount e6_dtrees (fun {F} _ x y h => e6_frames x y h) S hp
    hpL hTor hTp i h5 hn hkind Q hrec hQ

theorem lieModel_rationalComponent_of_dClassTwistedG_E7 (S : LangSetup Tag.E7 L p₀) (hp : p.Prime)
    (hpL : (p : L) ≠ 0) {a : Fin Tag.E7.rank → Lˣ} (hTor : rootDiagUnit Tag.E7 a ∈ S.D.torus)
    (hTp : rootDiagUnit Tag.E7 a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      2 * compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) - 1))
    (hkind : twistKind S.ρ (rootCharHom a) i = .twoD)
    (Q : ℕ → ℕ → Prop) (hrec : TwoDChainRecogAll L Q) (hQ : Q (ringChar L) S.D.q) :
    ∃ m e : ℕ, ringChar L ^ e = S.D.q ∧
      LieModel (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) .POmegaMinus m
        (ringChar L) e :=
  lieModel_rationalComponent_of_dClassTwistedG (Or.inr (Or.inr (Or.inl rfl))) kacE7 facts_E7
    e7_tree e7_adj e7_check e7_lt e7_card e7_dcount e7_dtrees (fun {F} _ x y h => e7_frames x y h)
    S hp hpL hTor hTp i h5 hn hkind Q hrec hQ

theorem lieModel_rationalComponent_of_dClassTwistedG_E8 (S : LangSetup Tag.E8 L p₀) (hp : p.Prime)
    (hpL : (p : L) ≠ 0) {a : Fin Tag.E8.rank → Lˣ} (hTor : rootDiagUnit Tag.E8 a ∈ S.D.torus)
    (hTp : rootDiagUnit Tag.E8 a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      2 * compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) - 1))
    (hkind : twistKind S.ρ (rootCharHom a) i = .twoD)
    (Q : ℕ → ℕ → Prop) (hrec : TwoDChainRecogAll L Q) (hQ : Q (ringChar L) S.D.q) :
    ∃ m e : ℕ, ringChar L ^ e = S.D.q ∧
      LieModel (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) .POmegaMinus m
        (ringChar L) e :=
  lieModel_rationalComponent_of_dClassTwistedG (Or.inr (Or.inr (Or.inr rfl))) kacE8 facts_E8
    e8_tree e8_adj e8_check e8_lt e8_card e8_dcount e8_dtrees (fun {F} _ x y h => e8_frames x y h)
    S hp hpL hTor hTp i h5 hn hkind Q hrec hQ

variable {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}

theorem lieModel_rationalComponent_of_twoD_highG {p : ℕ} (hp : p.Prime) {τ : Tag}
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      2 * compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) - 1))
    (hout : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    (Q : ℕ → ℕ → Prop) (hrec : CompsPTwoDRecog.TwoDChainRecogAll L Q)
    (hQ : Q (ringChar L) S.D.q) :
    ∃ m e : ℕ, ringChar L ^ e = S.D.q ∧
      LieModel (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) .POmegaMinus m
        (ringChar L) e := by
  classical
  have hℓp : ringChar L ≠ p := ringChar_ne_of_pow_eq_one hp hap h1
  have hpL : ((p : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hp hℓp
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  have hkind : twistKind S.ρ (rootCharHom a) i = .twoD := by
    unfold twistKind
    rw [if_neg hout, if_neg, if_pos ⟨by omega, hn⟩]
    rintro (⟨h6, h72⟩ | ⟨h4', -, -⟩)
    · rw [hn, h6] at h72
      omega
    · omega
  have hr := compRank_le_rank (componentRoots (rootCharHom a) i)
  cases τ with
  | G2 => exact absurd (le_trans h5 hr) (by simp [Tag.rank])
  | F4 => exact absurd (le_trans h5 hr) (by simp [Tag.rank])
  | D4 => exact absurd (le_trans h5 hr) (by simp [Tag.rank])
  | E6 =>
    exact lieModel_rationalComponent_of_dClassTwistedG_E6 S hp hpL hT hTp i h5 hn hkind Q hrec
      hQ
  | E7 =>
    exact lieModel_rationalComponent_of_dClassTwistedG_E7 S hp hpL hT hTp i h5 hn hkind Q hrec
      hQ
  | E8 =>
    exact lieModel_rationalComponent_of_dClassTwistedG_E8 S hp hpL hT hTp i h5 hn hkind Q hrec
      hQ

theorem ratCat_of_twoD_highG {p : ℕ} (hp : p.Prime) {τ : Tag} {L : Type} [Field L]
    [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      2 * compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) - 1))
    (hout : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    (Q : ℕ → ℕ → Prop) (hrec : CompsPTwoDRecog.TwoDChainRecogAll L Q)
    (hQ : Q (ringChar L) S.D.q) :
    RationalCatalogue S i := by
  obtain ⟨m, e, hq, hlie⟩ :=
    lieModel_rationalComponent_of_twoD_highG hp S hT hap h1 i h5 hn hout Q hrec hQ
  refine ⟨1, le_rfl, ?_⟩
  rw [pow_one, ← hq]
  exact catalogueOver_of_lieModel_pominus hlie

end TwoDClass

end ExcUntw

namespace ExcUntw

section D4Generic

theorem catalogueOver_map_conj {G : Type} [Group G] {ℓ Q : ℕ} {R : Subgroup G} (φ : G ≃* G)
    (h : CatalogueOver ℓ Q ↥R) : CatalogueOver ℓ Q ↥(R.map φ.toMonoidHom) :=
  h.of_mulEquiv (R.equivMapOfInjective φ.toMonoidHom φ.injective)

end D4Generic

section D4Cubic

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KD4T
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp

theorem catalogueOver_graphFixedRootGroup_cubic {ℓ f' : ℕ} (hℓ : ℓ.Prime) (hf' : 1 ≤ f')
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f') ^ 3) (σ : K ≃+* K) {r : ℕ}
    (hr : r = 1 ∨ r = 2) (hσ : ∀ c, σ c = c ^ ((ℓ ^ f') ^ r)) :
    CatalogueOver ℓ (ℓ ^ f') ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  classical
  let q' : TauCeti.PrimePower := ⟨ℓ, f', hℓ, hf'⟩
  have hv' : (TauCeti.LieTypeIndex.trialityD4 q').Valid := TauCeti.LieTypeIndex.valid_trialityD4 q'
  have hKq : Nat.card K = q'.card ^ 3 := by rw [hK, TauCeti.PrimePower.card_def]
  obtain ⟨σ₁, hσ₁, ⟨e⟩⟩ : ∃ σ₁ : K ≃+* K, (∀ c, σ₁ c = c ^ q'.card) ∧
      Nonempty (graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≃*
        graphFixedRootGroup TwistTag.D4 K σ₁.toRingHom) := by
    rcases hr with rfl | rfl
    · exact ⟨σ, fun c => by rw [hσ, pow_one, TauCeti.PrimePower.card_def], ⟨MulEquiv.refl _⟩⟩
    · have h₁ : ∀ c, σ.symm c = c ^ q'.card := fun c => by
        rw [RingEquiv.symm_apply_eq, hσ, TauCeti.PrimePower.card_def, ← pow_mul,
          show ℓ ^ f' * (ℓ ^ f') ^ 2 = (ℓ ^ f') ^ 3 by ring]
        have : Fintype K := Fintype.ofFinite K
        have hq : Fintype.card K = (ℓ ^ f') ^ 3 := by rw [← Nat.card_eq_fintype_card, hK]
        rw [← hq]
        exact (FiniteField.pow_card c).symm
      exact ⟨σ.symm, h₁,
        CFSG.HardMathSupport.Dickson.DefCharOuter.Export.exists_mulEquiv_graphFixedRootGroup_inv_D4
          K σ σ.symm (fun c => σ.apply_symm_apply c)⟩
  obtain ⟨eCat⟩ := catEquiv_trialityD4_of_field q' hv' K hKq σ₁ hσ₁
  have hZ : Subgroup.center ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  let e0 : (↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ⧸
      Subgroup.center ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ≃*
        ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  refine ⟨.lie ⟨.trialityD4 q', hv'⟩, ⟨(e0.trans e).trans eCat.symm⟩,
    Or.inl ⟨TauCeti.LieTypeIndex.characteristic_trialityD4 q', ?_, by simp [suzRee]⟩⟩
  simp [fieldSize, q', TauCeti.PrimePower.card_def]

end D4Cubic

section D4LayerDefs

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KD4T
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KD4L CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

@[expose] def D4TrialityLayerCat (τ : Tag) : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] (ℓ f : ℕ) [Fact ℓ.Prime] [CharP L ℓ], 1 ≤ f →
    ∀ a b c : Fin τ.rank, a ≠ b → b ≠ c → a ≠ c → a.val ∈ ({1, 2, 4} : Set ℕ) →
    b.val ∈ ({1, 2, 4} : Set ℕ) → c.val ∈ ({1, 2, 4} : Set ℕ) →
    ∀ (n : ModGL τ L) (hn : n ∈ monomialSubgroup τ L), n ∈ adjointGroup τ L →
      (∃ u ∈ parabolicWeylGroup τ (d4Nodes τ), ∀ α ∈ parabolicRoots τ (d4Nodes τ),
        weylQuotientHom τ L ⟨n, hn⟩ • α = u • permLattice (List.formPerm [a, b, c]) α) →
      ∀ P : Subgroup (ModGL τ L), P = rootSpan τ L (parabolicRoots τ (d4Nodes τ)) ⊓
        twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) →
      CatalogueOver ℓ (ℓ ^ f) ↥P

@[expose] def D4SwapLayerCatAll (τ : Tag) : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] (ℓ f : ℕ) [Fact ℓ.Prime] [CharP L ℓ], 1 ≤ f →
    ∀ i j : Fin τ.rank, i ≠ j → i.val ∈ ({1, 2, 4} : Set ℕ) → j.val ∈ ({1, 2, 4} : Set ℕ) →
    ∀ (n : ModGL τ L) (hn : n ∈ monomialSubgroup τ L), n ∈ adjointGroup τ L →
      (∃ u ∈ parabolicWeylGroup τ (d4Nodes τ), ∀ α ∈ parabolicRoots τ (d4Nodes τ),
        weylQuotientHom τ L ⟨n, hn⟩ • α = u • permLattice (Equiv.swap i j) α) →
      ∀ P : Subgroup (ModGL τ L), P = rootSpan τ L (parabolicRoots τ (d4Nodes τ)) ⊓
        twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) →
      CatalogueOver ℓ (ℓ ^ f) ↥P

end D4LayerDefs

section D4Tau

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KD4L CFSG.RankThree.PartOne.KD4T
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.Chevalley CFSG.RankThree.E6
  CFSG.Timmesfeld.LevisSpin CFSG.ClassicalInvolution.WeakCT
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPD4Tau
open scoped Matrix MatrixGroups

variable
  {L : Type} [Field L] [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime] [CharP L ℓ] {f : ℕ}
  (hf : 1 ≤ f)

include hf in
theorem catalogueOver_tauDatum_all :
    CatalogueOver ℓ (ℓ ^ f) ↥(tauDatum L ℓ f hf).orbitGroup := by
  classical
  have h1S : (1 : Fin Tag.E6.rank) ∈ d4Support := by
    change (1 : Fin Tag.E6.rank) ≠ 0 ∧ (1 : Fin Tag.E6.rank) ≠ 5
    decide
  have h2S : (2 : Fin Tag.E6.rank) ∈ d4Support := by
    change (2 : Fin Tag.E6.rank) ≠ 0 ∧ (2 : Fin Tag.E6.rank) ≠ 5
    decide
  have h3S : (3 : Fin Tag.E6.rank) ∈ d4Support := by
    change (3 : Fin Tag.E6.rank) ≠ 0 ∧ (3 : Fin Tag.E6.rank) ≠ 5
    decide
  have h4S : (4 : Fin Tag.E6.rank) ∈ d4Support := by
    change (4 : Fin Tag.E6.rank) ≠ 0 ∧ (4 : Fin Tag.E6.rank) ≠ 5
    decide
  refine catalogueOver_of_datum_four (τ := Tag.E6) (Or.inr (Or.inl rfl))
    (tauDatum L ℓ f hf) (m := 4) le_rfl (CompsPTwoDChainO.twoDChainRecog_all hf le_rfl) bTau
    bTau_root bTau_injective iform_bTau ?_ ?_ ?_ ?_ ?_
  ·
    ext β
    constructor
    · intro hβ
      rw [GenFixedRootDatum.simpleRootsJ_eq] at hβ
      obtain ⟨j, hj, rfl⟩ := d4Aux.mem_unionSimpleRoots_iff.1 hβ
      have hjS : j ∈ d4Support := d4Aux_support ▸ hj
      rcases d4Support_cases hjS with rfl | rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨3, rfl⟩
    · rintro ⟨j, rfl⟩
      fin_cases j
      · exact single_mem_simpleRootsJ hf h1S
      · exact single_mem_simpleRootsJ hf h3S
      · exact single_mem_simpleRootsJ hf h2S
      · exact single_mem_simpleRootsJ hf h4S
  ·
    intro j hj
    fin_cases j
    · exact (theta_single_tau hf h1S).trans (by rw [gam_one]; rfl)
    · exact (theta_single_tau hf h3S).trans (by rw [gam_three]; rfl)
    · exact absurd hj (by decide)
    · exact absurd hj (by decide)
  · exact (theta_single_tau hf h2S).trans (by rw [gam_two]; rfl)
  · exact (theta_single_tau hf h4S).trans (by rw [gam_four]; rfl)
  ·
    intro j k hjk
    fin_cases j <;> fin_cases k <;>
      first
      | (exfalso; revert hjk; decide)
      | exact exists_frame_E6 (by decide)

include hf in
theorem catalogueOver_fixE6_dN_all :
    CatalogueOver ℓ (ℓ ^ f) ↥(fixE6 ℓ f (dN L)) := by
  rw [fixE6_dN hf]
  exact catalogueOver_tauDatum_all hf

include hf in
theorem exists_fix_swap13_cat_all :
    ∃ n₂ : ModGL Tag.E6 L, Acts n₂ (Equiv.swap 1 3) ∧ E6Fix (ℓ := ℓ) f n₂ ∧
      CatalogueOver ℓ (ℓ ^ f) ↥(fixE6 ℓ f n₂) :=
  ⟨dN L, acts_dN, E6Fix_dN hf, catalogueOver_fixE6_dN_all hf⟩

include hf in
theorem exists_fix_swap03_cat_all :
    ∃ n₂ : ModGL Tag.E6 L, Acts n₂ (Equiv.swap 0 3) ∧ E6Fix (ℓ := ℓ) f n₂ ∧
      CatalogueOver ℓ (ℓ ^ f) ↥(fixE6 ℓ f n₂) := by
  refine ⟨d4TrialityRep L * dN L * (d4TrialityRep L)⁻¹, ?_, ?_, ?_⟩
  · have h := Acts.conj (acts_d4TrialityRep (L := L)) (acts_dN (L := L))
    rwa [rho_conj_swap] at h
  · exact E6Fix.conj map_conj_d4TrialityRep frob_d4TrialityRep (E6Fix_dN hf)
  · rw [fixE6_conj map_conj_d4TrialityRep frob_d4TrialityRep]
    exact catalogueOver_map_conj _ (catalogueOver_fixE6_dN_all hf)

include hf in
theorem exists_fix_swap01_cat_all :
    ∃ n₂ : ModGL Tag.E6 L, Acts n₂ (Equiv.swap 0 1) ∧ E6Fix (ℓ := ℓ) f n₂ ∧
      CatalogueOver ℓ (ℓ ^ f) ↥(fixE6 ℓ f n₂) := by
  have hR := map_conj_mul (L := L) map_conj_d4TrialityRep map_conj_d4TrialityRep
  have hF : Units.map (entrywiseHom (iterateFrobenius L ℓ f))
      (d4TrialityRep L * d4TrialityRep L) = d4TrialityRep L * d4TrialityRep L := by
    rw [map_mul, frob_d4TrialityRep]
  refine ⟨(d4TrialityRep L * d4TrialityRep L) * dN L * (d4TrialityRep L * d4TrialityRep L)⁻¹,
    ?_, ?_, ?_⟩
  · have h := Acts.conj ((acts_d4TrialityRep (L := L)).mul (acts_d4TrialityRep (L := L)))
      (acts_dN (L := L))
    rwa [rho_sq_conj_swap] at h
  · exact E6Fix.conj hR hF (E6Fix_dN hf)
  · rw [fixE6_conj hR hF]
    exact catalogueOver_map_conj _ (catalogueOver_fixE6_dN_all hf)

end D4Tau

section D4Std

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KD4L
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Yardstones.Md0ec50421ce4
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPD4Layers
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix MatrixGroups

variable {τ : Tag} [hτ : E6Sub τ]
variable
  {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ]

theorem catalogueOver_layer_swap {n₁ : ModGL τ L} {π : Equiv.Perm (Fin τ.rank)}
    {σ : Equiv.Perm (Fin Tag.D4.rank)} {n₂ : ModGL Tag.E6 L} (hstd : StdSwap n₁ π σ)
    (h₂ : Acts n₂ σ) (hRL : CatalogueOver ℓ (ℓ ^ f) ↥(fixE6 ℓ f n₂)) {n h : ModGL τ L}
    (hh : h ∈ subsystemGroup τ L (d4Set τ))
    (hlang : ∀ g : ModGL τ L,
      n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g * n⁻¹ = g ↔
        n₁ * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (h * g * h⁻¹) * n₁⁻¹ =
          h * g * h⁻¹)
    {P : Subgroup (ModGL τ L)}
    (hP : P = subsystemGroup τ L (d4Set τ) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :
    CatalogueOver ℓ (ℓ ^ f) ↥P := by
  obtain ⟨eP⟩ := nonempty_equiv_stdLayer hh hlang hP
  exact hRL.of_mulEquiv (eP.trans (hstd.layerEquiv (ℓ := ℓ) (f := f) h₂)).symm

theorem catalogueOver_layer_triality {n₁ : ModGL τ L} {π : Equiv.Perm (Fin τ.rank)} {e : ℕ}
    (hf : 1 ≤ f) (hstd : StdTwist n₁ π e) {n h : ModGL τ L}
    (hh : h ∈ subsystemGroup τ L (d4Set τ))
    (hlang : ∀ g : ModGL τ L,
      n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g * n⁻¹ = g ↔
        n₁ * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (h * g * h⁻¹) * n₁⁻¹ =
          h * g * h⁻¹)
    {P : Subgroup (ModGL τ L)}
    (hP : P = subsystemGroup τ L (d4Set τ) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :
    CatalogueOver ℓ (ℓ ^ f) ↥P := by
  obtain ⟨K, hK, hKf, σ, hKc, hσ, ⟨eP⟩⟩ := layer_graph_equiv_of_standard hf hstd hh hlang hP
  exact (catalogueOver_graphFixedRootGroup_cubic (Fact.out : ℓ.Prime) hf K hKc σ hstd.he
    hσ).of_mulEquiv eP.symm

theorem trialityLayerCat_generic (hf : 1 ≤ f) (π : Equiv.Perm (Fin τ.rank)) (e : ℕ)
    (he : e = 1 ∨ e = 2) (hπe : ∀ k : Fin Tag.D4.rank, π (d4Id k) = d4Id (rhoE e k))
    (hπ : ∀ i ∈ d4Set τ, π i ∈ d4Set τ) (hπ' : ∀ i ∈ d4Set τ, π.symm i ∈ d4Set τ)
    (n : ModGL τ L) (hn : n ∈ monomialSubgroup τ L)
    (hact : ∃ u ∈ parabolicWeylGroup τ (d4Nodes τ), ∀ α ∈ parabolicRoots τ (d4Nodes τ),
      weylQuotientHom τ L ⟨n, hn⟩ • α = u • permLattice π α)
    (P : Subgroup (ModGL τ L)) (hP : P = rootSpan τ L (parabolicRoots τ (d4Nodes τ)) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :
    CatalogueOver ℓ (ℓ ^ f) ↥P := by
  obtain ⟨u, hu, hu'⟩ := hact
  have hact' : ∀ j ∈ d4Set τ, weylQuotientHom τ L ⟨n, hn⟩ • (Pi.single j 1 : Fin τ.rank → ℤ) =
      u • (Pi.single (π j) 1 : Fin τ.rank → ℤ) := fun j hj => by
    have := hu' _ (single_mem_parabolicRoots hj)
    rwa [permLattice_single] at this
  obtain ⟨n₁, h, hn₁, hh, hgen, hlang⟩ := exists_conj_twistedFixed hf hn hπ hπ' hu hact'
  have hstd : StdTwist n₁ π e := ⟨he, hπe, hπ, hπ', hgen⟩
  rw [← subsystemGroup_eq_rootSpan] at hP
  exact catalogueOver_layer_triality hf hstd hh hlang hP

theorem swapLayerCatAll_generic (hf : 1 ≤ f)
    (σ : Equiv.Perm (Fin Tag.D4.rank))
    (hE : ∃ n₂ : ModGL Tag.E6 L, Acts n₂ σ ∧ E6Fix (ℓ := ℓ) f n₂ ∧
      CatalogueOver ℓ (ℓ ^ f) ↥(fixE6 ℓ f n₂))
    (π : Equiv.Perm (Fin τ.rank)) (hπσ : ∀ k : Fin Tag.D4.rank, π (d4Id k) = d4Id (σ k))
    (hπ : ∀ i ∈ d4Set τ, π i ∈ d4Set τ) (hπ' : ∀ i ∈ d4Set τ, π.symm i ∈ d4Set τ)
    (n : ModGL τ L) (hn : n ∈ monomialSubgroup τ L)
    (hact : ∃ u ∈ parabolicWeylGroup τ (d4Nodes τ), ∀ α ∈ parabolicRoots τ (d4Nodes τ),
      weylQuotientHom τ L ⟨n, hn⟩ • α = u • permLattice π α)
    (P : Subgroup (ModGL τ L)) (hP : P = rootSpan τ L (parabolicRoots τ (d4Nodes τ)) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :
    CatalogueOver ℓ (ℓ ^ f) ↥P := by
  obtain ⟨n₂, h₂, -, hRL⟩ := hE
  obtain ⟨u, hu, hu'⟩ := hact
  have hact' : ∀ j ∈ d4Set τ, weylQuotientHom τ L ⟨n, hn⟩ • (Pi.single j 1 : Fin τ.rank → ℤ) =
      u • (Pi.single (π j) 1 : Fin τ.rank → ℤ) := fun j hj => by
    have := hu' _ (single_mem_parabolicRoots hj)
    rwa [permLattice_single] at this
  obtain ⟨n₁, h, hn₁, hh, hgen, hlang⟩ := exists_conj_twistedFixed hf hn hπ hπ' hu hact'
  have hstd : StdSwap n₁ π σ := ⟨hπ, hπ', hπσ, hgen⟩
  rw [← subsystemGroup_eq_rootSpan] at hP
  exact catalogueOver_layer_swap hstd h₂ hRL hh hlang hP

end D4Std

section D4OfLeaf

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KD4L
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Yardstones.Md0ec50421ce4
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPD4Layers
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix MatrixGroups

variable {τ : Tag} [E6Sub τ]

theorem d4TrialityLayerCat_of_leafCycle
    (hleaf : ∀ a b c : Fin τ.rank, a.val = 1 ∨ a.val = 2 ∨ a.val = 4 →
      b.val = 1 ∨ b.val = 2 ∨ b.val = 4 → c.val = 1 ∨ c.val = 2 ∨ c.val = 4 →
      a ≠ b → b ≠ c → a ≠ c →
      ((∀ k : Fin Tag.D4.rank, List.formPerm [a, b, c] (d4Id k) = d4Id (rhoE 1 k)) ∨
        (∀ k : Fin Tag.D4.rank, List.formPerm [a, b, c] (d4Id k) = d4Id (rhoE 2 k))) ∧
      (∀ i : Fin τ.rank, (1 ≤ i.val ∧ i.val ≤ 4) →
        (1 ≤ (List.formPerm [a, b, c] i).val ∧ (List.formPerm [a, b, c] i).val ≤ 4)) ∧
      (∀ i : Fin τ.rank, (1 ≤ i.val ∧ i.val ≤ 4) →
        (1 ≤ ((List.formPerm [a, b, c]).symm i).val ∧
          ((List.formPerm [a, b, c]).symm i).val ≤ 4))) :
    D4TrialityLayerCat τ := by
  intro L _ _ ℓ f _ _ hf a b c hab hbc hac ha hb hc n hn _ hact P hP
  have ha' : a.val = 1 ∨ a.val = 2 ∨ a.val = 4 := by simpa using ha
  have hb' : b.val = 1 ∨ b.val = 2 ∨ b.val = 4 := by simpa using hb
  have hc' : c.val = 1 ∨ c.val = 2 ∨ c.val = 4 := by simpa using hc
  obtain ⟨hcyc, hπ, hπ'⟩ := hleaf a b c ha' hb' hc' hab hbc hac
  rcases hcyc with h1 | h2
  · exact trialityLayerCat_generic hf (List.formPerm [a, b, c]) 1 (Or.inl rfl) h1
      (fun i hi => hπ i hi) (fun i hi => hπ' i hi) n hn hact P hP
  · exact trialityLayerCat_generic hf (List.formPerm [a, b, c]) 2 (Or.inr rfl) h2
      (fun i hi => hπ i hi) (fun i hi => hπ' i hi) n hn hact P hP

theorem d4SwapLayerCatAll_of_leafSwap
    (hleaf : ∀ i j : Fin τ.rank, (i.val = 1 ∨ i.val = 2 ∨ i.val = 4) →
      (j.val = 1 ∨ j.val = 2 ∨ j.val = 4) → i ≠ j →
      ((∀ k : Fin Tag.D4.rank, Equiv.swap i j (d4Id k) = d4Id (Equiv.swap 1 3 k)) ∨
        (∀ k : Fin Tag.D4.rank, Equiv.swap i j (d4Id k) = d4Id (Equiv.swap 0 3 k)) ∨
        (∀ k : Fin Tag.D4.rank, Equiv.swap i j (d4Id k) = d4Id (Equiv.swap 0 1 k))) ∧
      (∀ x : Fin τ.rank, (1 ≤ x.val ∧ x.val ≤ 4) →
        (1 ≤ (Equiv.swap i j x).val ∧ (Equiv.swap i j x).val ≤ 4)) ∧
      (∀ x : Fin τ.rank, (1 ≤ x.val ∧ x.val ≤ 4) →
        (1 ≤ ((Equiv.swap i j).symm x).val ∧ ((Equiv.swap i j).symm x).val ≤ 4))) :
    D4SwapLayerCatAll τ := by
  intro L _ _ ℓ f _ _ hf i j hij hi hj n hn _ hact P hP
  have hi' : i.val = 1 ∨ i.val = 2 ∨ i.val = 4 := by simpa using hi
  have hj' : j.val = 1 ∨ j.val = 2 ∨ j.val = 4 := by simpa using hj
  obtain ⟨hcases, hπ, hπ'⟩ := hleaf i j hi' hj' hij
  rcases hcases with h1 | h2 | h3
  · exact swapLayerCatAll_generic hf (Equiv.swap 1 3) (exists_fix_swap13_cat_all hf)
      (Equiv.swap i j) h1 (fun x hx => hπ x hx) (fun x hx => hπ' x hx) n hn hact P hP
  · exact swapLayerCatAll_generic hf (Equiv.swap 0 3) (exists_fix_swap03_cat_all hf)
      (Equiv.swap i j) h2 (fun x hx => hπ x hx) (fun x hx => hπ' x hx) n hn hact P hP
  · exact swapLayerCatAll_generic hf (Equiv.swap 0 1) (exists_fix_swap01_cat_all hf)
      (Equiv.swap i j) h3 (fun x hx => hπ x hx) (fun x hx => hπ' x hx) n hn hact P hP

end D4OfLeaf

section D4Tags

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KD4L
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPD4Layers

theorem d4SwapLayerCatAll_E6 : D4SwapLayerCatAll .E6 := d4SwapLayerCatAll_of_leafSwap leafSwap_E6
theorem d4SwapLayerCatAll_E7 : D4SwapLayerCatAll .E7 := d4SwapLayerCatAll_of_leafSwap leafSwap_E7
theorem d4SwapLayerCatAll_E8 : D4SwapLayerCatAll .E8 := d4SwapLayerCatAll_of_leafSwap leafSwap_E8
theorem d4TrialityLayerCat_E6 : D4TrialityLayerCat .E6 :=
  d4TrialityLayerCat_of_leafCycle leafCycle_E6
theorem d4TrialityLayerCat_E7 : D4TrialityLayerCat .E7 :=
  d4TrialityLayerCat_of_leafCycle leafCycle_E7
theorem d4TrialityLayerCat_E8 : D4TrialityLayerCat .E8 :=
  d4TrialityLayerCat_of_leafCycle leafCycle_E8

end D4Tags

section D4Transport

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE6
  CFSG.RankThree.PartOne.KD4T CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.PartOne.KD4L CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints frobenius_canonicalRep
  D4TrialityLayer d4Nodes)

open CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPD4Layers

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem rootSpan_inf_model_cat_d4_of_layer (S : LangSetup τ L p)
    {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = Units.map (entrywiseHom Fr))
    {w : WeylGroup τ} (hn : S.D.n = canonicalRep (coxeterSystem τ) L w) (v : WeylGroup τ)
    {u : WeylGroup τ} (hu : u ∈ parabolicWeylGroup τ (d4Nodes τ)) {π : Equiv.Perm (Fin τ.rank)}
    (hlayer : ∀ (ℓ f : ℕ) [Fact ℓ.Prime] [CharP L ℓ], 1 ≤ f → S.D.q = ℓ ^ f →
      ∀ (n : ModGL τ L) (hn : n ∈ monomialSubgroup τ L), n ∈ adjointGroup τ L →
      (∃ u ∈ parabolicWeylGroup τ (d4Nodes τ), ∀ α ∈ parabolicRoots τ (d4Nodes τ),
        weylQuotientHom τ L ⟨n, hn⟩ • α = u • permLattice π α) →
      CatalogueOver ℓ (ℓ ^ f) ↥(rootSpan τ L (parabolicRoots τ (d4Nodes τ)) ⊓
          twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))))
    (hact : ∀ α ∈ parabolicRoots τ (d4Nodes τ),
      (v⁻¹ * w * v) • α = u • permLattice π α) :
    CatalogueOver (ringChar L) S.D.q
      ↥(rootSpan τ L ((fun α => v • α) '' parabolicRoots τ (d4Nodes τ)) ⊓ S.D.model) := by
  classical
  obtain ⟨ℓ, f, hℓ, hchar, hf, hq⟩ := S.exists_char_pow
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hring : ringChar L = ℓ := ringChar.eq L ℓ
  have hFr' : Fr = iterateFrobenius L ℓ f := by
    ext x
    rw [hFr, hq, iterateFrobenius_def]
  set nv := canonicalRep (coxeterSystem τ) L v with hnv
  set nw := canonicalRep (coxeterSystem τ) L w with hnw
  have hroots : ∀ α ∈ parabolicRoots τ (d4Nodes τ), IsRoot τ α := fun α hα => hα.1
  have hmodel : rootSpan τ L ((fun α => v • α) '' parabolicRoots τ (d4Nodes τ)) ⊓ S.D.model =
      rootSpan τ L ((fun α => v • α) '' parabolicRoots τ (d4Nodes τ)) ⊓
        twistedFixedPoints nw (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) := by
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
  rw [hmodel, rootSpan_inf_twistedFixedPoints_smul _ v nw hroots, hring, hq]
  have hnvM := canonicalRep_mem_monomialSubgroup L v
  have hnwM := canonicalRep_mem_monomialSubgroup L w
  have hn'M : nv⁻¹ * nw * nv ∈ monomialSubgroup τ L :=
    mul_mem (mul_mem (inv_mem hnvM) hnwM) hnvM
  have hn'C : nv⁻¹ * nw * nv ∈ adjointGroup τ L :=
    mul_mem (mul_mem (inv_mem (canonicalRep_mem_adjointGroup _ L v))
      (canonicalRep_mem_adjointGroup _ L w)) (canonicalRep_mem_adjointGroup _ L v)
  have hπ : weylQuotientHom τ L ⟨nv⁻¹ * nw * nv, hn'M⟩ = v⁻¹ * w * v := by
    have e : (⟨nv⁻¹ * nw * nv, hn'M⟩ : monomialSubgroup τ L) =
        (⟨nv, hnvM⟩ : monomialSubgroup τ L)⁻¹ * ⟨nw, hnwM⟩ * ⟨nv, hnvM⟩ := rfl
    rw [e, map_mul, map_mul, map_inv, weylQuotientHom_eq (mapsRootLines_canonicalRep v),
      weylQuotientHom_eq (mapsRootLines_canonicalRep w)]
  have hP := hlayer ℓ f hf hq (nv⁻¹ * nw * nv) hn'M hn'C
    ⟨u, hu, fun α hα => by rw [hπ]; exact hact α hα⟩
  exact catalogueOver_map_conj (MulAut.conj nv) hP

variable {Fr : L →+* L}

theorem rootSpan_inf_model_cat_d4_swap_all
    (hL : D4SwapLayerCatAll τ) (S : LangSetup τ L p)
    (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = Units.map (entrywiseHom Fr))
    {w : WeylGroup τ} (hn : S.D.n = canonicalRep (coxeterSystem τ) L w) (v : WeylGroup τ)
    {u : WeylGroup τ} (hu : u ∈ parabolicWeylGroup τ (d4Nodes τ)) {i j : Fin τ.rank}
    (hij : i ≠ j) (hi : i.val ∈ ({1, 2, 4} : Set ℕ)) (hj : j.val ∈ ({1, 2, 4} : Set ℕ))
    (hact : ∀ α ∈ parabolicRoots τ (d4Nodes τ),
      (v⁻¹ * w * v) • α = u • permLattice (Equiv.swap i j) α) :
    CatalogueOver (ringChar L) S.D.q
      ↥(rootSpan τ L ((fun α => v • α) '' parabolicRoots τ (d4Nodes τ)) ⊓ S.D.model) :=
  rootSpan_inf_model_cat_d4_of_layer S hFr hΦ hn v hu
    (fun ℓ f _ _ hf _ n hn hC hex => hL L ℓ f hf i j hij hi hj n hn hC hex _ rfl) hact

theorem rootSpan_inf_model_cat_d4 (hL : D4TrialityLayerCat τ) (S : LangSetup τ L p)
    (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = Units.map (entrywiseHom Fr))
    {w : WeylGroup τ} (hn : S.D.n = canonicalRep (coxeterSystem τ) L w) (v : WeylGroup τ)
    {u : WeylGroup τ} (hu : u ∈ parabolicWeylGroup τ (d4Nodes τ)) {a b c : Fin τ.rank}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (ha : a.val ∈ ({1, 2, 4} : Set ℕ))
    (hb : b.val ∈ ({1, 2, 4} : Set ℕ)) (hc : c.val ∈ ({1, 2, 4} : Set ℕ))
    (hact : ∀ α ∈ parabolicRoots τ (d4Nodes τ),
      (v⁻¹ * w * v) • α = u • permLattice (List.formPerm [a, b, c]) α) :
    CatalogueOver (ringChar L) S.D.q
      ↥(rootSpan τ L ((fun α => v • α) '' parabolicRoots τ (d4Nodes τ)) ⊓ S.D.model) :=
  rootSpan_inf_model_cat_d4_of_layer S hFr hΦ hn v hu
    (fun ℓ f _ _ hf _ n hn hC hex => hL L ℓ f hf a b c hab hbc hac ha hb hc n hn hC hex _ rfl)
    hact

end D4Transport

section D4Component

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE6
  CFSG.RankThree.PartOne.KD4T CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.PartOne.KD4L CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints frobenius_canonicalRep
  D4TrialityLayer d4Nodes)

open CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPD4Layers

variable
  {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem catalogueOver_rationalComponent_of_d4_outer_all [E6Sub τ] (hsearch : D4BaseSearch τ)
    (hL3 : D4TrialityLayer τ) (hL2 : D4SwapLayer τ) (hR3 : D4TrialityLayerCat τ)
    (hR2 : D4SwapLayerCatAll τ) (S : LangSetup τ L p) {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = Units.map (entrywiseHom Fr)) {w : WeylGroup τ}
    (hn : S.D.n = canonicalRep (coxeterSystem τ) L w) (hρw : ∀ γ, IsRoot τ γ → S.ρ γ = w • γ)
    {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a)) (v : WeylGroup τ)
    (hΨ : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots τ (d4Nodes τ))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (h1 : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    :
    CatalogueOver (ringChar L) S.D.q ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  set Ψ := componentRoots (rootCharHom a) i with hΨdef
  have hfin : Ψ.Finite := (finite_setOf_isRoot τ).subset fun γ hγ => hγ.1.1
  rw [componentOrbitLength_eq_one hfin hρ, Function.iterate_one] at h1
  have hw : ∀ γ ∈ Ψ, w • γ ∈ Ψ := fun γ hγ => by
    rw [← hρw γ hγ.1.1]
    exact hρ γ hγ
  have hmaps : MapsJ τ (d4Set τ) (v⁻¹ * w * v) := by
    intro α hα
    obtain ⟨β, hβ, hβe⟩ := (hΨ ▸ hw (v • α) (hΨ ▸ ⟨α, hα, rfl⟩) :
      w • v • α ∈ (fun α => v • α) '' parabolicRoots τ (d4Nodes τ))
    rw [mul_smul, mul_smul, ← hβe, inv_smul_smul]
    exact hβ
  obtain ⟨u, hu, w₀, hw₀, π, hπ, hw₀π⟩ := exists_d4_action hsearch hmaps
  have hlin0 : ∀ α ∈ parabolicRoots τ (d4Nodes τ), w₀ • α = permLattice π α := fun α hα => by
    have := smul_eq_of_simple (w := w₀) (u := 1) (π := π) (J := d4Set τ)
      (fun j hj => by rw [one_smul]; exact hw₀π j hj) hα.2
    rwa [one_smul] at this
  have hact : ∀ α ∈ parabolicRoots τ (d4Nodes τ),
      (v⁻¹ * w * v) • α = u • permLattice π α := fun α hα => by
    rw [hw₀, mul_smul, hlin0 α hα]
  have hπ1 : π ≠ 1 := by
    rintro rfl
    apply h1
    refine ⟨v * u * v⁻¹, hΨ ▸ conj_mem_closure_rootReflection v hu, ?_⟩
    rintro γ hγ
    obtain ⟨α, hα, rfl⟩ := (hΨ ▸ hγ : γ ∈ (fun α => v • α) '' parabolicRoots τ (d4Nodes τ))
    rw [hρw _ hγ.1.1]
    calc w • v • α = v • ((v⁻¹ * w * v) • α) := by
          rw [mul_smul, mul_smul, smul_inv_smul]
      _ = v • (u • α) := by
          rw [hact α hα]
          rfl
      _ = (v * u * v⁻¹) • v • α := by
          rw [mul_smul, mul_smul, inv_smul_smul]
  have h12 : e6Idx (τ := τ) 1 ≠ e6Idx 2 := e6Idx_ne (by decide)
  have h14 : e6Idx (τ := τ) 1 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have h24 : e6Idx (τ := τ) 2 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have hv1 : (e6Idx (τ := τ) 1).val ∈ ({1, 2, 4} : Set ℕ) := by
    rw [e6Idx_val']; exact Or.inl rfl
  have hv2 : (e6Idx (τ := τ) 2).val ∈ ({1, 2, 4} : Set ℕ) := by
    rw [e6Idx_val']; exact Or.inr (Or.inl rfl)
  have hv4 : (e6Idx (τ := τ) 4).val ∈ ({1, 2, 4} : Set ℕ) := by
    rw [e6Idx_val']; exact Or.inr (Or.inr rfl)
  have hlayer : CFSG.IsQuasisimple ↥(rootSpan τ L Ψ ⊓ S.D.model) ∧
      CatalogueOver (ringChar L) S.D.q ↥(rootSpan τ L Ψ ⊓ S.D.model) := by
    rw [hΨ]
    rcases hπ with rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hπ1
    · exact ⟨(rootSpan_inf_model_quasisimple_d4_swap hL2 S hFr hΦ hn v hu h12 hv1 hv2 hact).2,
        rootSpan_inf_model_cat_d4_swap_all hR2 S hFr hΦ hn v hu h12 hv1 hv2 hact⟩
    · exact ⟨(rootSpan_inf_model_quasisimple_d4_swap hL2 S hFr hΦ hn v hu h14 hv1 hv4 hact).2,
        rootSpan_inf_model_cat_d4_swap_all hR2 S hFr hΦ hn v hu h14 hv1 hv4 hact⟩
    · exact ⟨(rootSpan_inf_model_quasisimple_d4_swap hL2 S hFr hΦ hn v hu h24 hv2 hv4 hact).2,
        rootSpan_inf_model_cat_d4_swap_all hR2 S hFr hΦ hn v hu h24 hv2 hv4 hact⟩
    · exact ⟨(rootSpan_inf_model_quasisimple_d4 hL3 S hFr hΦ hn v hu h12 h24 h14 hv1 hv2 hv4
        hact).2, rootSpan_inf_model_cat_d4 hR3 S hFr hΦ hn v hu h12 h24
          h14 hv1 hv2 hv4 hact⟩
    · exact ⟨(rootSpan_inf_model_quasisimple_d4 hL3 S hFr hΦ hn v hu h14 h24.symm h12 hv1 hv4 hv2
        hact).2, rootSpan_inf_model_cat_d4 hR3 S hFr hΦ hn v hu h14
          h24.symm h12 hv1 hv4 hv2 hact⟩
  rw [rationalComponent_eq_of_layer S i hρ hlayer.1]
  exact hlayer.2

end D4Component

section D4TwLayers

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KD4L
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Yardstones.Md0ec50421ce4
  CFSG.RankThree.PartOne.KE6 CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPD4Layers
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix MatrixGroups

variable
  {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ]

theorem twisted_swap_layer_cat_all (hf : 1 ≤ f)
    {i j : Fin TwistTag.E6.tag.rank} (hij : i ≠ j) (hi : i.val = 1 ∨ i.val = 2 ∨ i.val = 4)
    (hj : j.val = 1 ∨ j.val = 2 ∨ j.val = 4)
    {n : ModGL TwistTag.E6.tag L} (hn : n ∈ monomialSubgroup TwistTag.E6.tag L)
    {u : WeylGroup TwistTag.E6.tag} (hu : u ∈ parabolicWeylGroup TwistTag.E6.tag (d4Nodes _))
    (hact : ∀ α ∈ parabolicRoots TwistTag.E6.tag (d4Nodes _),
      weylQuotientHom TwistTag.E6.tag L ⟨n, hn⟩ • permLattice TwistTag.E6.perm α =
        u • permLattice (Equiv.swap i j) α) :
    CatalogueOver ℓ (ℓ ^ f) ↥(rootSpan TwistTag.E6.tag L (parabolicRoots TwistTag.E6.tag (d4Nodes _)) ⊓
        twistedFixedPoints (n * diagramMap TwistTag.E6 L)
          (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) := by
  obtain ⟨hcases, hπ, hπ'⟩ := leafSwap_E6 i j hi hj hij
  have hact' : ∀ k ∈ d4Set TwistTag.E6.tag, weylQuotientHom TwistTag.E6.tag L ⟨n, hn⟩ •
      permLattice TwistTag.E6.perm (Pi.single k 1 : Fin TwistTag.E6.tag.rank → ℤ) =
        u • (Pi.single (Equiv.swap i j k) 1 : Fin TwistTag.E6.tag.rank → ℤ) := fun k hk => by
    have := hact _ (single_mem_parabolicRoots hk)
    rw [permLattice_single (Equiv.swap i j)] at this
    exact this
  obtain ⟨n₁, h, hh, hgen, hlang⟩ := exists_conj_twistedFixed_twist hf hn (fun x hx => hπ x hx)
    (fun x hx => hπ' x hx) hu hact'
  have hd4 : d4Nodes TwistTag.E6.tag = d4Set TwistTag.E6.tag := rfl
  rw [hd4, ← subsystemGroup_eq_rootSpan]
  rcases hcases with h1 | h2 | h3
  · obtain ⟨n₂, h₂, -, hRL⟩ := exists_fix_swap13_cat_all (L := L) (ℓ := ℓ) hf
    have hstd : StdSwap n₁ (Equiv.swap i j) (Equiv.swap 1 3) :=
      ⟨fun x hx => hπ x hx, fun x hx => hπ' x hx, h1, hgen⟩
    exact catalogueOver_layer_swap hstd h₂ hRL hh hlang rfl
  · obtain ⟨n₂, h₂, -, hRL⟩ := exists_fix_swap03_cat_all (L := L) (ℓ := ℓ) hf
    have hstd : StdSwap n₁ (Equiv.swap i j) (Equiv.swap 0 3) :=
      ⟨fun x hx => hπ x hx, fun x hx => hπ' x hx, h2, hgen⟩
    exact catalogueOver_layer_swap hstd h₂ hRL hh hlang rfl
  · obtain ⟨n₂, h₂, -, hRL⟩ := exists_fix_swap01_cat_all (L := L) (ℓ := ℓ) hf
    have hstd : StdSwap n₁ (Equiv.swap i j) (Equiv.swap 0 1) :=
      ⟨fun x hx => hπ x hx, fun x hx => hπ' x hx, h3, hgen⟩
    exact catalogueOver_layer_swap hstd h₂ hRL hh hlang rfl

theorem twisted_triality_layer_cat (hf : 1 ≤ f) {a b c : Fin TwistTag.E6.tag.rank}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (ha : a.val = 1 ∨ a.val = 2 ∨ a.val = 4)
    (hb : b.val = 1 ∨ b.val = 2 ∨ b.val = 4) (hc : c.val = 1 ∨ c.val = 2 ∨ c.val = 4)
    {n : ModGL TwistTag.E6.tag L} (hn : n ∈ monomialSubgroup TwistTag.E6.tag L)
    {u : WeylGroup TwistTag.E6.tag} (hu : u ∈ parabolicWeylGroup TwistTag.E6.tag (d4Nodes _))
    (hact : ∀ α ∈ parabolicRoots TwistTag.E6.tag (d4Nodes _),
      weylQuotientHom TwistTag.E6.tag L ⟨n, hn⟩ • permLattice TwistTag.E6.perm α =
        u • permLattice (List.formPerm [a, b, c]) α) :
    CatalogueOver ℓ (ℓ ^ f) ↥(rootSpan TwistTag.E6.tag L (parabolicRoots TwistTag.E6.tag (d4Nodes _)) ⊓
        twistedFixedPoints (n * diagramMap TwistTag.E6 L)
          (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) := by
  obtain ⟨hcyc, hπ, hπ'⟩ := leafCycle_E6 a b c ha hb hc hab hbc hac
  have hact' : ∀ j ∈ d4Set TwistTag.E6.tag, weylQuotientHom TwistTag.E6.tag L ⟨n, hn⟩ •
      permLattice TwistTag.E6.perm (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ) =
        u • (Pi.single (List.formPerm [a, b, c] j) 1 : Fin TwistTag.E6.tag.rank → ℤ) :=
    fun j hj => by
      have := hact _ (single_mem_parabolicRoots hj)
      rw [permLattice_single (List.formPerm [a, b, c])] at this
      exact this
  obtain ⟨n₁, h, hh, hgen, hlang⟩ := exists_conj_twistedFixed_twist hf hn (fun i hi => hπ i hi)
    (fun i hi => hπ' i hi) hu hact'
  have hd4 : d4Nodes TwistTag.E6.tag = d4Set TwistTag.E6.tag := rfl
  rw [hd4, ← subsystemGroup_eq_rootSpan]
  rcases hcyc with h1 | h2
  · have hstd : StdTwist n₁ (List.formPerm [a, b, c]) 1 :=
      ⟨Or.inl rfl, h1, fun i hi => hπ i hi, fun i hi => hπ' i hi, hgen⟩
    exact catalogueOver_layer_triality hf hstd hh hlang rfl
  · have hstd : StdTwist n₁ (List.formPerm [a, b, c]) 2 :=
      ⟨Or.inr rfl, h2, fun i hi => hπ i hi, fun i hi => hπ' i hi, hgen⟩
    exact catalogueOver_layer_triality hf hstd hh hlang rfl

end D4TwLayers

section D4TwComponent

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE6 CFSG.RankThree.PartOne.KD4T CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints frobenius_canonicalRep
  d4Nodes)

open CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPD4Layers

theorem catalogueOver_rationalComponent_of_d4_twE6_of_layer {L : Type} [Field L] [IsAlgClosed L]
    {p : ℕ} (S : LangSetup .E6 L p)
    (hS : ∃ (t : TwistTag) (h : t.tag = .E6) (Fr : L →+* L), (∀ c, Fr c = c ^ S.D.q) ∧
      ∀ g, S.D.Φ g = diagramAt .E6 L t h * Units.map (entrywiseHom Fr) g *
        (diagramAt .E6 L t h)⁻¹)
    {a : Fin Tag.E6.rank → Lˣ} (i : KernelComponent (rootCharHom a)) (v : WeylGroup .E6)
    (hΨ : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots .E6 (d4Nodes .E6))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (hnin : ¬ twistInner (componentRoots (rootCharHom a) i) (S.ρ : (Fin Tag.E6.rank → ℤ) → _))
    (hlay : ∀ (ℓ f : ℕ) [Fact ℓ.Prime] [CharP L ℓ], 1 ≤ f → S.D.q = ℓ ^ f →
      ∀ (n : ModGL Tag.E6 L) (hn : n ∈ monomialSubgroup Tag.E6 L) (u : WeylGroup Tag.E6),
      u ∈ parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6) → ∀ π : Equiv.Perm (Fin Tag.E6.rank),
      IsD4LeafPerm π → π ≠ 1 →
      (¬ twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2]) → π * π ≠ 1) →
      (∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
        weylQuotientHom Tag.E6 L ⟨n, hn⟩ • permLattice e6Graph α = u • permLattice π α) →
      CFSG.IsQuasisimple ↥(rootSpan Tag.E6 L (parabolicRoots Tag.E6 (d4Nodes Tag.E6)) ⊓
        twistedFixedPoints (n * e6Diagram L) (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) ∧
      CatalogueOver ℓ (ℓ ^ f) ↥(rootSpan Tag.E6 L (parabolicRoots Tag.E6 (d4Nodes Tag.E6)) ⊓
        twistedFixedPoints (n * e6Diagram L) (Units.map (entrywiseHom (iterateFrobenius L ℓ f))))) :
    CatalogueOver (ringChar L) S.D.q ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  obtain ⟨t, ht, Fr, hFr, hΦ⟩ := hS
  cases t with
  | D4 => exact absurd ht (by decide)
  | E6 =>
  classical
  have hΦ' : ∀ g, S.D.Φ g = e6Diagram L * Units.map (entrywiseHom Fr) g * (e6Diagram L)⁻¹ := hΦ
  obtain ⟨w, hn⟩ := S.D.n_weyl
  obtain ⟨ℓ, f, hℓ, hchar, hf, hq⟩ := S.exists_char_pow
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hFr' : Fr = iterateFrobenius L ℓ f := by
    ext x
    rw [hFr, hq, iterateFrobenius_def]
  have hq0 : 0 < S.D.q := by
    rw [hq]
    exact pow_pos hℓ.pos f
  have hFrs : Function.Surjective Fr := fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y hq0
    exact ⟨x, by rw [hFr, hx]⟩
  have hρw : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = w • permLattice e6Graph γ := by
    intro γ hγ
    have hst : S.D.step = twFrob TwistTag.E6 (canonicalRep (coxeterSystem TwistTag.E6.tag) L w)
        Fr := by
      ext1 g
      change S.D.n * S.D.Φ g * S.D.n⁻¹ = canonicalRep (coxeterSystem Tag.E6) L w *
        (e6Diagram L * Units.map (entrywiseHom Fr) g * (e6Diagram L)⁻¹) *
          (canonicalRep (coxeterSystem Tag.E6) L w)⁻¹
      rw [hΦ', hn]
    have h2 := map_twFrob_rootSubgroup TwistTag.E6 hFrs w hγ
    have h3 : rootSubgroup Tag.E6 L (S.ρ γ) =
        rootSubgroup Tag.E6 L (w • permLattice e6Graph γ) := by
      rw [← S.frob.map_rootSubgroup γ hγ, hst]
      exact h2
    have hr : IsRoot Tag.E6 (w • permLattice e6Graph γ) :=
      IsRoot.smul (hγ.permLattice e6Graph_cartan) w
    exact eq_of_rootSubgroup_eq ((S.frob.isRoot_iff γ).2 hγ) hr h3
  have hσσ : ∀ x : Fin Tag.E6.rank → ℤ, permLattice e6Graph (permLattice e6Graph x) = x :=
    fun x => by
      rw [← permLattice_mul, e6Graph_mul_self]
      rfl
  have hσpar : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      permLattice e6Graph α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6) := by
    intro α hα
    refine ⟨hα.1.permLattice e6Graph_cartan, fun k hk => ?_⟩
    exact hα.2 _ ((e6Graph_on_d4 k).2 hk).1
  set w' : WeylGroup Tag.E6 := v⁻¹ * w * e6WeylTwist v with hw'
  have hθ : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      v⁻¹ • S.ρ (v • α) = w' • permLattice e6Graph α := by
    intro α hα
    rw [hρw _ ((isRoot_smul_iff v).2 hα.1), ← e6WeylTwist_smul v α, hw', mul_smul, mul_smul]
  have hθmem : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      v⁻¹ • S.ρ (v • α) ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6) := by
    intro α hα
    have hmemΨ : v • α ∈ componentRoots (rootCharHom a) i := by
      rw [hΨ]
      exact ⟨α, hα, rfl⟩
    have h2 := hρ _ hmemΨ
    rw [hΨ] at h2
    obtain ⟨β, hβ, hβe⟩ := h2
    rw [← hβe, inv_smul_smul]
    exact hβ
  have hmaps : MapsJ Tag.E6 (d4Set Tag.E6) w' := by
    intro α hα
    have h1 := hθ (permLattice e6Graph α) (hσpar α hα)
    rw [hσσ] at h1
    rw [← h1]
    exact hθmem _ (hσpar α hα)
  obtain ⟨u, hu, w₀, hw₀, π', hπ', hw₀π⟩ := exists_d4_action d4Base_E6 hmaps
  set πJ : Equiv.Perm (Fin Tag.E6.rank) := π' * Equiv.swap (e6Idx 2) (e6Idx 4) with hπJ
  have hπJleaf : IsD4LeafPerm πJ := isD4LeafPerm_mul_swap hπ'
  have hlin : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      w₀ • permLattice e6Graph α = permLattice πJ α := by
    intro α hα
    have h1 := smul_eq_of_simple (w := w₀) (u := 1) (π := π') (J := d4Set Tag.E6)
      (fun j hj => by rw [one_smul]; exact hw₀π j hj) (hσpar α hα).2
    rw [one_smul] at h1
    rw [h1, hπJ, permLattice_mul]
    congr 1
    funext k
    simp only [permLattice, Function.comp]
    by_cases hk : 1 ≤ k.val ∧ k.val ≤ 4
    · rw [((e6Graph_on_d4 k).1 hk).2.1]
    · rw [hα.2 _ ((e6Graph_on_d4 k).2 hk).1, hα.2 _ ((e6Graph_on_d4 k).2 hk).2]
  have hθ' : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      v⁻¹ • S.ρ (v • α) = u • permLattice πJ α := by
    intro α hα
    rw [hθ α hα, hw₀, mul_smul, hlin α hα]
  have huJ := mapsJ_of_mem_parabolicWeylGroup hu
  have hπJpar : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      permLattice πJ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6) := by
    intro α hα
    have h1 := hθmem α hα
    rw [hθ' α hα] at h1
    have h2 := (mapsJ_of_mem_parabolicWeylGroup (inv_mem hu)) _ h1
    rwa [inv_smul_smul] at h2
  have hπ1 : πJ ≠ 1 := by
    intro h1
    apply hnin
    refine ⟨v * u * v⁻¹, hΨ ▸ conj_mem_closure_rootReflection v hu, ?_⟩
    rintro γ hγ
    obtain ⟨α, hα, rfl⟩ :=
      (hΨ ▸ hγ : γ ∈ (fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6))
    have h := hθ' α hα
    rw [h1] at h
    calc S.ρ (v • α) = v • (v⁻¹ • S.ρ (v • α)) := (smul_inv_smul v _).symm
      _ = v • (u • α) := by rw [h]; rfl
      _ = (v * u * v⁻¹) • v • α := by rw [mul_smul, mul_smul, inv_smul_smul]
  have hπ2 : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2]) → πJ * πJ ≠ 1 := by
    intro hnin2 h2
    apply hnin2
    have hδu : e6WeylTwist u ∈ parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6) := by
      have hle : (parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6)).map e6WeylTwist.toMonoidHom ≤
          parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6) := by
        rw [parabolicWeylGroup, MonoidHom.map_closure, Subgroup.closure_le]
        rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
        refine Subgroup.subset_closure ⟨e6Graph j, ((e6Graph_on_d4 j).1 hj).2.2, ?_⟩
        exact (e6WeylTwist_simple j).symm
      exact hle ⟨u, hu, rfl⟩
    have hconj : w₀ * e6WeylTwist u * w₀⁻¹ ∈ parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6) := by
      have hle : (parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6)).map (MulAut.conj w₀).toMonoidHom ≤
          parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6) := by
        rw [parabolicWeylGroup, MonoidHom.map_closure, Subgroup.closure_le]
        rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
        refine Subgroup.subset_closure ⟨π' j, hπ'.mem_d4Set hj, ?_⟩
        change simple Tag.E6 (π' j) = w₀ * simple Tag.E6 j * w₀⁻¹
        rw [← rootReflection_single, ← rootReflection_eq_conj (hw₀π j hj)]
      exact hle ⟨e6WeylTwist u, hδu, rfl⟩
    obtain ⟨u₂, hu₂⟩ : ∃ x, x = u * (w₀ * e6WeylTwist u * w₀⁻¹) := ⟨_, rfl⟩
    refine ⟨v * u₂ * v⁻¹, hΨ ▸ conj_mem_closure_rootReflection v (hu₂ ▸ mul_mem hu hconj), ?_⟩
    rintro γ hγ
    obtain ⟨α, hα, rfl⟩ :=
      (hΨ ▸ hγ : γ ∈ (fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6))
    have hpx : ∀ x ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6), permLattice πJ (u • x) =
        (w₀ * e6WeylTwist u * w₀⁻¹) • permLattice πJ x := by
      intro x hx
      rw [← hlin _ (huJ x hx), ← hlin x hx, ← e6WeylTwist_smul u x, mul_smul, mul_smul,
        inv_smul_smul]
    set β := u • permLattice πJ α with hβ
    have hβJ : β ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6) := by
      rw [hβ, ← hθ' α hα]
      exact hθmem α hα
    have e1 : S.ρ (v • α) = v • β := by
      rw [hβ, ← hθ' α hα, smul_inv_smul]
    have e2 : S.ρ (v • β) = v • (u • permLattice πJ β) := by
      rw [← hθ' β hβJ, smul_inv_smul]
    have e3 : permLattice πJ (permLattice πJ α) = α := by
      rw [← permLattice_mul, h2]
      rfl
    calc (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2] (v • α) = S.ρ (S.ρ (v • α)) := rfl
      _ = v • (u • permLattice πJ β) := by rw [e1, e2]
      _ = v • (u₂ • α) := by
          rw [hβ, hpx _ (hπJpar α hα), e3, hu₂, mul_smul u (w₀ * e6WeylTwist u * w₀⁻¹) α]
      _ = (v * u₂ * v⁻¹) • v • α := by simp only [mul_smul, inv_smul_smul]
  have hroots : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6), IsRoot Tag.E6 α := fun α hα => hα.1
  set nv := canonicalRep (coxeterSystem Tag.E6) L v with hnv
  set nw := canonicalRep (coxeterSystem Tag.E6) L w with hnw
  set nδ := canonicalRep (coxeterSystem Tag.E6) L (e6WeylTwist v) with hnδ
  have hnvM := canonicalRep_mem_monomialSubgroup L v
  have hnwM := canonicalRep_mem_monomialSubgroup L w
  have hnδM := canonicalRep_mem_monomialSubgroup L (e6WeylTwist v)
  have hn'M : nv⁻¹ * nw * nδ ∈ monomialSubgroup Tag.E6 L :=
    mul_mem (mul_mem (inv_mem hnvM) hnwM) hnδM
  have hπn' : weylQuotientHom Tag.E6 L ⟨nv⁻¹ * nw * nδ, hn'M⟩ = w' := by
    have e : (⟨nv⁻¹ * nw * nδ, hn'M⟩ : monomialSubgroup Tag.E6 L) =
        (⟨nv, hnvM⟩ : monomialSubgroup Tag.E6 L)⁻¹ * ⟨nw, hnwM⟩ * ⟨nδ, hnδM⟩ := rfl
    rw [e, map_mul, map_mul, map_inv, weylQuotientHom_eq (mapsRootLines_canonicalRep v),
      weylQuotientHom_eq (mapsRootLines_canonicalRep w),
      weylQuotientHom_eq (mapsRootLines_canonicalRep (e6WeylTwist v))]
  have hnPv : nv⁻¹ * (nw * e6Diagram L) * nv = (nv⁻¹ * nw * nδ) * e6Diagram L := by
    have h := e6Diagram_conj_canonicalRep Fr v
    calc nv⁻¹ * (nw * e6Diagram L) * nv =
        nv⁻¹ * nw * (e6Diagram L * nv * (e6Diagram L)⁻¹) * e6Diagram L := by group
      _ = (nv⁻¹ * nw * nδ) * e6Diagram L := by rw [h]
  have hact : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      weylQuotientHom Tag.E6 L ⟨nv⁻¹ * nw * nδ, hn'M⟩ • permLattice e6Graph α =
        u • permLattice πJ α := by
    intro α hα
    rw [hπn', hw₀, mul_smul, hlin α hα]
  have hlayer := hlay ℓ f hf hq _ hn'M u hu πJ hπJleaf hπ1 hπ2 hact
  have hmodel : rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ⊓ S.D.model =
      rootSpan Tag.E6 L ((fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6)) ⊓
        twistedFixedPoints (nw * e6Diagram L)
          (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) := by
    rw [hΨ]
    ext x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hx, -, hxF⟩
      refine ⟨hx, ?_⟩
      have hxF' : S.D.n * S.D.Φ x * S.D.n⁻¹ = x := hxF
      rw [hn, hΦ', hFr'] at hxF'
      change (nw * e6Diagram L) * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x *
        (nw * e6Diagram L)⁻¹ = x
      calc (nw * e6Diagram L) * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x *
            (nw * e6Diagram L)⁻¹ = nw * (e6Diagram L *
              Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x * (e6Diagram L)⁻¹) * nw⁻¹ := by
            group
        _ = x := hxF'
    · rintro ⟨hx, hxF⟩
      refine ⟨hx, rootSpan_le_adjointGroup L _ hx, ?_⟩
      have hxF' : (nw * e6Diagram L) * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x *
          (nw * e6Diagram L)⁻¹ = x := hxF
      change S.D.n * S.D.Φ x * S.D.n⁻¹ = x
      rw [hn, hΦ', hFr']
      calc nw * (e6Diagram L * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x *
            (e6Diagram L)⁻¹) * nw⁻¹ = (nw * e6Diagram L) *
              Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x * (nw * e6Diagram L)⁻¹ := by
            group
        _ = x := hxF'
  have hqs : CFSG.IsQuasisimple
        ↥(rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ⊓ S.D.model) ∧
      CatalogueOver ℓ (ℓ ^ f) ↥(rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ⊓ S.D.model) := by
    rw [hmodel, rootSpan_inf_twistedFixedPoints_smul _ v (nw * e6Diagram L) hroots, ← hnv, hnPv]
    set Q := rootSpan Tag.E6 L (parabolicRoots Tag.E6 (d4Nodes Tag.E6)) ⊓
      twistedFixedPoints ((nv⁻¹ * nw * nδ) * e6Diagram L)
        (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))
    have e : Q ≃* Q.map (MulAut.conj nv).toMonoidHom :=
      Q.equivMapOfInjective _ (MulAut.conj nv).injective
    exact ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e hlayer.1,
      catalogueOver_map_conj (MulAut.conj nv) hlayer.2⟩
  rw [rationalComponent_eq_of_layer S i hρ hqs.1, ringChar.eq L ℓ, hq]
  exact hqs.2

end D4TwComponent

section D4Rank4

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KD4L
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Yardstones.Md0ec50421ce4
  CFSG.RankThree.PartOne.KE6 CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPD4Layers
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.ComponentClassification.CatLeafProof
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix MatrixGroups

theorem catalogueOver_of_rank_four_all {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup τ L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hTp : rootDiagUnit τ a ^ p = 1)
    (ha1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hr : compRank (componentRoots (rootCharHom a) i) = 4)
    (hc : (componentRoots (rootCharHom a) i).ncard = 24)
    (hnin : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    :
    CatalogueOver (ringChar L) S.D.q ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  have hE6 := e6FixDNAll_proved
  cases τ with
  | G2 =>
    have hle := compRank_le_rank (componentRoots (rootCharHom a) i)
    rw [hr] at hle
    exact absurd hle (by decide)
  | F4 =>
    obtain ⟨v, μ, -, hpinned⟩ := S.exists_pinnedT_of_prime hp hpL facts_F4 hTp
    obtain ⟨x, C, -, -, -, hr', hc'⟩ := hpinned i
    exact absurd (hc' ▸ hc) (kacCount_F4_four C (hr' ▸ hr))
  | D4 => exact absurd (rootDiagUnit_eq_one_of_ncard i (by rw [hc]; rfl)) ha1
  | E6 =>
    obtain ⟨v, hv, hρ⟩ := S.d4_pinnedT_of_prime hp hpL facts_E6 kacCount_E6_four (by decide)
      (by decide)
      (fun y hy => far_d4_E6 y fun z hz => by
        have h := hy z hz
        rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
      ⟨none, by decide⟩ (lt_of_eq_of_lt kacCount_far_E6 (by decide)) hT hTp i hr hc
    have hfin : (componentRoots (rootCharHom a) i).Finite :=
      (finite_setOf_isRoot _).subset fun γ hγ => hγ.1.1
    have hs := componentOrbitLength_eq_one hfin hρ
    obtain ⟨w, hn⟩ := S.D.n_weyl
    obtain ⟨Fr, hFr, P, hP, hΦ⟩ := S.D.steinberg
    rcases hP with rfl | ⟨t, ht, rfl⟩
    · have hΦ' : S.D.Φ = Units.map (entrywiseHom Fr) := by
        ext1 g
        rw [hΦ, one_mul, inv_one, mul_one]
      exact catalogueOver_rationalComponent_of_d4_outer_all d4Base_E6
        d4TrialityLayer_E6 (d4SwapLayer_E6 hE6) d4TrialityLayerCat_E6
        d4SwapLayerCatAll_E6 S hFr hΦ' hn
        (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ' hn hγ) i v hv hρ hnin
    · rw [hs, Function.iterate_one] at hnin
      refine catalogueOver_rationalComponent_of_d4_twE6_of_layer S ⟨t, ht, Fr, hFr, hΦ⟩ i v hv
        hρ hnin (fun ℓ f _ _ hf hqf n hn u hu π hleaf hπ1 _ hact => ?_)
      have h12 : e6Idx (τ := Tag.E6) 1 ≠ e6Idx 2 := e6Idx_ne (by decide)
      have h14 : e6Idx (τ := Tag.E6) 1 ≠ e6Idx 4 := e6Idx_ne (by decide)
      have h24 : e6Idx (τ := Tag.E6) 2 ≠ e6Idx 4 := e6Idx_ne (by decide)
      have hv1 : (e6Idx (τ := Tag.E6) 1).val = 1 ∨ (e6Idx (τ := Tag.E6) 1).val = 2 ∨
          (e6Idx (τ := Tag.E6) 1).val = 4 := Or.inl rfl
      have hv2 : (e6Idx (τ := Tag.E6) 2).val = 1 ∨ (e6Idx (τ := Tag.E6) 2).val = 2 ∨
          (e6Idx (τ := Tag.E6) 2).val = 4 := Or.inr (Or.inl rfl)
      have hv4 : (e6Idx (τ := Tag.E6) 4).val = 1 ∨ (e6Idx (τ := Tag.E6) 4).val = 2 ∨
          (e6Idx (τ := Tag.E6) 4).val = 4 := Or.inr (Or.inr rfl)
      rcases hleaf with hc | hc | hc | hc | hc | hc
      · exact absurd hc hπ1
      · rw [hc] at hact
        exact ⟨(twisted_swap_layer_E6 hE6 hf h12 hv1 hv2 hn hu hact).2,
          twisted_swap_layer_cat_all hf h12 hv1 hv2 hn hu hact⟩
      · rw [hc] at hact
        exact ⟨(twisted_swap_layer_E6 hE6 hf h14 hv1 hv4 hn hu hact).2,
          twisted_swap_layer_cat_all hf h14 hv1 hv4 hn hu hact⟩
      · rw [hc] at hact
        exact ⟨(twisted_swap_layer_E6 hE6 hf h24 hv2 hv4 hn hu hact).2,
          twisted_swap_layer_cat_all hf h24 hv2 hv4 hn hu hact⟩
      · rw [hc] at hact
        exact ⟨(twisted_triality_layer_E6 hf h12 h24 h14 hv1 hv2 hv4 hn hu hact).2,
          twisted_triality_layer_cat hf h12 h24 h14 hv1 hv2 hv4 hn hu hact⟩
      · rw [hc] at hact
        exact ⟨(twisted_triality_layer_E6 hf h14 h24.symm h12 hv1 hv4 hv2 hn hu hact).2,
          twisted_triality_layer_cat hf h14 h24.symm h12 hv1 hv4 hv2 hn hu hact⟩
  | E7 =>
    obtain ⟨v, hv, hρ⟩ := S.d4_pinnedT_of_prime hp hpL facts_E7 kacCount_E7_four (by decide)
      (by decide)
      (fun y hy => far_d4_E7 y fun z hz => by
        have h := hy z hz
        rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
      ⟨some 0, by decide⟩ (lt_of_eq_of_lt kacCount_far_E7 (by decide)) hT hTp i hr hc
    obtain ⟨Fr, hFr, hΦ⟩ := S.D.exists_frob_of_untwisted twistTag_tag_ne_E7
    obtain ⟨w, hn⟩ := S.D.n_weyl
    exact catalogueOver_rationalComponent_of_d4_outer_all d4Base_E7
      CFSG.RankThree.PartOne.KD4L.d4TrialityLayer_E7 (d4SwapLayer_E7 hE6)
      d4TrialityLayerCat_E7 d4SwapLayerCatAll_E7 S hFr hΦ hn
      (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ hn hγ) i v hv hρ hnin
  | E8 =>
    obtain ⟨v, hv, hρ⟩ := S.d4_pinnedT_of_prime hp hpL facts_E8 kacCount_E8_four (by decide)
      (by decide)
      (fun y hy => far_d4_E8 y fun z hz => by
        have h := hy z hz
        rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
      ⟨some 0, by decide⟩ (lt_of_eq_of_lt kacCount_far_E8 (by decide)) hT hTp i hr hc
    obtain ⟨Fr, hFr, hΦ⟩ := S.D.exists_frob_of_untwisted twistTag_tag_ne_E8
    obtain ⟨w, hn⟩ := S.D.n_weyl
    exact catalogueOver_rationalComponent_of_d4_outer_all d4Base_E8
      CFSG.RankThree.PartOne.KD4L.d4TrialityLayer_E8 (d4SwapLayer_E8 hE6)
      d4TrialityLayerCat_E8 d4SwapLayerCatAll_E8 S hFr hΦ hn
      (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ hn hγ) i v hv hρ hnin

theorem ratCat_of_rank_four_all {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup τ L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hTp : rootDiagUnit τ a ^ p = 1)
    (ha1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hr : compRank (componentRoots (rootCharHom a) i) = 4)
    (hc : (componentRoots (rootCharHom a) i).ncard = 24)
    (hnin : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    RationalCatalogue S i :=
  ⟨1, le_rfl, by
    rw [pow_one]
    exact catalogueOver_of_rank_four_all S hp hpL hT hTp ha1 i hr hc hnin⟩

theorem ratCat_of_outerD_all {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {p : ℕ} (hp : p.Prime) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hshape : 4 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard =
        2 * compRank (componentRoots (rootCharHom a) i) *
          (compRank (componentRoots (rootCharHom a) i) - 1))
    (hout : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    RationalCatalogue S i := by
  by_cases h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i)
  · exact ratCat_of_twoD_highG hp S hT hap h1 i h5 hshape.2 hout (fun _ _ => True)
      (fun r _ _ e m he hm5 _ => CompsPTwoDChainO.twoDChainRecog_all he (by omega)) trivial
  · have hr4 : compRank (componentRoots (rootCharHom a) i) = 4 := by omega
    have hc : (componentRoots (rootCharHom a) i).ncard = 24 := by
      rw [hshape.2, hr4]
    have hℓp : ringChar L ≠ p := ringChar_ne_of_pow_eq_one hp hap h1
    have hpL : ((p : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hp hℓp
    have hTp := rootDiagUnit_pow_eq_one_of_forall hap
    exact ratCat_of_rank_four_all S hp hpL hT hTp h1 i hr4 hc hout

theorem excUntwOuterDCatalogue_holds : ExcUntwOuterDCatalogue := by
  intro τ _ L _ _ p₀ S _ p hp _ a hT hap h1 i hshape hout _
  exact ratCat_of_outerD_all S hp hT hap h1 i hshape hout

theorem ratCat_E6_all {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup Tag.E6 L p₀)
    {p : ℕ} (hp : p.Prime) {a : Fin Tag.E6.rank → Lˣ}
    (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1)
    (h1 : rootDiagUnit Tag.E6 a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hq : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    RationalCatalogue S i := by
  classical
  have hℓp : ringChar L ≠ p := ringChar_ne_of_pow_eq_one hp hap h1
  have hpL : ((p : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hp hℓp
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  by_cases hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)
  · exact ⟨_, (outer_componentOrbitLength_spec S hT i).1,
      catalogueOver_rationalComponent_typeA S hp hT hap h1 i hA hq⟩
  by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])
  · exact ratCat_of_inner_nonA_E6 S hp hpL hT hTp i hA hinner
  · obtain ⟨v, μ, x, c, -, hc, -, hlen, hroots, hrank, hncard⟩ :=
      exists_cand_of_class kacE6 facts_E6 e6_tree e6_adj e6_check e6_lt e6_card S hp hpL hTp i
    have hshape := e6_shape c hc hlen
    rw [← hncard, ← hrank] at hshape
    rcases hshape with hA' | hD' | hE'
    · exact (hA hA').elim
    · exact ratCat_of_outerD_all S hp hT hap h1 i hD' hinner
    · exact (false_of_e6Class_E S hp hpL hTp h1 i hE'.1 hE'.2).elim

end D4Rank4

end ExcUntw

section Main2

open ExcUntw

theorem lieCompIdx_excUntwisted :
    LieCompIdx isExcUntwistedIdx :=
  lieCompIdx_excUntwisted_of_rationalCatalogue
    (excUntwRationalCatalogue_of_outer excUntwOuterDCatalogue_holds excUntwOuterECatalogue_holds)

theorem twistedE6RationalCatalogue_holds :
    TwistedE6RationalCatalogue := by
  intro L _ _ p₀ S _ p hp _ a hT hap h1 i hq
  exact ratCat_E6_all S hp hT hap h1 i hq

theorem lieCompIdx_excTwisted :
    LieCompIdx isExcTwistedIdx :=
  lieCompIdx_excTwisted_of_rational twistedE6RationalCatalogue_holds

end Main2

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
