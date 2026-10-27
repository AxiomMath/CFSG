module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.ClassicalBridge
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Inner
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExcE6
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Basic

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Minuscule MinData.Valid CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Isogeny CFSG.LieType.CurtisTits
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.CatLeafProof TauCeti CFSG.Yardstones.Md0ec50421ce4
  CFSG.Adapters.RankTwoModelTransports

set_option linter.unusedSectionVars false


theorem lieModel_twistedE6_fixed {k : Type} [Field k] [Finite k] (θ : k →+* k)
    (hθ : ∀ c, θ (θ c) = c) {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 0 < f)
    (hk : Nat.card k = (ℓ ^ f) ^ 2) (hθq : ∀ c, θ c = c ^ ℓ ^ f) :
    LieModel (↥(fixedGroup k θ) ⧸ Subgroup.center ↥(fixedGroup k θ)) .twistedE6 0 ℓ f := by
  have hk4 : 4 ≤ Nat.card k := by
    rw [hk]
    have h2 : 2 ≤ ℓ ^ f := le_trans hℓ.two_le (Nat.le_self_pow (by omega) ℓ)
    nlinarith
  have hq := fixedGroup_isQuasisimple_of_four_le_card θ hθ hk4
  have hrange := range_e6IsogenyFixed θ hθ hk4
  let φ : ↥(fixedGroup k θ) →*
      ↥⁅twistedFixedGroup .E6 k θ, twistedFixedGroup .E6 k θ⁆ :=
    (e6IsogenyFixed θ).codRestrict _ fun g => by
      rw [← hrange]
      exact ⟨g, rfl⟩
  have hφ : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    rw [← hrange] at hy
    obtain ⟨g, rfl⟩ := hy
    exact ⟨g, rfl⟩
  have hφ1 : ∃ g, φ g ≠ 1 := by
    set i : Fin (Tag.rank .E6) := ⟨1, by decide⟩
    have hfix : e6Data_valid.xm k (Pi.single i 1) 1 ∈ fixedGroup k θ := by
      rw [mem_fixedGroup, sigma_xm_single, map_one]
      rfl
    refine ⟨⟨_, hfix⟩, fun h => ?_⟩
    have h' := congrArg (fun y : ↥⁅twistedFixedGroup .E6 k θ, twistedFixedGroup .E6 k θ⁆ =>
      (y : ModGL TwistTag.E6.tag k)) h
    simp only [OneMemClass.coe_one] at h'
    exact e6Isogeny_xm_single_one_ne_one k i (Subtype.ext h')
  have hadm : StatedLieAdmissible .twistedE6 0 ℓ f := ⟨hℓ, hf, rfl⟩
  exact Or.inr (Or.inl ⟨rfl, by decide, hadm,
    twistedChevalleyModel_of_surjective hq (t := TwistTag.E6) hk θ hθq φ hφ hφ1
      (MulEquiv.refl _)⟩)


theorem lieModel_twistedE6_chev {G : Type} [Group G] {p f : ℕ} (h : LieModel G .twistedE6 0 p f) :
    IsChevSimple p G ∧ IsEmpty (G ≃* alternatingGroup (Fin 6)) := by
  have hadm := h.admissible
  have hp : p.Prime := hadm.1
  have hf : 0 < f := hadm.2.1
  refine ⟨?_, isEmpty_alt6_of_lieModel_gen h (by simp [lieSylowExponent]; omega)⟩
  rcases h with ⟨ht, -⟩ | ⟨-, -, hmod⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · simp [classicalTags] at ht
  · obtain ⟨-, K, _, _, hK, σ, hσ, ⟨e⟩⟩ := hmod
    let q : PrimePower := ⟨p, f, hp, hf⟩
    have hv := LieTypeIndex.valid_twistedE6 q
    obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.twistedE6 q hv K
      (by rw [hK, PrimePower.card_def]) σ (fun x => by rw [hσ, PrimePower.card_def])
    exact isChevSimple_of_lie ⟨.twistedE6 q, hv⟩ (LieTypeIndex.characteristic_twistedE6 q)
      (e.trans b)
  · simp [reeTitsTags] at ht
  · exact absurd ht (by decide)


section Layer

open CFSG.RankThree.PartOne.KE6 CFSG.RankThree.PartOne.KD4T
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints frobenius_canonicalRep)


theorem rationalComponent_eq_of_layer {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a))
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

theorem conj_parabolicWeyl_mem_closure {τ : Tag} (v : WeylGroup τ) {J : Set (Fin τ.rank)}
    {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : Ψ = (fun α => v • α) '' parabolicRoots τ J)
    {u : WeylGroup τ} (hu : u ∈ parabolicWeylGroup τ J) :
    v * u * v⁻¹ ∈ Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ Ψ, s = rootReflection γ} := by
  have hu' : u ∈ Subgroup.closure (simple τ '' J) := hu
  clear hu
  induction hu' using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    apply Subgroup.subset_closure
    refine ⟨v • (Pi.single j 1 : Fin τ.rank → ℤ), ?_, ?_⟩
    · rw [hΨ]
      exact ⟨Pi.single j 1, ⟨isRoot_single τ j, fun k hk => by
        have hjk : k ≠ j := fun h => hk (by rw [h]; exact hj)
        simp [Pi.single_apply, hjk]⟩, rfl⟩
    · rw [rootReflection_smul_root v (isRoot_single τ j)]
      have : rootReflection (Pi.single j 1 : Fin τ.rank → ℤ) = simple τ j := by
        have := rootReflection_eq_conj (w := 1) (j := j)
          (by rw [one_smul] : (1 : WeylGroup τ) • (Pi.single j 1 : Fin τ.rank → ℤ) =
            Pi.single j 1)
        simpa using this
      rw [this]
  | one => simpa using one_mem _
  | mul x y _ _ hx hy =>
    have : v * (x * y) * v⁻¹ = (v * x * v⁻¹) * (v * y * v⁻¹) := by group
    rw [this]
    exact mul_mem hx hy
  | inv x _ hx =>
    have : v * x⁻¹ * v⁻¹ = (v * x * v⁻¹)⁻¹ := by group
    rw [this]
    exact inv_mem hx

theorem rationalLieType_of_e6_outer {τ : Tag} [hτ : M27Ok τ] [E6Sub τ] {L : Type} [Field L]
    [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ}
    (haT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a)) (v : WeylGroup τ)
    (hΨ : componentRoots (rootCharHom a) i =
      (fun α => v • α) '' parabolicRoots τ (e6Nodes τ))
    (hout : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    RationalLieType (ringChar L) (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
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
  rw [hR]
  have hqiso : ↥(rootSpan τ L Ψ ⊓ S.D.model) ⧸ Subgroup.center ↥(rootSpan τ L Ψ ⊓ S.D.model) ≃*
      ↥(fixedGroup (K2 L ℓ f) (theta2 L ℓ f)) ⧸
        Subgroup.center ↥(fixedGroup (K2 L ℓ f) (theta2 L ℓ f)) :=
    QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
  have hlie : LieModel (↥(rootSpan τ L Ψ ⊓ S.D.model) ⧸
      Subgroup.center ↥(rootSpan τ L Ψ ⊓ S.D.model)) .twistedE6 0 ℓ f :=
    LieModel.of_mulEquiv hqiso.symm
      (lieModel_twistedE6_fixed (theta2 L ℓ f) theta2_theta2 hℓ hf hk hθq)
  obtain ⟨h1, h2⟩ := lieModel_twistedE6_chev hlie
  have hring : ringChar L = ℓ := ringChar.eq L ℓ
  rw [hring]
  exact ⟨h1, h2⟩

end Layer

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
