module

public import CFSG.RankThree.PartOne.KE6.E6LLayer
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcRoots

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE6
  CFSG.RankThree.PartOne.KD4T CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Steinberg.Adjoint
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints frobenius_canonicalRep)

section Layer

theorem e6Layer_finite_quasisimple (τ : Tag) [M27Ok τ] [E6Sub τ] {L : Type} [Field L]
    [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ] (hf : 1 ≤ f) {n : ModGL τ L}
    (hn : n ∈ monomialSubgroup τ L)
    (hmaps : ∀ α ∈ parabolicRoots τ (e6Nodes τ),
      weylQuotientHom τ L ⟨n, hn⟩ • α ∈ parabolicRoots τ (e6Nodes τ)) :
    Finite ↥(rootSpan τ L (parabolicRoots τ (e6Nodes τ)) ⊓
        twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) ∧
      CFSG.IsQuasisimple ↥(rootSpan τ L (parabolicRoots τ (e6Nodes τ)) ⊓
        twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) := by
  have hw : MapsJ τ (e6Set τ) (weylQuotientHom τ L ⟨n, hn⟩) := by
    intro α hα
    have := hmaps α (by rwa [e6Nodes_eq_e6Set])
    rwa [e6Nodes_eq_e6Set] at this
  obtain ⟨u, hu, π, hπ, hact⟩ := exists_action hw
  have hπJ : ∀ i ∈ e6Set τ, π i ∈ e6Set τ := by
    rcases hπ with rfl | rfl
    · exact fun i hi => hi
    · exact fun i hi => rhoτ_mem hi
  have hπJ' : ∀ i ∈ e6Set τ, π.symm i ∈ e6Set τ := by
    rcases hπ with rfl | rfl
    · exact fun i hi => hi
    · exact fun i hi => rhoτ_symm_mem hi
  obtain ⟨n₁, h, hn₁, hh, hgen, hlang⟩ :=
    CFSG.RankThree.PartOne.KE6.exists_conj_twistedFixed hf hn hπJ hπJ' hu hact
  have hstd : StdTwist6 n₁ π := ⟨hπ, hgen⟩
  have hP' : rootSpan τ L (parabolicRoots τ (e6Nodes τ)) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) =
      subsystemGroup τ L (e6Set τ) ⊓
        twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) := by
    rw [subsystemGroup_eq_rootSpan, e6Nodes_eq_e6Set]
  obtain ⟨h1, h2, -, -⟩ := layer_of_standard6 hf hstd hh hlang hP'
  exact ⟨h1, h2⟩

end Layer

section Transport

variable {τ : Tag} {L : Type} [Field L]

theorem rootSpan_inf_twistedFixedPoints_smul (Fr : L →+* L) (v : WeylGroup τ) (n : ModGL τ L)
    {S : Set (Fin τ.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot τ α) :
    rootSpan τ L ((fun α => v • α) '' S) ⊓ twistedFixedPoints n (Units.map (entrywiseHom Fr)) =
      (rootSpan τ L S ⊓ twistedFixedPoints ((canonicalRep (coxeterSystem τ) L v)⁻¹ * n *
        canonicalRep (coxeterSystem τ) L v) (Units.map (entrywiseHom Fr))).map
          (MulAut.conj (canonicalRep (coxeterSystem τ) L v)).toMonoidHom := by
  set nv := canonicalRep (coxeterSystem τ) L v with hnv
  set F : ModGL τ L →* ModGL τ L := Units.map (entrywiseHom Fr) with hF
  have hFnv : F nv = nv := frobenius_canonicalRep Fr v
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj nv).injective,
    (canonical_weyl_root_transport τ L).1 v S hS]
  congr 1
  ext x
  constructor
  · intro hx
    have hx' : n * F x * n⁻¹ = x := hx
    refine ⟨nv⁻¹ * x * nv, ?_, ?_⟩
    · change (nv⁻¹ * n * nv) * F (nv⁻¹ * x * nv) * (nv⁻¹ * n * nv)⁻¹ = nv⁻¹ * x * nv
      rw [map_mul, map_mul, map_inv, hFnv]
      calc nv⁻¹ * n * nv * (nv⁻¹ * F x * nv) * (nv⁻¹ * n * nv)⁻¹ =
          nv⁻¹ * (n * F x * n⁻¹) * nv := by group
        _ = nv⁻¹ * x * nv := by rw [hx']
    · change nv * (nv⁻¹ * x * nv) * nv⁻¹ = x
      group
  · rintro ⟨y, hy, rfl⟩
    have hy' : (nv⁻¹ * n * nv) * F y * (nv⁻¹ * n * nv)⁻¹ = y := hy
    change n * F (nv * y * nv⁻¹) * n⁻¹ = nv * y * nv⁻¹
    rw [map_mul, map_mul, map_inv, hFnv]
    calc n * (nv * F y * nv⁻¹) * n⁻¹ =
        nv * ((nv⁻¹ * n * nv) * F y * (nv⁻¹ * n * nv)⁻¹) * nv⁻¹ := by group
      _ = nv * y * nv⁻¹ := by rw [hy']

end Transport

theorem twistTag_tag_ne_E7 (t : TwistTag) : t.tag ≠ .E7 := by
  cases t <;> decide

theorem twistTag_tag_ne_E8 (t : TwistTag) : t.tag ≠ .E8 := by
  cases t <;> decide

theorem LangSetup.exists_char_pow
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p) :
    ∃ ℓ f : ℕ, ℓ.Prime ∧ CharP L ℓ ∧ 1 ≤ f ∧ S.D.q = ℓ ^ f := by
  obtain ⟨⟨ℓ, f, hℓ, hf, hq⟩, h0⟩ := S.hqpow
  have hℓ' : ℓ.Prime := Nat.prime_iff.2 hℓ
  refine ⟨ℓ, f, hℓ', ?_, hf, hq.symm⟩
  rw [CharP.charP_iff_prime_eq_zero hℓ']
  rw [← hq, Nat.cast_pow] at h0
  exact pow_eq_zero_iff hf.ne' |>.1 h0

theorem rationalComponent_eq_rootSpan_inf_model_of_layer
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
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

theorem isQuasisimple_rationalComponent_of_layer
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (hqs : CFSG.IsQuasisimple ↥(rootSpan τ L (componentRoots (rootCharHom a) i) ⊓ S.D.model)) :
    CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  rw [rationalComponent_eq_rootSpan_inf_model_of_layer S i hρ hqs]
  exact hqs

section Component

variable {τ : Tag} [M27Ok τ] [E6Sub τ] {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem rootSpan_inf_model_quasisimple (hτ : ∀ t : TwistTag, t.tag ≠ τ) (S : LangSetup τ L p)
    {w : WeylGroup τ} (hn : S.D.n = canonicalRep (coxeterSystem τ) L w) (v : WeylGroup τ)
    (hw : ∀ γ ∈ (fun α => v • α) '' parabolicRoots τ (e6Nodes τ),
      w • γ ∈ (fun α => v • α) '' parabolicRoots τ (e6Nodes τ)) :
    Finite ↥(rootSpan τ L ((fun α => v • α) '' parabolicRoots τ (e6Nodes τ)) ⊓ S.D.model) ∧
      CFSG.IsQuasisimple
        ↥(rootSpan τ L ((fun α => v • α) '' parabolicRoots τ (e6Nodes τ)) ⊓ S.D.model) := by
  classical
  obtain ⟨ℓ, f, hℓ, hchar, hf, hq⟩ := S.exists_char_pow
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨Fr, hFr, hΦ⟩ := S.D.exists_frob_of_untwisted hτ
  have hFr' : Fr = iterateFrobenius L ℓ f := by
    ext c
    rw [hFr, hq, iterateFrobenius_def]
  set nv := canonicalRep (coxeterSystem τ) L v with hnv
  set nw := canonicalRep (coxeterSystem τ) L w with hnw
  have hroots : ∀ α ∈ parabolicRoots τ (e6Nodes τ), IsRoot τ α := fun α hα => hα.1
  have hmodel : rootSpan τ L ((fun α => v • α) '' parabolicRoots τ (e6Nodes τ)) ⊓ S.D.model =
      rootSpan τ L ((fun α => v • α) '' parabolicRoots τ (e6Nodes τ)) ⊓
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
  rw [hmodel, rootSpan_inf_twistedFixedPoints_smul _ v nw hroots]
  have hnvM := canonicalRep_mem_monomialSubgroup L v
  have hnwM := canonicalRep_mem_monomialSubgroup L w
  have hn'M : nv⁻¹ * nw * nv ∈ monomialSubgroup τ L :=
    mul_mem (mul_mem (inv_mem hnvM) hnwM) hnvM
  have hπ : weylQuotientHom τ L ⟨nv⁻¹ * nw * nv, hn'M⟩ = v⁻¹ * w * v := by
    have e : (⟨nv⁻¹ * nw * nv, hn'M⟩ : monomialSubgroup τ L) =
        (⟨nv, hnvM⟩ : monomialSubgroup τ L)⁻¹ * ⟨nw, hnwM⟩ * ⟨nv, hnvM⟩ := rfl
    rw [e, map_mul, map_mul, map_inv, weylQuotientHom_eq (mapsRootLines_canonicalRep v),
      weylQuotientHom_eq (mapsRootLines_canonicalRep w)]
  have hmaps : ∀ α ∈ parabolicRoots τ (e6Nodes τ),
      weylQuotientHom τ L ⟨nv⁻¹ * nw * nv, hn'M⟩ • α ∈ parabolicRoots τ (e6Nodes τ) := by
    intro α hα
    rw [hπ]
    obtain ⟨β, hβ, hβe⟩ := hw (v • α) ⟨α, hα, rfl⟩
    rw [mul_smul, mul_smul, ← hβe, inv_smul_smul]
    exact hβ
  obtain ⟨hfin, hqs⟩ := e6Layer_finite_quasisimple τ (ℓ := ℓ) hf hn'M hmaps
  set P := rootSpan τ L (parabolicRoots τ (e6Nodes τ)) ⊓
    twistedFixedPoints (nv⁻¹ * nw * nv) (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))
  have e : P ≃* P.map (MulAut.conj nv).toMonoidHom :=
    P.equivMapOfInjective _ (MulAut.conj nv).injective
  exact ⟨Finite.of_equiv _ e.toEquiv, CFSG.LocalCores.isQuasisimple_of_mulEquiv e hqs⟩

theorem isQuasisimple_rationalComponent_of_e6 (hτ : ∀ t : TwistTag, t.tag ≠ τ)
    (S : LangSetup τ L p) {w : WeylGroup τ} (hn : S.D.n = canonicalRep (coxeterSystem τ) L w)
    (a : Fin τ.rank → Lˣ) (i : KernelComponent (rootCharHom a)) (v : WeylGroup τ)
    (hΨ : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots τ (e6Nodes τ))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (hw : ∀ γ ∈ componentRoots (rootCharHom a) i, w • γ ∈ componentRoots (rootCharHom a) i) :
    CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  rw [hΨ] at hw
  obtain ⟨-, hqs⟩ := rootSpan_inf_model_quasisimple hτ S hn v hw
  exact isQuasisimple_rationalComponent_of_layer S i hρ (by rw [hΨ]; exact hqs)

end Component

theorem orth_e6_E7 : ∀ l ∈ Tag.E7.artifactRoots,
    ¬ ∀ j : Fin 6, iform (τ := Tag.E7) (fun k : Fin Tag.E7.rank => l.getD k 0)
      (Pi.single (Fin.castLE (by decide) j) 1) = 0 := by
  decide +kernel

theorem orth_e6_E8 : ∀ l ∈ Tag.E8.artifactRoots,
    (∀ j : Fin 6, iform (τ := Tag.E8) (fun k : Fin Tag.E8.rank => l.getD k 0)
      (Pi.single (Fin.castLE (by decide) j) 1) = 0) →
    l ∈ ([[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, -1], [2, 3, 4, 6, 5, 4, 3, 2],
      [-2, -3, -4, -6, -5, -4, -3, -2], [2, 3, 4, 6, 5, 4, 3, 1],
      [-2, -3, -4, -6, -5, -4, -3, -1]] : List (List ℤ)) := by
  decide +kernel

theorem single_mem_parabolicRoots_e6 {τ : Tag}
    (j : Fin τ.rank) (hj : j.val ≤ 5) :
    (Pi.single j 1 : Fin τ.rank → ℤ) ∈ parabolicRoots τ (e6Nodes τ) := by
  refine ⟨isRoot_single τ j, fun i hi => ?_⟩
  have hij : i ≠ j := fun h => hi (by rw [h]; exact hj)
  simp [hij]

theorem card_le_of_orth_e6 {τ : Tag} (h6 : 6 ≤ τ.rank)
    (cands : List (List ℤ))
    (horth : ∀ l ∈ τ.artifactRoots, (∀ j : Fin 6, iform (τ := τ)
      (fun k : Fin τ.rank => l.getD k 0) (Pi.single (Fin.castLE h6 j) 1) = 0) → l ∈ cands)
    (s : Finset (Fin τ.rank → ℤ))
    (hs : ∀ β ∈ s, IsRoot τ β ∧ ∀ α ∈ parabolicRoots τ (e6Nodes τ), iform β α = 0) :
    s.card ≤ cands.toFinset.card := by
  classical
  have hsub : s.image List.ofFn ⊆ cands.toFinset := by
    intro l hl
    obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.1 hl
    rw [List.mem_toFinset]
    refine horth _ (isRoot_iff_mem_artifactRoots.1 (hs β hβ).1) fun j => ?_
    have hfun : (fun k : Fin τ.rank => (List.ofFn β).getD k 0) = β := by
      funext k
      rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact k.2), List.getElem_ofFn]
    rw [hfun]
    exact (hs β hβ).2 _ (single_mem_parabolicRoots_e6 _ (by
      simp only [Fin.val_castLE]
      omega))
  calc s.card = (s.image List.ofFn).card :=
        (Finset.card_image_of_injective _ List.ofFn_injective).symm
    _ ≤ cands.toFinset.card := Finset.card_le_card hsub

section KernelExhaustion

theorem kernelRoots_eq_componentRoots_of_E7_e6
    {T : Type*} [CommGroup T] (chi : Multiplicative (Fin Tag.E7.rank → ℤ) →* T)
    (i : KernelComponent chi) (v : WeylGroup .E7)
    (hPsi : componentRoots chi i =
      (fun alpha => v • alpha) '' parabolicRoots .E7 (e6Nodes .E7)) :
    kernelRoots chi = componentRoots chi i := by
  apply Set.Subset.antisymm
  · intro beta hbeta
    by_contra hout
    let j : KernelComponent chi := Quotient.mk _ ⟨beta, hbeta⟩
    have hbj : beta ∈ componentRoots chi j := ⟨hbeta, rfl⟩
    have hji : j ≠ i := fun h => hout (h ▸ hbj)
    have hperp : ∀ alpha ∈ parabolicRoots .E7 (e6Nodes .E7),
        iform (v⁻¹ • beta) alpha = 0 := by
      intro alpha halpha
      have hai : v • alpha ∈ componentRoots chi i := by
        rw [hPsi]
        exact ⟨alpha, halpha, rfl⟩
      have hz : iform beta (v • alpha) = 0 :=
        iform_eq_zero_of_mem_componentRoots hji hbj hai
      calc iform (v⁻¹ • beta) alpha
          = iform (v • (v⁻¹ • beta)) (v • alpha) := (iform_smul v _ _).symm
        _ = 0 := by simpa only [smul_inv_smul] using hz
    have hroot : IsRoot .E7 (v⁻¹ • beta) := IsRoot.smul hbeta.1 v⁻¹
    have hc := card_le_of_orth_e6 (τ := Tag.E7) (by decide) []
      (fun l hl h => False.elim ((orth_e6_E7 l hl) h))
      ({v⁻¹ • beta} : Finset (Fin Tag.E7.rank → ℤ)) (by
        intro alpha halpha
        obtain rfl := Finset.mem_singleton.mp halpha
        exact ⟨hroot, hperp⟩)
    simpa using hc
  · intro alpha halpha
    exact halpha.1

end KernelExhaustion

section Final

theorem isQuasisimple_rationalComponent_e6T {τ : Tag} [hτ : M27Ok τ] [E6Sub τ] {L : Type}
    [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ}
    (haT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a)) (v : WeylGroup τ)
    (hΨ : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots τ (e6Nodes τ)) :
    CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
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
  exact isQuasisimple_rationalComponent_of_e6 hτ' S hn a i v hΨ hρ hw

end Final

end CFSG.HardMathSupport.Timmesfeld.LangTorus
