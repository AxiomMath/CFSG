module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwoDFour
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Monster.B.E6.StdF4RadicalRoots
public import CFSG.Quasithin.Vol2.Ch11SecOE5B
public import CFSG.RankThree.Chevalley.SteinbergBIWE8Code
public import CFSG.RankThree.Chevalley.SteinbergBNF4Block
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.DX

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KD4L
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE6
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints D4TrialityLayer d4Nodes)



@[expose] def LayerComm {τ : Tag} {L : Type} [Field L] (Ψ₀ : Set (Fin τ.rank → ℤ))
    (P : Subgroup (ModGL τ L)) : Prop :=
  CFSG.IsQuasisimple ↥P ∧
    ∀ y ∈ rootSpan τ L Ψ₀, (∀ u ∈ P, y * u = u * y) →
      y ∈ Subgroup.centralizer (rootSpan τ L Ψ₀ : Set (ModGL τ L))

@[expose] def ShapeComm {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup τ L p) (Ψ : Set (Fin τ.rank → ℤ)) : Prop :=
  CFSG.IsQuasisimple ↥(rootSpan τ L Ψ ⊓ S.D.model) ∧
    ∀ z ∈ rootSpan τ L Ψ, (∀ u ∈ rootSpan τ L Ψ ⊓ S.D.model, z * u = u * z) →
      ∀ g ∈ rootSpan τ L Ψ, Commute z g

section Setup

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

private theorem smul_mem_of_rho_eq (S : LangSetup τ L p) {Ψ : Set (Fin τ.rank → ℤ)}
    (hΨ : ∀ γ ∈ Ψ, IsRoot τ γ) {w : WeylGroup τ} (hρ : ∀ γ ∈ Ψ, S.ρ γ ∈ Ψ)
    (hρw : ∀ γ, IsRoot τ γ → S.ρ γ = w • γ) :
    ∀ γ ∈ Ψ, w • γ ∈ Ψ := by
  intro γ hγ
  rw [← hρw γ (hΨ γ hγ)]
  exact hρ γ hγ

private theorem smul_inv_mul_mem {Ψ₀ : Set (Fin τ.rank → ℤ)} {v w : WeylGroup τ}
    (hw : ∀ γ ∈ (fun α => v • α) '' Ψ₀, w • γ ∈ (fun α => v • α) '' Ψ₀) :
    ∀ α ∈ Ψ₀, (v⁻¹ * w * v) • α ∈ Ψ₀ := by
  intro α hα
  obtain ⟨β, hβ, hβe⟩ := hw (v • α) ⟨α, hα, rfl⟩
  rw [mul_smul, mul_smul, ← hβe, inv_smul_smul]
  exact hβ

private structure ConjMonomial (S : LangSetup τ L p) (v w : WeylGroup τ) where
  mem_monomial : ((canonicalRep (coxeterSystem τ) L v)⁻¹ * canonicalRep (coxeterSystem τ) L w *
    canonicalRep (coxeterSystem τ) L v) ∈ monomialSubgroup τ L
  mem_adjoint : ((canonicalRep (coxeterSystem τ) L v)⁻¹ * canonicalRep (coxeterSystem τ) L w *
    canonicalRep (coxeterSystem τ) L v) ∈ adjointGroup τ L
  weyl : weylQuotientHom τ L
    ⟨(canonicalRep (coxeterSystem τ) L v)⁻¹ * canonicalRep (coxeterSystem τ) L w *
      canonicalRep (coxeterSystem τ) L v, mem_monomial⟩ = v⁻¹ * w * v

private theorem existsConjMonomial (S : LangSetup τ L p) (v w : WeylGroup τ) :
    ConjMonomial S v w := by
  have hnvM := canonicalRep_mem_monomialSubgroup L v
  have hnwM := canonicalRep_mem_monomialSubgroup L w
  have hn'M : ((canonicalRep (coxeterSystem τ) L v)⁻¹ * canonicalRep (coxeterSystem τ) L w *
      canonicalRep (coxeterSystem τ) L v) ∈ monomialSubgroup τ L :=
    mul_mem (mul_mem (inv_mem hnvM) hnwM) hnvM
  have hn'C : ((canonicalRep (coxeterSystem τ) L v)⁻¹ * canonicalRep (coxeterSystem τ) L w *
      canonicalRep (coxeterSystem τ) L v) ∈ adjointGroup τ L :=
    mul_mem (mul_mem (inv_mem (canonicalRep_mem_adjointGroup _ L v))
      (canonicalRep_mem_adjointGroup _ L w)) (canonicalRep_mem_adjointGroup _ L v)
  refine ⟨hn'M, hn'C, ?_⟩
  have e : (⟨(canonicalRep (coxeterSystem τ) L v)⁻¹ * canonicalRep (coxeterSystem τ) L w *
        canonicalRep (coxeterSystem τ) L v, hn'M⟩ : monomialSubgroup τ L) =
      (⟨canonicalRep (coxeterSystem τ) L v, hnvM⟩ : monomialSubgroup τ L)⁻¹ *
        ⟨canonicalRep (coxeterSystem τ) L w, hnwM⟩ *
          ⟨canonicalRep (coxeterSystem τ) L v, hnvM⟩ := rfl
  rw [e, map_mul, map_mul, map_inv, weylQuotientHom_eq (mapsRootLines_canonicalRep v),
    weylQuotientHom_eq (mapsRootLines_canonicalRep w)]

private theorem rootSpan_inf_model_eq_of_untw (S : LangSetup τ L p) {Fr : L →+* L}
    (hΦ : S.D.Φ = Units.map (entrywiseHom Fr)) {w : WeylGroup τ}
    (hn : S.D.n = canonicalRep (coxeterSystem τ) L w) (Ψ : Set (Fin τ.rank → ℤ)) :
    rootSpan τ L Ψ ⊓ S.D.model =
      rootSpan τ L Ψ ⊓ twistedFixedPoints (canonicalRep (coxeterSystem τ) L w)
        (Units.map (entrywiseHom Fr)) := by
  ext x
  simp only [Subgroup.mem_inf]
  constructor
  · rintro ⟨hx, -, hxF⟩
    refine ⟨hx, ?_⟩
    have hxF' : S.D.n * S.D.Φ x * S.D.n⁻¹ = x := hxF
    rw [hn, hΦ] at hxF'
    exact hxF'
  · rintro ⟨hx, hxF⟩
    refine ⟨hx, rootSpan_le_adjointGroup L _ hx, ?_⟩
    change S.D.n * S.D.Φ x * S.D.n⁻¹ = x
    rw [hn, hΦ]
    exact hxF

private theorem conj_mul_mem_rootSpan {Ψ₀ : Set (Fin τ.rank → ℤ)}
    (hΨ₀ : ∀ α ∈ Ψ₀, IsRoot τ α) {v : WeylGroup τ} {x : ModGL τ L}
    (hx : x ∈ rootSpan τ L ((fun α => v • α) '' Ψ₀)) :
    (canonicalRep (coxeterSystem τ) L v)⁻¹ * x * canonicalRep (coxeterSystem τ) L v ∈
      rootSpan τ L Ψ₀ := by
  have htrans : (rootSpan τ L Ψ₀).map
        (MulAut.conj (canonicalRep (coxeterSystem τ) L v)).toMonoidHom =
      rootSpan τ L ((fun α => v • α) '' Ψ₀) := (canonical_weyl_root_transport τ L).1 v Ψ₀ hΨ₀
  obtain ⟨y, hy, hyx⟩ := (htrans.symm ▸ hx : x ∈ (rootSpan τ L Ψ₀).map
    (MulAut.conj (canonicalRep (coxeterSystem τ) L v)).toMonoidHom)
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
  have e : (canonicalRep (coxeterSystem τ) L v)⁻¹ * x * canonicalRep (coxeterSystem τ) L v = y := by
    rw [← hyx]
    group
  rw [e]
  exact hy

private theorem commute_conj_mul {nv z u : ModGL τ L}
    (h : z * (nv * u * nv⁻¹) = (nv * u * nv⁻¹) * z) :
    (nv⁻¹ * z * nv) * u = u * (nv⁻¹ * z * nv) := by
  calc (nv⁻¹ * z * nv) * u = nv⁻¹ * (z * (nv * u * nv⁻¹)) * nv := by group
    _ = nv⁻¹ * ((nv * u * nv⁻¹) * z) * nv := by rw [h]
    _ = u * (nv⁻¹ * z * nv) := by group

private theorem commute_of_conj_commute {nv z g : ModGL τ L}
    (h : (nv⁻¹ * g * nv) * (nv⁻¹ * z * nv) = (nv⁻¹ * z * nv) * (nv⁻¹ * g * nv)) :
    z * g = g * z := by
  have e1 : z * g = nv * ((nv⁻¹ * z * nv) * (nv⁻¹ * g * nv)) * nv⁻¹ := by group
  have e2 : g * z = nv * ((nv⁻¹ * g * nv) * (nv⁻¹ * z * nv)) * nv⁻¹ := by group
  rw [e1, e2, h]

private theorem commute_of_layer_conj (S : LangSetup τ L p) {Ψ₀ : Set (Fin τ.rank → ℤ)}
    (hΨ₀ : ∀ α ∈ Ψ₀, IsRoot τ α) {v : WeylGroup τ} {P : Subgroup (ModGL τ L)}
    (hmap : rootSpan τ L ((fun α => v • α) '' Ψ₀) ⊓ S.D.model =
      P.map (MulAut.conj (canonicalRep (coxeterSystem τ) L v)).toMonoidHom)
    (hcen : ∀ y ∈ rootSpan τ L Ψ₀, (∀ u ∈ P, y * u = u * y) →
      y ∈ Subgroup.centralizer (rootSpan τ L Ψ₀ : Set (ModGL τ L))) :
    ∀ z ∈ rootSpan τ L ((fun α => v • α) '' Ψ₀),
      (∀ u ∈ rootSpan τ L ((fun α => v • α) '' Ψ₀) ⊓ S.D.model, z * u = u * z) →
      ∀ g ∈ rootSpan τ L ((fun α => v • α) '' Ψ₀), Commute z g := by
  intro z hz hzc g hg
  rw [hmap] at hzc
  have hc₀ : ∀ u ∈ P,
      ((canonicalRep (coxeterSystem τ) L v)⁻¹ * z * canonicalRep (coxeterSystem τ) L v) * u =
        u * ((canonicalRep (coxeterSystem τ) L v)⁻¹ * z * canonicalRep (coxeterSystem τ) L v) :=
    fun u hu => commute_conj_mul (hzc _ ⟨u, hu, rfl⟩)
  have hcent := hcen _ (conj_mul_mem_rootSpan hΨ₀ hz) hc₀
  exact commute_of_conj_commute ((Subgroup.mem_centralizer_iff.mp hcent) _
    (conj_mul_mem_rootSpan hΨ₀ hg))

end Setup

section Transport

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem commute_of_layer_transport (S : LangSetup τ L p) {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = Units.map (entrywiseHom Fr)) {w : WeylGroup τ}
    (hn : S.D.n = canonicalRep (coxeterSystem τ) L w) (v : WeylGroup τ)
    {Ψ₀ : Set (Fin τ.rank → ℤ)} (hΨ₀ : ∀ α ∈ Ψ₀, IsRoot τ α)
    (hlayer : ∀ (ℓ f : ℕ) [Fact ℓ.Prime] [CharP L ℓ], 1 ≤ f →
      LayerComm Ψ₀ (rootSpan τ L Ψ₀ ⊓ twistedFixedPoints
        ((canonicalRep (coxeterSystem τ) L v)⁻¹ * canonicalRep (coxeterSystem τ) L w *
          canonicalRep (coxeterSystem τ) L v)
        (Units.map (entrywiseHom (iterateFrobenius L ℓ f))))) :
    CFSG.IsQuasisimple ↥(rootSpan τ L ((fun α => v • α) '' Ψ₀) ⊓ S.D.model) ∧
      ∀ z ∈ rootSpan τ L ((fun α => v • α) '' Ψ₀),
        (∀ u ∈ rootSpan τ L ((fun α => v • α) '' Ψ₀) ⊓ S.D.model, z * u = u * z) →
        ∀ g ∈ rootSpan τ L ((fun α => v • α) '' Ψ₀), Commute z g := by
  classical
  obtain ⟨ℓ, f, hℓ, hchar, hf, hq⟩ := S.exists_char_pow
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hFr' : Fr = iterateFrobenius L ℓ f := by
    ext x
    rw [hFr, hq, iterateFrobenius_def]
  subst hFr'
  set P : Subgroup (ModGL τ L) := rootSpan τ L Ψ₀ ⊓ twistedFixedPoints
    ((canonicalRep (coxeterSystem τ) L v)⁻¹ * canonicalRep (coxeterSystem τ) L w *
      canonicalRep (coxeterSystem τ) L v) (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))
    with hP
  have hmap : rootSpan τ L ((fun α => v • α) '' Ψ₀) ⊓ S.D.model =
      P.map (MulAut.conj (canonicalRep (coxeterSystem τ) L v)).toMonoidHom := by
    rw [hP, rootSpan_inf_model_eq_of_untw S hΦ hn ((fun α => v • α) '' Ψ₀)]
    exact rootSpan_inf_twistedFixedPoints_smul (iterateFrobenius L ℓ f) v
      (canonicalRep (coxeterSystem τ) L w) hΨ₀
  refine ⟨?_, commute_of_layer_conj S hΨ₀ hmap (hlayer ℓ f hf).2⟩
  rw [hmap]
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (P.equivMapOfInjective _ (MulAut.conj (canonicalRep (coxeterSystem τ) L v)).injective)
    (hlayer ℓ f hf).1

end Transport

section E6Layer

variable {τ : Tag} [M27Ok τ] [E6Sub τ] {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ}
  [Fact ℓ.Prime] [CharP L ℓ]

theorem e6Layer_commutant (τ : Tag) [M27Ok τ] [E6Sub τ] {L : Type} [Field L]
    [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ] (hf : 1 ≤ f) {n : ModGL τ L}
    (hn : n ∈ monomialSubgroup τ L)
    (hmaps : ∀ α ∈ parabolicRoots τ (e6Nodes τ),
      weylQuotientHom τ L ⟨n, hn⟩ • α ∈ parabolicRoots τ (e6Nodes τ)) :
    LayerComm (parabolicRoots τ (e6Nodes τ))
      (rootSpan τ L (parabolicRoots τ (e6Nodes τ)) ⊓
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
  have hP : rootSpan τ L (parabolicRoots τ (e6Nodes τ)) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) =
      subsystemGroup τ L (e6Set τ) ⊓
        twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) := by
    rw [subsystemGroup_eq_rootSpan, e6Nodes_eq_e6Set]
  obtain ⟨-, hqs, hcomm, -⟩ := layer_of_standard6 hf hstd hh hlang hP
  refine ⟨hqs, fun y hy hc g hg => ?_⟩
  rw [e6Nodes_eq_e6Set, ← subsystemGroup_eq_rootSpan] at hy hg
  exact (Subgroup.mem_centralizer_iff.mp
    (hcomm y (Subgroup.mem_sup_right hy) hc).2) g hg

end E6Layer

section D4Untwisted

variable {τ : Tag} [E6Sub τ] {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

@[expose] def IsLeafSwapTable (τ : Tag) [E6Sub τ] : Prop :=
  ∀ i j : Fin τ.rank, (i.val = 1 ∨ i.val = 2 ∨ i.val = 4) →
    (j.val = 1 ∨ j.val = 2 ∨ j.val = 4) → i ≠ j →
    ((∀ k : Fin Tag.D4.rank, Equiv.swap i j (d4Id k) = d4Id (Equiv.swap 1 3 k)) ∨
      (∀ k : Fin Tag.D4.rank, Equiv.swap i j (d4Id k) = d4Id (Equiv.swap 0 3 k)) ∨
      (∀ k : Fin Tag.D4.rank, Equiv.swap i j (d4Id k) = d4Id (Equiv.swap 0 1 k))) ∧
    (∀ x : Fin τ.rank, (1 ≤ x.val ∧ x.val ≤ 4) →
      (1 ≤ (Equiv.swap i j x).val ∧ (Equiv.swap i j x).val ≤ 4)) ∧
    (∀ x : Fin τ.rank, (1 ≤ x.val ∧ x.val ≤ 4) →
      (1 ≤ ((Equiv.swap i j).symm x).val ∧ ((Equiv.swap i j).symm x).val ≤ 4))

variable {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ]

private theorem layerComm_of_swap (hf : 1 ≤ f) (hleaf : IsLeafSwapTable τ) {i j : Fin τ.rank}
    (hij : i ≠ j) (hi : i.val ∈ ({1, 2, 4} : Set ℕ)) (hj : j.val ∈ ({1, 2, 4} : Set ℕ))
    {n : ModGL τ L} (hn : n ∈ monomialSubgroup τ L)
    (hact : ∃ u ∈ parabolicWeylGroup τ (d4Nodes τ), ∀ α ∈ parabolicRoots τ (d4Nodes τ),
      weylQuotientHom τ L ⟨n, hn⟩ • α = u • permLattice (Equiv.swap i j) α) :
    LayerComm (parabolicRoots τ (d4Nodes τ))
      (rootSpan τ L (parabolicRoots τ (d4Nodes τ)) ⊓
        twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) := by
  obtain ⟨-, hqs, hcomm, -⟩ :=
    transposition_layer_of_leafSwap hleaf hf hij hi hj n hn hact _ rfl
  exact ⟨hqs, fun y hy hc => (hcomm y (Subgroup.mem_sup_right hy) hc).2⟩

private theorem layerComm_of_triality (hf : 1 ≤ f) (hL : D4TrialityLayer τ)
    {a b c : Fin τ.rank} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (ha : a.val ∈ ({1, 2, 4} : Set ℕ)) (hb : b.val ∈ ({1, 2, 4} : Set ℕ))
    (hc : c.val ∈ ({1, 2, 4} : Set ℕ))
    {n : ModGL τ L} (hn : n ∈ monomialSubgroup τ L) (hC : n ∈ adjointGroup τ L)
    (hact : ∃ u ∈ parabolicWeylGroup τ (d4Nodes τ), ∀ α ∈ parabolicRoots τ (d4Nodes τ),
      weylQuotientHom τ L ⟨n, hn⟩ • α = u • permLattice (List.formPerm [a, b, c]) α) :
    LayerComm (parabolicRoots τ (d4Nodes τ))
      (rootSpan τ L (parabolicRoots τ (d4Nodes τ)) ⊓
        twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) := by
  obtain ⟨u, hu, hact'⟩ := hact
  obtain ⟨-, hqs, hcomm, -⟩ :=
    hL L ℓ f hf a b c hab hbc hac ha hb hc n hn hC ⟨u, hu, hact'⟩ _ rfl
  exact ⟨hqs, fun y hy hc => (hcomm y (Subgroup.mem_sup_right hy) hc).2⟩

private theorem layerComm_of_leafPerm (hf : 1 ≤ f) (hTri : D4TrialityLayer τ)
    (hleaf : IsLeafSwapTable τ) {n : ModGL τ L} (hn : n ∈ monomialSubgroup τ L)
    (hC : n ∈ adjointGroup τ L) {u : WeylGroup τ} (hu : u ∈ parabolicWeylGroup τ (d4Nodes τ))
    {π : Equiv.Perm (Fin τ.rank)} (hπ : IsD4LeafPerm π) (hπ1 : π ≠ 1)
    (hact : ∀ α ∈ parabolicRoots τ (d4Nodes τ),
      weylQuotientHom τ L ⟨n, hn⟩ • α = u • permLattice π α) :
    LayerComm (parabolicRoots τ (d4Nodes τ))
      (rootSpan τ L (parabolicRoots τ (d4Nodes τ)) ⊓
        twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) := by
  have h12 : e6Idx (τ := τ) 1 ≠ e6Idx 2 := e6Idx_ne (by decide)
  have h14 : e6Idx (τ := τ) 1 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have h24 : e6Idx (τ := τ) 2 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have hv1 : (e6Idx (τ := τ) 1).val ∈ ({1, 2, 4} : Set ℕ) := by
    rw [e6Idx_val']; exact Or.inl rfl
  have hv2 : (e6Idx (τ := τ) 2).val ∈ ({1, 2, 4} : Set ℕ) := by
    rw [e6Idx_val']; exact Or.inr (Or.inl rfl)
  have hv4 : (e6Idx (τ := τ) 4).val ∈ ({1, 2, 4} : Set ℕ) := by
    rw [e6Idx_val']; exact Or.inr (Or.inr rfl)
  rcases hπ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hπ1
  · exact layerComm_of_swap hf hleaf h12 hv1 hv2 hn ⟨u, hu, hact⟩
  · exact layerComm_of_swap hf hleaf h14 hv1 hv4 hn ⟨u, hu, hact⟩
  · exact layerComm_of_swap hf hleaf h24 hv2 hv4 hn ⟨u, hu, hact⟩
  · exact layerComm_of_triality hf hTri h12 h24 h14 hv1 hv2 hv4 hn hC ⟨u, hu, hact⟩
  · exact layerComm_of_triality hf hTri h14 h24.symm h12 hv1 hv4 hv2 hn hC ⟨u, hu, hact⟩

private theorem d4_leafPerm_ne_one (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ}
    (i : KernelComponent (rootCharHom a)) {v w : WeylGroup τ} {u : WeylGroup τ}
    (hu : u ∈ parabolicWeylGroup τ (d4Nodes τ)) {π : Equiv.Perm (Fin τ.rank)}
    (hΨ : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots τ (d4Nodes τ))
    (hρw : ∀ γ, IsRoot τ γ → S.ρ γ = w • γ)
    (h1 : ¬ twistInner (componentRoots (rootCharHom a) i) (S.ρ : (Fin τ.rank → ℤ) → _))
    (hact : ∀ α ∈ parabolicRoots τ (d4Nodes τ),
      (v⁻¹ * w * v) • α = u • permLattice π α) :
    π ≠ 1 := by
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

theorem d4_commute_untw (hsearch : D4BaseSearch τ) (hTri : D4TrialityLayer τ)
    (hleaf : IsLeafSwapTable τ) (S : LangSetup τ L p) {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = Units.map (entrywiseHom Fr)) {w : WeylGroup τ}
    (hn : S.D.n = canonicalRep (coxeterSystem τ) L w) (hρw : ∀ γ, IsRoot τ γ → S.ρ γ = w • γ)
    {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a)) (v : WeylGroup τ)
    (hΨ : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots τ (d4Nodes τ))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (h1 : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    ShapeComm S (componentRoots (rootCharHom a) i) := by
  classical
  have hfin : (componentRoots (rootCharHom a) i).Finite :=
    (finite_setOf_isRoot τ).subset fun γ hγ => hγ.1.1
  rw [componentOrbitLength_eq_one hfin hρ, Function.iterate_one] at h1
  have hmaps : MapsJ τ (d4Set τ) (v⁻¹ * w * v) :=
    smul_inv_mul_mem (hΨ ▸ smul_mem_of_rho_eq S (fun γ hγ => hγ.1.1) hρ hρw)
  obtain ⟨u, hu, w₀, hw₀, π, hπ, hw₀π⟩ := exists_d4_action hsearch hmaps
  have hlin0 : ∀ α ∈ parabolicRoots τ (d4Nodes τ), w₀ • α = permLattice π α := fun α hα => by
    have := smul_eq_of_simple (w := w₀) (u := 1) (π := π) (J := d4Set τ)
      (fun j hj => by rw [one_smul]; exact hw₀π j hj) hα.2
    rwa [one_smul] at this
  have hact : ∀ α ∈ parabolicRoots τ (d4Nodes τ),
      (v⁻¹ * w * v) • α = u • permLattice π α := fun α hα => by
    rw [hw₀, mul_smul, hlin0 α hα]
  have hπ1 := d4_leafPerm_ne_one S i hu hΨ hρw h1 hact
  obtain ⟨hn'M, hn'C, hπn'⟩ := existsConjMonomial S v w
  have hact' : ∀ α ∈ parabolicRoots τ (d4Nodes τ),
      weylQuotientHom τ L
        ⟨(canonicalRep (coxeterSystem τ) L v)⁻¹ * canonicalRep (coxeterSystem τ) L w *
          canonicalRep (coxeterSystem τ) L v, hn'M⟩ • α = u • permLattice π α := by
    intro α hα
    rw [hπn']
    exact hact α hα
  have hlayer : ∀ (ℓ f : ℕ) [Fact ℓ.Prime] [CharP L ℓ], 1 ≤ f →
      LayerComm (parabolicRoots τ (d4Nodes τ))
        (rootSpan τ L (parabolicRoots τ (d4Nodes τ)) ⊓ twistedFixedPoints
          ((canonicalRep (coxeterSystem τ) L v)⁻¹ * canonicalRep (coxeterSystem τ) L w *
            canonicalRep (coxeterSystem τ) L v)
          (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :=
    fun ℓ f _ _ hf => layerComm_of_leafPerm hf hTri hleaf hn'M hn'C hu hπ hπ1 hact'
  have h := commute_of_layer_transport S hFr hΦ hn v (fun α hα => hα.1) hlayer
  rwa [← hΨ] at h

end D4Untwisted

section E6Components

variable {τ : Tag} [hτ : M27Ok τ] [E6Sub τ] {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

private theorem e6_rho_stable (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ}
    (haT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a)) (v : WeylGroup τ)
    (hΨ : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots τ (e6Nodes τ)) :
    ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i := by
  have h6 : 6 ≤ τ.rank := by rcases hτ.isE7E8 with rfl | rfl <;> decide
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

theorem e6_commute (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ}
    (haT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a)) (v : WeylGroup τ)
    (hΨ : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots τ (e6Nodes τ)) :
    ShapeComm S (componentRoots (rootCharHom a) i) := by
  classical
  have hτ' : ∀ t : TwistTag, t.tag ≠ τ := by
    rcases hτ.isE7E8 with rfl | rfl
    · exact twistTag_tag_ne_E7
    · exact twistTag_tag_ne_E8
  obtain ⟨w, hn⟩ := S.D.n_weyl
  obtain ⟨Fr, hFr, hΦ⟩ := S.D.exists_frob_of_untwisted hτ'
  have hρ := e6_rho_stable S haT i v hΨ
  have hw : ∀ γ ∈ (fun α => v • α) '' parabolicRoots τ (e6Nodes τ),
      w • γ ∈ (fun α => v • α) '' parabolicRoots τ (e6Nodes τ) :=
    hΨ ▸ smul_mem_of_rho_eq S (fun γ hγ => hγ.1.1) hρ (fun γ hγ => S.rho_eq_smul hτ' hn hγ)
  obtain ⟨hn'M, -, hπn'⟩ := existsConjMonomial S v w
  have hlayer : ∀ (ℓ f : ℕ) [Fact ℓ.Prime] [CharP L ℓ], 1 ≤ f →
      LayerComm (parabolicRoots τ (e6Nodes τ))
        (rootSpan τ L (parabolicRoots τ (e6Nodes τ)) ⊓ twistedFixedPoints
          ((canonicalRep (coxeterSystem τ) L v)⁻¹ * canonicalRep (coxeterSystem τ) L w *
            canonicalRep (coxeterSystem τ) L v)
          (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) := by
    intro ℓ f _ _ hf
    have hmaps : ∀ α ∈ parabolicRoots τ (e6Nodes τ),
        weylQuotientHom τ L
          ⟨(canonicalRep (coxeterSystem τ) L v)⁻¹ * canonicalRep (coxeterSystem τ) L w *
            canonicalRep (coxeterSystem τ) L v, hn'M⟩ • α ∈ parabolicRoots τ (e6Nodes τ) := by
      intro α hα
      rw [hπn']
      exact smul_inv_mul_mem hw α hα
    exact e6Layer_commutant τ hf hn'M hmaps
  have h := commute_of_layer_transport S hFr hΦ hn v (fun α hα => hα.1) hlayer
  rwa [← hΨ] at h

end E6Components

section Dispatch

private theorem shapeComm_of_d4_E6 {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup .E6 L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0) {a : Fin Tag.E6.rank → Lˣ}
    (hT : rootDiagUnit .E6 a ∈ S.D.torus) (hTp : rootDiagUnit .E6 a ^ p = 1)
    (i : KernelComponent (rootCharHom a))
    (hr : compRank (componentRoots (rootCharHom a) i) = 4)
    (hc : (componentRoots (rootCharHom a) i).ncard = 24)
    (hnin : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    (hTw : ∀ {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup .E6 L p)
      (_ : ∃ (t : TwistTag) (h : t.tag = .E6) (Fr : L →+* L), (∀ c, Fr c = c ^ S.D.q) ∧
        ∀ g, S.D.Φ g = diagramAt .E6 L t h * Units.map (entrywiseHom Fr) g *
          (diagramAt .E6 L t h)⁻¹)
      {a : Fin Tag.E6.rank → Lˣ} (i : KernelComponent (rootCharHom a)) (v : WeylGroup .E6),
      componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots .E6 (d4Nodes .E6) →
      (∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i) →
      ¬ twistInner (componentRoots (rootCharHom a) i) (S.ρ : (Fin Tag.E6.rank → ℤ) → _) →
      CFSG.IsQuasisimple ↥(rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ⊓ S.D.model) ∧
      ∀ z ∈ rootSpan Tag.E6 L (componentRoots (rootCharHom a) i),
        (∀ u ∈ rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ⊓ S.D.model, z * u = u * z) →
        ∀ g ∈ rootSpan Tag.E6 L (componentRoots (rootCharHom a) i), Commute z g) :
    (∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i) ∧
      ShapeComm S (componentRoots (rootCharHom a) i) := by
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
    exact ⟨hρ, d4_commute_untw d4Base_E6 d4TrialityLayer_E6 leafSwap_E6 S hFr hΦ' hn
      (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ' hn hγ) i v hv hρ hnin⟩
  · rw [hs, Function.iterate_one] at hnin
    exact ⟨hρ, hTw S ⟨t, ht, Fr, hFr, hΦ⟩ i v hv hρ hnin⟩

private theorem shapeComm_of_d4_E7 {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup .E7 L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0) {a : Fin Tag.E7.rank → Lˣ}
    (hT : rootDiagUnit .E7 a ∈ S.D.torus) (hTp : rootDiagUnit .E7 a ^ p = 1)
    (i : KernelComponent (rootCharHom a))
    (hr : compRank (componentRoots (rootCharHom a) i) = 4)
    (hc : (componentRoots (rootCharHom a) i).ncard = 24)
    (hnin : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E7.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    (∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i) ∧
      ShapeComm S (componentRoots (rootCharHom a) i) := by
  obtain ⟨v, hv, hρ⟩ := S.d4_pinnedT_of_prime hp hpL facts_E7 kacCount_E7_four (by decide)
    (by decide)
    (fun y hy => far_d4_E7 y fun z hz => by
      have h := hy z hz
      rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
    ⟨some 0, by decide⟩ (lt_of_eq_of_lt kacCount_far_E7 (by decide)) hT hTp i hr hc
  obtain ⟨Fr, hFr, hΦ⟩ := S.D.exists_frob_of_untwisted twistTag_tag_ne_E7
  obtain ⟨w, hn⟩ := S.D.n_weyl
  exact ⟨hρ, d4_commute_untw d4Base_E7 d4TrialityLayer_E7 leafSwap_E7 S hFr hΦ hn
    (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ hn hγ) i v hv hρ hnin⟩

private theorem shapeComm_of_d4_E8 {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup .E8 L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0) {a : Fin Tag.E8.rank → Lˣ}
    (hT : rootDiagUnit .E8 a ∈ S.D.torus) (hTp : rootDiagUnit .E8 a ^ p = 1)
    (i : KernelComponent (rootCharHom a))
    (hr : compRank (componentRoots (rootCharHom a) i) = 4)
    (hc : (componentRoots (rootCharHom a) i).ncard = 24)
    (hnin : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E8.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    (∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i) ∧
      ShapeComm S (componentRoots (rootCharHom a) i) := by
  obtain ⟨v, hv, hρ⟩ := S.d4_pinnedT_of_prime hp hpL facts_E8 kacCount_E8_four (by decide)
    (by decide)
    (fun y hy => far_d4_E8 y fun z hz => by
      have h := hy z hz
      rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
    ⟨some 0, by decide⟩ (lt_of_eq_of_lt kacCount_far_E8 (by decide)) hT hTp i hr hc
  obtain ⟨Fr, hFr, hΦ⟩ := S.D.exists_frob_of_untwisted twistTag_tag_ne_E8
  obtain ⟨w, hn⟩ := S.D.n_weyl
  exact ⟨hρ, d4_commute_untw d4Base_E8 d4TrialityLayer_E8 leafSwap_E8 S hFr hΦ hn
    (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ hn hγ) i v hv hρ hnin⟩

private theorem shapeComm_of_d4Shape {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hTp : rootDiagUnit τ a ^ p = 1)
    (ha1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hr : compRank (componentRoots (rootCharHom a) i) = 4)
    (hc : (componentRoots (rootCharHom a) i).ncard = 24)
    (hnin : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    (hTw : ∀ {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup .E6 L p)
      (_ : ∃ (t : TwistTag) (h : t.tag = .E6) (Fr : L →+* L), (∀ c, Fr c = c ^ S.D.q) ∧
        ∀ g, S.D.Φ g = diagramAt .E6 L t h * Units.map (entrywiseHom Fr) g *
          (diagramAt .E6 L t h)⁻¹)
      {a : Fin Tag.E6.rank → Lˣ} (i : KernelComponent (rootCharHom a)) (v : WeylGroup .E6),
      componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots .E6 (d4Nodes .E6) →
      (∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i) →
      ¬ twistInner (componentRoots (rootCharHom a) i) (S.ρ : (Fin Tag.E6.rank → ℤ) → _) →
      CFSG.IsQuasisimple ↥(rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ⊓ S.D.model) ∧
      ∀ z ∈ rootSpan Tag.E6 L (componentRoots (rootCharHom a) i),
        (∀ u ∈ rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ⊓ S.D.model, z * u = u * z) →
        ∀ g ∈ rootSpan Tag.E6 L (componentRoots (rootCharHom a) i), Commute z g) :
    (∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i) ∧
      ShapeComm S (componentRoots (rootCharHom a) i) := by
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
  | E6 => exact shapeComm_of_d4_E6 S hp hpL hT hTp i hr hc hnin hTw
  | E7 => exact shapeComm_of_d4_E7 S hp hpL hT hTp i hr hc hnin
  | E8 => exact shapeComm_of_d4_E8 S hp hpL hT hTp i hr hc hnin

private theorem shapeComm_of_e6Shape {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup τ L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hTp : rootDiagUnit τ a ^ p = 1)
    (ha1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (h6 : compRank (componentRoots (rootCharHom a) i) = 6)
    (hc6 : (componentRoots (rootCharHom a) i).ncard = 72) :
    (∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i) ∧
      ShapeComm S (componentRoots (rootCharHom a) i) := by
  cases τ with
  | G2 =>
    have hle := compRank_le_rank (componentRoots (rootCharHom a) i)
    rw [h6] at hle
    exact absurd hle (by decide)
  | F4 =>
    have hle := compRank_le_rank (componentRoots (rootCharHom a) i)
    rw [h6] at hle
    exact absurd hle (by decide)
  | D4 =>
    have hle := compRank_le_rank (componentRoots (rootCharHom a) i)
    rw [h6] at hle
    exact absurd hle (by decide)
  | E6 => exact absurd (rootDiagUnit_eq_one_of_ncard i (by rw [hc6]; rfl)) ha1
  | E7 =>
    obtain ⟨v, hv⟩ := S.e6_pinnedT_of_prime hp hpL facts_E7 kacCount_E7_six (by decide)
      (by decide) hTp i h6 hc6
    exact ⟨e6_rho_stable S hT i v hv, e6_commute S hT i v hv⟩
  | E8 =>
    obtain ⟨v, hv⟩ := S.e6_pinnedT_of_prime hp hpL facts_E8 kacCount_E8_six (by decide)
      (by decide) hTp i h6 hc6
    exact ⟨e6_rho_stable S hT i v hv, e6_commute S hT i v hv⟩

theorem shapeComm_of_layer {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup τ L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hTp : rootDiagUnit τ a ^ p = 1)
    (ha1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hk : (twistKind S.ρ (rootCharHom a) i = .twoD ∧
            compRank (componentRoots (rootCharHom a) i) = 4) ∨
          twistKind S.ρ (rootCharHom a) i = .exc)
    (hTw : ∀ {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup .E6 L p)
      (_ : ∃ (t : TwistTag) (h : t.tag = .E6) (Fr : L →+* L), (∀ c, Fr c = c ^ S.D.q) ∧
        ∀ g, S.D.Φ g = diagramAt .E6 L t h * Units.map (entrywiseHom Fr) g *
          (diagramAt .E6 L t h)⁻¹)
      {a : Fin Tag.E6.rank → Lˣ} (i : KernelComponent (rootCharHom a)) (v : WeylGroup .E6),
      componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots .E6 (d4Nodes .E6) →
      (∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i) →
      ¬ twistInner (componentRoots (rootCharHom a) i) (S.ρ : (Fin Tag.E6.rank → ℤ) → _) →
      CFSG.IsQuasisimple ↥(rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ⊓ S.D.model) ∧
      ∀ z ∈ rootSpan Tag.E6 L (componentRoots (rootCharHom a) i),
        (∀ u ∈ rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ⊓ S.D.model, z * u = u * z) →
        ∀ g ∈ rootSpan Tag.E6 L (componentRoots (rootCharHom a) i), Commute z g) :
    (∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i) ∧
      ShapeComm S (componentRoots (rootCharHom a) i) := by
  rcases hk with ⟨hk2, hr⟩ | hk
  · obtain ⟨hnin, -, hcard⟩ := twoD_kind_unpack hk2
    have hc : (componentRoots (rootCharHom a) i).ncard = 24 := by rw [hcard, hr]
    exact shapeComm_of_d4Shape S hp hpL hT hTp ha1 i hr hc hnin hTw
  · obtain ⟨hnin, hA | ⟨hr, hc, -⟩⟩ := exc_kind hk
    · exact shapeComm_of_e6Shape S hp hpL hT hTp ha1 i hA.1 hA.2
    · exact shapeComm_of_d4Shape S hp hpL hT hTp ha1 i hr hc hnin hTw

end Dispatch

end CFSG.LocalAnalysis.GLTheoremA.T263.DX

end
