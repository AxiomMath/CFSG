module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExcTw
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsTwAux.NormGroup

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KD4L
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints d4Nodes)


@[expose] def SsQB (ℓ : ℕ) {G : Type*} [Group G] (P : Subgroup G) : Prop :=
  CFSG.IsQuasisimple ↥P ∧ SsBig ℓ P

theorem SsQB.map_conj {ℓ : ℕ} {G : Type*} [Group G] {P : Subgroup G} (h : SsQB ℓ P) (g : G) :
    SsQB ℓ (P.map (MulAut.conj g).toMonoidHom) :=
  ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (P.equivMapOfInjective _ (MulAut.conj g).injective) h.1,
    h.2.map _ (MulAut.conj g).injective⟩

section Gen

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem ssTw_layer_untw_adj (S : LangSetup τ L p) {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ]
    (hq : S.D.q = ℓ ^ f) {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q)
    (hΦ : S.D.Φ = Units.map (entrywiseHom Fr)) {w : WeylGroup τ}
    (hn : S.D.n = canonicalRep (coxeterSystem τ) L w) (v : WeylGroup τ) (J : Set (Fin τ.rank))
    (Q : Subgroup (ModGL τ L) → Prop)
    (hQ : ∀ (P : Subgroup (ModGL τ L)) (g : ModGL τ L), Q P →
      Q (P.map (MulAut.conj g).toMonoidHom))
    (hlayer : ∀ (n : ModGL τ L) (hn : n ∈ monomialSubgroup τ L), n ∈ adjointGroup τ L →
      weylQuotientHom τ L ⟨n, hn⟩ = v⁻¹ * w * v →
      Q (rootSpan τ L (parabolicRoots τ J) ⊓
        twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))))) :
    Q (rootSpan τ L ((fun α => v • α) '' parabolicRoots τ J) ⊓ S.D.model) := by
  classical
  have hFr' : Fr = iterateFrobenius L ℓ f := by
    ext x
    rw [hFr, hq, iterateFrobenius_def]
  set nv := canonicalRep (coxeterSystem τ) L v with hnv
  set nw := canonicalRep (coxeterSystem τ) L w with hnw
  have hroots : ∀ α ∈ parabolicRoots τ J, IsRoot τ α := fun α hα => hα.1
  have hmodel : rootSpan τ L ((fun α => v • α) '' parabolicRoots τ J) ⊓ S.D.model =
      rootSpan τ L ((fun α => v • α) '' parabolicRoots τ J) ⊓
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
  have hn'C : nv⁻¹ * nw * nv ∈ adjointGroup τ L :=
    mul_mem (mul_mem (inv_mem (canonicalRep_mem_adjointGroup _ L v))
      (canonicalRep_mem_adjointGroup _ L w)) (canonicalRep_mem_adjointGroup _ L v)
  have hπ : weylQuotientHom τ L ⟨nv⁻¹ * nw * nv, hn'M⟩ = v⁻¹ * w * v := by
    have e : (⟨nv⁻¹ * nw * nv, hn'M⟩ : monomialSubgroup τ L) =
        (⟨nv, hnvM⟩ : monomialSubgroup τ L)⁻¹ * ⟨nw, hnwM⟩ * ⟨nv, hnvM⟩ := rfl
    rw [e, map_mul, map_mul, map_inv, weylQuotientHom_eq (mapsRootLines_canonicalRep v),
      weylQuotientHom_eq (mapsRootLines_canonicalRep w)]
  exact hQ _ nv (hlayer _ hn'M hn'C hπ)

theorem ssTw_layer_tw_adj (S : LangSetup Tag.E6 L p) {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ]
    (hq : S.D.q = ℓ ^ f) {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q)
    (hΦ : ∀ g, S.D.Φ g = e6Diagram L * Units.map (entrywiseHom Fr) g * (e6Diagram L)⁻¹)
    {w : WeylGroup Tag.E6} (hn : S.D.n = canonicalRep (coxeterSystem Tag.E6) L w)
    (v : WeylGroup Tag.E6) (J : Set (Fin Tag.E6.rank))
    (Q : Subgroup (ModGL Tag.E6 L) → Prop)
    (hQ : ∀ (P : Subgroup (ModGL Tag.E6 L)) (g : ModGL Tag.E6 L), Q P →
      Q (P.map (MulAut.conj g).toMonoidHom))
    (hlayer : ∀ (n : ModGL Tag.E6 L) (hn : n ∈ monomialSubgroup Tag.E6 L),
      n ∈ adjointGroup Tag.E6 L → weylQuotientHom Tag.E6 L ⟨n, hn⟩ = v⁻¹ * w * e6WeylTwist v →
      Q (rootSpan Tag.E6 L (parabolicRoots Tag.E6 J) ⊓
        twistedFixedPoints (n * e6Diagram L)
          (Units.map (entrywiseHom (iterateFrobenius L ℓ f))))) :
    Q (rootSpan Tag.E6 L ((fun α => v • α) '' parabolicRoots Tag.E6 J) ⊓ S.D.model) := by
  classical
  have hFr' : Fr = iterateFrobenius L ℓ f := by
    ext x
    rw [hFr, hq, iterateFrobenius_def]
  have hroots : ∀ α ∈ parabolicRoots Tag.E6 J, IsRoot Tag.E6 α := fun α hα => hα.1
  set nv := canonicalRep (coxeterSystem Tag.E6) L v with hnv
  set nw := canonicalRep (coxeterSystem Tag.E6) L w with hnw
  set nδ := canonicalRep (coxeterSystem Tag.E6) L (e6WeylTwist v) with hnδ
  have hnvM := canonicalRep_mem_monomialSubgroup L v
  have hnwM := canonicalRep_mem_monomialSubgroup L w
  have hnδM := canonicalRep_mem_monomialSubgroup L (e6WeylTwist v)
  have hn'M : nv⁻¹ * nw * nδ ∈ monomialSubgroup Tag.E6 L :=
    mul_mem (mul_mem (inv_mem hnvM) hnwM) hnδM
  have hn'C : nv⁻¹ * nw * nδ ∈ adjointGroup Tag.E6 L :=
    mul_mem (mul_mem (inv_mem (canonicalRep_mem_adjointGroup _ L v))
      (canonicalRep_mem_adjointGroup _ L w)) (canonicalRep_mem_adjointGroup _ L (e6WeylTwist v))
  have hπn' : weylQuotientHom Tag.E6 L ⟨nv⁻¹ * nw * nδ, hn'M⟩ = v⁻¹ * w * e6WeylTwist v := by
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
  have hmodel : rootSpan Tag.E6 L ((fun α => v • α) '' parabolicRoots Tag.E6 J) ⊓ S.D.model =
      rootSpan Tag.E6 L ((fun α => v • α) '' parabolicRoots Tag.E6 J) ⊓
        twistedFixedPoints (nw * e6Diagram L)
          (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) := by
    ext x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hx, -, hxF⟩
      refine ⟨hx, ?_⟩
      have hxF' : S.D.n * S.D.Φ x * S.D.n⁻¹ = x := hxF
      rw [hn, hΦ, hFr'] at hxF'
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
      rw [hn, hΦ, hFr']
      calc nw * (e6Diagram L * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x *
            (e6Diagram L)⁻¹) * nw⁻¹ = (nw * e6Diagram L) *
              Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x * (nw * e6Diagram L)⁻¹ := by
            group
        _ = x := hxF'
  rw [hmodel, rootSpan_inf_twistedFixedPoints_smul _ v (nw * e6Diagram L) hroots, ← hnv, hnPv]
  exact hQ _ nv (hlayer _ hn'M hn'C hπn')

theorem ssTw_layer_untw (S : LangSetup τ L p) {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ]
    (hq : S.D.q = ℓ ^ f) {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q)
    (hΦ : S.D.Φ = Units.map (entrywiseHom Fr)) {w : WeylGroup τ}
    (hn : S.D.n = canonicalRep (coxeterSystem τ) L w) (v : WeylGroup τ) (J : Set (Fin τ.rank))
    (Q : Subgroup (ModGL τ L) → Prop)
    (hQ : ∀ (P : Subgroup (ModGL τ L)) (g : ModGL τ L), Q P →
      Q (P.map (MulAut.conj g).toMonoidHom))
    (hlayer : ∀ (n : ModGL τ L) (hn : n ∈ monomialSubgroup τ L),
      weylQuotientHom τ L ⟨n, hn⟩ = v⁻¹ * w * v →
      Q (rootSpan τ L (parabolicRoots τ J) ⊓
        twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))))) :
    Q (rootSpan τ L ((fun α => v • α) '' parabolicRoots τ J) ⊓ S.D.model) :=
  ssTw_layer_untw_adj S hq hFr hΦ hn v J Q hQ fun n hn _ hw => hlayer n hn hw

theorem ssTw_layer_tw (S : LangSetup Tag.E6 L p) {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ]
    (hq : S.D.q = ℓ ^ f) {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q)
    (hΦ : ∀ g, S.D.Φ g = e6Diagram L * Units.map (entrywiseHom Fr) g * (e6Diagram L)⁻¹)
    {w : WeylGroup Tag.E6} (hn : S.D.n = canonicalRep (coxeterSystem Tag.E6) L w)
    (v : WeylGroup Tag.E6) (J : Set (Fin Tag.E6.rank))
    (Q : Subgroup (ModGL Tag.E6 L) → Prop)
    (hQ : ∀ (P : Subgroup (ModGL Tag.E6 L)) (g : ModGL Tag.E6 L), Q P →
      Q (P.map (MulAut.conj g).toMonoidHom))
    (hlayer : ∀ (n : ModGL Tag.E6 L) (hn : n ∈ monomialSubgroup Tag.E6 L),
      weylQuotientHom Tag.E6 L ⟨n, hn⟩ = v⁻¹ * w * e6WeylTwist v →
      Q (rootSpan Tag.E6 L (parabolicRoots Tag.E6 J) ⊓
        twistedFixedPoints (n * e6Diagram L)
          (Units.map (entrywiseHom (iterateFrobenius L ℓ f))))) :
    Q (rootSpan Tag.E6 L ((fun α => v • α) '' parabolicRoots Tag.E6 J) ⊓ S.D.model) :=
  ssTw_layer_tw_adj S hq hFr hΦ hn v J Q hQ fun n hn _ hw => hlayer n hn hw

end Gen

end CFSG.HardMathSupport.Dickson.Sec6
