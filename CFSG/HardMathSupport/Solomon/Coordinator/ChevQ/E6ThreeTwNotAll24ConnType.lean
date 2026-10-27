module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnComp
public import CFSG.LocalAnalysis.GLTheoremA.CatC.LieCompHolds
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerBridge
import CFSG.LocalAnalysis.GLTheoremA.S10.CaseGamma
import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.Transport
import CFSG.HardMathSupport.Dickson.Bal207.NoThreeCover

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

namespace KSNotAll24

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Seitz
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Yardstones.Md0ec50421ce4
  CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp (catEquiv_twistedE6_of_field)
open CFSG.HardMathSupport.Solomon.LocalBalance

section Chev

set_option linter.unusedSectionVars false


theorem isChevSimple_of_mulEquiv {r : ℕ} {S S' : Type} [Group S] [Group S'] (e : S ≃* S')
    (h : IsChevSimple r S) : IsChevSimple r S' := by
  rcases h with ⟨i, hi, ⟨e'⟩⟩ | ⟨i, hi, ⟨e'⟩⟩
  · exact Or.inl ⟨i, hi, ⟨e.symm.trans e'⟩⟩
  · exact Or.inr ⟨i, hi, ⟨e.symm.trans e'⟩⟩

theorem component_isChevSimple (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ)
    (hK3 : ringChar K ≠ 3) (hσ : ∀ c, σ c = c ^ q) (hKq : Nat.card K = q ^ 2) (hq2 : 2 ≤ q)
    {f : MulAut (twistedE6RootGroup K σ)} (hf3 : f ^ 3 = 1)
    {J : Subgroup (twistedE6RootGroup K σ)}
    (hJ : CFSG.Open.IsComponentOf J (fixedPoints (Subgroup.zpowers f)))
    (h3J : 3 ∣ Nat.card (J ⧸ Subgroup.center J)) :
    IsChevSimple (ringChar K) (J ⧸ Subgroup.center J) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨hp, f', hf', hqf⟩ := prime_ringChar_and_eq_pow_of_card_sq K q hKq hq2
  let qp : TauCeti.PrimePower := ⟨ringChar K, f', hp, by omega⟩
  have hqp : qp.card = q := by
    rw [TauCeti.PrimePower.card_def]
    exact hqf.symm
  have hv : (TauCeti.LieTypeIndex.twistedE6 qp).Valid := TauCeti.LieTypeIndex.valid_twistedE6 qp
  obtain ⟨e⟩ := catEquiv_twistedE6_of_field qp hv K (hqp ▸ hKq) σ (hqp ▸ hσ)
  obtain ⟨-, hsimple⟩ := finite_isSimpleGroup_cat_twistedE6 hv
  haveI := hsimple
  haveI : IsSimpleGroup (twistedE6RootGroup K σ) := e.symm.isSimpleGroup
  have hZ := exceptional_fixed_center_trivial TwistTag.E6 K σ
  have hnc : ∃ a b : twistedE6RootGroup K σ, a * b ≠ b * a :=
    CFSG.HardMathSupport.Dickson.Sec6.I923.exists_noncomm_of_center_bot hZ
  have hfix : CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns.fixSub f =
      fixedPoints (Subgroup.zpowers f) := by
    rw [← fixSubgroup_eq_fixedPoints]
    ext x
    exact Iff.rfl
  have hJ3 : GLAPComponent 3
      (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns.fixSub f) J :=
    CFSG.LocalAnalysis.GLTheoremA.S10.glaPComponent_of_quasisimple Nat.prime_three
      (by rw [hfix]; exact hJ.2.1) hJ.2.2 h3J
  obtain ⟨hD, -⟩ := CFSG.LocalAnalysis.GLTheoremA.lieComp_holds (twistedE6RootGroup K σ)
    inferInstance hnc ⟨_, hv⟩ ⟨e.symm⟩ f hf3 J hJ3
  have hchar : lieIndexChar (TauCeti.LieTypeIndex.twistedE6 qp) = ringChar K := rfl
  have hchev := hD.chev
  rw [hchar] at hchev
  let φ : ↥J →* barOf 3 J := QuotientGroup.mk' (GLAPPrimeCore 3 ↥J)
  have hφ : Function.Surjective φ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥J)
  have hperf : commutator ↥J = ⊤ := (Subgroup.isPerfect_iff.2
    (CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJ3)).1
  have hbarQ : CFSG.Open.IsQuasisimple (barOf 3 J) := isQuasisimple_quotient_of_glaPComponent hJ3
  haveI : Nontrivial (barOf 3 J ⧸ Subgroup.center (barOf 3 J)) := hbarQ.2.toNontrivial
  have hkφ : φ.ker ≤ Subgroup.center ↥J :=
    CFSG.HardMathSupport.Dickson.Bal207.Small.ker_le_center_of_surjective hJ.2.2 φ hφ
  obtain ⟨g⟩ := LieComp.nonempty_centralQuotient_mulEquiv hperf φ hφ hkφ
  exact isChevSimple_of_mulEquiv g.symm hchev

theorem noPlane3_of_mulEquiv {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q')
    (h : NoPlane3 Q) : NoPlane3 Q' := by
  intro D hD hcard
  let φ : MulAut Q' ≃* MulAut Q := (MulAut.congr e).symm
  have hD' : CFSG.Open.IsElemAbelian 3 (D.map φ.toMonoidHom) :=
    CFSG.SectionRank.isElemAbelian_map hD φ.toMonoidHom
  apply h _ hD'
  rw [Subgroup.card_map_of_injective φ.injective]
  exact hcard

theorem chevSimple_odd {r : ℕ} (hr2 : r ≠ 2) (hr3 : r ≠ 3) {S : Type} [Group S]
    (h : IsChevSimple r S) :
    (∃ d : TauCeti.ValidLieTypeIndex,
        Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) ∧ 3 ≠ d.1.characteristic ∧
          ¬ AGLEmbeddingD2.IsD2SeitzException 3 d.1) ∨ NoPlane3 S := by
  rcases h with ⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩
  · cases i with
    | lie d =>
      have hd : d.1.characteristic = r := hi
      refine Or.inl ⟨d, ⟨e⟩, by omega, ?_⟩
      intro hexc
      rcases hexc with ⟨-, h2⟩ | ⟨h35, -⟩
      · rcases h2 with ⟨q, hq, -, hdq⟩ | ⟨q, hq, -, hdq⟩ | ⟨q, hq, -, hdq⟩ |
          ⟨q, hq, -, hdq | hdq⟩ | hdt
        · rw [hdq] at hd; simp at hd; omega
        · rw [hdq] at hd; simp at hd; omega
        · rw [hdq] at hd; simp at hd; omega
        · rw [hdq] at hd; simp at hd; omega
        · rw [hdq] at hd; simp at hd; omega
        · rw [hdt] at hd; simp at hd; omega
      · omega
    | alternating n hn => exact hi.elim
    | cyclic p hp => exact hi.elim
    | sporadic s => exact hi.elim
  · cases i with
    | alternating n hn =>
      rcases hi with ⟨h5, h25⟩ | ⟨h6, h23⟩ | ⟨h8, h2⟩
      · subst h5
        exact Or.inr (noPlane3_of_mulEquiv e.symm noPlane3_alternatingGroup_five)
      · omega
      · omega
    | lie d =>
      exfalso
      obtain ⟨d, hdv⟩ := d
      cases d with
      | A rank q =>
        rcases rank with _ | _ | rank
        · simp [ambiguousChev] at hi
        · simp [ambiguousChev] at hi; omega
        · simp [ambiguousChev] at hi
      | twistedA rank q =>
        rcases rank with _ | _ | _ | _ | rank
        · simp [ambiguousChev] at hi
        · simp [ambiguousChev] at hi
        · simp [ambiguousChev] at hi; omega
        · simp [ambiguousChev] at hi; omega
        · simp [ambiguousChev] at hi
      | _ => simp [ambiguousChev] at hi
    | cyclic p hp => exact hi.elim
    | sporadic s => exact hi.elim

end Chev

end KSNotAll24

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
