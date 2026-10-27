module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPF4Small
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPFinal
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightTorBase
import CFSG.RankThree.Chevalley.SteinbergCFEvenF4StandardParabolic

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG CFSG.Open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits CFSG.ComponentClassification.CatLeafProof
  CFSG.Timmesfeld CFSG.Timmesfeld.LevisExtras CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Timmesfeld.RootAut
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.ClassicalInvolution.WeakCT (exists_b2Hom hom_block_eq spBlock)
open CFSG.SeitzReduction.SymplecticPilot (isSimpleGroup_commutator_statedSp_two)
open scoped MatrixGroups commutatorElement

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

namespace CompsPF4B2Two

theorem lieCompData_of_range_simple {q : ℕ} {X : Type} [Group X] [Finite X]
    (hX : LieFactorData q X) (hs : IsSimpleGroup X) {H : Type} [Group H] (Φ : X →* H)
    {R : Subgroup H} (hR : R = Φ.range) (hR1 : R ≠ ⊥) : LieCompData q ↥R := by
  subst hR
  have hker : Φ.ker = ⊥ := by
    rcases hs.eq_bot_or_eq_top_of_normal Φ.ker with h | h
    · exact h
    · exfalso
      apply hR1
      rw [Subgroup.eq_bot_iff_forall]
      rintro _ ⟨x, rfl⟩
      exact MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top x)
  exact hX.lieCompData Φ.rangeRestrict Φ.rangeRestrict_surjective (by rw [MonoidHom.ker_rangeRestrict, hker]; exact bot_le)

end CompsPF4B2Two

section Cover


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
  {ta : Fin τ.rank → Lˣ}

theorem exists_inner_cover_derived_two (hT : rootDiagUnit τ ta ∈ S.D.torus)
    (i : KernelComponent (rootCharHom ta))
    (hinner : twistInner (componentRoots (rootCharHom ta) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom ta) i)]))
    (hQ : S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i) < 3) :
    ∃ (K' : Subfield L) (_ : Finite ↥K') (C D : Subgroup (ModGL τ ↥K')),
      C = componentRootSpan K' (rootCharHom ta) i ∧ D = ⁅C, C⁆ ∧ Nat.card ↥K' = 2 ∧
      ∃ f : ↥D →* ModGL τ L,
        rationalComponent S.ρ S.Γ (rootCharHom ta) i ≤ f.range ∧
        f.ker ≤ Subgroup.center ↥D ∧
        (⁅D, D⁆ = D → f.range ≤ rationalComponent S.ρ S.Γ (rootCharHom ta) i) := by
  classical
  obtain ⟨hs0, hs, hmin⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i) with hsdef
  haveI : NeZero s := ⟨hs0.ne'⟩
  obtain ⟨σ, z, hσ, hnorm, hz⟩ := exists_untwistT S hT i hs0 hinner
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : CharP L r := hchar
  have hσ' : ∀ c, σ c = c ^ (r ^ (e * s)) := fun c => by rw [hσ, hq, ← pow_mul]
  obtain ⟨hfinK, hKcard⟩ := finite_card_fixSubfield (L := L) (r := r) (n := e * s)
    (Nat.mul_pos he hs0) σ hσ'
  have hK2 : Nat.card ↥(fixSubfield σ) = 2 := by
    have h2 : 2 ≤ r ^ (e * s) :=
      le_trans hr.two_le (Nat.le_self_pow (Nat.mul_pos he hs0).ne' r)
    have h3 : r ^ (e * s) < 3 := by rw [pow_mul, ← hq]; exact hQ
    rw [hKcard]
    omega
  have hsL : ∃ u : Lˣ, u ^ 2 ≠ 1 := by
    obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset ({0, 1, -1} : Finset L)
    have hc0 : c ≠ 0 := fun h => hc (by simp [h])
    refine ⟨Units.mk0 c hc0, fun h => hc ?_⟩
    have h2 : c ^ 2 = 1 := by simpa using congrArg (fun x : Lˣ => (x : L)) h
    have h3 : (c - 1) * (c + 1) = 0 := by linear_combination h2
    rcases mul_eq_zero.1 h3 with h | h
    · simp [sub_eq_zero.1 h]
    · simp [eq_neg_of_add_eq_zero_left h]
  have hF : ∀ d : L, σ d = d → d ≠ 0 → d = 1 := by
    intro d hd hd0
    let : Fintype (fixSubfield σ) := Fintype.ofFinite _
    have hcard : Fintype.card (fixSubfield σ) = 2 := by
      rw [← Nat.card_eq_fintype_card]; exact hK2
    have hdK : d ∈ fixSubfield σ := hd
    have h1 := FiniteField.pow_card_sub_one_eq_one (⟨d, hdK⟩ : fixSubfield σ)
      (fun h => hd0 (congrArg Subtype.val h))
    rw [hcard] at h1
    simpa using congrArg Subtype.val h1
  set C := componentRootSpan (fixSubfield σ) (rootCharHom ta) i with hCdef
  have hY : ∀ g g' : ModGL τ L, g ∈ rootSpan τ L (componentRoots (rootCharHom ta) i) →
      g' ∈ rootSpan τ L (componentRoots (rootCharHom ta) i) →
      frobGL σ g * g⁻¹ ∈ (outerOrbitFamily S hT i hs hmin).Z →
      frobGL σ g' * g'⁻¹ ∈ (outerOrbitFamily S hT i hs hmin).Z →
      ⁅g, g'⁆ ∈ (⁅C, C⁆).map (baseChangeGL (fixSubfield σ).subtype) := by
    intro g g' hg hg' hgZ hgZ'
    have := orbit_commutator_mem_commutator_CQT S hT i hs hmin σ hsL hF hg hg' hgZ hgZ'
    rwa [CQ_eq_map, ← Subgroup.map_commutator] at this
  obtain ⟨f, hf1, hker, hf2⟩ := rationalComponent_eq_rangeT S hT i hs hmin σ z hnorm hz
    ⁅C, C⁆ (Subgroup.commutator_le_self _ |>.trans le_rfl) hY
  exact ⟨fixSubfield σ, hfinK, C, ⁅C, C⁆, rfl, rfl, hK2, f, hf1, hker, hf2⟩

end Cover

section Main


theorem lieCompData_of_f4B2_two {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup Tag.F4 L p₀) {a : Fin Tag.F4.rank → Lˣ}
    (hT : rootDiagUnit Tag.F4 a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (v : WeylGroup Tag.F4)
    (hroots : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots Tag.F4 f4LeviB2)
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    (hQ : S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) < 3)
    (hqs : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    LieCompData (ringChar L) ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  obtain ⟨K', hfin, C, D, hC, hD, hcard, f, hf1, hker, hf2⟩ :=
    exists_inner_cover_derived_two S hT i hinner hQ
  haveI : Fintype ↥K' := Fintype.ofFinite _
  have hcard' : Fintype.card ↥K' = 2 := by rw [← Nat.card_eq_fintype_card]; exact hcard
  have hch : ringChar L = 2 := by
    have h2 := ringChar_eq_of_natCard_eq_pow Nat.prime_two (K := ↥K') (f := 1)
      (by rw [hcard]; norm_num) Nat.one_pos
    rw [← ringChar_subfield' K', h2]
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (f4Datum ↥K').isFiniteType
    (Dv := (f4Datum ↥K').divisible) rfl
  obtain ⟨Cc, -, hCc⟩ := f4_commutatorFormula ↥K' O
  have hE := f4_chevalleyExtras ↥K' O Cc hCc
  choose ρF hρFi hρFr hρFv using exists_rankOne_param hE
  obtain ⟨φ, hφl, hφs⟩ : ∃ φ : StatedSp 2 ↥K' →* adjointGroup .F4 ↥K',
      φ.comp (spBlock ↥K' 1) = ρF (f4Node 1) ∧ φ.comp (spBlock ↥K' 0) = ρF (f4Node 2) := by
    obtain ⟨φ, e, -, he1, he2, he3, he4, hφ⟩ :=
      exists_b2Hom hE (s := f4Node 2) (l := f4Node 1) rfl f4_cartan_21 f4_cartan_12
    obtain ⟨hb0, hb1⟩ := hom_block_eq he1 he2 he3 he4 hφ (hρFv (f4Node 2)) (hρFv (f4Node 1))
    exact ⟨φ, hb1, hb0⟩
  have hφrange : φ.range = rankOne (f4Datum ↥K').rootGroup (f4Node 1) ⊔
      rankOne (f4Datum ↥K').rootGroup (f4Node 2) := by
    rw [ClassicalInvolution.Q3.Q3V.range_eq_sup_of_spBlocks hφs hφl, hρFr, hρFr, sup_comm]
  set n := canonicalRep (coxeterSystem Tag.F4) ↥K' v with hn
  set ψ : StatedSp 2 ↥K' →* ModGL Tag.F4 ↥K' :=
    (MulAut.conj n).toMonoidHom.comp ((adjointGroup .F4 ↥K').subtype.comp φ) with hψ
  have hψrange : ψ.range = C := by
    have hmap := (canonical_weyl_root_transport Tag.F4 ↥K').1 v (parabolicRoots Tag.F4 f4LeviB2)
      (fun α hα => hα.1)
    have hsub : subsystemGroup Tag.F4 ↥K' f4LeviB2 =
        rootSpan Tag.F4 ↥K' (parabolicRoots Tag.F4 f4LeviB2) :=
      CFSG.RankThree.Chevalley.subsystemGroup_eq_iSup_rootSubgroup (τ := Tag.F4) (J := f4LeviB2) ↥K'
    have hCeq : C = rootSpan Tag.F4 ↥K' ((fun α => v • α) '' parabolicRoots Tag.F4 f4LeviB2) := by
      rw [hC]
      show rootSpan Tag.F4 ↥K' (componentRoots (rootCharHom a) i) = _
      rw [hroots]
    rw [hCeq, ← hmap, ← hsub, ← map_subtype_sup_b2, ← hφrange, hψ, MonoidHom.range_comp,
      MonoidHom.range_comp]
  set X' : Subgroup (StatedSp 2 ↥K') := commutator (StatedSp 2 ↥K') with hX'
  have hDmap : D = X'.map ψ := by
    rw [hD, ← hψrange, MonoidHom.range_eq_map, ← Subgroup.map_commutator, hX', commutator_def]
  have hX : LieFactorData 2 ↥X' := spFourTwoFacts_holds ↥K' hcard'
  have hs : IsSimpleGroup ↥X' := isSimpleGroup_commutator_statedSp_two hcard
  have hXp : ⁅X', X'⁆ = X' := Subgroup.isPerfect_iff.1 (Group.isPerfect_def.2 hX.perfect)
  have hperfD : ⁅D, D⁆ = D := by
    rw [hDmap, ← Subgroup.map_commutator, hXp]
  have hRf := le_antisymm hf1 (hf2 hperfD)
  let ψX : ↥X' →* ↥D := (ψ.comp X'.subtype).codRestrict D (fun x => by
    rw [hDmap]
    exact ⟨x, x.2, rfl⟩)
  have hψXsurj : Function.Surjective ψX := by
    rintro ⟨y, hy⟩
    rw [hDmap] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hΦrange : (f.comp ψX).range = f.range := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 hψXsurj, ← MonoidHom.range_eq_map]
  have hR1 : rationalComponent S.ρ S.Γ (rootCharHom a) i ≠ ⊥ := by
    intro h
    have hsimple : IsSimpleGroup (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := hqs.2.1
    haveI := hsimple.toNontrivial
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    apply hx
    have : g = 1 := Subtype.ext ((Subgroup.eq_bot_iff_forall _).1 h g.1 g.2)
    rw [this]
    rfl
  rw [hch]
  exact CompsPF4B2Two.lieCompData_of_range_simple hX hs (f.comp ψX) (hRf.trans hΦrange.symm) hR1

theorem excRationalLieTypesF4B2TwoP_holds {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ExcRationalLieTypesF4B2TwoP p := by
  intro L _ _ p₀ S a hT hap h1 i hA hinner hr2 hn8 hQ hqs
  classical
  have hp2' : p % 2 = 1 := (hp.eq_two_or_odd).resolve_left hp2
  have hℓp : ringChar L ≠ p := ringChar_ne_of_pow_eq_one hp hap h1
  have hpL : ((p : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hp hℓp
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  rcases f4_nonA_casesP2 hp hp2' S hpL hTp h1 i hA with ⟨v, hroots, -, -⟩ | ⟨v, J, -, -, hr, -⟩
  · exact lieCompData_of_f4B2_two S hT i v hroots hinner (not_le.1 hQ) hqs
  · omega

theorem excRationalLieTypesF4SmallP_holds {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ExcRationalLieTypesF4SmallP p :=
  excRationalLieTypesF4SmallP_of_B2two hp hp2 (excRationalLieTypesF4B2TwoP_holds hp hp2)

theorem lieCompsOn_exceptional_of_outerD {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hD : ExcRationalLieTypesOuterDP p) : LieCompsOn p .exceptional :=
  lieCompsOn_exceptional_of_two_residuals hp hp5 hD (excRationalLieTypesF4SmallP_holds hp (by omega))

end Main

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
