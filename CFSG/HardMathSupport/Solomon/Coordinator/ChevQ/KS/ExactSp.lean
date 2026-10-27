module

public import CFSG.Adapters.ClassicalCatalogReverse
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Defs
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.RecogF4
public import CFSG.RankThree.Chevalley.SteinbergCFEvenF4StandardParabolic

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSExactSp

open Matrix TauCeti CFSG.Assembly.LowTwoRank CFSG.Adapters.RankTwoModelTransports
  CFSG.ClassicalModels CFSG.Open

theorem exists_B_of_statedClassicalModel_PSp_even {G : Type} [Group G] {n f : ℕ}
    (h : StatedClassicalModel G .PSp n 2 f) (hn : 3 ≤ n) :
    ∃ (q : PrimePower) (hv : (LieTypeIndex.B n q).Valid), q.p = 2 ∧ q.exponent = f ∧
      Nonempty (G ≃* (CFSGIndex.lie ⟨.B n q, hv⟩).Group) := by
  obtain ⟨hadm, K, hfield, hfinite, hK, ⟨θ⟩⟩ := h
  let _ := hfield
  let _ := hfinite
  let q : PrimePower := ⟨2, f, hadm.1, by have := hadm.2.1; omega⟩
  have hv : (LieTypeIndex.B n q).Valid := by
    rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
      LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨⟨by omega, fun h => by omega⟩, fun h => by omega⟩
  have hfo : Nat.card K = (ValidLieTypeIndex.fieldOrder ⟨.B n q, hv⟩) := by
    simp [ValidLieTypeIndex.fieldOrder, q, hK]
  obtain ⟨φ⟩ := nonempty_ringEquiv_validIndex_fixedField ⟨.B n q, hv⟩ K hfo
  exact ⟨q, hv, rfl, rfl, ⟨(θ.trans (statedProjCongr (glCongr φ)
    (glCongr_statedSp φ n) (glCongr_statedScalars φ))).trans
    (CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj n q hv rfl hn).symm⟩⟩

theorem isLieQuot_of_B_model {G : Type} [Group G] {n f : ℕ}
    (h : StatedClassicalModel (G ⧸ Subgroup.center G) .PSp n 2 f) (hn : 3 ≤ n)
    (P : LieTypeIndex → Prop)
    (hP : ∀ q : PrimePower, q.p = 2 → q.exponent = f → P (.B n q)) : IsLieQuot G P := by
  obtain ⟨q, hv, hqp, hqf, ⟨e⟩⟩ := exists_B_of_statedClassicalModel_PSp_even h hn
  exact ⟨⟨.B n q, hv⟩, hP q hqp hqf, ⟨e⟩⟩

open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits CFSG.ComponentClassification.CatLeafProof
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockStandardPair
  SymplecticBlockPair linearBlockStandardPair_subgroupOf linearBlockStandardPair_le_sup
  symplecticBlockStandardPair_subgroupOf symplecticBlockStandardPair_le_sup
  symplecticBlockPair_subgroupOf symplecticBlockPair_le_sup iSup_subgroupOf_eq_top)
open CFSG.ClassicalInvolution.Generic (Commutes)

set_option linter.unusedSectionVars false


theorem exists_sp3_cover_f4_C3_even {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}
    (hf : 0 < f) (hK : Nat.card K = 2 ^ f) (hK4 : 4 ≤ Nat.card K) :
    ∃ Ψ : StatedSp 3 K →* ModGL Tag.F4 K, Ψ.ker ≤ Subgroup.center (StatedSp 3 K) ∧
      Ψ.range = subsystemGroup .F4 K f4LeviC3 := by
  obtain ⟨W, hW⟩ := f4_linearPair (K := K) (i := f4Node 2) (j := f4Node 3) (k := f4Node 1)
    f4Node_two_ne_three f4_cartan_23 f4_cartan_32 f4_sl3_witness
  obtain ⟨Wsp, hsp⟩ := f4_spPair_even (K := K) hK4
  have hadm : StatedLieAdmissible .PSp 3 2 f := ⟨Nat.prime_two, hf, by norm_num, by simp⟩
  obtain ⟨Ψ, hker, hrange⟩ := weakCT_symplectic_even_subgroup hadm le_rfl hK hK4
    (U := fun k => rankOne (f4Datum K).rootGroup (c3Node k))
    (fun i j hij a ha b hb => by
      obtain ⟨rfl, rfl⟩ := fin3_lt_cases i j hij
      exact (f4_commutes_rankOne_one_three b hb a ha).symm)
    (fun i j hij hj => by
      obtain ⟨rfl, rfl⟩ := fin3_adj_cases i j hij hj
      exact ⟨W, hW.symm⟩)
    (fun i j hi hj => by
      obtain ⟨rfl, rfl⟩ := fin3_end_cases i j hi hj
      exact ⟨Wsp, hsp⟩)
  refine ⟨(adjointGroup .F4 K).subtype.comp Ψ, ?_, ?_⟩
  · intro x hx
    exact hker (Subtype.ext (MonoidHom.mem_ker.mp hx))
  · rw [MonoidHom.range_comp, hrange, map_subtype_iSup_c3]

theorem exists_sp3_cover_f4_B3_even {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}
    (hf : 0 < f) (hK : Nat.card K = 2 ^ f) (hK4 : 4 ≤ Nat.card K) :
    ∃ Ψ : StatedSp 3 K →* ModGL Tag.F4 K, Ψ.ker ≤ Subgroup.center (StatedSp 3 K) ∧
      Ψ.range = subsystemGroup .F4 K f4LeviB3 := by
  obtain ⟨W, hW⟩ := f4_linearPair (K := K) (i := f4Node 0) (j := f4Node 1) (k := f4Node 2)
    f4Node_zero_ne_one f4_cartan_01 f4_cartan_10 f4_sl3_witness_01
  obtain ⟨Wsp, hsp⟩ := f4_spPair_even_swap (K := K) hK4
  have hadm : StatedLieAdmissible .PSp 3 2 f := ⟨Nat.prime_two, hf, by norm_num, by simp⟩
  obtain ⟨Ψ, hker, hrange⟩ := weakCT_symplectic_even_subgroup hadm le_rfl hK hK4
    (U := fun k => rankOne (f4Datum K).rootGroup (b3Node k))
    (fun i j hij a ha b hb => by
      obtain ⟨rfl, rfl⟩ := fin3_lt_cases i j hij
      exact f4_commutes_rankOne_zero_two a ha b hb)
    (fun i j hij hj => by
      obtain ⟨rfl, rfl⟩ := fin3_adj_cases i j hij hj
      exact ⟨W, hW⟩)
    (fun i j hi hj => by
      obtain ⟨rfl, rfl⟩ := fin3_end_cases i j hi hj
      exact ⟨Wsp, hsp⟩)
  refine ⟨(adjointGroup .F4 K).subtype.comp Ψ, ?_, ?_⟩
  · intro x hx
    exact hker (Subtype.ext (MonoidHom.mem_ker.mp hx))
  · rw [MonoidHom.range_comp, hrange, map_subtype_iSup_b3]

section Lane

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.KE CFSG.Timmesfeld


variable {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}

theorem rationalComponent_sp3_model (S : LangSetup Tag.F4 L p₀) {a : Fin Tag.F4.rank → Lˣ}
    (hTor : rootDiagUnit Tag.F4 a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (v : WeylGroup Tag.F4) {J : Set (Fin (Tag.rank .F4))} (hJ : J = f4LeviB3 ∨ J = f4LeviC3)
    (hroots : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots Tag.F4 J)
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    (hQ : S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 8) :
    CFSG.Open.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ∧
      StatedClassicalModel (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) .PSp 3 2 3 := by
  classical
  obtain ⟨σ, hfin, hcard, f, hf1, hker, hf2⟩ := exists_inner_cover S hTor i hinner
  haveI : Fintype ↥(fixSubfield σ) := Fintype.ofFinite ↥(fixSubfield σ)
  haveI : CharP ↥(fixSubfield σ) 2 := ((fixSubfield σ).subtype.charP_iff (fixSubfield σ).subtype_injective 2).2 inferInstance
  have hKcard : Nat.card ↥(fixSubfield σ) = 2 ^ 3 := by rw [hcard, hQ]; norm_num
  have hK4 : 4 ≤ Nat.card ↥(fixSubfield σ) := by rw [hKcard]; norm_num
  obtain ⟨Ψ, hΨk, hΨr⟩ : ∃ Ψ : StatedSp 3 ↥(fixSubfield σ) →* ModGL Tag.F4 ↥(fixSubfield σ),
      Ψ.ker ≤ Subgroup.center (StatedSp 3 ↥(fixSubfield σ)) ∧
        Ψ.range = rootSpan Tag.F4 ↥(fixSubfield σ) ((fun α => v • α) '' parabolicRoots Tag.F4 J) := by
    obtain ⟨Ψ0, hk0, hr0⟩ : ∃ Ψ0 : StatedSp 3 ↥(fixSubfield σ) →* ModGL Tag.F4 ↥(fixSubfield σ),
        Ψ0.ker ≤ Subgroup.center (StatedSp 3 ↥(fixSubfield σ)) ∧
          Ψ0.range = subsystemGroup .F4 ↥(fixSubfield σ) J := by
      rcases hJ with rfl | rfl
      · exact exists_sp3_cover_f4_B3_even (by norm_num) hKcard hK4
      · exact exists_sp3_cover_f4_C3_even (by norm_num) hKcard hK4
    have hsub : subsystemGroup Tag.F4 ↥(fixSubfield σ) J = rootSpan Tag.F4 ↥(fixSubfield σ) (parabolicRoots Tag.F4 J) :=
      CFSG.RankThree.Chevalley.subsystemGroup_eq_iSup_rootSubgroup (τ := Tag.F4) (J := J) ↥(fixSubfield σ)
    rw [hsub] at hr0
    have hmap := (canonical_weyl_root_transport Tag.F4 ↥(fixSubfield σ)).1 v (parabolicRoots Tag.F4 J)
      (fun α hα => hα.1)
    refine ⟨(MulAut.conj (canonicalRep (coxeterSystem Tag.F4) ↥(fixSubfield σ) v)).toMonoidHom.comp Ψ0,
      fun x hx => hk0 ?_, ?_⟩
    · rw [MonoidHom.mem_ker] at hx ⊢
      exact (MulAut.conj (canonicalRep (coxeterSystem Tag.F4) ↥(fixSubfield σ) v)).injective
        (by simpa using hx)
    · rw [MonoidHom.range_comp, hr0]
      exact hmap
  have hcomp : componentRootSpan (fixSubfield σ) (rootCharHom a) i =
      rootSpan Tag.F4 ↥(fixSubfield σ) ((fun α => v • α) '' parabolicRoots Tag.F4 J) := by
    show rootSpan Tag.F4 (fixSubfield σ) (componentRoots (rootCharHom a) i) = _
    rw [hroots]
  rw [← hcomp] at hΨr
  have hperfSp : commutator (StatedSp 3 ↥(fixSubfield σ)) = ⊤ :=
    (spFactorFacts_holds ↥(fixSubfield σ) 3 (by norm_num) (by simp [← Nat.card_eq_fintype_card, hKcard])).perfect
  have hCperf : ⁅componentRootSpan (fixSubfield σ) (rootCharHom a) i, componentRootSpan (fixSubfield σ) (rootCharHom a) i⁆ =
      componentRootSpan (fixSubfield σ) (rootCharHom a) i := by
    rw [← hΨr, MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def, hperfSp]
  have hRf : f.range = rationalComponent S.ρ S.Γ (rootCharHom a) i :=
    le_antisymm (hf2 hCperf) hf1
  let g0 : StatedSp 3 ↥(fixSubfield σ) →* ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i) :=
    Ψ.codRestrict _ (fun x => by rw [← hΨr]; exact ⟨x, rfl⟩)
  have hg0surj : Function.Surjective g0 := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx⟩ : y ∈ Ψ.range := hΨr ▸ hy
    exact ⟨x, Subtype.ext hx⟩
  have hg0ker : g0.ker ≤ Subgroup.center (StatedSp 3 ↥(fixSubfield σ)) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    apply hΨk
    rw [MonoidHom.mem_ker]
    exact congrArg Subtype.val hx
  let g : StatedSp 3 ↥(fixSubfield σ) →* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    (f.comp g0).codRestrict _ (fun x => by rw [← hRf]; exact ⟨g0 x, rfl⟩)
  have hgsurj : Function.Surjective g := by
    rintro ⟨y, hy⟩
    obtain ⟨c, hc⟩ : y ∈ f.range := hRf ▸ hy
    obtain ⟨x, rfl⟩ := hg0surj c
    exact ⟨x, Subtype.ext hc⟩
  have hgker : g.ker ≤ Subgroup.center (StatedSp 3 ↥(fixSubfield σ)) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 : f (g0 x) = 1 := congrArg Subtype.val hx
    have h2 : g0 x ∈ Subgroup.center ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i) := hker h1
    rw [← comap_center_of_surjective hperfSp g0 hg0surj hg0ker]
    exact h2
  obtain ⟨e1⟩ := nonempty_centralQuotient_mulEquiv hperfSp g hgsurj hgker
  let e2 := QuotientGroup.quotientMulEquivOfEq (CFSG.LieType.Universal.Symplectic.center_eq 3 ↥(fixSubfield σ))
  have hmodel : StatedClassicalModel (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) .PSp 3 2 3 :=
    ⟨⟨Nat.prime_two, by norm_num, by norm_num, by simp⟩, ↥(fixSubfield σ), inferInstance, inferInstance,
      hKcard, ⟨e1.symm.trans e2⟩⟩
  refine ⟨⟨?_, CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp _ 3 2 3
    hmodel⟩, hmodel⟩
  have h1 := congrArg (Subgroup.map g) hperfSp
  rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective g hgsurj] at h1
  rw [commutator_def]
  exact h1

end Lane

end KSExactSp

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
