module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154NonCfgDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPF4B2Two
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.ExactSp
public import CFSG.HardMathSupport.Dickson.Bal207.FamF42Levi
public import CFSG.SignalizerFunctorTheorem.NonLocal.SpTwoTwo
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightTorBase

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.CurtisTits
  CFSG.ComponentClassification.CatLeafProof
open CFSG.ClassicalInvolution.WeakCT (exists_b2Hom hom_block_eq spBlock)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (symplecticBlockStandardPair_le_sup)
open CFSG.SeitzReduction.SymplecticPilot (isSimpleGroup_commutator_statedSp_two)

theorem l154f4_four_le_two_pow {f : ℕ} (h : 3 ≤ 2 ^ f) : 4 ≤ 2 ^ f := by
  rcases Nat.lt_or_ge f 2 with hf | hf
  · interval_cases f <;> omega
  · calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf

theorem l154f4_nonCfgModel_of_spSurj {m f : ℕ} (hadm : StatedLieAdmissible .PSp m 2 f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ f) {X : Type} [Group X]
    (g : StatedSp m K →* X) (hg : Function.Surjective g)
    (hker : g.ker ≤ Subgroup.center (StatedSp m K)) :
    L154NonCfgModel (X ⧸ Subgroup.center X) := by
  have hperf : commutator (StatedSp m K) = ⊤ := Group.isPerfect_def.mp
    (CFSG.LieType.Universal.Symplectic.isQuasisimple_of_admissible m K hadm hK).1
  obtain ⟨e⟩ := nonempty_centralQuotient_mulEquiv hperf g hg hker
  exact Or.inl ⟨.PSp, m, f, Or.inl ⟨by decide, hadm, K, inferInstance, inferInstance, hK,
    ⟨e.symm.trans (CFSG.LieType.Universal.Symplectic.centerQuotientEquiv m K)⟩⟩,
    Or.inr (Or.inl rfl)⟩

theorem l154f4_nonCfgModel_of_sp42 {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {X : Type} [Group X] (eR : ↥(commutator ↥(StatedSp 2 K)) ≃* X) :
    L154NonCfgModel (X ⧸ Subgroup.center X) := by
  let e : X ≃* alternatingGroup (Fin 6) :=
    eR.symm.trans (CFSG.SignalizerFunctorTheorem.NonLocal.commutatorSpTwoEquiv hK)
  exact Or.inr ⟨(QuotientGroup.congr (Subgroup.center X)
    (Subgroup.center (alternatingGroup (Fin 6))) e (Subgroup.map_center_eq e)).trans
    ((QuotientGroup.quotientMulEquivOfEq (alternatingGroup.center_eq_bot (by norm_num))).trans
      QuotientGroup.quotientBot)⟩

theorem l154f4_ne_bot_of_isQuasisimple {G : Type} [Group G] {R : Subgroup G}
    (hqs : CFSG.IsQuasisimple ↥R) : R ≠ ⊥ := by
  intro h
  haveI := hqs.2.1.toNontrivial
  obtain ⟨x, hx⟩ := exists_ne (1 : ↥R ⧸ Subgroup.center ↥R)
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  apply hx
  have : g = 1 := Subtype.ext ((Subgroup.eq_bot_iff_forall _).1 h g.1 g.2)
  rw [this]
  rfl

theorem l154f4_subfield_params {L : Type} [Field L] [CharP L 2] (K : Subfield L) [Finite ↥K]
    {m Q : ℕ} (hm : 2 ≤ m) (hK : Nat.card ↥K = Q) (hQ : m = 2 → 3 ≤ Q) :
    CharP ↥K 2 ∧ ∃ f : ℕ, 0 < f ∧ Nat.card ↥K = 2 ^ f ∧ StatedLieAdmissible .PSp m 2 f ∧
      (m = 2 → 4 ≤ Nat.card ↥K) := by
  haveI : Fintype ↥K := Fintype.ofFinite ↥K
  haveI hch : CharP ↥K 2 := (K.subtype.charP_iff K.subtype_injective 2).2 inferInstance
  obtain ⟨f, -, hf⟩ := FiniteField.card ↥K 2
  have hKf : Nat.card ↥K = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hf]
  have h4 : m = 2 → 4 ≤ Nat.card ↥K := fun h2 => by
    have h3 := hQ h2
    rw [← hK, hKf] at h3
    rw [hKf]
    exact l154f4_four_le_two_pow h3
  refine ⟨hch, f, f.pos, hKf, ⟨Nat.prime_two, f.pos, hm, fun h => ?_⟩, h4⟩
  obtain ⟨h1, h2⟩ := Prod.mk.inj h
  have h4' := h4 h1
  rw [hKf] at h4'
  omega

theorem l154f4_equiv_of_derived_two {K' : Type} [Field K'] [Finite K'] (hcard : Nat.card K' = 2)
    {M G : Type} [Group M] [Group G] {C D : Subgroup M} (ψ : StatedSp 2 K' →* M)
    (hψ : ψ.range = C) (hD : D = ⁅C, C⁆) (f : ↥D →* G) {R : Subgroup G} (hf1 : R ≤ f.range)
    (hf2 : ⁅D, D⁆ = D → f.range ≤ R) (hR1 : R ≠ ⊥) :
    Nonempty (↥(commutator ↥(StatedSp 2 K')) ≃* ↥R) := by
  classical
  haveI : Fintype K' := Fintype.ofFinite _
  have hcard' : Fintype.card K' = 2 := by rw [← Nat.card_eq_fintype_card]; exact hcard
  set X' : Subgroup (StatedSp 2 K') := commutator (StatedSp 2 K') with hX'
  have hDmap : D = X'.map ψ := by
    rw [hD, ← hψ, MonoidHom.range_eq_map, ← Subgroup.map_commutator, hX', commutator_def]
  have hX : LieFactorData 2 ↥X' := spFourTwoFacts_holds K' hcard'
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
  have hRΦ : R = (f.comp ψX).range := by
    rw [hRf, MonoidHom.range_comp, MonoidHom.range_eq_top.2 hψXsurj, ← MonoidHom.range_eq_map]
  have hkerΦ : (f.comp ψX).ker = ⊥ := by
    rcases hs.eq_bot_or_eq_top_of_normal (f.comp ψX).ker with h | h
    · exact h
    · exfalso
      apply hR1
      rw [hRΦ, Subgroup.eq_bot_iff_forall]
      rintro _ ⟨x, rfl⟩
      exact MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top x)
  exact ⟨(MonoidHom.ofInjective ((MonoidHom.ker_eq_bot_iff _).1 hkerΦ)).trans
    (MulEquiv.subgroupCongr hRΦ.symm)⟩

section Weyl


theorem l154f4_conj_range {K : Type} [Field K] (v : WeylGroup Tag.F4)
    {J : Set (Fin (Tag.rank .F4))} {G : Type} [Group G] {Ψ : G →* ModGL Tag.F4 K}
    (hrange : Ψ.range = subsystemGroup .F4 K J) :
    ((MulAut.conj (canonicalRep (coxeterSystem Tag.F4) K v)).toMonoidHom.comp Ψ).range =
      rootSpan Tag.F4 K ((fun α => v • α) '' parabolicRoots Tag.F4 J) := by
  have hsub : subsystemGroup Tag.F4 K J = rootSpan Tag.F4 K (parabolicRoots Tag.F4 J) :=
    CFSG.RankThree.Chevalley.subsystemGroup_eq_iSup_rootSubgroup (τ := Tag.F4) (J := J) K
  rw [MonoidHom.range_comp, hrange, hsub]
  exact (canonical_weyl_root_transport Tag.F4 K).1 v (parabolicRoots Tag.F4 J) (fun α hα => hα.1)

theorem l154f4_spRange_smul {K : Type} [Field K] (v : WeylGroup Tag.F4)
    {J : Set (Fin (Tag.rank .F4))} {m : ℕ} {Ψ : StatedSp m K →* ModGL Tag.F4 K}
    (hker : Ψ.ker ≤ Subgroup.center (StatedSp m K)) (hrange : Ψ.range = subsystemGroup .F4 K J) :
    ∃ Ψ' : StatedSp m K →* ModGL Tag.F4 K, Ψ'.ker ≤ Subgroup.center (StatedSp m K) ∧
      Ψ'.range = rootSpan Tag.F4 K ((fun α => v • α) '' parabolicRoots Tag.F4 J) := by
  refine ⟨(MulAut.conj (canonicalRep (coxeterSystem Tag.F4) K v)).toMonoidHom.comp Ψ,
    fun x hx => hker ?_, l154f4_conj_range v hrange⟩
  rw [MonoidHom.mem_ker] at hx ⊢
  exact (MulAut.conj (canonicalRep (coxeterSystem Tag.F4) K v)).injective
    (hx.trans (map_one _).symm)

end Weyl

section Cover


theorem l154f4_exists_spSurj {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) {m : ℕ}
    (hrec : ∀ K : Subfield L, Finite ↥K →
      Nat.card ↥K = S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) →
      commutator (StatedSp m ↥K) = ⊤ ∧ ∃ Ψ : StatedSp m ↥K →* ModGL τ ↥K,
        Ψ.ker ≤ Subgroup.center (StatedSp m ↥K) ∧
        Ψ.range = componentRootSpan K (rootCharHom a) i) :
    ∃ (K : Subfield L) (_ : Finite ↥K),
      Nat.card ↥K = S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) ∧
      ∃ g : StatedSp m ↥K →* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i),
        Function.Surjective g ∧ g.ker ≤ Subgroup.center (StatedSp m ↥K) := by
  classical
  obtain ⟨σ, hfin, hcard, f, hf1, hker, hf2⟩ := exists_inner_cover S hT i hinner
  obtain ⟨hperf, Ψ, hΨk, hΨr⟩ := hrec _ hfin hcard
  haveI : Group.IsPerfect (StatedSp m ↥(fixSubfield σ)) := Group.isPerfect_def.2 hperf
  have hmem : ∀ y, Ψ y ∈ componentRootSpan (fixSubfield σ) (rootCharHom a) i :=
    fun y => hΨr ▸ ⟨y, rfl⟩
  let g₀ := Ψ.codRestrict _ hmem
  have hg₀ : Function.Surjective g₀ := by
    rintro ⟨c, hc⟩
    obtain ⟨y, hy⟩ : c ∈ Ψ.range := hΨr ▸ hc
    exact ⟨y, Subtype.ext hy⟩
  have hg₀k : g₀.ker ≤ Subgroup.center (StatedSp m ↥(fixSubfield σ)) := fun y hy =>
    hΨk (by rw [MonoidHom.mem_ker] at hy ⊢; exact congrArg Subtype.val hy)
  have hCperf := Subgroup.isPerfect_iff.1 (Group.IsPerfect.ofSurjective (f := g₀) hg₀)
  have hRf : f.range = rationalComponent S.ρ S.Γ (rootCharHom a) i :=
    le_antisymm (hf2 hCperf) hf1
  have hmem' : ∀ y, f (g₀ y) ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i :=
    fun y => hRf ▸ ⟨g₀ y, rfl⟩
  refine ⟨fixSubfield σ, hfin, hcard, (f.comp g₀).codRestrict _ hmem', ?_, fun y hy => ?_⟩
  · rintro ⟨r, hr⟩
    obtain ⟨c, hc⟩ : r ∈ f.range := hRf ▸ hr
    obtain ⟨y, rfl⟩ := hg₀ c
    exact ⟨y, Subtype.ext hc⟩
  · rw [MonoidHom.mem_ker] at hy
    have h1 : f (g₀ y) = 1 := congrArg Subtype.val hy
    have h2 : g₀ y ∈ Subgroup.center _ := hker (MonoidHom.mem_ker.2 h1)
    rw [← comap_center_of_surjective hperf g₀ hg₀ hg₀k]
    exact h2

theorem l154f4_classModel_of_cover {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}
    (S : LangSetup Tag.F4 L p₀) {a : Fin Tag.F4.rank → Lˣ}
    (hT : rootDiagUnit Tag.F4 a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (v : WeylGroup Tag.F4) {J : Set (Fin (Tag.rank .F4))}
    (hroots : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots Tag.F4 J)
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) {m : ℕ} (hm : 2 ≤ m)
    (hQ : m = 2 → 3 ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
    (hcov : ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (f : ℕ), 0 < f →
      Nat.card K = 2 ^ f → (m = 2 → 4 ≤ Nat.card K) → ∃ Ψ : StatedSp m K →* ModGL Tag.F4 K,
        Ψ.ker ≤ Subgroup.center (StatedSp m K) ∧ Ψ.range = subsystemGroup .F4 K J) :
    L154ClassModel S i := by
  classical
  obtain ⟨K, hfin, hcard, g, hg, hker⟩ := l154f4_exists_spSurj S hT i hinner (m := m)
    (fun K hfin hK => by
      haveI := hfin
      obtain ⟨hch, f, hf, hKf, hadm, h4⟩ := l154f4_subfield_params K hm hK hQ
      haveI := hch
      refine ⟨Group.isPerfect_def.mp
        (CFSG.LieType.Universal.Symplectic.isQuasisimple_of_admissible m ↥K hadm hKf).1, ?_⟩
      obtain ⟨Ψ, hΨk, hΨr⟩ := hcov ↥K f hf hKf h4
      obtain ⟨Ψ', hk', hr'⟩ := l154f4_spRange_smul v hΨk hΨr
      refine ⟨Ψ', hk', ?_⟩
      rw [hr']
      show _ = rootSpan Tag.F4 ↥K (componentRoots (rootCharHom a) i)
      rw [hroots])
  haveI := hfin
  obtain ⟨-, f, -, hKf, hadm, -⟩ := l154f4_subfield_params K hm hcard hQ
  exact l154f4_nonCfgModel_of_spSurj hadm hKf g hg hker

end Cover

section Pres


theorem l154f4_b2Hom {K : Type} [Field K] [Finite K] :
    ∃ φ : StatedSp 2 K →* adjointGroup .F4 K, φ.range =
      rankOne (f4Datum K).rootGroup (f4Node 1) ⊔ rankOne (f4Datum K).rootGroup (f4Node 2) := by
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (f4Datum K).isFiniteType
    (Dv := (f4Datum K).divisible) rfl
  obtain ⟨Cc, -, hCc⟩ := f4_commutatorFormula K O
  have hE := f4_chevalleyExtras K O Cc hCc
  choose ρF hρFi hρFr hρFv using exists_rankOne_param hE
  obtain ⟨φ, e, -, he1, he2, he3, he4, hφ⟩ :=
    exists_b2Hom hE (s := f4Node 2) (l := f4Node 1) rfl f4_cartan_21 f4_cartan_12
  obtain ⟨hb0, hb1⟩ := hom_block_eq he1 he2 he3 he4 hφ (hρFv (f4Node 2)) (hρFv (f4Node 1))
  refine ⟨φ, ?_⟩
  rw [CFSG.ClassicalInvolution.Q3.Q3V.range_eq_sup_of_spBlocks hb0 hb1, hρFr, hρFr, sup_comm]

end Pres

section Levi


theorem l154f4_cover_levi {J : Set (Fin (Tag.rank .F4))} (hJ : J = f4LeviB3 ∨ J = f4LeviC3)
    {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ} (hf : 0 < f) (hK : Nat.card K = 2 ^ f) :
    ∃ Ψ : StatedSp 3 K →* ModGL Tag.F4 K, Ψ.ker ≤ Subgroup.center (StatedSp 3 K) ∧
      Ψ.range = subsystemGroup .F4 K J := by
  rcases hJ with rfl | rfl
  · by_cases hK4 : 4 ≤ Nat.card K
    · exact CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSExactSp.exists_sp3_cover_f4_B3_even
        hf hK hK4
    · exact CFSG.HardMathSupport.Dickson.Bal207.FamF42.exists_sp3Hom_f4_B3_two
        (CompsPF4Small.card_eq_two_of_lt_four hf hK hK4)
  · exact CFSG.HardMathSupport.Dickson.Bal207.FamF42.exists_sp3Hom_f4_C3 Nat.prime_two hf hK

end Levi

section B2


theorem l154f4_cover_B2 {K : Type} [Field K] [Finite K] [CharP K 2] (hK4 : 4 ≤ Nat.card K) :
    ∃ Ψ : StatedSp 2 K →* ModGL Tag.F4 K, Ψ.ker ≤ Subgroup.center (StatedSp 2 K) ∧
      Ψ.range = subsystemGroup .F4 K f4LeviB2 := by
  classical
  obtain ⟨W, hW⟩ := f4_spPair_even hK4
  have hle := symplecticBlockStandardPair_le_sup hW
  obtain ⟨θ, c, hrange, hker, -, -, hU, hV⟩ := hW
  have hUW : rankOne (f4Datum K).rootGroup (f4Node 1) ≤ W := by
    rw [← hU, ← hrange]
    exact Subgroup.map_le_range _ _
  have hVW : rankOne (f4Datum K).rootGroup (f4Node 2) ≤ W := by
    rw [← hV, ← hrange]
    exact Subgroup.map_le_range _ _
  have hWeq : W = rankOne (f4Datum K).rootGroup (f4Node 1) ⊔
      rankOne (f4Datum K).rootGroup (f4Node 2) := le_antisymm hle (sup_le hUW hVW)
  refine ⟨(adjointGroup .F4 K).subtype.comp θ, fun x hx => ?_, ?_⟩
  · exact hker (Subtype.ext (MonoidHom.mem_ker.mp hx))
  · rw [MonoidHom.range_comp, hrange, hWeq, map_subtype_sup_b2]

theorem l154f4_classModel_b2_two {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup Tag.F4 L p₀) {a : Fin Tag.F4.rank → Lˣ}
    (hT : rootDiagUnit Tag.F4 a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (v : WeylGroup Tag.F4)
    (hroots : componentRoots (rootCharHom a) i =
      (fun α => v • α) '' parabolicRoots Tag.F4 f4LeviB2)
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    (hQ : S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) < 3)
    (hqs : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    L154ClassModel S i := by
  classical
  obtain ⟨K', hfin, C, D, hC, hD, hcard, f, hf1, -, hf2⟩ :=
    exists_inner_cover_derived_two S hT i hinner hQ
  haveI := hfin
  obtain ⟨φ, hφ⟩ := l154f4_b2Hom (K := ↥K')
  have hr : ((adjointGroup .F4 ↥K').subtype.comp φ).range = subsystemGroup .F4 ↥K' f4LeviB2 := by
    rw [MonoidHom.range_comp, hφ, map_subtype_sup_b2]
  have hψ : ((MulAut.conj (canonicalRep (coxeterSystem Tag.F4) ↥K' v)).toMonoidHom.comp
      ((adjointGroup .F4 ↥K').subtype.comp φ)).range = C := by
    rw [l154f4_conj_range v hr, hC]
    show _ = rootSpan Tag.F4 ↥K' (componentRoots (rootCharHom a) i)
    rw [hroots]
  obtain ⟨eR⟩ := l154f4_equiv_of_derived_two hcard _ hψ hD f hf1 hf2
    (l154f4_ne_bot_of_isQuasisimple hqs)
  exact l154f4_nonCfgModel_of_sp42 hcard eR

end B2

section F4


theorem l154F4Models_holds : L154F4Models := by
  intro L _ _ _ p₀ S p a i hc hinner hshape
  obtain ⟨hp, hp2, hT, hap, h1, hqs⟩ := hc
  have hp2' : p % 2 = 1 := (hp.eq_two_or_odd).resolve_left hp2
  have hℓp : ringChar L ≠ p := ringChar_ne_of_pow_eq_one hp hap h1
  have hpL : ((p : ℕ) : L) ≠ 0 :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.natCast_ne_zero_of_ringChar_ne hp hℓp
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  have hnonA : ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)) := by
    rintro ⟨-, hn⟩
    rcases hshape with ⟨hr, hc⟩ | ⟨hr, hc⟩ <;> rw [hr, hc] at hn <;> omega
  rcases f4_nonA_casesP2 hp hp2' S hpL hTp h1 i hnonA with ⟨v, hroots, -, -⟩ |
      ⟨v, J, hJ, hroots, -, -⟩
  · by_cases hQ : 3 ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)
    · exact l154f4_classModel_of_cover S hT i v hroots hinner le_rfl (fun _ => hQ)
        (fun K _ _ _ _ _ _ h4 => l154f4_cover_B2 (h4 rfl))
    · exact l154f4_classModel_b2_two S hT i v hroots hinner (not_le.1 hQ) hqs
  · exact l154f4_classModel_of_cover S hT i v hroots hinner (by norm_num)
      (fun h => absurd h (by norm_num)) (fun K _ _ _ _ hf hK _ => l154f4_cover_levi hJ hf hK)

end F4

end CFSG.LocalAnalysis.GLTheoremA.K155X

end
