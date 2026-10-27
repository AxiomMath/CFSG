module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShCompDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShCompTransport
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShClaim
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeBoundOther
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeBoundGenBaseW
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamInLUComp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamInOmGen
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.LinearFieldType
public import CFSG.Adapters.CatalogueFieldBridges.Linear
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_13
public import CFSG.GroupTheory.CentralizerSup
public import CFSG.GroupTheory.ElemAbelianPlaneAction
public import CFSG.GroupTheory.PLayer.PIndex
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27D4Field
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossSp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I137Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431Core
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431Defs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bDesc
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154Holds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GTriD4Fix
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterIdxSymplectic
public import CFSG.RankThree.PartOne.CTP.StdSub

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.T171Sh CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.StandardType
open CFSG.Assembly (LargeEvenSLGroup LargeEvenProj LargeEvenProjMk LargeEvenInduces
  LargeEvenMatConjImage LargeEvenScalars)
open scoped commutatorElement

private theorem linShape_facts {S : Type} [Group S] {p N m : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hcat : catalogIs S (onLie fun i => ∃ q : TauCeti.PrimePower, i = .A (N - 1) q ∧
      q.exponent = m ∧ I171.I171LieShape p i)) :
    p ∣ N ∧ 3 ≤ N ∧ catalogIs S (onLie fun i => ∃ q : TauCeti.PrimePower,
      i = .A (N - 1) q ∧ q.card = 2 ^ m) := by
  obtain ⟨i, hv, hi, he⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.exists_lieIndex hcat
  obtain ⟨q, hqA, hqexp, hshape⟩ := hi
  subst hqA
  have hcardq : q.card = 2 ^ q.exponent := by
    rw [TauCeti.PrimePower.card_def, hshape.1]
  have hqcardm : q.card = 2 ^ m := by
    rw [hcardq, hqexp]
  have hN2 : 2 ≤ N := by
    have h := ((TauCeti.LieTypeIndex.inStandardRange_iff _).mp
      ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1).1
    omega
  have hpN : p ∣ N := by
    have h : p ∣ N.gcd (q.card - 1) := by
      have h' := hshape.2
      rwa [show N - 1 + 1 = N by omega] at h'
    exact (Nat.dvd_gcd_iff.mp h).1
  have hp3 : 3 ≤ p := Nat.succ_le_of_lt (Nat.lt_of_le_of_ne hp.two_le (Ne.symm hp2))
  have hNpos : 0 < N := by omega
  have hN : 3 ≤ N := le_trans hp3 (Nat.le_of_dvd hNpos hpN)
  exact ⟨hpN, hN, ⟨.lie ⟨.A (N - 1) q, hv⟩, ⟨q, rfl, hqcardm⟩, he⟩⟩

private theorem linearImage_isComponent {G : Type} [Group G] [Finite G] {p N : ℕ}
    {L J : Subgroup G} {d : G} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hpk : (p : K) ≠ 0)
    (hdN : d ∈ Subgroup.normalizer (L : Set G))
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj (LargeEvenSLGroup (Fin N) K))
    (D : GL (Fin N) K)
    (hD : D ∈ Subgroup.normalizer (LargeEvenSLGroup (Fin N) K : Set (GL (Fin N) K)))
    {c : Kˣ} (hDp : D ^ p = Matrix.GeneralLinearGroup.scalar (Fin N) c)
    (hind : LargeEvenInduces θ (conjRel d)
      (TableB.projConj (LargeEvenSLGroup (Fin N) K) ⟨D, hD⟩))
    (hJ : GLAPComponent p (L ⊓ Subgroup.centralizer ({d} : Set G)) J) :
    CFSG.Open.IsComponentOf ((J.subgroupOf L).map (piCenterQuot θ))
      (fixSubgroup (TableB.projConj (LargeEvenSLGroup (Fin N) K) ⟨D, hD⟩)) := by
  classical
  let e := CFSG.LocalAnalysis.GLTheoremA.I2015.linRecipeEquiv N K
  let φ := TableB.projConj (LargeEvenSLGroup (Fin N) K) ⟨D, hD⟩
  let T : Subgroup (LargeEvenProj (LargeEvenSLGroup (Fin N) K)) :=
    (J.subgroupOf L).map (piCenterQuot θ)
  have hJT : GLAPComponent p (fixSubgroup φ) T :=
    glaPComponent_fixSubgroup_map_piCenterQuot hp hdN hJ θ hind
  have hφ : MulAut.congr e.symm φ = LinearFlag.conjAut N K D := projConj_recipe D hD
  have hfix : (fixSubgroup φ).map e.symm.toMonoidHom =
      fixSubgroup (LinearFlag.conjAut N K D) := by
    rw [← hφ]
    exact (fixSubgroup_congr e.symm φ).symm
  have hJT' : GLAPComponent p (fixSubgroup (LinearFlag.conjAut N K D))
      (T.map e.symm.toMonoidHom) := by
    rw [← hfix]
    exact glaPComponent_map_central hp e.symm.toMonoidHom (by
      intro y hy x _
      have hy1 : y = 1 := e.symm.injective (by simpa using MonoidHom.mem_ker.1 hy.2)
      rw [hy1]
      simp) hJT
  have hperf : ⁅T.map e.symm.toMonoidHom, T.map e.symm.toMonoidHom⁆ =
      T.map e.symm.toMonoidHom := glaPComponent_perfect hJT'
  have hle : T.map e.symm.toMonoidHom ≤ GLALayer (fixSubgroup (LinearFlag.conjAut N K D)) :=
    (perfectInLayer_conjAut (p := p) hpk hDp) (T.map e.symm.toMonoidHom) hJT'.1 hperf
  obtain ⟨hcomp, -⟩ := glaPComponent_isComponent_of_le_layer hJT' hle
  refine ⟨hJT.1, hJT.2.1, ?_⟩
  exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
    (Subgroup.equivMapOfInjective T e.symm.toMonoidHom e.symm.injective).symm hcomp.2.2

private theorem lin_component_step {G : Type} [Group G] [Finite G] {p N : ℕ}
    {L J : Subgroup G} {d : G} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hpk : (p : K) ≠ 0)
    (hdN : d ∈ Subgroup.normalizer (L : Set G))
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj (LargeEvenSLGroup (Fin N) K))
    (D : GL (Fin N) K)
    (hD : D ∈ Subgroup.normalizer (LargeEvenSLGroup (Fin N) K : Set (GL (Fin N) K)))
    {c : Kˣ} (hDp : D ^ p = Matrix.GeneralLinearGroup.scalar (Fin N) c)
    (hind : LargeEvenInduces θ (conjRel d)
      (TableB.projConj (LargeEvenSLGroup (Fin N) K) ⟨D, hD⟩))
    (hJ : GLAPComponent p (L ⊓ Subgroup.centralizer ({d} : Set G)) J) :
    CFSG.Open.IsComponentOf J (L ⊓ Subgroup.centralizer ({d} : Set G)) ∧
      GLAPComponent p (fixSubgroup (TableB.projConj (LargeEvenSLGroup (Fin N) K) ⟨D, hD⟩))
        ((J.subgroupOf L).map (piCenterQuot θ)) ∧
      CFSG.Open.IsComponentOf ((J.subgroupOf L).map (piCenterQuot θ))
        (fixSubgroup (TableB.projConj (LargeEvenSLGroup (Fin N) K) ⟨D, hD⟩)) := by
  have hJT : GLAPComponent p
      (fixSubgroup (TableB.projConj (LargeEvenSLGroup (Fin N) K) ⟨D, hD⟩))
      ((J.subgroupOf L).map (piCenterQuot θ)) :=
    glaPComponent_fixSubgroup_map_piCenterQuot hp hdN hJ θ hind
  have hTcomp : CFSG.Open.IsComponentOf ((J.subgroupOf L).map (piCenterQuot θ))
      (fixSubgroup (TableB.projConj (LargeEvenSLGroup (Fin N) K) ⟨D, hD⟩)) :=
    linearImage_isComponent hp hpk hdN θ D hD hDp hind hJ
  exact ⟨isComponentOf_of_isComponentOf_map_piCenterQuot inf_le_left θ hJ hTcomp, hJT, hTcomp⟩

private theorem lin_field_type_data {G : Type} [Group G] [Finite G] {p N m : ℕ}
    {L J A : Subgroup G} {d b : G} {K : Type} [Field K] [Finite K]
    (hpre : PreSetup p L J A d b) (hKcard : Nat.card K = 2 ^ m)
    {D : GL (Fin N) K} {lam : Kˣ}
    (hDp : D ^ p = Matrix.GeneralLinearGroup.scalar (Fin N) lam)
    (hcube : ¬ ∃ c : Kˣ, c ^ p = lam)
    {T : Subgroup (LinearFlag.projectiveSL N K)}
    (hcompT : CFSG.Open.IsComponentOf T (fixSubgroup (LinearFlag.conjAut N K D))) :
    p ∣ N ∧ 2 ≤ N / p ∧
      (∀ T' : Subgroup (LinearFlag.projectiveSL N K),
        CFSG.Open.IsComponentOf T' (fixSubgroup (LinearFlag.conjAut N K D)) → T' = T) ∧
      ∃ (E : Type) (_ : Field E) (_ : Fintype E),
        Nat.card E = Nat.card K ^ p ∧
          ∃ g : Matrix.SpecialLinearGroup (Fin (N / p)) E →* ↥T,
            Function.Surjective g ∧
              g.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (N / p)) E) := by
  have hne : ∀ x : K, x ^ p ≠ (lam : K) := by
    intro x hx
    by_cases hx0 : x = 0
    · subst hx0
      rw [zero_pow hpre.prime.ne_zero] at hx
      exact lam.ne_zero hx.symm
    · refine hcube ⟨Units.mk0 x hx0, Units.ext ?_⟩
      rw [Units.val_pow_eq_pow_val, Units.val_mk0]
      exact hx
  exact linear_fieldType_component (k := K) (n := N) (p := p) hpre.prime
    (natCast_ne_zero_of_card_two_pow hKcard hpre.prime hpre.odd) hDp hne hcompT

private theorem lin_field_layer {G : Type} [Group G] [Finite G] {p N : ℕ}
    {L J A : Subgroup G} {d b : G} {K : Type} [Field K] [Finite K]
    (hpre : PreSetup p L J A d b)
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj (LargeEvenSLGroup (Fin N) K))
    (D : GL (Fin N) K)
    (hD : D ∈ Subgroup.normalizer (LargeEvenSLGroup (Fin N) K : Set (GL (Fin N) K)))
    (hind : LargeEvenInduces θ (conjRel d)
      (TableB.projConj (LargeEvenSLGroup (Fin N) K) ⟨D, hD⟩))
    (hcompJ : CFSG.Open.IsComponentOf J (L ⊓ Subgroup.centralizer ({d} : Set G)))
    (huniq : ∀ T' : Subgroup (LinearFlag.projectiveSL N K),
      CFSG.Open.IsComponentOf T' (fixSubgroup (LinearFlag.conjAut N K D)) →
        T' = (((J.subgroupOf L).map (piCenterQuot θ)).map
          (CFSG.LocalAnalysis.GLTheoremA.I2015.linRecipeEquiv N K).symm.toMonoidHom)) :
    GLALayer (L ⊓ Subgroup.centralizer ({d} : Set G)) = J := by
  let e := CFSG.LocalAnalysis.GLTheoremA.I2015.linRecipeEquiv N K
  have hφ : MulAut.congr e.symm (TableB.projConj (LargeEvenSLGroup (Fin N) K) ⟨D, hD⟩) =
      LinearFlag.conjAut N K D := projConj_recipe D hD
  have hfix : (fixSubgroup (TableB.projConj (LargeEvenSLGroup (Fin N) K) ⟨D, hD⟩)).map
      e.symm.toMonoidHom = fixSubgroup (LinearFlag.conjAut N K D) := by
    rw [← hφ]
    exact (fixSubgroup_congr e.symm _).symm
  refine glaLayer_eq_of_forall_map_eq inf_le_left θ hcompJ ?_
  intro K' hK'
  have hK'asm : CFSG.Assembly.IsComponentOf K'
      (L ⊓ Subgroup.centralizer ({d} : Set G)) :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open
      K' (L ⊓ Subgroup.centralizer ({d} : Set G))).2 hK'
  have hK'descA : CFSG.Assembly.IsComponentOf ((K'.subgroupOf L).map (piCenterQuot θ))
      (fixSubgroup (TableB.projConj (LargeEvenSLGroup (Fin N) K) ⟨D, hD⟩)) :=
    componentDescent_component θ (hpre.norm hpre.d_mem) hind hK'asm
  have hK'desc : CFSG.Open.IsComponentOf ((K'.subgroupOf L).map (piCenterQuot θ))
      (fixSubgroup (TableB.projConj (LargeEvenSLGroup (Fin N) K) ⟨D, hD⟩)) :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open _ _).1 hK'descA
  have hK'trans : CFSG.Open.IsComponentOf
      (((K'.subgroupOf L).map (piCenterQuot θ)).map e.symm.toMonoidHom)
      (fixSubgroup (LinearFlag.conjAut N K D)) := by
    have h1 := CFSG.Fischer.Classification.Recognition.IsComponentOf.map_mulEquiv e.symm hK'desc
    rwa [hfix] at h1
  have heq : (((K'.subgroupOf L).map (piCenterQuot θ)).map e.symm.toMonoidHom) =
      (((J.subgroupOf L).map (piCenterQuot θ)).map e.symm.toMonoidHom) := by
    rw [huniq _ hK'trans]
  exact Subgroup.map_injective (f := e.symm.toMonoidHom) e.symm.injective heq

private theorem lin_catalogue_field {G : Type} [Group G] [Finite G] {p N m : ℕ}
    {L J A : Subgroup G} {d b : G} {K E : Type} [Field K] [Finite K] [Field E] [Fintype E]
    (hpre : PreSetup p L J A d b)
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj (LargeEvenSLGroup (Fin N) K))
    (hKcard : Nat.card K = 2 ^ m) (h2Np : 2 ≤ N / p)
    (hEcard : Nat.card E = Nat.card K ^ p)
    {φ : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin N) K))}
    (hJbar : GLAPComponent p (fixSubgroup φ) ((J.subgroupOf L).map (piCenterQuot θ)))
    (hcompJbar : CFSG.Open.IsComponentOf ((J.subgroupOf L).map (piCenterQuot θ))
      (fixSubgroup φ))
    {T : Subgroup (LinearFlag.projectiveSL N K)}
    (eJ : ↥((J.subgroupOf L).map (piCenterQuot θ)) ≃* ↥T)
    {g : Matrix.SpecialLinearGroup (Fin (N / p)) E →* ↥T}
    (hg : Function.Surjective g)
    (hgk : g.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (N / p)) E)) :
    catalogIs (PSimple p J) (onLie fun i => ∃ q : TauCeti.PrimePower,
      i = .A (N / p - 1) q ∧ q.p = 2 ∧ q.exponent = m * p) := by
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · exfalso
      rw [h, pow_zero] at hKcard
      have h2 := Finite.one_lt_card (α := K)
      omega
    · exact h
  have hp3 : 3 ≤ p := Nat.succ_le_of_lt (Nat.lt_of_le_of_ne hpre.prime.two_le
    (Ne.symm hpre.odd))
  have hmp : 0 < m * p := Nat.mul_pos (by omega) (by omega)
  have hmp3 : 3 ≤ m * p := by
    have h := Nat.mul_le_mul hm1 hp3
    simpa using h
  let q : TauCeti.PrimePower := ⟨2, m * p, Nat.prime_two, hmp⟩
  have hq8 : 8 ≤ q.card := by
    rw [TauCeti.PrimePower.card_def]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (m * p) := Nat.pow_le_pow_right (by norm_num) hmp3
  have hk : Nat.card E = q.card := by
    rw [TauCeti.PrimePower.card_def, hEcard, hKcard, ← pow_mul]
  have h22 : N / p ≠ 2 ∨ Nat.card E ≠ 2 := Or.inr (by omega)
  have h23 : N / p ≠ 2 ∨ Nat.card E ≠ 3 := Or.inr (by omega)
  have hq2dvd : 2 ∣ q.card := by
    rw [TauCeti.PrimePower.card_def]
    exact dvd_pow_self 2 hmp.ne'
  have hv : (TauCeti.LieTypeIndex.A (N / p - 1) q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    refine ⟨⟨Nat.le_sub_one_of_lt (lt_of_lt_of_le (by norm_num) h2Np), ?_⟩, ?_⟩
    · intro _
      omega
    · rintro (⟨-, h | h | h⟩ | ⟨-, h⟩ | ⟨-, h⟩)
      · rw [h] at hq8; omega
      · rw [h] at hq2dvd; norm_num at hq2dvd
      · rw [h] at hq2dvd; norm_num at hq2dvd
      · rw [h] at hq8; omega
      · rw [h] at hq8; omega
  haveI : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin (N / p)) E ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin (N / p)) E)) :=
    CFSG.BenderSuzuki.External.huppert_II_6_13 (K := E) (N / p) h2Np h22 h23
  let g' : Matrix.SpecialLinearGroup (Fin (N / p)) E →*
      ↥((J.subgroupOf L).map (piCenterQuot θ)) := eJ.symm.toMonoidHom.comp g
  have hg' : Function.Surjective g' := eJ.symm.surjective.comp hg
  have hgk' : g'.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (N / p)) E) := by
    rw [show g' = eJ.symm.toMonoidHom.comp g from rfl,
      MonoidHom.ker_comp_of_injective g eJ.symm.toMonoidHom eJ.symm.injective]
    exact hgk
  obtain ⟨e5⟩ := nonempty_pSimple_equiv_of_central_surjective (p := p) hpre.prime inf_le_left
    θ hpre.pcomp hJbar hcompJbar g' hg' hgk' inferInstance
  let eC : (Matrix.SpecialLinearGroup (Fin (N / p)) E ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin (N / p)) E)) ≃*
      LinearFlag.projectiveSL (N / p) E :=
    QuotientGroup.quotientMulEquivOfEq (LinearFlag.scalars_eq_center (N / p) E).symm
  obtain ⟨eLie⟩ := CFSG.Adapters.CatalogueFieldBridges.nonempty_projectiveSL_mulEquiv_lie
    (n := N / p - 1) (k := E) q hv hk
  rw [Nat.sub_add_cancel (show 1 ≤ N / p by omega)] at eLie
  exact ⟨.lie ⟨.A (N / p - 1) q, hv⟩, ⟨q, rfl, rfl, rfl⟩, ⟨e5.trans (eC.trans eLie)⟩⟩

theorem t158CompLin_of (hLM : T171Sh.LinMarking) (hMI : T158MISetup)
    (hT : T158LinTypeOneW) : T158CompLin := by
  intro G _ _ p L J A d b N m hpre hcat
  obtain ⟨hpN, hN, hcatLin⟩ := linShape_facts hpre.prime hpre.odd hcat
  let A' : Subgroup G := Subgroup.zpowers d ⊔ Subgroup.zpowers b
  have hw : WSetup p L J A' d b := hpre.toWSetup
  have hdN : d ∈ Subgroup.normalizer (L : Set G) :=
    S11.le_normalizer_of_innerDiag hpre.idiag₂ (Subgroup.mem_sup_left (Subgroup.mem_zpowers d))
  obtain ⟨K, hK, hKfin, hKcard, θ, hact⟩ := hLM G p L J A' d b N m hw hcatLin
  letI := hK
  letI := hKfin
  letI : Fintype K := Fintype.ofFinite K
  have hS : (Set.univ : Set (GL (Fin N) K)) ⊆ Subgroup.normalizer
      (LargeEvenSLGroup (Fin N) K : Set (GL (Fin N) K)) := by
    intro x _
    rw [Subgroup.normalizer_eq_top_iff.mpr
      (inferInstance : (LargeEvenSLGroup (Fin N) K).Normal)]
    exact Subgroup.mem_top x
  obtain ⟨M⟩ := LiftMap.exists (L := L) (A := A') (S := Set.univ) θ hact hS
  let D : GL (Fin N) K := M.mat ⟨d, hw.d_mem⟩
  have hD : D ∈ Subgroup.normalizer (LargeEvenSLGroup (Fin N) K : Set (GL (Fin N) K)) :=
    hS (M.mem ⟨d, hw.d_mem⟩)
  have hDpM : D ^ p ∈ LargeEvenScalars (Fin N) K :=
    M.dpow_mem_scalars_of_wSetup (L := L) (A := A') hw
      (linKernelScalar_of_three_le (K := K) (N := N) hN)
  obtain ⟨lam, hlam⟩ := hDpM
  have hDp : D ^ p = Matrix.GeneralLinearGroup.scalar (Fin N) lam := hlam.symm
  have hind : LargeEvenInduces θ (conjRel d)
      (TableB.projConj (LargeEvenSLGroup (Fin N) K) ⟨D, hD⟩) := M.ind ⟨d, hw.d_mem⟩
  have hpk : (p : K) ≠ 0 := natCast_ne_zero_of_card_two_pow hKcard hpre.prime hpre.odd
  obtain ⟨hcompJ, hJT, hTcomp⟩ :=
    lin_component_step hpre.prime hpk hdN θ D hD hDp hind hpre.pcomp
  by_cases hcube : ∃ c : Kˣ, c ^ p = lam
  · obtain ⟨c, hc⟩ := hcube
    exact (hT G p N m L J A' d b K hKcard hN θ hact hS hw hcompJ
      (hpre.not_innDiagOn_of_mi hMI) M ⟨c, by rw [hDp, hc]⟩).elim
  let e := CFSG.LocalAnalysis.GLTheoremA.I2015.linRecipeEquiv N K
  have hφ : MulAut.congr e.symm (TableB.projConj (LargeEvenSLGroup (Fin N) K) ⟨D, hD⟩) =
      LinearFlag.conjAut N K D := projConj_recipe D hD
  have hfix : (fixSubgroup (TableB.projConj (LargeEvenSLGroup (Fin N) K) ⟨D, hD⟩)).map
      e.symm.toMonoidHom = fixSubgroup (LinearFlag.conjAut N K D) := by
    rw [← hφ]
    exact (fixSubgroup_congr e.symm _).symm
  have hT'trans : CFSG.Open.IsComponentOf
      (((J.subgroupOf L).map (piCenterQuot θ)).map e.symm.toMonoidHom)
      (fixSubgroup (LinearFlag.conjAut N K D)) := by
    have h1 := CFSG.Fischer.Classification.Recognition.IsComponentOf.map_mulEquiv e.symm hTcomp
    rwa [hfix] at h1
  obtain ⟨hpN', h2Np, huniq, E, hEfield, hEfin, hEcard, g, hgsurj, hgker⟩ :=
    lin_field_type_data hpre hKcard hDp hcube hT'trans
  letI := hEfield
  letI := hEfin
  have hLayer : GLALayer (L ⊓ Subgroup.centralizer ({d} : Set G)) = J :=
    lin_field_layer hpre θ D hD hind hcompJ huniq
  let T : Subgroup (LinearFlag.projectiveSL N K) :=
    ((J.subgroupOf L).map (piCenterQuot θ)).map e.symm.toMonoidHom
  let eJ : ↥((J.subgroupOf L).map (piCenterQuot θ)) ≃* ↥T :=
    Subgroup.equivMapOfInjective _ e.symm.toMonoidHom e.symm.injective
  have hcat := lin_catalogue_field hpre θ hKcard h2Np hEcard hJT hTcomp eJ hgsurj hgker
  exact ⟨⟨hcompJ, hLayer⟩, (Nat.le_div_iff_mul_le hpre.prime.pos).mp h2Np, hcat⟩

end CFSG.LocalAnalysis.GLTheoremA.T158

end
