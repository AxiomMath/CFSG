module

public import CFSG.GH74.GLS.IVK.Proofs2.Lemma44bOrd
public import CFSG.GH74.GLS.Stage1.Main.NoFAutProof
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LnToral
public import CFSG.HardMathSupport.Solomon.Coordinator.L514B182
public import CFSG.HardMathSupport.Solomon.LocalBalance.AutL3Struct
public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultLie
public import CFSG.LocalAnalysis.GLTheoremA.S4.LBalanceBridge
public import CFSG.LocalAnalysis.GLTheoremA.S6.InputsAlt73
public import CFSG.LocalAnalysis.GLTheoremA.S9.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S9.Inputs95
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt
public import CFSG.RankThree.PartTwo.Sec16.KSL3TwoTailProofKP1Short

public section

namespace CFSG.LocalAnalysis.GLTheoremA

section Schreier


theorem lBalanceAt_holds (G : Type) [Group G] [Finite G] (p : ℕ) (hp : p.Prime) :
    LBalanceAt G p :=
  lBalanceAt_of_catalogueSchreier
    (CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog
      CFSG.RankThree.PartOne.SPOR.schreierFor_catalog) hp

theorem input18_3_4_holds : CFSG.HardMathSupport.Solomon.UniquenessMaximal.Input18_3_4 :=
  CFSG.HardMathSupport.Solomon.Coordinator.input18_3_4_of_schreier
    (CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog
      CFSG.RankThree.PartOne.SPOR.schreierFor_catalog)

theorem i182At_holds (G : Type) [Group G] [Finite G] : I182At G :=
  CFSG.HardMathSupport.Solomon.Coordinator.lemma514Cover_input18_2_of_schreier
    (CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog
      CFSG.RankThree.PartOne.SPOR.schreierFor_catalog) G

end Schreier

section Griess


theorem i61L62At_holds : I61L62At := by
  intro Q _ _ hcomm hcat
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  cases i with
  | cyclic _ _ => exact hi.elim
  | alternating _ _ => exact hi.elim
  | sporadic _ => exact hi.elim
  | lie j =>
    obtain ⟨d, hv⟩ := j
    have hd : d = TauCeti.LieTypeIndex.A 5 gfTwoPP := hi
    subst hd
    have hm := CFSG.Models.lieModel_A 5 gfTwoPP hv e
    rcases hm.2 with hcl | ⟨h0, -⟩
    swap
    · exact absurd h0 (by norm_num)
    obtain ⟨-, F, hFf, hFfin, hFcard, ⟨eF⟩⟩ := hcl
    haveI := CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln.isSimpleGroup_projectiveSL (K := F) (n := 5 + 1)
      (by norm_num)
    have hsimp : IsSimpleGroup (Q ⧸ Subgroup.center Q) :=
      (eF.trans (CFSG.QuasithinUnique.Id2519.projectiveSLEquivStatedProj (5 + 1) F).symm).isSimpleGroup
    have hQ : CFSG.Open.IsQuasisimple Q := ⟨hcomm, hsimp⟩
    have hgo : CFSG.Blueprint.Multiplier.genericOrders .PSL (5 + 1) gfTwoPP.p gfTwoPP.exponent =
        (1, 1) := by
      decide
    have heo : CFSG.Blueprint.Multiplier.exceptionalOrders .PSL (5 + 1) gfTwoPP.p gfTwoPP.exponent =
        (1, 1) := rfl
    have hdvd := card_center_dvd_of_table
      CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement hQ hm hgo heo (by norm_num)
    exact Nat.dvd_one.mp (by simpa using hdvd)

end Griess

section Lie


open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut)

theorem i71L62At_holds (G : Type) [Group G] [Finite G] : I71L62At G := by
  intro K hK b hb hbp
  obtain ⟨hcat, hcen⟩ := hK
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  cases i with
  | cyclic _ _ => exact hi.elim
  | alternating _ _ => exact hi.elim
  | sporadic _ => exact hi.elim
  | lie j =>
    obtain ⟨d, hv⟩ := j
    have hd : d = TauCeti.LieTypeIndex.A 5 gfTwoPP := hi
    subst hd
    have hm := CFSG.Models.lieModel_A 5 gfTwoPP hv e
    rcases hm.2 with hcl | ⟨h0, -⟩
    swap
    · exact absurd h0 (by norm_num)
    obtain ⟨-, F, hFf, hFfin, hFcard, ⟨eF⟩⟩ := hcl
    have hPS : CFSG.Yardstones.Md0ec50421ce4.PSimple 3 K ≃* PQuot 3 K :=
      (QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot
    have ePQ := hPS.symm.trans eF
    have ePQ' := ePQ.trans (CFSG.QuasithinUnique.Id2519.projectiveSLEquivStatedProj (5 + 1) F).symm
    have hOut : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer (PQuot 3 K)) ∣ 2 := by
      have h := CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.higher_linear_outer_order_divides_field_gcd_bound
        (k := F) Nat.prime_two le_rfl (by norm_num : 3 ≤ 5 + 1) hFcard
      rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence ePQ').toEquiv]
      simpa using h
    haveI : Finite (CFSG.ComponentClassification.OuterAutomorphisms.Outer (PQuot 3 K)) :=
      Nat.finite_of_card_ne_zero (fun h0 => by rw [h0] at hOut; norm_num at hOut)
    obtain ⟨k, hk⟩ := hbp ⟨b, Subgroup.mem_zpowers b⟩
    have hbk : b ^ 3 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hpow : barAut 3 K ⟨b, hb⟩ ^ 3 ^ k = 1 := by
      rw [← map_pow]
      have h1 : (⟨b, hb⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ 3 ^ k = 1 :=
        Subtype.ext (by simpa using hbk)
      rw [h1, map_one]
    have hxpow : (QuotientGroup.mk (barAut 3 K ⟨b, hb⟩) :
        CFSG.ComponentClassification.OuterAutomorphisms.Outer (PQuot 3 K)) ^ 3 ^ k = 1 := by
      rw [← QuotientGroup.mk_pow, hpow]
      rfl
    have hord1 := orderOf_dvd_of_pow_eq_one hxpow
    have hord2 := (orderOf_dvd_natCard (QuotientGroup.mk (barAut 3 K ⟨b, hb⟩) :
        CFSG.ComponentClassification.OuterAutomorphisms.Outer (PQuot 3 K))).trans hOut
    have hgcd := Nat.dvd_gcd hord1 hord2
    have hcop : Nat.gcd (3 ^ k) 2 = 1 := Nat.Coprime.pow_left k (by norm_num)
    rw [hcop] at hgcd
    have hx1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hgcd)
    have hmem := (QuotientGroup.eq_one_iff (barAut 3 K ⟨b, hb⟩)).mp hx1
    exact (inducesInnerMod_iff_barAut_mem_inner hb).mpr hmem

end Lie

section Dickson

theorem i7_false_of_three {S : Type} [Group S] [Nontrivial S] [Group.IsPerfect S]
    (ψ : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3) →* S) (hψ : Function.Surjective ψ) : False := by
  haveI := CFSG.GH74.GLS.Stage1.Main.isSolvable_sl2_zmod_three
  exact Group.IsPerfect.not_isSolvable S (Group.isSolvable_of_surjective hψ)

theorem i7_psl_iso_of_surjective (r : ℕ) [Fact r.Prime] (h5 : 5 ≤ r) {S : Type} [Group S]
    [IsSimpleGroup S] [Group.IsPerfect S] (ψ : Matrix.SpecialLinearGroup (Fin 2) (ZMod r) →* S)
    (hψ : Function.Surjective ψ) :
    Nonempty (S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod r)) := by
  haveI : NeZero r := ⟨by omega⟩
  have hnotTop : Subgroup.center S ≠ ⊤ := by
    intro htop
    have hmc : IsMulCommutative S := Subgroup.center_eq_top_iff.mp htop
    exact not_subsingleton S inferInstance
  have hZ : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod r)) ≤ ψ.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    have hcS : ψ z ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨x, rfl⟩ := hψ g
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz x]
    rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center S) with h | h
    · rw [h] at hcS
      exact Subgroup.mem_bot.mp hcS
    · exact absurd h hnotTop
  let χ : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod r) →* S :=
    QuotientGroup.lift (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod r))) ψ hZ
  have hχs : Function.Surjective χ := by
    intro s
    obtain ⟨x, hx⟩ := hψ s
    exact ⟨QuotientGroup.mk x, hx⟩
  have hsimpleL : IsSimpleGroup
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 2 (ZMod r)) :=
    CFSG.RankThree.PartTwo.Sec16.ProofKS1624KP1.isSimpleGroup_projectiveSL_two
      (F := ZMod r) (by rw [Nat.card_zmod]; omega)
  have hsimple : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod r)) :=
    (QuotientGroup.quotientMulEquivOfEq
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center 2 (ZMod r)).symm).isSimpleGroup
  have hker : χ.ker = ⊥ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top χ.ker with h | h
    · exact h
    · exfalso
      apply not_subsingleton S
      refine ⟨fun a b => ?_⟩
      obtain ⟨x, rfl⟩ := hχs a
      obtain ⟨y, rfl⟩ := hχs b
      have hx : x ∈ χ.ker := by rw [h]; exact Subgroup.mem_top x
      have hy : y ∈ χ.ker := by rw [h]; exact Subgroup.mem_top y
      rw [MonoidHom.mem_ker.mp hx, MonoidHom.mem_ker.mp hy]
  exact ⟨(MulEquiv.ofBijective χ ⟨(MonoidHom.ker_eq_bot_iff χ).mp hker, hχs⟩).symm⟩

theorem i7_valid_A1 (r : ℕ) (hr : r.Prime) (h7 : 7 ≤ r) :
    (TauCeti.LieTypeIndex.A 1 ⟨r, 1, hr, Nat.one_pos⟩).Valid := by
  have h9 : r ≠ 9 := by
    rintro rfl
    norm_num at hr
  rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
    TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
  simp only [TauCeti.PrimePower.card_def, pow_one]
  omega

theorem i7_catalog_of_psl (r : ℕ) [hr : Fact r.Prime] (h5 : 5 ≤ r)
    {S : Type} [Group S] (e : S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod r)) :
    CFSG.Yardstones.Md0ec50421ce4.catalogIs S CFSG.LocalAnalysis.GLTheoremA.S9.isL2prime := by
  by_cases h5' : r = 5
  · subst h5'
    obtain ⟨f⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five (ZMod 5)
      (Or.inr (Nat.card_zmod 5))
    have hA : S ≃* (TauCeti.CFSGIndex.alternating 5 (le_refl 5)).Group :=
      e.trans ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 (ZMod 5)).trans f)
    exact ⟨TauCeti.CFSGIndex.alternating 5 (le_refl 5),
      by simp [CFSG.LocalAnalysis.GLTheoremA.S9.isL2prime], ⟨hA⟩⟩
  · have h7 : 7 ≤ r := by
      have hne6 : r ≠ 6 := fun h => by
        have := (Fact.out : r.Prime)
        rw [h] at this
        norm_num at this
      omega
    have hv := i7_valid_A1 r hr.out h7
    haveI : NeZero r := ⟨by omega⟩
    haveI : Fact (Nat.Prime (⟨r, 1, hr.out, Nat.one_pos⟩ : TauCeti.PrimePower).p) := ⟨hr.out⟩
    have hcard : Nat.card (ZMod r) = r ^ 1 := by rw [Nat.card_zmod, pow_one]
    let T : ZMod r ≃+* GaloisField r 1 :=
      CFSG.ClassicalModels.finiteFieldEquivGaloisField (ZMod r) r 1 Nat.one_pos hcard
    let P := CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv T (Fin 2)
    let L := CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1
      (⟨r, 1, hr.out, Nat.one_pos⟩ : TauCeti.PrimePower) hv
    refine ⟨TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.A 1 ⟨r, 1, hr.out, Nat.one_pos⟩, hv⟩,
      ?_, ⟨e.trans (P.trans L.symm)⟩⟩
    simp only [CFSG.LocalAnalysis.GLTheoremA.S9.isL2prime, TauCeti.PrimePower.card_def, pow_one]
    exact ⟨hr.out, by omega⟩

theorem i7_catalog_of_surj (r : ℕ) [Fact r.Prime] (hr2 : r ≠ 2)
    {S : Type} [Group S] [IsSimpleGroup S] [Group.IsPerfect S]
    (ψ : Matrix.SpecialLinearGroup (Fin 2) (ZMod r) →* S) (hψ : Function.Surjective ψ) :
    CFSG.Yardstones.Md0ec50421ce4.catalogIs S CFSG.LocalAnalysis.GLTheoremA.S9.isL2prime := by
  by_cases h3 : r = 3
  · subst h3
    exact (i7_false_of_three ψ hψ).elim
  · have h5 : 5 ≤ r := by
      have h2 := (Fact.out : r.Prime).two_le
      have hne4 : r ≠ 4 := fun h => by
        have := (Fact.out : r.Prime)
        rw [h] at this
        norm_num at this
      omega
    obtain ⟨e⟩ := i7_psl_iso_of_surjective r h5 ψ hψ
    exact i7_catalog_of_psl r h5 e

theorem i7_exists_perfect_cover {Γ S : Type} [Group Γ] [Finite Γ] [Group S] [Nontrivial S]
    [Group.IsPerfect S] (φ : Γ →* S) (hφ : Function.Surjective φ) :
    ∃ K : Subgroup Γ, K.map φ = ⊤ ∧ Group.IsPerfect K ∧ K ≠ ⊥ := by
  classical
  have hex : ∃ n : ℕ, ∃ K : Subgroup Γ, Nat.card K = n ∧ K.map φ = ⊤ :=
    ⟨Nat.card Γ, ⊤, Nat.card_congr Subgroup.topEquiv.toEquiv,
      Subgroup.map_top_of_surjective φ hφ⟩
  obtain ⟨K, hKcard, hKtop⟩ := Nat.find_spec hex
  have hmin : ∀ K' : Subgroup Γ, K'.map φ = ⊤ → Nat.find hex ≤ Nat.card K' :=
    fun K' h => Nat.find_min' hex ⟨K', rfl, h⟩
  have hle : ⁅K, K⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro g₁ h₁ g₂ h₂
    rw [commutatorElement_def]
    exact K.mul_mem (K.mul_mem (K.mul_mem h₁ h₂) (K.inv_mem h₁)) (K.inv_mem h₂)
  have hcomm : ⁅K, K⁆ = K := by
    apply Subgroup.eq_of_le_of_card_ge hle
    by_contra hlt
    have hlt' : Nat.card (⁅K, K⁆ : Subgroup Γ) < Nat.card K := not_le.mp hlt
    have himg : (⁅K, K⁆ : Subgroup Γ).map φ = ⊤ := by
      rw [Subgroup.map_commutator, hKtop]
      exact Group.IsPerfect.commutator_eq_top
    have := hmin _ himg
    omega
  refine ⟨K, hKtop, Subgroup.isPerfect_iff.mpr hcomm, ?_⟩
  intro hK
  obtain ⟨a, ha⟩ := exists_ne (1 : S)
  have hmem : a ∈ K.map φ := by
    rw [hKtop]
    exact Subgroup.mem_top a
  rw [hK, Subgroup.map_bot] at hmem
  exact ha (Subgroup.mem_bot.mp hmem)

theorem i7_catalog_of_cover {Γ S : Type} [Group Γ] [Group S] [IsSimpleGroup S]
    [Group.IsPerfect S] (K : Subgroup Γ) (φ : Γ →* S)
    (hK : K.map φ = ⊤) (r : ℕ) [Fact r.Prime] (hr2 : r ≠ 2)
    (ε : Matrix.SpecialLinearGroup (Fin 2) (ZMod r) ≃* K) :
    CFSG.Yardstones.Md0ec50421ce4.catalogIs S CFSG.LocalAnalysis.GLTheoremA.S9.isL2prime := by
  have hφK : Function.Surjective (φ.comp K.subtype) := by
    intro s
    have hs : s ∈ K.map φ := by
      rw [hK]
      exact Subgroup.mem_top s
    obtain ⟨x, hx, hxs⟩ := Subgroup.mem_map.mp hs
    exact ⟨⟨x, hx⟩, hxs⟩
  exact i7_catalog_of_surj r hr2 ((φ.comp K.subtype).comp ε.toMonoidHom)
    (hφK.comp ε.surjective)

theorem involvedSL2At_holds (G : Type) [Group G] [Finite G] :
    InvolvedSL2At G := by
  intro p q X J hp hq hq2 _hX hJ hinv
  obtain ⟨H, φ, hφ⟩ := hinv
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Finite (Matrix.GeneralLinearGroup (Fin 2) (ZMod q)) := inferInstance
  have hQ := isQuasisimple_pQuot_of_glaPComponent hp hJ
  haveI : Group.IsPerfect (CFSG.Yardstones.Md0ec50421ce4.PQuot p J) := ⟨hQ.1⟩
  haveI : IsSimpleGroup (CFSG.Yardstones.Md0ec50421ce4.PSimple p J) := hQ.2
  haveI : Group.IsPerfect (CFSG.Yardstones.Md0ec50421ce4.PSimple p J) := inferInstance
  obtain ⟨K, hKtop, hKperf, hK0⟩ := i7_exists_perfect_cover φ hφ
  haveI := hKperf
  have hεK := Subgroup.equivMapOfInjective K H.subtype H.subtype_injective
  haveI : Group.IsPerfect ↥(K.map H.subtype) :=
    Group.IsPerfect.ofSurjective (f := hεK.toMonoidHom) hεK.surjective
  have hJne : K.map H.subtype ≠ ⊥ := by
    intro h
    apply hK0
    apply Subgroup.map_injective H.subtype_injective
    rw [h, Subgroup.map_bot]
  rcases CFSG.RankThree.SubgroupLists.perfect_gl2_mulEquiv hq2 (K.map H.subtype) hJne with
    ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact i7_catalog_of_cover K φ hKtop q hq2 (e.symm.trans hεK.symm)
  · haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    exact i7_catalog_of_cover K φ hKtop 5 (by norm_num) (e.symm.trans hεK.symm)

end Dickson

section SL34

theorem i4_sl3_card_four (q P g : ℕ) (hq : 2 ≤ q) (hg : g = Nat.gcd 3 (q - 1))
    (hP : P = 20160) (h : P * g = q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1)) : q = 4 := by
  have hg3 : g ∣ 3 := by rw [hg]; exact Nat.gcd_dvd_left _ _
  have hgle : g ≤ 3 := Nat.le_of_dvd (by norm_num) hg3
  subst hP
  rcases (show q = 2 ∨ q = 3 ∨ q = 4 ∨ 5 ≤ q by omega) with rfl | rfl | rfl | h5
  · have : g = 1 := by rw [hg]; norm_num
    subst this
    norm_num at h
  · have : g = 1 := by rw [hg]; norm_num
    subst this
    norm_num at h
  · rfl
  · exfalso
    have h1 : 125 ≤ q ^ 3 := le_trans (by norm_num) (Nat.pow_le_pow_left h5 3)
    have h2 : 24 ≤ q ^ 2 - 1 := by
      have : 5 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left h5 2
      omega
    have h3 : 124 ≤ q ^ 3 - 1 := by omega
    have h4 : 125 * 24 * 124 ≤ q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
    have h5' : 20160 * g ≤ 20160 * 3 := Nat.mul_le_mul_left _ hgle
    omega

theorem i4_su3_card_false (q P g : ℕ) (hq : 2 ≤ q) (hg : g = Nat.gcd 3 (q + 1))
    (hP : P = 20160) (h : P * g = q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1)) : False := by
  have hg3 : g ∣ 3 := by rw [hg]; exact Nat.gcd_dvd_left _ _
  have hgle : g ≤ 3 := Nat.le_of_dvd (by norm_num) hg3
  subst hP
  rcases (show q = 2 ∨ q = 3 ∨ q = 4 ∨ 5 ≤ q by omega) with rfl | rfl | rfl | h5
  · have : g = 3 := by rw [hg]; norm_num
    subst this
    norm_num at h
  · have : g = 1 := by rw [hg]; norm_num
    subst this
    norm_num at h
  · have : g = 1 := by rw [hg]; norm_num
    subst this
    norm_num at h
  · have h1 : 125 ≤ q ^ 3 := le_trans (by norm_num) (Nat.pow_le_pow_left h5 3)
    have h2 : 24 ≤ q ^ 2 - 1 := by
      have : 5 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left h5 2
      omega
    have h3 : 126 ≤ q ^ 3 + 1 := by omega
    have h4 : 125 * 24 * 126 ≤ q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
    have h5' : 20160 * g ≤ 20160 * 3 := Nat.mul_le_mul_left _ hgle
    omega

theorem i4_ringEquiv_eq_id_of_card_four {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 4) (σ : K ≃+* K) (h3 : ∀ x, σ (σ (σ x)) = x) (x : K) : σ x = x := by
  have hfin : Fintype K := Fintype.ofFinite K
  have hcardF : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card]; exact hK
  obtain ⟨n, hp, hn⟩ := FiniteField.card K (ringChar K)
  have hp2 : ringChar K = 2 := by
    have hdvd : ringChar K ∣ 4 := by
      rw [← hcardF, hn]
      exact dvd_pow_self _ (by exact_mod_cast n.ne_zero)
    have : ringChar K ∣ 2 := by
      have h22 : (4 : ℕ) = 2 * 2 := by norm_num
      rw [h22] at hdvd
      rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h <;> exact h
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this
  have hchar : CharP K 2 := by
    rw [← hp2]
    exact ringChar.charP K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Algebra (ZMod 2) K := ZMod.algebra K 2
  have hcomm : ∀ r : ZMod 2, σ (algebraMap (ZMod 2) K r) = algebraMap (ZMod 2) K r := by
    intro r
    exact congrArg (fun f : ZMod 2 →+* K => f r)
      (RingHom.ext_zmod (σ.toRingHom.comp (algebraMap (ZMod 2) K)) (algebraMap (ZMod 2) K))
  let σ' : K ≃ₐ[ZMod 2] K := AlgEquiv.ofRingEquiv (f := σ) hcomm
  have hσ'3 : σ' ^ 3 = 1 := by
    ext y
    simp only [pow_succ, pow_zero, one_mul, AlgEquiv.mul_apply, AlgEquiv.one_apply]
    exact h3 y
  have hfr : Module.finrank (ZMod 2) K = 2 := by
    have h1 : Nat.card K = 2 ^ Module.finrank (ZMod 2) K := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    rw [hK] at h1
    have : (2 : ℕ) ^ 2 = 2 ^ Module.finrank (ZMod 2) K := by rw [← h1]; norm_num
    exact (Nat.pow_right_injective (le_refl 2) this).symm
  have hgal : Nat.card (K ≃ₐ[ZMod 2] K) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, hfr]
  have hord3 : orderOf σ' ∣ 3 := orderOf_dvd_of_pow_eq_one (by rw [hσ'3])
  have hord2 : orderOf σ' ∣ 2 := by
    have := orderOf_dvd_natCard σ'
    rwa [hgal] at this
  have hord1 : orderOf σ' = 1 := by
    have : orderOf σ' ∣ Nat.gcd 3 2 := Nat.dvd_gcd hord3 hord2
    simpa using this
  have hσ'1 : σ' = 1 := orderOf_eq_one_iff.mp hord1
  have := congrArg (fun g : K ≃ₐ[ZMod 2] K => g x) hσ'1
  simpa [σ'] using this


section I4Matrix

variable {K : Type} [Field K]

noncomputable def i4_diagGL (u : Kˣ) : GL (Fin 3) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    (Matrix.diagonal ![(u : K), ((u⁻¹ : Kˣ) : K), 1]) (by
      rw [Matrix.det_diagonal, Fin.prod_univ_three]
      simp)

lemma i4_diagGL_mem (u : Kˣ) : i4_diagGL (K := K) u ∈ CFSG.Open.StatedSL 3 K :=
  Subgroup.subset_closure (show i4_diagGL (K := K) u ∈
      {A : GL (Fin 3) K | (A : Matrix (Fin 3) (Fin 3) K).det = 1} by
    show (Matrix.diagonal ![(u : K), ((u⁻¹ : Kˣ) : K), 1]).det = 1
    rw [Matrix.det_diagonal, Fin.prod_univ_three]
    simp)

noncomputable def i4_diagSL (u : Kˣ) : ↥(CFSG.Open.StatedSL 3 K) :=
  ⟨i4_diagGL u, i4_diagGL_mem u⟩

lemma i4_diagSL_apply_two (u : Kˣ) :
    ((i4_diagSL u : ↥(CFSG.Open.StatedSL 3 K)) : GL (Fin 3) K) 2 2 = 1 := by
  simp [i4_diagSL, i4_diagGL]

lemma i4_diagSL_apply_zero (u : Kˣ) :
    ((i4_diagSL u : ↥(CFSG.Open.StatedSL 3 K)) : GL (Fin 3) K) 0 0 = (u : K) := by
  simp [i4_diagSL, i4_diagGL]

lemma i4_diagSL_map (σ : K ≃+* K) (u : Kˣ) :
    (((i4_diagSL (Units.map σ.toMonoidHom u) : ↥(CFSG.Open.StatedSL 3 K)) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) =
      (((i4_diagSL u : ↥(CFSG.Open.StatedSL 3 K)) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K).map σ := by
  change Matrix.diagonal _ = (Matrix.diagonal _).map σ
  rw [Matrix.diagonal_map (map_zero σ)]
  congr 1
  funext m
  fin_cases m <;> simp [map_inv₀]

lemma i4_mk_entry {a b : ↥(CFSG.Open.StatedSL 3 K)}
    (h : (QuotientGroup.mk a : CFSG.Open.StatedProj (CFSG.Open.StatedSL 3 K)) =
      QuotientGroup.mk b) :
    ∃ z : K, ∀ i j, (((b : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) i j =
      (((a : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) i j * z := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
  have h' : ((a⁻¹ * b : ↥(CFSG.Open.StatedSL 3 K)) : GL (Fin 3) K) ∈
      CFSG.Open.StatedScalars (Fin 3) K := h
  rw [CFSG.Open.StatedScalars, MonoidHom.mem_range] at h'
  obtain ⟨u, hu⟩ := h'
  refine ⟨(u : K), fun i j => ?_⟩
  have hb : (b : GL (Fin 3) K) =
      (a : GL (Fin 3) K) * Matrix.GeneralLinearGroup.scalar (Fin 3) u := by
    rw [hu]
    simp
  have hm := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) i j) hb
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.mul_diagonal] at hm
  exact hm

end I4Matrix

theorem i4_psl3_case {Y : Type} [Group Y] (hZ : Subgroup.center Y = ⊥) (α : MulAut Y)
    (h3 : α ^ 3 = 1) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    (θ : (Y ⧸ Subgroup.center Y) ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSL 3 K))
    (σ : K ≃+* K) (φ γ : MulAut (CFSG.Open.StatedProj (CFSG.Open.StatedSL 3 K)))
    (hσφ : CFSG.HardMathSupport.Solomon.LocalBalance.IsEntrywiseAutPSL σ φ)
    (hθ : ∀ y : Y, θ (QuotientGroup.mk (α y)) = (γ * φ * γ⁻¹) (θ (QuotientGroup.mk y))) :
    α = 1 := by
  have hα3 : ∀ y : Y, α (α (α y)) = y := by
    intro y
    have := congrArg (fun f : MulAut Y => f y) h3
    simpa [pow_succ, MulAut.mul_apply] using this
  have hψ3 : ∀ y : Y, (γ * φ * γ⁻¹) ((γ * φ * γ⁻¹) ((γ * φ * γ⁻¹) (θ (QuotientGroup.mk y))))
      = θ (QuotientGroup.mk y) := by
    intro y
    have e1 := hθ y
    have e2 := hθ (α y)
    have e3 := hθ (α (α y))
    rw [hα3 y] at e3
    rw [e2, e1] at e3
    exact e3.symm
  have hall : ∀ s, (γ * φ * γ⁻¹) ((γ * φ * γ⁻¹) ((γ * φ * γ⁻¹) s)) = s := by
    intro s
    obtain ⟨x, rfl⟩ := θ.surjective s
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    exact hψ3 y
  have hφ3 : ∀ t, φ (φ (φ t)) = t := by
    intro t
    have h := hall (γ t)
    simp only [MulAut.mul_apply, MulAut.inv_apply_self] at h
    exact γ.injective h
  have hstep : ∀ u : Kˣ, φ (QuotientGroup.mk (i4_diagSL u)) =
      QuotientGroup.mk (i4_diagSL (Units.map σ.toMonoidHom u)) :=
    fun u => hσφ _ _ (i4_diagSL_map σ u)
  have hcycle : ∀ u : Kˣ, σ (σ (σ (u : K))) = (u : K) := by
    intro u
    have hu := hφ3 (QuotientGroup.mk (i4_diagSL u))
    simp only [hstep] at hu
    obtain ⟨z, hz⟩ := i4_mk_entry hu
    have h22 := hz 2 2
    rw [i4_diagSL_apply_two, i4_diagSL_apply_two, one_mul] at h22
    have hz1 : z = 1 := h22.symm
    have h00 := hz 0 0
    rw [i4_diagSL_apply_zero, i4_diagSL_apply_zero, hz1, mul_one] at h00
    simp only [Units.coe_map] at h00
    exact h00.symm
  have hσ3 : ∀ x : K, σ (σ (σ x)) = x := by
    intro x
    by_cases hx : x = 0
    · subst hx
      simp
    · simpa using hcycle (Units.mk0 x hx)
  have hσid : ∀ x, σ x = x := i4_ringEquiv_eq_id_of_card_four hK σ hσ3
  have hφid : ∀ s, φ s = s := by
    intro s
    obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective s
    apply hσφ A A
    ext i j
    simp [Matrix.map_apply, hσid]
  have hφ1 : φ = 1 := MulEquiv.ext fun s => by simpa using hφid s
  apply MulEquiv.ext
  intro y
  have hy' : θ (QuotientGroup.mk (α y)) = θ (QuotientGroup.mk y) := by
    rw [hθ y, hφ1]
    simp
  have hmk : (QuotientGroup.mk (α y) : Y ⧸ Subgroup.center Y) = QuotientGroup.mk y :=
    θ.injective hy'
  rw [QuotientGroup.eq, hZ, Subgroup.mem_bot, inv_mul_eq_one] at hmk
  simpa using hmk

theorem i4_psu3_false {K : Type} [Field K] [Finite K] (q : ℕ) (hK : Nat.card K = q ^ 2)
    (hP : Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 q K)) = 20160) : False := by
  have hq2 : 2 ≤ q := by
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    by_contra hlt
    have hq1 : q ≤ 1 := by omega
    have : q ^ 2 ≤ 1 := by interval_cases q <;> norm_num
    omega
  haveI := Fintype.ofFinite K
  obtain ⟨n, hp, hn⟩ := FiniteField.card K (ringChar K)
  have hdvd : q ∣ ringChar K ^ (n : ℕ) := by
    rw [← hn, ← Nat.card_eq_fintype_card, hK]
    exact dvd_pow_self q two_ne_zero
  obtain ⟨j, -, hqj⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  have hj1 : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with h | h
    · subst h
      simp at hqj
      omega
    · exact h
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData (ringChar K) j K :=
    ⟨hp, hj1, by rw [hK, hqj, ← pow_mul, mul_comm]⟩
  have hform := CFSG.GH74.GLS.IVK.Proofs2.Lemma44bOrd.card_statedProj_statedSU_three_mul hU
  rw [← hqj, hP] at hform
  exact i4_su3_card_false q 20160 (Nat.gcd 3 (q + 1)) hq2 rfl rfl hform

theorem i4_fieldAut_eq_one {Y : Type} [Group Y] (hZ : Subgroup.center Y = ⊥)
    (hY : Nat.card Y = 20160) (α : MulAut Y) (h3 : α ^ 3 = 1)
    (hα : CFSG.HardMathSupport.Solomon.LocalBalance.IsFieldAutThree α) : α = 1 := by
  have hcenter : Nat.card (Y ⧸ Subgroup.center Y) = 20160 := by
    rw [hZ]
    exact (Nat.card_congr QuotientGroup.quotientBot.toEquiv).trans hY
  rcases hα with h | ⟨K, hKf, hKfin, θ, σ, φ, γ, hσφ, hθ⟩ |
    ⟨K, hKf, hKfin, q, θ, σ, φ, γ, hKq, -, hσφ, hθ⟩
  · exact h
  · have hP : Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedSL 3 K)) = 20160 := by
      rw [← Nat.card_congr θ.toEquiv]
      exact hcenter
    have hform :=
      CFSG.GH74.GLS.IVK.Proofs2.Lemma44bOrd.card_statedProj_statedSL_three_mul (F := K)
    rw [hP] at hform
    have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
    have hK4 : Nat.card K = 4 :=
      i4_sl3_card_four (Nat.card K) 20160 (Nat.gcd 3 (Nat.card K - 1)) hq2 rfl rfl hform
    exact i4_psl3_case hZ α h3 hK4 θ σ φ γ hσφ hθ
  · have hP : Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 q K)) = 20160 := by
      rw [← Nat.card_congr θ.toEquiv]
      exact hcenter
    exact (i4_psu3_false q hKq hP).elim

theorem i4_index_A2 (d : TauCeti.LieTypeIndex) (hv : d.Valid)
    (h : S9.isL3four (TauCeti.CFSGIndex.lie ⟨d, hv⟩)) :
    ∃ q : TauCeti.PrimePower, d = TauCeti.LieTypeIndex.A 2 q ∧ q.card = 4 := by
  match d, hv, h with
  | .A r q, hv, h =>
    rcases r with _ | _ | _ | r
    · exact (show False from h).elim
    · exact (show False from h).elim
    · exact ⟨q, rfl, h⟩
    · exact (show False from h).elim
  | .twistedA _ _, _, h => exact (show False from h).elim
  | .B _ _, _, h => exact (show False from h).elim
  | .C _ _, _, h => exact (show False from h).elim
  | .D _ _, _, h => exact (show False from h).elim
  | .twistedD _ _, _, h => exact (show False from h).elim
  | .E6 _, _, h => exact (show False from h).elim
  | .E7 _, _, h => exact (show False from h).elim
  | .E8 _, _, h => exact (show False from h).elim
  | .F4 _, _, h => exact (show False from h).elim
  | .G2 _, _, h => exact (show False from h).elim
  | .twistedE6 _, _, h => exact (show False from h).elim

theorem i71SL34At_holds (G : Type) [Group G] [Finite G] : I71SL34At G := by
  intro X L B hL hcat hB hBN
  have hp : Nat.Prime 3 := Nat.prime_three
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  cases i with
  | cyclic _ _ => exact (show False from hi).elim
  | alternating _ _ => exact (show False from hi).elim
  | sporadic _ => exact (show False from hi).elim
  | lie j =>
    obtain ⟨d, hv⟩ := j
    obtain ⟨q, rfl, hq4⟩ := i4_index_A2 d hv hi
    have hm := CFSG.Models.lieModel_A 2 q hv e
    rcases hm.2 with hcl | ⟨h0, -⟩
    swap
    · exact absurd h0 (by norm_num)
    obtain ⟨-, K, hKf, hKfin, hKcard, ⟨eK⟩⟩ := hcl
    have hK4 : Nat.card K = 4 := by
      rw [hKcard, ← TauCeti.PrimePower.card_def]
      exact hq4
    have eK' : CFSG.Yardstones.Md0ec50421ce4.PSimple 3 L ≃*
        CFSG.Open.StatedProj (CFSG.Open.StatedSL 3 K) := eK
    have hExt : CFSG.HardMathSupport.Solomon.LocalBalance.IsExtremalType
        (CFSG.Yardstones.Md0ec50421ce4.PSimple 3 L) :=
      Or.inl ⟨K, hKf, hKfin, by rw [hK4], ⟨eK'⟩⟩
    have hPQ := CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_pQuot_of_glaPComponent hp hL
    have hQ : CFSG.Open.IsQuasisimple (CFSG.Yardstones.Md0ec50421ce4.PSimple 3 L) :=
      CFSG.ComponentClassification.Quasisimple.central_quotient hPQ (Subgroup.center _) le_rfl
    have hsimp : IsSimpleGroup (CFSG.Yardstones.Md0ec50421ce4.PSimple 3 L) := hPQ.2
    have hZ : Subgroup.center (CFSG.Yardstones.Md0ec50421ce4.PSimple 3 L) = ⊥ := by
      rcases hsimp.eq_bot_or_eq_top_of_normal (Subgroup.center _) with h | h
      · exact h
      · exfalso
        have hc : commutator (CFSG.Yardstones.Md0ec50421ce4.PSimple 3 L) = ⊥ :=
          (commutator_eq_bot_iff_center_eq_top _).mpr h
        have ht := hQ.1
        rw [hc] at ht
        exact bot_ne_top ht
    have hY : Nat.card (CFSG.Yardstones.Md0ec50421ce4.PSimple 3 L) = 20160 := by
      rw [Nat.card_congr eK'.toEquiv]
      have hform :=
        CFSG.GH74.GLS.IVK.Proofs2.Lemma44bOrd.card_statedProj_statedSL_three_mul (F := K)
      rw [hK4] at hform
      norm_num at hform
      omega
    let N : Subgroup G := Subgroup.normalizer (L : Set G)
    let H : Subgroup N := B.subgroupOf N
    let ψ : H →* MulAut (CFSG.Yardstones.Md0ec50421ce4.PSimple 3 L) :=
      (CFSG.LocalAnalysis.GLTheoremA.chevAut 3 L).comp H.subtype
    have hcardH : Nat.card H = Nat.card B :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBN).toEquiv
    have hsplit : Nat.card H = Nat.card ψ.range * Nat.card ψ.ker := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
    have hf : Function.Injective (N.subtype.comp H.subtype) :=
      Subtype.val_injective.comp Subtype.val_injective
    have hmap : ψ.ker.map (N.subtype.comp H.subtype) =
        B ⊓ CFSG.LocalAnalysis.GLTheoremA.centModSubgroup 3 L := by
      ext g
      simp only [Subgroup.mem_map, MonoidHom.mem_ker, Subgroup.mem_inf]
      constructor
      · rintro ⟨x, hx, rfl⟩
        have hx' : CFSG.LocalAnalysis.GLTheoremA.chevAut 3 L x.1 = 1 := hx
        have hcent : CFSG.Yardstones.Md0ec50421ce4.CentMod 3 L (x.1 : G) :=
          (CFSG.LocalAnalysis.GLTheoremA.chevAut_eq_one_iff hp hL x.1.2).1 hx'
        exact ⟨Subgroup.mem_subgroupOf.1 x.2,
          CFSG.LocalAnalysis.GLTheoremA.centMod_iff.1 hcent⟩
      · rintro ⟨hgB, hgC⟩
        have hgN : g ∈ N := (CFSG.LocalAnalysis.GLTheoremA.mem_centModSubgroup.1 hgC).1
        refine ⟨⟨⟨g, hgN⟩, Subgroup.mem_subgroupOf.2 hgB⟩, ?_, rfl⟩
        show CFSG.LocalAnalysis.GLTheoremA.chevAut 3 L ⟨g, hgN⟩ = 1
        exact (CFSG.LocalAnalysis.GLTheoremA.chevAut_eq_one_iff hp hL hgN).2
          (CFSG.LocalAnalysis.GLTheoremA.centMod_iff.2 hgC)
    have hkerCard : Nat.card ψ.ker =
        Nat.card ↥(B ⊓ CFSG.LocalAnalysis.GLTheoremA.centModSubgroup 3 L) := by
      rw [← hmap, Subgroup.card_map_of_injective hf]
    have hHcomm : ∀ x y : H, x * y = y * x := by
      intro x y
      have hxB : (x.1 : G) ∈ B := Subgroup.mem_subgroupOf.1 x.2
      have hyB : (y.1 : G) ∈ B := Subgroup.mem_subgroupOf.1 y.2
      have h1 := congrArg Subtype.val
        ((isMulCommutative_iff.mp hB.1) ⟨(x.1 : G), hxB⟩ ⟨(y.1 : G), hyB⟩)
      apply Subtype.ext
      apply Subtype.ext
      simpa using h1
    have hE0 : CFSG.Open.IsElemAbelian 3 ψ.range := by
      refine ⟨isMulCommutative_iff.mpr ?_, ?_⟩
      · rintro ⟨a, ha⟩ ⟨b, hb⟩
        obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 ha
        obtain ⟨y, rfl⟩ := MonoidHom.mem_range.1 hb
        apply Subtype.ext
        show ψ x * ψ y = ψ y * ψ x
        rw [← map_mul, ← map_mul, hHcomm x y]
      · intro a ha
        obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 ha
        have hxB : (x.1 : G) ∈ B := Subgroup.mem_subgroupOf.1 x.2
        have hx3 : x ^ 3 = 1 := by
          apply Subtype.ext
          apply Subtype.ext
          simpa using hB.2 _ hxB
        rw [← map_pow, hx3, map_one]
    obtain ⟨F, hFle, hFindex, hFfield⟩ :=
      CFSG.HardMathSupport.Solomon.LocalBalance.AutL3.input7_L3Aut_holds
        (CFSG.Yardstones.Md0ec50421ce4.PSimple 3 L) hQ (Or.inl hExt) ψ.range hE0
    have hFtriv : F = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro α hα
      exact i4_fieldAut_eq_one hZ hY α (hE0.2 α (hFle hα)) (hFfield α hα)
    have hsub : F.subgroupOf ψ.range = ⊥ := by
      rw [hFtriv]
      ext x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_bot, Subgroup.mem_bot]
      constructor
      · intro h
        exact Subtype.ext h
      · intro h
        rw [h]
        rfl
    have hE0card : Nat.card ψ.range ≤ 9 := by
      have h9 := hFindex
      rw [hsub, Subgroup.index_bot] at h9
      exact h9
    calc Nat.card B = Nat.card H := hcardH.symm
      _ = Nat.card ψ.range * Nat.card ψ.ker := hsplit
      _ ≤ 9 * Nat.card ψ.ker := Nat.mul_le_mul_right _ hE0card
      _ = 9 * Nat.card ↥(B ⊓ CFSG.LocalAnalysis.GLTheoremA.centModSubgroup 3 L) := by
        rw [hkerCard]

end SL34

end CFSG.LocalAnalysis.GLTheoremA
