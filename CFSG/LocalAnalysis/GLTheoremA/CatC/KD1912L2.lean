module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1912Core
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1912Facts
public import CFSG.CharacterTheory.PSL2Table.Partition
public import CFSG.CharacterTheory.PSL2Table.Classes
public import CFSG.Dihedral.Glauberman.DicksonMaxStructure
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthLinearOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddQuadraticIsotropy
public import CFSG.RankThree.PartTwo.KFacts.K72FixL2
public import CFSG.RankThree.PartTwo.KFacts.K71bOutAbelian
public import CFSG.HardMathSupport.Solomon.Coordinator.I19_5_2L2Fix
public import CFSG.GroupTheory.ABGLocalTools.PStabilityQDickson
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_14
public import CFSG.Foundations.SteinbergCADefinitionNodes
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreBasics
public import CFSG.Adapters.LinearCatalog

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD1912

open CFSG.Open CFSG.PSL2Table CFSG.GorensteinWalter
open CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.RankThree.PartTwo.KFacts
open scoped commutatorElement

private theorem isCyclic_centralizer_of_mem_splitTorus
    {F : Type} [Field F] [Fintype F] (hF2 : ringChar F ≠ 2)
    {y : PSL2 F} (hyT : y ∈ splitTorus F) (hyord : orderOf y = 3) :
    IsCyclic (Subgroup.centralizer ({y} : Set (PSL2 F))) := by
  have hy1 : y ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hyord
    omega
  have hle : Subgroup.centralizer ({y} : Set (PSL2 F)) ≤ splitTorus F := by
    intro g hg
    have hgy : g * y * g⁻¹ = y := by
      have h := Subgroup.mem_centralizer_singleton_iff.mp hg
      calc g * y * g⁻¹ = y * g * g⁻¹ := by rw [h]
        _ = y := by group
    have hmem : g * y * g⁻¹ ∈ splitTorus F := by rw [hgy]; exact hyT
    rcases (splitTorus_conj_mem_iff hyT hy1 g).mp hmem with h | h
    · exact h
    · obtain ⟨t, htmem, ht⟩ := h
      let t' : PSL2 F := mk t
      have ht'T : t' ∈ splitTorus F := ⟨t, htmem, rfl⟩
      have hg_eq : g = splitWeyl F * t' := by
        calc g = splitWeyl F * (splitWeyl F)⁻¹ * g := by group
          _ = splitWeyl F * ((splitWeyl F)⁻¹ * g) := by group
          _ = splitWeyl F * t' := by rw [show t' = (splitWeyl F)⁻¹ * g from ht]
      have hty : t' * y * t'⁻¹ = y := by
        rw [splitTorus_mul_comm ht'T hyT, mul_assoc, mul_inv_cancel, mul_one]
      have hinv : g * y * g⁻¹ = y⁻¹ := by
        rw [hg_eq]
        calc splitWeyl F * t' * y * (splitWeyl F * t')⁻¹
            = splitWeyl F * (t' * y * t'⁻¹) * (splitWeyl F)⁻¹ := by group
          _ = splitWeyl F * y * (splitWeyl F)⁻¹ := by rw [hty]
          _ = y⁻¹ := splitWeyl_conj hyT
      have hyy : y = y⁻¹ := hgy.symm.trans hinv
      have hy2 : y * y = 1 := (eq_inv_iff_mul_eq_one).mp hyy
      have hdvd : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hy2)
      have := Nat.le_of_dvd (by norm_num) hdvd
      omega
  letI : IsCyclic (splitTorus F) := splitTorus_isCyclic
  exact Subgroup.isCyclic_of_le hle

private theorem isCyclic_centralizer_of_mem_nonsplitTorus
    {F : Type} [Field F] [Fintype F] (hF2 : ringChar F ≠ 2) {ν : F} (hν : ¬ IsSquare ν)
    {y : PSL2 F} (hyT : y ∈ nonsplitTorus ν) (hyord : orderOf y = 3) :
    IsCyclic (Subgroup.centralizer ({y} : Set (PSL2 F))) := by
  obtain ⟨w, hw_not, hw_sq, hw_inv, hw_iff⟩ := exists_nonsplitWeyl hF2 hν
  have hy1 : y ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hyord
    omega
  have hle : Subgroup.centralizer ({y} : Set (PSL2 F)) ≤ nonsplitTorus ν := by
    intro g hg
    have hgy : g * y * g⁻¹ = y := by
      have h := Subgroup.mem_centralizer_singleton_iff.mp hg
      calc g * y * g⁻¹ = y * g * g⁻¹ := by rw [h]
        _ = y := by group
    have hmem : g * y * g⁻¹ ∈ nonsplitTorus ν := by rw [hgy]; exact hyT
    rcases (hw_iff y hyT hy1 g).mp hmem with h | h
    · exact h
    · obtain ⟨t, htmem, ht⟩ := h
      let t' : PSL2 F := mk t
      have ht'T : t' ∈ nonsplitTorus ν := ⟨t, htmem, rfl⟩
      have hg_eq : g = w * t' := by
        calc g = w * w⁻¹ * g := by group
          _ = w * (w⁻¹ * g) := by group
          _ = w * t' := by rw [show t' = w⁻¹ * g from ht]
      have hty : t' * y * t'⁻¹ = y := by
        rw [nonsplitTorus_mul_comm ht'T hyT, mul_assoc, mul_inv_cancel, mul_one]
      have hinv : g * y * g⁻¹ = y⁻¹ := by
        rw [hg_eq]
        calc w * t' * y * (w * t')⁻¹
            = w * (t' * y * t'⁻¹) * w⁻¹ := by group
          _ = w * y * w⁻¹ := by rw [hty]
          _ = y⁻¹ := hw_inv y hyT
      have hyy : y = y⁻¹ := hgy.symm.trans hinv
      have hy2 : y * y = 1 := (eq_inv_iff_mul_eq_one).mp hyy
      have hdvd : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hy2)
      have := Nat.le_of_dvd (by norm_num) hdvd
      omega
  letI : IsCyclic (nonsplitTorus ν) :=
    CFSG.Glauberman.Dickson.MaxStructure.nonsplitTorus_isCyclic hν
  exact Subgroup.isCyclic_of_le hle

private theorem isCyclic_centralizer_psl2_of_odd_card_order_three
    {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    (h4 : 4 ≤ Nat.card F) (h3 : ¬ 3 ∣ Nat.card F) {x : PSL2 F} (hx : orderOf x = 3) :
    IsCyclic (Subgroup.centralizer ({x} : Set (PSL2 F))) := by
  classical
  let : Fintype F := Fintype.ofFinite F
  have hF2 : ringChar F ≠ 2 :=
    CFSG.ComponentClassification.CatalogueBOddQuadratic.char_ne_two_of_odd_card hodd
  have h5 : 5 ≤ Nat.card F := by
    obtain ⟨k, hk⟩ := hodd
    omega
  have hq5 : 5 ≤ Fintype.card F := by
    simpa [Nat.card_eq_fintype_card] using h5
  obtain ⟨ν, hν⟩ := FiniteField.exists_nonsquare hF2
  rcases mem_conjSet_cases hF2 hq5 hν x with hx1 | hU | hT | hS
  · rw [hx1, orderOf_one] at hx
    omega
  · obtain ⟨-, g, hg⟩ := hU
    have hxconj : orderOf (g * x * g⁻¹) = 3 := by
      change orderOf ((MulAut.conj g) x) = 3
      rw [MulEquiv.orderOf_eq, hx]
    let p := ringChar F
    have hp : p.Prime := CharP.char_is_prime F p
    let : Fact p.Prime := ⟨hp⟩
    obtain ⟨f, hfpos, hFcard⟩ := FiniteField.card F p
    have h2F : (2 : F) ≠ 0 := Ring.two_ne_zero hF2
    have hUcard : Nat.card (unipotent F) = p ^ (f : ℕ) := by
      rw [card_unipotent h2F, hFcard]
    have hUp : IsPGroup p (unipotent F) := IsPGroup.of_card hUcard
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hUp ⟨g * x * g⁻¹, hg⟩
    rw [Subgroup.orderOf_mk] at hk
    have h3eq : 3 = p ^ k := by rw [← hxconj, hk]
    have hp3 : p = 3 := by
      rcases k with _ | k
      · simp at h3eq
      · have hpdvd : p ∣ 3 := ⟨p ^ k, by simpa [pow_succ'] using h3eq⟩
        exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hpdvd
    have hpdvdF : p ∣ Nat.card F := by
      rw [Nat.card_eq_fintype_card, hFcard]
      exact dvd_pow_self p f.pos.ne'
    exact absurd (hp3 ▸ hpdvdF) h3
  · obtain ⟨-, g, hg⟩ := hT
    let y := g * x * g⁻¹
    have hyord : orderOf y = 3 := by
      change orderOf ((MulAut.conj g) x) = 3
      rw [MulEquiv.orderOf_eq, hx]
    have hycyc : IsCyclic (Subgroup.centralizer ({y} : Set (PSL2 F))) :=
      isCyclic_centralizer_of_mem_splitTorus hF2 hg hyord
    exact (CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator.elementCentralizerEquiv
      (MulAut.conj g) x).isCyclic.mpr hycyc
  · obtain ⟨-, g, hg⟩ := hS
    let y := g * x * g⁻¹
    have hyord : orderOf y = 3 := by
      change orderOf ((MulAut.conj g) x) = 3
      rw [MulEquiv.orderOf_eq, hx]
    have hycyc : IsCyclic (Subgroup.centralizer ({y} : Set (PSL2 F))) :=
      isCyclic_centralizer_of_mem_nonsplitTorus hF2 hν hg hyord
    exact (CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator.elementCentralizerEquiv
      (MulAut.conj g) x).isCyclic.mpr hycyc

private theorem isCyclic_centralizer_psl2_of_even_card_order_three
    {F : Type} [Field F] [Finite F] (heven : Even (Nat.card F))
    (h4 : 4 ≤ Nat.card F) {x : PSL2 F} (hx : orderOf x = 3) :
    IsCyclic (Subgroup.centralizer ({x} : Set (PSL2 F))) := by
  obtain ⟨f, hf, hcard⟩ :=
    CFSG.ShultStronglyClosedTI.TwoCoreGrowth.even_field_binary_size heven h4
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx
    omega
  have hxodd : Odd (orderOf x) := by
    rw [hx]
    exact ⟨1, rfl⟩
  exact (CFSG.ShultStronglyClosedTI.TwoCoreGrowth.psl2_even_odd_element_full_centralizer
    f hf hcard x hx1 hxodd).1

private theorem isCyclic_centralizer_psl2_order_three
    {F : Type} [Field F] [Finite F] (h4 : 4 ≤ Nat.card F)
    (h3 : ¬ 3 ∣ Nat.card F) {x : PSL2 F} (hx : orderOf x = 3) :
    IsCyclic (Subgroup.centralizer ({x} : Set (PSL2 F))) := by
  rcases Nat.even_or_odd (Nat.card F) with heven | hodd
  · exact isCyclic_centralizer_psl2_of_even_card_order_three heven h4 hx
  · exact isCyclic_centralizer_psl2_of_odd_card_order_three hodd h4 h3 hx

private theorem pPrimeCore_three_psl2_of_card_two
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    CFSG.pPrimeCore 3 (PSL2 K) = ⊥ := by
  classical
  let : Fintype K := Fintype.ofFinite K
  have hchar : ringChar K = 2 :=
    FiniteField.even_card_iff_char_two.mpr (by rw [← Nat.card_eq_fintype_card, hK])
  have hneg : (-1 : K) = 1 := neg_one_eq_one_iff.mpr hchar
  have hcard6 : Nat.card (PSL2 K) = 6 := by
    have h := CFSG.BenderSuzuki.External.huppert614_card_psl_mul_center (K := K)
    rw [CFSG.BenderSuzuki.External.huppert614_card_center_of_neg_one_eq_one hneg, hK] at h
    simpa using h
  rw [CFSG.pPrimeCore_eq_bot_iff]
  intro N hN hcop
  have hdvd : Nat.card N ∣ 6 := hcard6 ▸ Subgroup.card_subgroup_dvd_card N
  have hnot3 : ¬ 3 ∣ Nat.card N :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcop
  have hNcard : Nat.card N = 1 ∨ Nat.card N = 2 := by
    have hpos : 0 < Nat.card N := Nat.card_pos
    have hle : Nat.card N ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases Nat.card N <;> simp_all
  rcases hNcard with h1 | h2
  · exact Subgroup.card_eq_one.mp h1
  · have hle : N ≤ Subgroup.center (PSL2 K) :=
      CFSG.ABGLocalTools.le_center_of_normal_of_card_eq_two hN h2
    rw [psl2_center_eq_bot K] at hle
    exact le_bot_iff.mp hle

private theorem pPrimeCore_three_l2opFix_of_outer_order_three
    {F : Type} [Field F] [Finite F] (h3 : ¬ 3 ∣ Nat.card F) (h4 : 4 ≤ Nat.card F)
    {x : MulAut (PSL2 F)} (hx3 : x ^ 3 = 1) (hout : ¬ IsInnerAut x) :
    CFSG.pPrimeCore 3 ↥(l2opFix x) = ⊥ := by
  obtain ⟨σ, hσ3, ⟨e⟩⟩ := exists_eqLocus_mulEquiv_psl2 hx3 hout
  have hK : Nat.card (GH74.GLS.IVK.fixedField σ) ^ 3 = Nat.card F := by
    have h := GH74.GLS.IVK.fixedField_card_pow σ
    rw [hσ3] at h
    exact h
  have hq2 : 2 ≤ Nat.card (GH74.GLS.IVK.fixedField σ) := by
    by_contra h
    have h1 : Nat.card (GH74.GLS.IVK.fixedField σ) = 1 := by
      have := Nat.card_pos (α := GH74.GLS.IVK.fixedField σ)
      omega
    rw [h1] at hK
    norm_num at hK
    omega
  rcases Nat.lt_or_ge (Nat.card (GH74.GLS.IVK.fixedField σ)) 4 with hlt | hge
  · have hq0 : Nat.card (GH74.GLS.IVK.fixedField σ) = 2 ∨
        Nat.card (GH74.GLS.IVK.fixedField σ) = 3 := by omega
    rcases hq0 with h2 | h3q
    · have hcore : CFSG.pPrimeCore 3 (PSL2 (GH74.GLS.IVK.fixedField σ)) = ⊥ :=
        pPrimeCore_three_psl2_of_card_two h2
      exact l2op_glapPrimeCore_eq_bot_of_mulEquiv e hcore
    · exfalso
      apply h3
      rw [← hK, h3q]
      norm_num
  · obtain ⟨hZ, hq, hdvd, -⟩ :=
      fixedPoints_facts_psl2 hge (by rw [← hK]) hx3 hout
    have hZ' : Subgroup.center (l2opFix x) = ⊥ := by
      unfold l2opFix
      exact hZ
    have hq' : IsQuasisimple (l2opFix x) := by
      unfold l2opFix
      exact hq
    have hqOpen : CFSG.Open.IsQuasisimple (l2opFix x) :=
      ((CFSG.Foundations.SteinbergCA.quasisimple_iff (l2opFix x)).2.2.1).mp hq'
    have hdvd' : 3 ∣ Nat.card (l2opFix x) := by
      unfold l2opFix
      exact hdvd
    have hZP : IsPGroup 3 (Subgroup.center (l2opFix x)) := by
      rw [hZ']
      exact IsPGroup.of_bot
    have hdvdQ : 3 ∣ Nat.card (l2opFix x ⧸ Subgroup.center (l2opFix x)) := by
      rw [hZ']
      rw [Nat.card_congr QuotientGroup.quotientBot.toEquiv]
      exact hdvd'
    exact gLAPPrimeCore_eq_bot_of_quasisimple_of_isPGroup_center Nat.prime_three hqOpen hZP hdvdQ

theorem cyclicCoreFact_three_psl2 (F : Type) [Field F] [Finite F]
    (h3 : ¬ 3 ∣ Nat.card F) (h4 : 4 ≤ Nat.card F) :
    CyclicCoreFact 3 (PSL2 F) := by
  classical
  have hZ : Subgroup.center (PSL2 F) = ⊥ := psl2_center_eq_bot F
  constructor
  · rw [Subgroup.commutator_le]
    intro σ _ τ _
    change σ * τ * σ⁻¹ * τ⁻¹ ∈ (MulAut.conj : PSL2 F →* MulAut (PSL2 F)).range
    exact isInnerAut_commutator_psl2_all σ τ
  · intro x hx
    have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
    by_cases hin : IsInnerAut x
    · obtain ⟨s, rfl⟩ := hin
      have hs : orderOf s = 3 := by
        rw [← orderOf_injective (MulAut.conj : PSL2 F →* MulAut (PSL2 F))
          (l2op_conj_injective hZ) s]
        exact hx
      have hcyc : IsCyclic (Subgroup.centralizer ({s} : Set (PSL2 F))) :=
        isCyclic_centralizer_psl2_order_three h4 h3 hs
      have hfix : l2opFix (MulAut.conj s) = Subgroup.centralizer ({s} : Set (PSL2 F)) := by
        ext t
        rw [l2opFix, Subgroup.mem_centralizer_singleton_iff]
        change (MulAut.conj s) t = t ↔ t * s = s * t
        rw [MulAut.conj_apply]
        constructor
        · intro h
          calc t * s = (s * t * s⁻¹) * s := by rw [h]
            _ = s * t := by group
        · intro h
          calc s * t * s⁻¹ = (t * s) * s⁻¹ := by rw [← h]
            _ = t := by group
      rw [l2op_innerAut_inf_centralizer hZ (MulAut.conj s), hfix]
      have hcycMap : IsCyclic ((Subgroup.centralizer ({s} : Set (PSL2 F))).map
          (MulAut.conj : PSL2 F →* MulAut (PSL2 F))) :=
        ((Subgroup.centralizer ({s} : Set (PSL2 F))).equivMapOfInjective
          (MulAut.conj : PSL2 F →* MulAut (PSL2 F))
          (l2op_conj_injective hZ)).isCyclic.mp hcyc
      letI : IsCyclic ((Subgroup.centralizer ({s} : Set (PSL2 F))).map
          (MulAut.conj : PSL2 F →* MulAut (PSL2 F))) := hcycMap
      exact Subgroup.isCyclic_of_le (CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreOf_le _)
    · have hcore : CFSG.pPrimeCore 3 ↥(l2opFix x) = ⊥ :=
        pPrimeCore_three_l2opFix_of_outer_order_three h3 h4 hx3 hin
      have hH : GLAPPrimeCore 3 ↥(innerAut (PSL2 F) ⊓
          Subgroup.centralizer ({x} : Set (MulAut (PSL2 F)))) = ⊥ := by
        rw [l2op_innerAut_inf_centralizer hZ x]
        exact l2op_glapPrimeCore_eq_bot_of_mulEquiv
          ((l2opFix x).equivMapOfInjective _ (l2op_conj_injective hZ)).symm hcore
      rw [GLAPPrimeCoreOf, hH, Subgroup.map_bot]
      infer_instance

theorem cyclicCoreFact_three_of_mulEquiv_psl2 {S : Type} [Group S] [Finite S]
    {F : Type} [Field F] [Finite F] (h3 : ¬ 3 ∣ Nat.card F) (h4 : 4 ≤ Nat.card F)
    (e : S ≃* PSL2 F) : CyclicCoreFact 3 S :=
  (cyclicCoreFact_congr (p := 3) e).mpr (cyclicCoreFact_three_psl2 F h3 h4)


theorem cyclicCoreFact_three_catGroup_A1 {S : Type} [Group S] [Finite S]
    (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.A 1 q).Valid)
    (h3 : ¬ 3 ∣ q.card)
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.A 1 q, hv⟩).Group) :
    CyclicCoreFact 3 S := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  let eCat : (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.A 1 q, hv⟩).Group ≃*
      PSL2 (GaloisField q.p q.exponent) :=
    CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv
  have hcard : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', TauCeti.PrimePower.card_def]
  have h4 : 4 ≤ Nat.card (GaloisField q.p q.exponent) := by
    rw [hcard]
    have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    exact hrange.2 rfl
  have h3' : ¬ 3 ∣ Nat.card (GaloisField q.p q.exponent) := by
    rwa [hcard]
  exact cyclicCoreFact_three_of_mulEquiv_psl2 h3' h4 (e.trans eCat)


theorem kd1912TwoL2_holds : KD1912TwoL2 := by
  refine kd1912TwoLieAt_of_facts Nat.prime_three (by norm_num) ?_
  intro S _ _ hS hnc d hd hP e
  obtain ⟨e⟩ := e
  rcases d with ⟨d1, hv⟩
  obtain ⟨q, rfl⟩ : ∃ q, d1 = TauCeti.LieTypeIndex.A 1 q := by
    cases d1 with
    | A n q =>
        by_cases hn : n = 1
        · subst hn
          exact ⟨q, rfl⟩
        · simp [LieL2, hn] at hP
    | _ => simp [LieL2] at hP
  have h3q : ¬ 3 ∣ q.card := by
    simpa [CFSG.Yardstones.Md0ec50421ce4.k2Lie] using hd
  exact Or.inr (cyclicCoreFact_three_catGroup_A1 q hv h3q e)

end CFSG.LocalAnalysis.GLTheoremA.KD1912
