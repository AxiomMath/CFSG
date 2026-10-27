module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitLocalBalanceTypes
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitKernel
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitTypeClosure
public import CFSG.GH74.KGroups.L27
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.Adapters.LinearSmallCatalog
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bOrders
public import Mathlib.GroupTheory.Perm.Centralizer
public meta import CFSG.GH74.KGroups.L27
public import Certificates.Certificate2331
public import Certificates.Certificate43
public import Certificates.Certificate5117
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.LieType.Universal.SpinOmega.Range
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bBasic
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitReduction
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFourPresentation
public import CFSG.LocalAnalysis.SignalizerFunctor
public import TauCeti.LinearAlgebra.QuadraticForm.Prod

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.GH74.KGroups Equiv

theorem pPrimeCore_eq_bot_of_isPGroup {H : Type*} [Group H] [Finite H] (hp : IsPGroup 2 H) :
    pPrimeCore 2 H = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [pPrimeCore_eq_bot_iff]
  intro N _ hN
  obtain ⟨k, hk⟩ := (hp.to_subgroup N).exists_card_eq
  rw [hk] at hN
  rcases k with _ | k
  · exact card_eq_one.mp (by rw [hk, pow_zero])
  · exfalso
    have h2 : 2 ∣ 2 ^ (k + 1) := dvd_pow_self 2 (Nat.succ_ne_zero k)
    rw [Nat.Coprime, Nat.gcd_eq_left h2] at hN
    exact absurd hN (by norm_num)

theorem isLocallyTwoBalanced_of_autModel {K : Type} [Group K] {n : ℕ}
    (M : AutModel K (Equiv.Perm (Fin n))) (hPA : M.P ≤ M.A)
    (hAN : M.A ≤ normalizer (M.P : Set (Equiv.Perm (Fin n))))
    (hcard : Nat.card M.A ≤ 2 * Nat.card M.P)
    (hinv : ∀ x ∈ M.P, x * x = 1 → x ≠ 1 → ∀ y ∈ M.A, y * x = x * y → y ^ 16 = 1) :
    ClassicalInvolution.Balance.IsLocallyTwoBalanced K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut K) := Finite.of_equiv M.A M.Φ.symm.toEquiv
  intro H _ F hF4 hF2
  set F' : Subgroup (MulAut K) := M.P.comap M.ι with hF'
  have hF'n : F'.Normal := by
    refine ⟨fun φ hφ ψ => ?_⟩
    rw [hF', mem_comap] at hφ ⊢
    rw [map_mul, map_mul, map_inv]
    exact (mem_normalizer_iff.mp (hAN (M.ι_mem ψ)) _).mp hφ
  have hcardF' : Nat.card F' = Nat.card M.P := by
    refine Nat.card_congr (Equiv.ofBijective (fun φ : F' => (⟨M.ι φ, φ.2⟩ : M.P)) ⟨?_, ?_⟩)
    · intro φ ψ h
      have h1 := Subtype.ext_iff.mp h
      exact Subtype.ext (M.ι_injective h1)
    · rintro ⟨p, hp⟩
      obtain ⟨φ, hφ⟩ := M.Φ.surjective ⟨p, hPA hp⟩
      refine ⟨⟨φ, ?_⟩, Subtype.ext ?_⟩
      · rw [hF', mem_comap]
        show ((M.Φ φ : M.A) : Equiv.Perm (Fin n)) ∈ M.P
        rw [hφ]
        exact hp
      · show ((M.Φ φ : M.A) : Equiv.Perm (Fin n)) = p
        rw [hφ]
  have hidx : F'.index ≤ 2 := by
    have h1 := card_mul_index F'
    rw [hcardF', M.card_mulAut] at h1
    have hP0 : 0 < Nat.card M.P := Nat.card_pos
    by_contra h
    push Not at h
    have : Nat.card M.P * 3 ≤ Nat.card M.P * F'.index := Nat.mul_le_mul_left _ h
    omega
  set F'' : Subgroup H := F'.subgroupOf H with hF''
  have hF''n : F''.Normal := hF'n.subgroupOf H
  have hidx' : F''.index ≤ 2 :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero index_ne_zero_of_finite)
      (relIndex_dvd_index_of_normal (H := F') (K := H))).trans hidx
  have hcore : ∀ t ∈ F'', orderOf t = 2 → pPrimeCore 2 (centralizer ({t} : Set H)) = ⊥ := by
    intro t ht ht2
    have htP : M.ι t ∈ M.P := mem_subgroupOf.mp ht
    have htt' : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
    have ht1 : M.ι t ≠ 1 := by
      intro h
      have h1 : (t : MulAut K) = 1 := M.ι_injective (by rw [h, map_one])
      have h2 : t = 1 := Subtype.ext h1
      rw [h2, orderOf_one] at ht2
      exact absurd ht2 (by norm_num)
    have htt : M.ι t * M.ι t = 1 := by
      rw [← map_mul]
      have : ((t : MulAut K) * t) = 1 := congrArg Subtype.val htt'
      rw [this, map_one]
    apply pPrimeCore_eq_bot_of_isPGroup
    intro c
    refine ⟨4, ?_⟩
    have hc := mem_centralizer_singleton_iff.mp c.2
    have hcomm : M.ι ((c : H) : MulAut K) * M.ι t = M.ι t * M.ι ((c : H) : MulAut K) := by
      rw [← map_mul, ← map_mul]
      exact congrArg (fun w : H => M.ι (w : MulAut K)) hc
    have h16 := hinv _ htP htt ht1 _ (M.ι_mem _) hcomm
    have h16' : ((c : H) : MulAut K) ^ 16 = 1 := M.ι_injective (by rw [map_pow, h16, map_one])
    apply Subtype.ext
    apply Subtype.ext
    simpa using h16'
  have h := deltaCore_eq_bot_of_index_le_two hidx' hcore (nonempty_mulEquiv_four hF4 hF2)
  rw [deltaCore_eq_iInf_pPrimeCore]
  exact h

theorem l27_sub_check : (elemsT L27.QP).all (fun x => L27.QA.sift x 0) = true :=
  Certificates.certificate2331.1

theorem l27_norm_check : (elemsT L27.QA).all
    (fun y => (elemsT L27.QP).all fun x => L27.QP.sift (y * x * y⁻¹) 0) = true :=
  Certificates.certificate2331.2.1

theorem l27_inv_check : (elemsT L27.QP).all (fun x => !(decide (x * x = 1)) || decide (x = 1) ||
    (elemsT L27.QA).all fun y => !(decide (y * x = x * y)) || decide (y ^ 16 = 1)) = true :=
  Certificates.certificate2331.2.2.1

theorem isLocallyTwoBalanced_of_psl27 {K : Type} [Group K] (h : Blueprint.LieModel K .PSL 2 7 1) :
    ClassicalInvolution.Balance.IsLocallyTwoBalanced K := by
  obtain ⟨e⟩ := L27.equiv_of_lieModel h
  obtain ⟨M, hP, hA⟩ := L27.autModel e
  refine isLocallyTwoBalanced_of_autModel M ?_ ?_ ?_ ?_
  · rw [hP, hA]
    intro x hx
    exact (mem_iff_sift _ L27.QA_ok x).2 (forall_of_all _ L27.QP_ok l27_sub_check x hx)
  · rw [hP, hA]
    intro y hy
    have hy' := forall_of_all _ L27.QA_ok l27_norm_check y hy
    exact mem_normalizer_of_conj_mem _ y fun x hx =>
      (mem_iff_sift _ L27.QP_ok _).2 (List.all_eq_true.1 hy' x ((mem_elemsT _ L27.QP_ok x).2 hx))
  · rw [hP, hA, card_group _ L27.QA_ok, card_group _ L27.QP_ok, L27.QA_valid.2, L27.QP_valid.2]
  · rw [hP, hA]
    intro x hx hx2 hx1 y hy hyx
    have h1 := forall_of_all _ L27.QP_ok l27_inv_check x hx
    simp only [hx2, hx1, decide_true, decide_false, Bool.not_true, Bool.false_or] at h1
    have h2 := List.all_eq_true.1 h1 y ((mem_elemsT _ L27.QA_ok y).2 hy)
    simpa [hyx] using h2

theorem a5_inv_check : ∀ x y : Perm (Fin 5), Perm.sign x = 1 → x * x = 1 → x ≠ 1 →
    y * x = x * y → y ^ 16 = 1 :=
  Certificates.certificate2331.2.2.2

theorem isLocallyTwoBalanced_of_alternating_five {K : Type} [Group K]
    (e : K ≃* alternatingGroup (Fin 5)) : ClassicalInvolution.Balance.IsLocallyTwoBalanced K := by
  have hbij := GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by norm_num)
    (by norm_num)
  let Φ' : (⊤ : Subgroup (Perm (Fin 5))) ≃* MulAut (alternatingGroup (Fin 5)) :=
    topEquiv.trans (MulEquiv.ofBijective _ hbij)
  let M : AutModel K (Perm (Fin 5)) := AutModel.ofRealization (alternatingGroup (Fin 5)) ⊤ e Φ'
    (fun σ x => by
      show ((MulAut.conjNormal (σ : Perm (Fin 5)) x : alternatingGroup (Fin 5)) : Perm (Fin 5)) =
        σ * x * (σ : Perm (Fin 5))⁻¹
      rw [MulAut.conjNormal_apply])
  refine isLocallyTwoBalanced_of_autModel M le_top ?_ ?_ ?_
  · intro y _
    show y ∈ normalizer ((alternatingGroup (Fin 5) : Subgroup (Perm (Fin 5))) : Set (Perm (Fin 5)))
    rw [normalizer_eq_top_iff.mpr inferInstance]
    exact mem_top y
  · show Nat.card (⊤ : Subgroup (Perm (Fin 5))) ≤ 2 * Nat.card (alternatingGroup (Fin 5))
    rw [card_top, nat_card_alternatingGroup, Nat.card_perm, Nat.card_fin]
    decide
  · intro x hx hx2 hx1 y _ hyx
    exact a5_inv_check x y (Perm.mem_alternatingGroup.mp hx) hx2 hx1 hyx

theorem isLocallyTwoBalanced_of_psl25 {K : Type} [Group K] (h : Blueprint.LieModel K .PSL 2 5 1) :
    ClassicalInvolution.Balance.IsLocallyTwoBalanced K := by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := GSThmB.statedClassicalModel_of_lieModel_ne_zero (by norm_num) h
  obtain ⟨e'⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five F
    (Or.inr (by simpa using hF))
  exact isLocallyTwoBalanced_of_alternating_five (e.trans e')

section Components

variable {G : Type} [Group G] [Finite G]

theorem commutator_wGroup_le_of_l2 {a : G} {J E : Subgroup G}
    (hJa : J ≤ centralizer ({a} : Set G))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set G))))
    (hmodel : IsL2Type 5 (J ⧸ Open.fusionZStar J) ∨ IsL2Type 7 (J ⧸ Open.fusionZStar J))
    (hE : E ≤ normalizer (J : Set G) ⊓ centralizer ({a} : Set G))
    (hE4 : Nonempty (E ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) :
    ⁅J, wGroup E ⊓ centralizer ({a} : Set G)⁆ ≤
      (pPrimeCore 2 (centralizer ({a} : Set G))).map (centralizer ({a} : Set G)).subtype := by
  obtain ⟨φ⟩ := hE4
  have h4 : Nat.card E = 4 := by
    rw [Nat.card_congr φ.toEquiv, Nat.card_prod, Nat.card_eq_fintype_card]
    rfl
  have h2 : ∀ e ∈ E, e * e = 1 := by
    intro e he
    have hm : ∀ y : Multiplicative (ZMod 2) × Multiplicative (ZMod 2), y * y = 1 := by decide
    have : (⟨e, he⟩ : E) * ⟨e, he⟩ = 1 := φ.injective (by rw [map_mul, map_one, hm])
    exact congrArg Subtype.val this
  rw [wGroup_eq_iInf_of_four h4 h2]
  obtain ⟨e⟩ := nonempty_image_center_quotient_equiv hJa hJ
  refine commutator_deltaCore_le_of_isLocallyTwoBalanced hJa hJ rfl ?_
    (fun x hx => mem_inf.mpr ⟨(mem_inf.mp (hE hx)).2, (mem_inf.mp (hE hx)).1⟩) h4 h2
  rcases hmodel with h5 | h7
  · exact isLocallyTwoBalanced_of_psl25 (LieType.CurtisTits.lieModel_of_mulEquiv e.symm h5)
  · exact isLocallyTwoBalanced_of_psl27 (LieType.CurtisTits.lieModel_of_mulEquiv e.symm h7)

end Components

end CFSG.ComponentClassification.GrSLit
