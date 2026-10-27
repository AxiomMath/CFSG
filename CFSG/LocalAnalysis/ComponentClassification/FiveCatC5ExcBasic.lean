module

public import CFSG.LocalAnalysis.ComponentClassification.FiveCatDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofSLForm
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofA6Core
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddB
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Lemma44
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.G2SylIASL2
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.ComponentClassification.SolMax.FiveCat.C5Exc

open CFSG Subgroup CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped MatrixGroups

@[expose] def NoLitA5 (G : Type) [Group G] : Prop :=
  ∀ L : Subgroup G, IsComponent L → Nonempty (↥L ⧸ center ↥L ≃* alternatingGroup (Fin 5)) →
    ∃ z : ↥L, z ∈ center ↥L ∧ orderOf z = 2

theorem NoLitA5.of_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H) (h : NoLitA5 H) :
    NoLitA5 G := by
  rintro L hL ⟨eA⟩
  let eL : L ≃* L.map e.toMonoidHom := L.equivMapOfInjective _ e.injective
  obtain ⟨z, hz, hz2⟩ := h _ (LocalCores.isComponent_map_mulEquiv e hL)
    ⟨(QuotientGroup.congr _ _ eL (Subgroup.map_center_eq eL)).symm.trans eA⟩
  refine ⟨eL.symm z, mem_center_iff.mpr fun y => eL.injective ?_, ?_⟩
  · rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact mem_center_iff.mp hz (eL y)
  · rw [MulEquiv.orderOf_eq]
    exact hz2

theorem card_alt_five {X : Type*} [Group X] (e : X ≃* alternatingGroup (Fin 5)) :
    Nat.card X = 60 := by
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  decide

theorem lieModel_card_sixty (hO : LieOrderFormulasInput) {X : Type} [Group X] {τ : StatedLieTag}
    {n p f : ℕ} (hadm : StatedLieAdmissible τ n p f) (hp2 : p ≠ 2)
    (hm : Blueprint.LieModel X τ n p f) (hX : Nat.card X = 60) : τ = .PSL ∧ n = 2 := by
  obtain ⟨-, -, hfac⟩ := hO X τ n p f hadm hm
  have hf : 1 ≤ f := hadm.2.1
  rw [hX] at hfac
  have hdvd : p ^ (lieSylowExponent τ n * f) ∣ 60 := by
    rw [← hfac]
    exact Nat.ordProj_dvd 60 p
  rcases lieSylowExponent_ge_three hadm hp2 with h | h3
  · exact h
  · exfalso
    have h3f : 3 ≤ lieSylowExponent τ n * f := le_trans h3 (Nat.le_mul_of_pos_right _ hf)
    have h27 : p ^ 3 ∣ 60 := (pow_dvd_pow p h3f).trans hdvd
    have hp : p.Prime := hadm.1
    have hp3 : p ≤ 3 := by
      by_contra hlt
      push Not at hlt
      have h1 : 4 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left hlt 3
      have h2 := Nat.le_of_dvd (by norm_num) h27
      omega
    interval_cases p <;> revert hp hp2 h27 <;> decide

theorem isEmpty_a5_of_lieModel (hO : LieOrderFormulasInput) {B H : Type} [Group B] [Group H]
    (e : B ≃* H) {τ' : StatedLieTag} {n' p f : ℕ} (hadm : StatedLieAdmissible τ' n' p f)
    (hp2 : p ≠ 2) (hlie : Blueprint.LieModel (H ⧸ center H) τ' n' p f)
    (hne : ¬ (τ' = .PSL ∧ n' = 2)) : IsEmpty (B ⧸ center B ≃* alternatingGroup (Fin 5)) := by
  refine ⟨fun eA => hne ?_⟩
  have hlieB : Blueprint.LieModel (B ⧸ center B) τ' n' p f :=
    LieType.CurtisTits.lieModel_of_mulEquiv
      (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).symm hlie
  exact lieModel_card_sixty hO hadm hp2 hlieB (card_alt_five eA)

theorem exists_central_involution_sl2 {F : Type} [Field F] (hF : ringChar F ≠ 2) :
    ∃ z : SL(2, F), z ∈ center SL(2, F) ∧ orderOf z = 2 := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  refine ⟨-1, ?_, ?_⟩
  · rw [mem_center_iff]
    intro g
    simp
  · have hz1 : (-1 : SL(2, F)) ≠ 1 := by
      intro h1
      have h00 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h1
      simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
        Matrix.neg_apply, Matrix.one_apply_eq] at h00
      exact h2 (by linear_combination -h00)
    exact orderOf_eq_prime (by rw [neg_one_sq]) hz1

theorem eight_dvd_card_sl2 {F : Type} [Field F] [Finite F] (hF : ringChar F ≠ 2) :
    8 ∣ Nat.card SL(2, F) := by
  rw [GH74.GLS.Stage1.Thm3.Sec6.G2Syl.IASL2.natCard_sl2]
  have hq : Nat.card F % 2 = 1 :=
    GH74.GLS.Stage1.Thm3.Sec6.G2Syl.IASL2.natCard_mod_two_of_two_ne_zero (Ring.two_ne_zero hF)
  obtain ⟨m, hm⟩ : ∃ m, Nat.card F = 2 * m + 1 := ⟨Nat.card F / 2, by omega⟩
  rw [hm]
  have hsq : (2 * m + 1) ^ 2 - 1 = 4 * (m * (m + 1)) := Nat.sub_eq_of_eq_add (by ring)
  rw [hsq]
  obtain ⟨k, hk⟩ := (Nat.even_mul_succ_self m).two_dvd
  exact ⟨(2 * m + 1) * k, by rw [hk]; ring⟩

theorem noLitA5_of_slComponentForm {K : Type} [Field K] [Finite K] (hK2 : ringChar K ≠ 2)
    {G : Type} [Group G] [Finite G] (h : SLComponentForm K G) : NoLitA5 G := by
  rintro L hL ⟨eA⟩
  rcases h L hL with ⟨⟨e⟩⟩ | ⟨hdvd, -⟩
  · obtain ⟨z, hz, hz2⟩ := exists_central_involution_sl2 hK2
    refine ⟨e.symm z, mem_center_iff.mpr fun y => e.injective ?_, ?_⟩
    · rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact mem_center_iff.mp hz (e y)
    · rw [MulEquiv.orderOf_eq]
      exact hz2
  · have hcard : Nat.card ↥L = 60 * Nat.card ↥(center ↥L) := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥L), card_alt_five eA]
    have h2 : 2 ∣ Nat.card ↥(center ↥L) := by
      have h8 := (eight_dvd_card_sl2 hK2).trans hdvd
      rw [hcard] at h8
      omega
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2
    exact ⟨(z : ↥L), z.2, by rw [Subgroup.orderOf_coe]; exact hz⟩

@[expose] def OddLieA5For (t : StatedLieTag) : Prop :=
  ∀ (J : Type) [Group J] (n p f : ℕ), p.Prime → p ≠ 2 → p ≠ 3 → StatedLieAdmissible t n p f →
    Blueprint.LieModel J t n p f → ∀ α : MulAut J, orderOf α = 2 → NoLitA5 (fixedSubgroup α)

theorem eq_one_of_mem_center_of_zStar {P : Type} [Group P] [Finite P]
    (hZ : Open.fusionZStar P = pPrimeCore 2 P) {w : P} (hw : w ∈ center P) (hww : w * w = 1) :
    w = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hwZ : w ∈ Open.fusionZStar P := by
    rw [GrSLit.GrS4.fusionZStar_eq_comap_pPrimeCore, Subgroup.mem_comap, Subgroup.mem_center_iff]
    intro y'
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ y'
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hw y]
  rw [hZ] at hwZ
  have hcop := LocalAnalysis.ComponentInitial.coprime_orderOf_of_mem_pPrimeCore (p := 2) hwZ
  have h2 : orderOf w ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hww)
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop.symm h2)

theorem false_of_central_involution {S : Type} [Group S] [Finite S] {σ : MulAut S}
    {P : Subgroup S} (hPF : P ≤ fixedSubgroup σ) (hZ : Open.fusionZStar ↥P = pPrimeCore 2 ↥P)
    {z : ↥(P.subgroupOf (fixedSubgroup σ))} (hzc : z ∈ center ↥(P.subgroupOf (fixedSubgroup σ)))
    (hz2 : orderOf z = 2) : False := by
  have hzP : ((z : ↥(fixedSubgroup σ)) : S) ∈ P := mem_subgroupOf.mp z.2
  have hwc : (⟨((z : ↥(fixedSubgroup σ)) : S), hzP⟩ : ↥P) ∈ center ↥P := by
    rw [Subgroup.mem_center_iff]
    intro y
    have h1 := mem_center_iff.mp hzc ⟨⟨(y : S), hPF y.2⟩, mem_subgroupOf.mpr y.2⟩
    exact Subtype.ext (congrArg (fun u : ↥(P.subgroupOf (fixedSubgroup σ)) =>
      ((u : ↥(fixedSubgroup σ)) : S)) h1)
  have hzz : z * z = 1 := by
    rw [← sq, ← hz2]
    exact pow_orderOf_eq_one z
  have hzz' : ((z : ↥(fixedSubgroup σ)) : S) * ((z : ↥(fixedSubgroup σ)) : S) = 1 :=
    congrArg (fun u : ↥(P.subgroupOf (fixedSubgroup σ)) => ((u : ↥(fixedSubgroup σ)) : S)) hzz
  have hww : (⟨((z : ↥(fixedSubgroup σ)) : S), hzP⟩ : ↥P) *
      ⟨((z : ↥(fixedSubgroup σ)) : S), hzP⟩ = 1 := Subtype.ext hzz'
  have h1 := eq_one_of_mem_center_of_zStar hZ hwc hww
  have h2 : ((z : ↥(fixedSubgroup σ)) : S) = 1 := congrArg Subtype.val h1
  have h3 : z = 1 := Subtype.ext (Subtype.ext h2)
  rw [h3, orderOf_one] at hz2
  exact absurd hz2 (by norm_num)

theorem fivePump_char5_of_oddLieA5For
    {t : StatedLieTag} (h : OddLieA5For t) : FivePumpCharFiveClause t := by
  intro S _ _ hs hna ⟨n, f, hm⟩ σ P hP hZ eP _
  exfalso
  have hadm : StatedLieAdmissible t n 5 f := hm.admissible
  haveI : IsSimpleGroup S := hs
  have hQ : FixedTwoComponentsQuasisimple S :=
    fixedTwoComponentsQuasisimple_of_oddLieType hna
      ⟨t, n, 5, f, Nat.prime_five, by norm_num, hadm, hm⟩
  have hσ1 : σ ≠ 1 := hP.ne_one
  have hσσ : σ * σ = 1 := MulEquiv.ext fun y => hP.1 y
  have hσ2 : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact hσσ) hσ1
  have hq : IsQuasisimple (P.subgroupOf (fixedSubgroup σ)) := hQ σ hσσ hσ1 _ hP.2.2.1
  obtain ⟨hcomp, ⟨eZ⟩⟩ := hP.fusionZStar_equiv_of_quasisimple hq
  have hA5 : Nonempty (↥(P.subgroupOf (fixedSubgroup σ)) ⧸
      center ↥(P.subgroupOf (fixedSubgroup σ)) ≃* alternatingGroup (Fin 5)) :=
    ⟨eZ.symm.trans eP.some⟩
  obtain ⟨z, hzc, hz2⟩ := h S n 5 f Nat.prime_five (by norm_num) (by norm_num) hadm hm σ hσ2 _
    hcomp hA5
  exact false_of_central_involution hP.2.1 hZ hzc hz2

end CFSG.ComponentClassification.SolMax.FiveCat.C5Exc
