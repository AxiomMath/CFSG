module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3ExcLift
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOBlocks
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBOdd
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDOdd

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Matrix CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

section RhoSigned

variable {K : Type} [Field K]

@[expose] def skewM : Matrix (Fin 2) (Fin 2) K := !![0, -1; 1, 0]

@[expose] noncomputable def rhoOneSignedMat :
    SL(2, K) →* Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K where
  toFun A := fromBlocks ((A : Matrix (Fin 2) (Fin 2) K) 0 0 • 1)
    ((A : Matrix (Fin 2) (Fin 2) K) 0 1 • skewM) (-(A : Matrix (Fin 2) (Fin 2) K) 1 0 • skewM)
    ((A : Matrix (Fin 2) (Fin 2) K) 1 1 • 1)
  map_one' := by
    ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;> simp [skewM]
  map_mul' A B := by
    ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
      simp [skewM, Matrix.mul_apply, Fin.sum_univ_two, Fintype.sum_sum_type] <;> ring

theorem rhoOneSignedMat_apply (A : SL(2, K)) :
    rhoOneSignedMat A = fromBlocks ((A : Matrix (Fin 2) (Fin 2) K) 0 0 • 1)
      ((A : Matrix (Fin 2) (Fin 2) K) 0 1 • skewM) (-(A : Matrix (Fin 2) (Fin 2) K) 1 0 • skewM)
      ((A : Matrix (Fin 2) (Fin 2) K) 1 1 • 1) :=
  rfl

theorem quadPlus_two_rhoOneSigned (A : SL(2, K)) (u : Fin 2 ⊕ Fin 2 → K) :
    StatedQuadPlus 2 K (rhoOneSignedMat A *ᵥ u) = StatedQuadPlus 2 K u := by
  have hdet := A.2
  rw [det_fin_two] at hdet
  simp only [StatedQuadPlus, CFSG.MatrixModel.plusQuadCore, Fin.sum_univ_two, rhoOneSignedMat_apply,
    mulVec, dotProduct, Fintype.sum_sum_type, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
    fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.smul_apply, smul_eq_mul, skewM, Matrix.one_apply]
  simp
  linear_combination (u (.inl 0) * u (.inr 0) + u (.inl 1) * u (.inr 1)) * hdet

theorem rhoOneSigned_mul_rhoTwo (A B : SL(2, K)) :
    rhoOneSignedMat B * rhoTwoMat A = rhoTwoMat A * rhoOneSignedMat B := by
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [rhoOneSignedMat_apply, rhoTwoMat_apply, skewM, Matrix.mul_apply, Fin.sum_univ_two,
      Fintype.sum_sum_type, adjugate_fin_two] <;> ring

theorem rhoOneSignedMat_injective : Function.Injective (rhoOneSignedMat (K := K)) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  have e00 := congrFun (congrFun hA (.inl 0)) (.inl 0)
  have e01 := congrFun (congrFun hA (.inl 0)) (.inr 1)
  have e10 := congrFun (congrFun hA (.inr 1)) (.inl 0)
  have e11 := congrFun (congrFun hA (.inr 0)) (.inr 0)
  simp [rhoOneSignedMat_apply, skewM] at e00 e01 e10 e11
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e00, e01, e10, e11]

theorem rhoTwoMat_injective : Function.Injective (rhoTwoMat (K := K)) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  rw [rhoTwoMat_apply, ← fromBlocks_one] at hA
  exact Subtype.ext (fromBlocks_inj.1 hA).1

end RhoSigned

section OmegaSigned

open Subgroup

variable {K : Type} [Field K] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂] [Fintype ι]
  [DecidableEq ι] (oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι) {Q : (ι → K) → K} {Q₂ : (ι₂ → K) → K}

@[expose] noncomputable def oRhoOneSignedGL : SL(2, K) →* GL ι K :=
  (oblkGL oe).comp ((MonoidHom.inr _ _).comp rhoOneSignedMat.toHomUnits)

variable (hQ : ∀ v, Q v = Q₂ (fun a => v (oe (.inl a))) +
  StatedQuadPlus 2 K (fun b => v (oe (.inr b))))
include hQ

theorem oRhoOneSignedGL_mem_closure (B : SL(2, K)) :
    oRhoOneSignedGL oe B ∈ closure {M : GL ι K | ∀ v, Q ((M : Matrix ι ι K) *ᵥ v) = Q v} :=
  subset_closure fun v =>
    quad_oblk_mulVec_eq hQ (fun w => by simp) (quadPlus_two_rhoOneSigned B) v

@[expose] noncomputable def oRhoOneSigned (hSL : commutator SL(2, K) = ⊤) :
    SL(2, K) →* StatedOmega Q :=
  (oRhoOneSignedGL oe).codRestrict _
    (mem_statedOmega_of_perfect hSL _ (oRhoOneSignedGL_mem_closure oe hQ))

end OmegaSigned

end CFSG.ComponentClassification.RankTwoClassical

namespace CFSG.LocalAnalysis.GLTheoremA.S267.P3

open Matrix CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.ComponentClassification.RankTwoClassical
open scoped MatrixGroups

namespace ClassExc

section Four

variable {K : Type} [Field K] {ι ι₂ ι₃ : Type} [Fintype ι] [DecidableEq ι] [Fintype ι₂]
  [DecidableEq ι₂] [Fintype ι₃] [DecidableEq ι₃]

private theorem eq_one_of_oblk_one_eq_smul [Nonempty ι₂] {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι}
    {X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K} {c : K} (h : oblk oe 1 X = c • 1) :
    X = 1 := by
  have h' : oblk oe 1 X = oblk oe (c • 1) (c • 1) := by rw [h, ← oblk_smul, oblk_one]
  obtain ⟨h1, h2⟩ := oblk_injective h'
  obtain ⟨a⟩ := ‹Nonempty ι₂›
  have hc : c = 1 := by
    have := congrFun (congrFun h1 a) a
    simpa using this.symm
  rw [h2, hc, one_smul]

private theorem eq_one_of_oblk_eq_smul_one {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι}
    {Y : Matrix ι₂ ι₂ K} {c : K} (h : oblk oe Y 1 = c • 1) : Y = 1 := by
  have h' : oblk oe Y 1 = oblk oe (c • 1) (c • 1) := by rw [h, ← oblk_smul, oblk_one]
  obtain ⟨h1, h2⟩ := oblk_injective h'
  have hc : c = 1 := by
    have := congrFun (congrFun h2 (.inl 0)) (.inl 0)
    simpa using this.symm
  rw [h1, hc, one_smul]

private theorem injective_mk_comp {Q : (ι → K) → K} {ψ : SL(2, K) →* StatedOmega Q}
    {m : SL(2, K) → Matrix ι ι K}
    (hm : ∀ g, (((ψ g : StatedOmega Q) : GL ι K) : Matrix ι ι K) = m g)
    (hinj : ∀ g (c : K), m g = c • 1 → g = 1) :
    Function.Injective
      ((QuotientGroup.mk' ((StatedScalars ι K).subgroupOf (StatedOmega Q))).comp ψ) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 hg)
  have hc' := congrArg Units.val hc
  rw [Matrix.GeneralLinearGroup.coe_scalar, hm, Matrix.scalar_apply,
    ← Matrix.smul_one_eq_diagonal] at hc'
  exact hinj g c hc'.symm

private theorem commute_mk_comp {Q : (ι → K) → K} {ψ ψ' : SL(2, K) →* StatedOmega Q}
    {m m' : SL(2, K) → Matrix ι ι K}
    (hm : ∀ g, (((ψ g : StatedOmega Q) : GL ι K) : Matrix ι ι K) = m g)
    (hm' : ∀ g, (((ψ' g : StatedOmega Q) : GL ι K) : Matrix ι ι K) = m' g)
    (h : ∀ A B, m A * m' B = m' B * m A) (A B : SL(2, K)) :
    (QuotientGroup.mk' ((StatedScalars ι K).subgroupOf (StatedOmega Q))).comp ψ A *
        (QuotientGroup.mk' ((StatedScalars ι K).subgroupOf (StatedOmega Q))).comp ψ' B =
      (QuotientGroup.mk' ((StatedScalars ι K).subgroupOf (StatedOmega Q))).comp ψ' B *
        (QuotientGroup.mk' ((StatedScalars ι K).subgroupOf (StatedOmega Q))).comp ψ A := by
  simp only [MonoidHom.comp_apply]
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, hm, hm']
  exact h A B

theorem exists_four_commuting_SL2_omega (hSL : commutator SL(2, K) = ⊤)
    (oe₁ : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι) (oe₂ : ι₃ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι₂)
    {Q : (ι → K) → K} {Q₂ : (ι₂ → K) → K} {Q₃ : (ι₃ → K) → K}
    (hQ₁ : ∀ v, Q v = Q₂ (fun a => v (oe₁ (.inl a))) +
      StatedQuadPlus 2 K (fun b => v (oe₁ (.inr b))))
    (hQ₂ : ∀ w, Q₂ w = Q₃ (fun a => w (oe₂ (.inl a))) +
      StatedQuadPlus 2 K (fun b => w (oe₂ (.inr b)))) :
    ∃ φ : Fin 4 → SL(2, K) →* StatedProj (StatedOmega Q), (∀ i, Function.Injective (φ i)) ∧
      ∀ i j, i ≠ j → ∀ A B : SL(2, K), φ i A * φ j B = φ j B * φ i A := by
  haveI : Nonempty ι₂ := ⟨oe₂ (.inr (.inl 0))⟩
  set π := QuotientGroup.mk' ((StatedScalars ι K).subgroupOf (StatedOmega Q)) with hπ
  set ψ₀ := oRhoTwo oe₁ hQ₁ hSL
  set ψ₁ := oRhoOneSigned oe₁ hQ₁ hSL
  set ψ₂ := (oKappa oe₁ hQ₁).comp (oRhoTwo oe₂ hQ₂ hSL)
  set ψ₃ := (oKappa oe₁ hQ₁).comp (oRhoOneSigned oe₂ hQ₂ hSL)
  have h₀ : ∀ g, (((ψ₀ g : StatedOmega Q) : GL ι K) : Matrix ι ι K) =
      oblk oe₁ 1 (rhoTwoMat g) := fun _ => rfl
  have h₁ : ∀ g, (((ψ₁ g : StatedOmega Q) : GL ι K) : Matrix ι ι K) =
      oblk oe₁ 1 (rhoOneSignedMat g) := fun _ => rfl
  have h₂ : ∀ g, (((ψ₂ g : StatedOmega Q) : GL ι K) : Matrix ι ι K) =
      oblk oe₁ (oblk oe₂ 1 (rhoTwoMat g)) 1 := fun _ => rfl
  have h₃ : ∀ g, (((ψ₃ g : StatedOmega Q) : GL ι K) : Matrix ι ι K) =
      oblk oe₁ (oblk oe₂ 1 (rhoOneSignedMat g)) 1 := fun _ => rfl
  have i₀ := injective_mk_comp h₀ fun g c h =>
    rhoTwoMat_injective ((eq_one_of_oblk_one_eq_smul h).trans (map_one _).symm)
  have i₁ := injective_mk_comp h₁ fun g c h =>
    rhoOneSignedMat_injective ((eq_one_of_oblk_one_eq_smul h).trans (map_one _).symm)
  have i₂ := injective_mk_comp h₂ fun g c h => by
    have h1 := (oblk_injective ((eq_one_of_oblk_eq_smul_one h).trans oblk_one.symm)).2
    exact rhoTwoMat_injective (h1.trans (map_one _).symm)
  have i₃ := injective_mk_comp h₃ fun g c h => by
    have h1 := (oblk_injective ((eq_one_of_oblk_eq_smul_one h).trans oblk_one.symm)).2
    exact rhoOneSignedMat_injective (h1.trans (map_one _).symm)
  have c01 := commute_mk_comp h₀ h₁ fun A B => by
    rw [oblk_mul, oblk_mul, rhoOneSigned_mul_rhoTwo]
  have c02 := commute_mk_comp h₀ h₂ fun A B => by
    rw [oblk_mul, oblk_mul, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_one]
  have c03 := commute_mk_comp h₀ h₃ fun A B => by
    rw [oblk_mul, oblk_mul, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_one]
  have c12 := commute_mk_comp h₁ h₂ fun A B => by
    rw [oblk_mul, oblk_mul, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_one]
  have c13 := commute_mk_comp h₁ h₃ fun A B => by
    rw [oblk_mul, oblk_mul, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_one]
  have c23 := commute_mk_comp h₂ h₃ fun A B => by
    rw [oblk_mul, oblk_mul, oblk_mul, oblk_mul, rhoOneSigned_mul_rhoTwo]
  refine ⟨![π.comp ψ₀, π.comp ψ₁, π.comp ψ₂, π.comp ψ₃], fun i => ?_, fun i j hij A B => ?_⟩
  · fin_cases i
    · exact i₀
    · exact i₁
    · exact i₂
    · exact i₃
  · fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact c01 A B
    · exact c02 A B
    · exact c03 A B
    · exact (c01 B A).symm
    · exact absurd rfl hij
    · exact c12 A B
    · exact c13 A B
    · exact (c02 B A).symm
    · exact (c12 B A).symm
    · exact absurd rfl hij
    · exact c23 A B
    · exact (c03 B A).symm
    · exact (c13 B A).symm
    · exact (c23 B A).symm
    · exact absurd rfl hij

end Four

section Forms

variable {K : Type} [Field K]

@[expose] def hypTail (r : ℕ) {T : Type} (qT : (T → K) → K) (v : Fin r ⊕ (Fin r ⊕ T) → K) : K :=
  ∑ i, v (.inl i) * v (.inr (.inl i)) + qT (fun t => v (.inr (.inr t)))

@[expose] def oeTail (s : ℕ) (T : Type) :
    (Fin s ⊕ (Fin s ⊕ T)) ⊕ (Fin 2 ⊕ Fin 2) ≃ Fin (s + 2) ⊕ (Fin (s + 2) ⊕ T) :=
  (Equiv.sumSumSumComm _ _ _ _).trans (Equiv.sumCongr finSumFinEquiv
    (((Equiv.sumAssoc _ _ _).trans ((Equiv.sumCongr (Equiv.refl _) (Equiv.sumComm _ _)).trans
      (Equiv.sumAssoc _ _ _).symm)).trans (Equiv.sumCongr finSumFinEquiv (Equiv.refl _))))

theorem hypTail_split (s : ℕ) {T : Type} (qT : (T → K) → K)
    (v : Fin (s + 2) ⊕ (Fin (s + 2) ⊕ T) → K) :
    hypTail (s + 2) qT v = hypTail s qT (fun a => v (oeTail s T (.inl a))) +
      StatedQuadPlus 2 K (fun b => v (oeTail s T (.inr b))) := by
  simp only [hypTail, StatedQuadPlus, CFSG.MatrixModel.plusQuadCore, Fin.sum_univ_add]
  simp [oeTail, Fin.sum_univ_two]
  ring

@[expose] def oePlus (s : ℕ) : (Fin s ⊕ Fin s) ⊕ (Fin 2 ⊕ Fin 2) ≃ Fin (s + 2) ⊕ Fin (s + 2) :=
  (Equiv.sumSumSumComm _ _ _ _).trans (Equiv.sumCongr finSumFinEquiv finSumFinEquiv)

theorem quadPlus_split (s : ℕ) (v : Fin (s + 2) ⊕ Fin (s + 2) → K) :
    StatedQuadPlus (s + 2) K v = StatedQuadPlus s K (fun a => v (oePlus s (.inl a))) +
      StatedQuadPlus 2 K (fun b => v (oePlus s (.inr b))) := by
  simp only [StatedQuadPlus, CFSG.MatrixModel.plusQuadCore, Fin.sum_univ_add]
  simp [oePlus, Fin.sum_univ_two]

theorem statedQuadMinus_eq (s : ℕ) (b c : K) (v : Fin s ⊕ (Fin s ⊕ Fin 2) → K) :
    StatedQuadMinus (s + 1) K b c v =
      hypTail s (fun w : Fin 2 → K => w 0 ^ 2 + b * w 0 * w 1 + c * w 1 ^ 2) v := by
  show (∑ i : Fin s, v (Sum.inl i) * v (Sum.inr (Sum.inl i)) + v (Sum.inr (Sum.inr 0)) ^ 2 +
    b * v (Sum.inr (Sum.inr 0)) * v (Sum.inr (Sum.inr 1)) + c * v (Sum.inr (Sum.inr 1)) ^ 2) = _
  simp only [hypTail]
  ring

end Forms

private theorem commutator_sl2_eq_top_of_ringChar {F : Type} [Field F] (h2 : ringChar F ≠ 2)
    (h3 : ringChar F ≠ 3) : commutator SL(2, F) = ⊤ := by
  refine Matrix.SL2.commutator_eq_top (a := (2 : F)) (Ring.two_ne_zero h2) fun h => h3 ?_
  have h3' : ((3 : ℕ) : F) = 0 := by
    push_cast
    linear_combination h
  rw [ringChar.spec] at h3'
  rcases CharP.char_is_prime_or_zero F (ringChar F) with hp | hp
  · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h3'
  · rw [hp, zero_dvd_iff] at h3'
    norm_num at h3'

private theorem ringChar_fixedField' (d : TauCeti.ValidLieTypeIndex) :
    ringChar d.fixedField = d.characteristic := by
  haveI : Fintype d.fixedField := Fintype.ofFinite _
  haveI : Fact d.characteristic.Prime := ⟨d.characteristic_prime⟩
  haveI : CharP d.fixedField d.characteristic :=
    charP_of_card_eq_prime_pow (f := d.fieldExponent) (by
      rw [← Nat.card_eq_fintype_card, TauCeti.ValidLieTypeIndex.card_fixedField,
        TauCeti.ValidLieTypeIndex.fieldOrder_eq_characteristic_pow])
  exact ringChar.eq _ _

end ClassExc

open ClassExc

private theorem P3Hyp.false_of_omega_model {q : ℕ} {Ω : Type} [Group Ω] [Finite Ω]
    {S B : Subgroup Ω} (H : P3Hyp q S B) {d : TauCeti.ValidLieTypeIndex}
    (e : PSimple 3 S ≃* (TauCeti.CFSGIndex.lie d).Group) (hchar : d.1.characteristic = q)
    {ι : Type} [Fintype ι] [DecidableEq ι] {Q : (ι → d.fixedField) → d.fixedField}
    (E : (TauCeti.CFSGIndex.lie d).Group ≃* StatedProj (StatedOmega Q))
    (h : commutator SL(2, d.fixedField) = ⊤ →
      ∃ φ : Fin 4 → SL(2, d.fixedField) →* StatedProj (StatedOmega Q),
        (∀ i, Function.Injective (φ i)) ∧
          ∀ i j, i ≠ j → ∀ A B : SL(2, d.fixedField), φ i A * φ j B = φ j B * φ i A) :
    False := by
  have hc : ringChar d.fixedField = q := (ringChar_fixedField' d).trans hchar
  obtain ⟨φ, hinj, hcomm⟩ := h (commutator_sl2_eq_top_of_ringChar (by rw [hc]; exact H.two)
    (by rw [hc]; exact H.three))
  refine H.false_of_commuting_SL2_fixedField e hchar (fun i => E.symm.toMonoidHom.comp (φ i))
    (fun i => E.symm.injective.comp (hinj i)) fun i j hij A B => ?_
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [← map_mul, ← map_mul, hcomm i j hij A B]

theorem p3At_B_of_four_le {n : ℕ} (hn : 4 ≤ n) {Q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.B n Q).Valid) : P3At ⟨_, hv⟩ := by
  intro q Ω _ _ S B H hchar ⟨e⟩
  exfalso
  obtain ⟨s, rfl⟩ : ∃ s, n = s + 2 + 2 := ⟨n - 4, by omega⟩
  have hQp : Q.p ≠ 2 := by
    rw [← TauCeti.LieTypeIndex.characteristic_B (s + 2 + 2) Q]
    exact hchar ▸ H.two
  refine H.false_of_omega_model e hchar
    (CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj_odd (s + 2 + 2) Q hv
      hQp (by omega)) fun hSL => ?_
  exact exists_four_commuting_SL2_omega hSL (oeTail (s + 2) Unit) (oeTail s Unit)
    (fun v => hypTail_split (s + 2) (fun w : Unit → _ => w () ^ 2) v)
    (fun w => hypTail_split s _ w)

theorem p3At_D_of_five_le {n : ℕ} (hn : 5 ≤ n) {Q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.D n Q).Valid) : P3At ⟨_, hv⟩ := by
  intro q Ω _ _ S B H hchar ⟨e⟩
  exfalso
  obtain ⟨s, rfl⟩ : ∃ s, n = s + 2 + 2 := ⟨n - 4, by omega⟩
  refine H.false_of_omega_model e hchar
    (CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid (s + 2 + 2)
      Q hv) fun hSL => ?_
  exact exists_four_commuting_SL2_omega hSL (oePlus (s + 2)) (oePlus s)
    (fun v => quadPlus_split (s + 2) v) (fun w => quadPlus_split s w)

theorem p3At_twistedD_of_five_le {n : ℕ} (hn : 5 ≤ n) {Q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedD n Q).Valid) : P3At ⟨_, hv⟩ := by
  intro q Ω _ _ S B H hchar ⟨e⟩
  exfalso
  obtain ⟨s, rfl⟩ : ∃ s, n = s + 2 + 2 + 1 := ⟨n - 5, by omega⟩
  obtain ⟨b, c, -, ⟨E⟩⟩ :=
    CFSG.RankThree.PartTwo.Census.Carrier.SpinD.exists_typeTwistedDGroupEquivStatedProj_of_valid
      (s + 2 + 2 + 1) Q hv
  refine H.false_of_omega_model e hchar E fun hSL => ?_
  exact exists_four_commuting_SL2_omega hSL (oeTail (s + 2) (Fin 2)) (oeTail s (Fin 2))
    (fun v => (statedQuadMinus_eq (s + 2 + 2) b c v).trans (hypTail_split (s + 2) _ v))
    (fun w => hypTail_split s _ w)

end CFSG.LocalAnalysis.GLTheoremA.S267.P3

end
