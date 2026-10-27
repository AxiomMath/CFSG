module

public import CFSG.ClassicalInvolution.Uniform.U8Basic
public import CFSG.ClassicalInvolution.Asc77.AscR10E24
public import CFSG.ClassicalInvolution.Asc77.AscR10E20
public import CFSG.ClassicalInvolution.Uniform.U3Thm8

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3MT

open CFSG.Open hiding StatedLieTag
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.ModelFacts (Gen3)
open CFSG.LieType.Steinberg CFSG.LieType.BorelTits
open scoped MatrixGroups commutatorElement


section Transfer

variable {K G : Type} [Group K] [Finite K] [Group G]

theorem mem_normalizer_of_map_gen3 (ψ : K →* G) (hker : ψ.ker ≤ Subgroup.center K)
    (hk3 : ∀ x ∈ ψ.ker, x ^ 3 = 1 → x = 1) {R : Subgroup K} (hR : Gen3 R) {g : K}
    (hg : ψ g ∈ Subgroup.normalizer ((R.map ψ : Subgroup G) : Set G)) :
    g ∈ Subgroup.normalizer (R : Set K) := by
  apply ih8_mem_normalizer_of_conjSub_eq
  apply eq_of_map_eq_of_gen3 ψ hker hk3 (hR.map _) hR
  rw [map_conj_eq_conjSub_map ψ g R]
  exact conjSub_eq_of_mem_normalizer hg

end Transfer

section NbrModel

variable {K G : Type} [Group K] [Finite K] [Group G]

theorem ih8_nbr_model3 (ψ : K →* G) (hker : ψ.ker ≤ Subgroup.center K)
    (hk3 : ∀ x ∈ ψ.ker, x ^ 3 = 1 → x = 1) {F₁ F₂ : Type} [Field F₁] [Finite F₁] [Field F₂]
    [Finite F₂] (hodd₁ : Odd (Nat.card F₁)) (hodd₂ : Odd (Nat.card F₂)) {R S : Subgroup K}
    (hR : Gen3 R) (eR : R ≃* SL(2, F₁)) (eS : S ≃* SL(2, F₂)) {A : Subgroup G}
    (hA2 : IsPGroup 2 A) (hAS : A ≤ S.map ψ) (hnc : ∃ x ∈ A, ∃ y ∈ A, x * y ≠ y * x)
    (hAN : A ≤ Subgroup.normalizer ((R.map ψ : Subgroup G) : Set G)) :
    ∃ T : Subgroup K, T ≤ S ∧ IsPGroup 2 T ∧ (∃ x ∈ T, ∃ y ∈ T, x * y ≠ y * x) ∧
      T ≤ Subgroup.normalizer (R : Set K) ∧ sl2Inv eS ∈ T ∧
      sl2Inv eS * sl2Inv eR = sl2Inv eR * sl2Inv eS := by
  set T := S ⊓ A.comap ψ with hT
  have hTS : T ≤ S := inf_le_left
  have hTn : T ≤ Subgroup.normalizer (R : Set K) := by
    intro g hg
    exact mem_normalizer_of_map_gen3 ψ hker hk3 hR (hAN hg.2)
  have hker2 : ∀ x ∈ S, x ∈ ψ.ker → x * x = 1 := by
    intro x hxS hxk
    have hc := Subgroup.mem_center_iff.mp (hker hxk)
    rcases eq_one_or_eq_sl2Inv_of_central eS hxS (fun y _ => (hc y).symm) with h | h
    · rw [h, mul_one]
    · rw [h]
      exact sl2Inv_mul_self hodd₂ eS
  have hT2 : IsPGroup 2 ↥T := ih8_pGroup_lift hA2 hker2
  obtain ⟨a, ha, b, hb, hab⟩ := ih8_nonabelian_lift hAS hnc
  have hne : ∃ g ∈ T, g ≠ 1 := by
    by_cases ha1 : a = 1
    · refine ⟨b, hb, fun hb1 => hab ?_⟩
      rw [ha1, hb1]
    · exact ⟨a, ha, ha1⟩
  obtain ⟨g, hgT, hg1⟩ := hne
  have hinv : ∃ w ∈ T, orderOf w = 2 := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hT2) ⟨g, hgT⟩
    have h1 : orderOf g = 2 ^ k := by
      rw [← hk, Subgroup.orderOf_mk]
    have hk1 : 1 ≤ k := by
      by_contra h0
      have hk0 : k = 0 := by omega
      rw [hk0, pow_zero, orderOf_eq_one_iff] at h1
      exact hg1 h1
    refine ⟨g ^ 2 ^ (k - 1), T.pow_mem hgT _, ?_⟩
    have hdvd : 2 ^ (k - 1) ∣ orderOf g := by
      rw [h1]
      exact pow_dvd_pow 2 (Nat.sub_le k 1)
    have h2 := orderOf_pow_of_dvd (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0)) hdvd
    rw [h1, Nat.pow_div (Nat.sub_le k 1) (by norm_num)] at h2
    rw [h2]
    have h3 : k - (k - 1) = 1 := by omega
    rw [h3, pow_one]
  obtain ⟨w, hwT, hw2⟩ := hinv
  have hwz : w = sl2Inv eS := eq_sl2Inv_of_orderOf_eq_two hodd₂ eS (hTS hwT) hw2
  have hzT : sl2Inv eS ∈ T := hwz ▸ hwT
  have hzN : sl2Inv eS ∈ Subgroup.normalizer (R : Set K) := hTn hzT
  have hRz : sl2Inv eR ∈ R := sl2Inv_mem eR
  have hconj : sl2Inv eS * sl2Inv eR * (sl2Inv eS)⁻¹ ∈ R :=
    (Subgroup.mem_normalizer_iff.mp hzN _).mp hRz
  have hord : orderOf (sl2Inv eS * sl2Inv eR * (sl2Inv eS)⁻¹) = 2 := by
    have := MulEquiv.orderOf_eq (MulAut.conj (sl2Inv eS)) (sl2Inv eR)
    rw [MulAut.conj_apply] at this
    rw [this]
    exact orderOf_sl2Inv hodd₁ eR
  have hcomm := eq_sl2Inv_of_orderOf_eq_two hodd₁ eR hconj hord
  refine ⟨T, hTS, hT2, ⟨a, ha, b, hb, hab⟩, hTn, hzT, ?_⟩
  calc sl2Inv eS * sl2Inv eR = (sl2Inv eS * sl2Inv eR * (sl2Inv eS)⁻¹) * sl2Inv eS := by group
    _ = sl2Inv eR * sl2Inv eS := by rw [hcomm]

end NbrModel

section Pairs

open CFSG.ClassicalInvolution.Asc77.T3CII (center_sl3_eq_bot center_su3_eq_bot)
open CFSG.ClassicalInvolution.Models (suMat det_suMat)

variable {X : Type} [Group X]

theorem mem_normalizer_of_map_injective' {G H : Type*} [Group G] [Group H] {f : G →* H}
    (hf : Function.Injective f) {L : Subgroup G} {g : G}
    (h : f g ∈ Subgroup.normalizer ((L.map f : Subgroup H) : Set H)) :
    g ∈ Subgroup.normalizer (L : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at h ⊢
  intro y
  have := h (f y)
  rw [Subgroup.mem_map_iff_mem hf, show f g * f y * (f g)⁻¹ = f (g * y * g⁻¹) by simp,
    Subgroup.mem_map_iff_mem hf] at this
  exact this

theorem LinearBlockStandardPair.comm_of_normalizes3 {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 3) {W U V : Subgroup X} (h : WeakCT.LinearBlockStandardPair F W U V)
    {x y : X} (hxV : x ∈ V) (hyV : y ∈ V) (hxN : x ∈ Subgroup.normalizer (U : Set X))
    (hyN : y ∈ Subgroup.normalizer (U : Set X)) : x * y = y * x := by
  obtain ⟨θ, -, hker, hU, hV⟩ := WeakCT.pair_normalize h
  have hinj : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    intro c hc1
    have := hker (MonoidHom.mem_ker.2 hc1)
    rwa [center_sl3_eq_bot hF, Subgroup.mem_bot] at this
  rw [← hV] at hxV hyV
  obtain ⟨g, hg, rfl⟩ := hxV
  obtain ⟨g', hg', rfl⟩ := hyV
  rw [← hU] at hxN hyN
  have key : ∀ g ∈ WeakCT.B23 F,
      θ g ∈ Subgroup.normalizer (((WeakCT.B12 F).map θ : Subgroup X) : Set X) →
      ∃ M : SL(2, F), g = WeakCT.blockSL F 3 2 1 (by omega) M ∧
        (M : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 ∧ (M : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    intro g hg hgN
    have hgN' := mem_normalizer_of_map_injective' hinj hgN
    obtain ⟨M, rfl⟩ := hg
    refine ⟨M, rfl, ?_⟩
    have hb : WeakCT.blockSL F 3 2 0 (by omega) (WeakCT.rotSL) ∈ WeakCT.B12 F := ⟨_, rfl⟩
    obtain ⟨A', hA'⟩ := (Subgroup.mem_normalizer_iff.mp hgN' _).mp hb
    have h2 : WeakCT.blockSL F 3 2 0 (by omega) A' * WeakCT.blockSL F 3 2 1 (by omega) M =
        WeakCT.blockSL F 3 2 1 (by omega) M * WeakCT.blockSL F 3 2 0 (by omega) WeakCT.rotSL := by
      rw [hA']
      group
    have h3 := congrArg (fun z : SL(3, F) => (z : Matrix (Fin 3) (Fin 3) F)) h2
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_blockSL_zero, coe_blockSL_one] at h3
    exact embPair_zero_conj_rot _ _ h3.symm
  obtain ⟨M, rfl, h01, h10⟩ := key g hg hxN
  obtain ⟨M', rfl, h01', h10'⟩ := key g' hg' hyN
  have hMM : M * M' = M' * M :=
    Subtype.ext (by
      simp only [Matrix.SpecialLinearGroup.coe_mul]
      exact mul_comm_of_offDiag_eq_zero h01 h10 h01' h10')
  rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, hMM]

theorem UnitaryBlockStandardPair.comm_of_normalizes3 {K : Type} [Field K] [Finite K] {p f : ℕ}
    [Fact p.Prime] [CharP K p] (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f = 3)
    {W U V : Subgroup X} (h : Phan.UnitaryBlockStandardPair K p f W U V) {x y : X}
    (hxV : x ∈ V) (hyV : y ∈ V) (hxN : x ∈ Subgroup.normalizer (U : Set X))
    (hyN : y ∈ Subgroup.normalizer (U : Set X)) : x * y = y * x := by
  obtain ⟨θ, -, hker, hU, hV⟩ := Phan.pair_normalize h
  have hinj : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    intro c hc1
    have := hker (MonoidHom.mem_ker.2 hc1)
    rwa [center_su3_eq_bot hK hq, Subgroup.mem_bot] at this
  rw [← hV] at hxV hyV
  obtain ⟨g, hg, rfl⟩ := hxV
  obtain ⟨g', hg', rfl⟩ := hyV
  rw [← hU] at hxN hyN
  have key : ∀ g ∈ Phan.B23 K p f,
      θ g ∈ Subgroup.normalizer (((Phan.B12 K p f).map θ : Subgroup X) : Set X) →
      ∃ M : Phan.Su K p f 2, g = embSUid (unitaryInvolution K p f) 0 M ∧
        suMat M 0 1 = 0 ∧ suMat M 1 0 = 0 := by
    intro g hg hgN
    have hgN' := mem_normalizer_of_map_injective' hinj hgN
    obtain ⟨M, rfl⟩ := hg
    refine ⟨M, rfl, ?_⟩
    have hb : embSUid (unitaryInvolution K p f) 2 (Phan.rotSU (unitaryInvolution K p f)) ∈
        Phan.B12 K p f := ⟨_, rfl⟩
    obtain ⟨A', hA'⟩ := (Subgroup.mem_normalizer_iff.mp hgN' _).mp hb
    have h2 : embSUid (unitaryInvolution K p f) 2 A' * embSUid (unitaryInvolution K p f) 0 M =
        embSUid (unitaryInvolution K p f) 0 M *
          embSUid (unitaryInvolution K p f) 2 (Phan.rotSU (unitaryInvolution K p f)) := by
      rw [hA']
      group
    have h3 := congrArg suMat h2
    simp only [Models.suMat_mul] at h3
    exact embPair_zero_conj_rot _ _ h3.symm
  obtain ⟨M, rfl, h01, h10⟩ := key g hg hxN
  obtain ⟨M', rfl, h01', h10'⟩ := key g' hg' hyN
  have hMM : M * M' = M' * M := by
    apply Models.suMat_injective
    simp only [Models.suMat_mul]
    exact mul_comm_of_offDiag_eq_zero h01 h10 h01' h10'
  rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, hMM]

end Pairs

section Nbr

open CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem ih8_nbr_sylow3 (hΩ : HypOmegaGen Ω) {K J : Subgroup G} (hJ : J ∈ omegaNbr Ω K) :
    ∃ A : Subgroup G, IsPGroup 2 A ∧ A ≤ J ∧ A ≤ Subgroup.normalizer (K : Set G) ∧
      ∃ x ∈ A, ∃ y ∈ A, x * y ≠ y * x := by
  obtain ⟨-, -, A, hA, hAJ, hAN⟩ := hJ
  have hA' := hA
  obtain ⟨M, -, P, rfl⟩ := hA
  exact ⟨_, P.isPGroup'.map _, hAJ, hAN,
    (Sec6Gen.isQuatSub_of_mem_RSet hΩ hA').exists_not_commute⟩

theorem commutes_of_omegaNbr3 {t : StatedLieTag} {k e : ℕ}
    (M : Ih8Model 3 1 Ω t k e) (hΩ : HypOmegaModU (.sl2 3 1) Ω) (hG2 : t ≠ .G2)
    (hD4 : t ≠ .trialityD4) {R S : Subgroup (modelUniv t k 3 e Fact.out).K} (hR : R ∈ M.cls)
    (hS : S ∈ M.cls) (hJ : S.map M.ψ ∈ omegaNbr Ω (R.map M.ψ)) : Commutes R S := by
  have he := ih8Model_exp_eq_one M hD4
  subst he
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have : Finite (modelUniv t k 3 1 Fact.out).K :=
    ModelFacts.finite_modelUniv hp2 Nat.prime_three (ih8_isFundTag_mf M.isFundTag) M.admissible
  have hΩg : HypOmegaGen Ω := hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) hΩ
  obtain ⟨A, hA2, hAJ, hAN, hAnc⟩ := ih8_nbr_sylow3 hΩg hJ
  obtain ⟨eR⟩ := M.cls_equiv_sl2 hp2 hG2 hD4 hR
  obtain ⟨eS⟩ := M.cls_equiv_sl2 hp2 hG2 hD4 hS
  have hFcard : Nat.card (GaloisField 3 1) = 3 := by
    rw [GaloisField.card 3 1 (by norm_num)]; norm_num
  have hodd : Odd (Nat.card (GaloisField 3 1)) := by rw [hFcard]; decide
  have hgR := ih8Model_gen3 M hG2 hD4 hR
  have hRS : R ≠ S := fun h => hJ.2.1 (by rw [h])
  obtain ⟨T, hTS, hT2, hTnc, hTN, -, hzcomm⟩ := ih8_nbr_model3 M.ψ M.ker_le_center
    (ih8Model_ker_pow_three M hD4) hodd hodd hgR eR eS hA2 hAJ hAnc hAN
  have hdich := T3CII.stdDich3_all ModelFacts.stdDich3Orth ModelFacts.stdDich3Exc t k M.isFundTag
    M.admissible hG2 hD4
  have hRl := ModelFacts.fundamentalSubgroups_subset_longest hG2 hD4 _ (M.cls_sub hR)
  have hSl := ModelFacts.fundamentalSubgroups_subset_longest hG2 hD4 _ (M.cls_sub hS)
  rcases hdich R hRl S hSl (sl2Inv eR) (sl2Inv eS) (sl2Inv_mem eR) (sl2Inv_mem eS)
    (orderOf_sl2Inv hodd eR) (orderOf_sl2Inv hodd eS) hzcomm.symm with h | h | ⟨W, hW⟩ | ⟨W, hW⟩
  · exact absurd h hRS
  · exact h
  · obtain ⟨x, hx, y, hy, hxy⟩ := hTnc
    exact absurd (LinearBlockStandardPair.comm_of_normalizes3 hFcard hW (hTS hx) (hTS hy)
      (hTN hx) (hTN hy)) hxy
  · have hK9 : Nat.card (GaloisField 3 2) = (3 ^ 1) ^ 2 := by
      rw [GaloisField.card 3 2 (by norm_num)]; norm_num
    obtain ⟨x, hx, y, hy, hxy⟩ := hTnc
    exact absurd (UnitaryBlockStandardPair.comm_of_normalizes3 hK9 (by norm_num) hW (hTS hx)
      (hTS hy) (hTN hx) (hTN hy)) hxy

theorem finite_K3 {t : StatedLieTag} {k e : ℕ} (M : Ih8Model 3 1 Ω t k e) :
    Finite (modelUniv t k 3 e Fact.out).K :=
  ModelFacts.finite_modelUniv (by norm_num) Nat.prime_three (ih8_isFundTag_mf M.isFundTag)
    M.admissible

theorem map_inj3 {t : StatedLieTag} {k e : ℕ} (M : Ih8Model 3 1 Ω t k e)
    (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4) {R S : Subgroup (modelUniv t k 3 e Fact.out).K}
    (hR : R ∈ M.cls) (hS : S ∈ M.cls) (h : R.map M.ψ = S.map M.ψ) : R = S := by
  have := finite_K3 M
  exact eq_of_map_eq_of_gen3 M.ψ M.ker_le_center (ih8Model_ker_pow_three M hD4)
    (ih8Model_gen3 M hG2 hD4 hR) (ih8Model_gen3 M hG2 hD4 hS) h

theorem omegaNbr_iff3 {t : StatedLieTag} {k e : ℕ} (M : Ih8Model 3 1 Ω t k e)
    (hΩ : HypOmegaModU (.sl2 3 1) Ω) (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    {R S : Subgroup (modelUniv t k 3 e Fact.out).K} (hR : R ∈ M.cls) (hS : S ∈ M.cls) :
    S.map M.ψ ∈ omegaNbr Ω (R.map M.ψ) ↔ R ≠ S ∧ Commutes R S := by
  constructor
  · intro hJ
    exact ⟨fun h => hJ.2.1 (by rw [h]), commutes_of_omegaNbr3 M hΩ hG2 hD4 hR hS hJ⟩
  · rintro ⟨-, hc⟩
    have hcomm := ih8_commutes_map M.ψ hc
    exact MuTab.mem_omegaNbr_of_commutes (M.map_mem hS)
      (fun h => ne_of_commutes_members hΩ (M.map_mem hR) hcomm h.symm) hcomm

end Nbr

end CFSG.ClassicalInvolution.Q3.Q3MT
