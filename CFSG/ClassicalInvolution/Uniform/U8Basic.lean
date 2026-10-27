module

public import CFSG.LieType.HighestRoot.ModelCenter
public import CFSG.ClassicalInvolution.Asc77.AscR10D3a
public import CFSG.ClassicalInvolution.Asc77.AscR10E1
public import CFSG.ClassicalInvolution.ModelFacts.CF3A
public import CFSG.ClassicalInvolution.Uniform.U3Witness
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.Open hiding StatedLieTag
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.ModelFacts (Gen3 gen3_of_equiv_sl2 commute_of_map_commute_of_gen3)
open CFSG.LieType.Steinberg CFSG.LieType.BorelTits
open scoped MatrixGroups commutatorElement


section Model

variable {G : Type} [Group G] {Ω : Set (Subgroup G)} {t : StatedLieTag} {k e : ℕ}

theorem ih8Model_exp_eq_one (M : Ih8Model 3 1 Ω t k e) (hD4 : t ≠ .trialityD4) : e = 1 :=
  M.exp_eq_f hD4

theorem ih8Model_gen3 (M : Ih8Model 3 1 Ω t k e) (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    {R : Subgroup (modelUniv t k 3 e Fact.out).K} (hR : R ∈ M.cls) : Gen3 R := by
  have he := ih8Model_exp_eq_one M hD4
  subst he
  obtain ⟨φ⟩ := M.cls_equiv_sl2 (by norm_num) hG2 hD4 hR
  exact gen3_of_equiv_sl2 φ

theorem ih8Model_ker_pow_three (M : Ih8Model 3 1 Ω t k e) (hD4 : t ≠ .trialityD4) :
    ∀ x ∈ M.ψ.ker, x ^ 3 = 1 → x = 1 := by
  have he := ih8Model_exp_eq_one M hD4
  subst he
  intro x hx hx3
  exact CFSG.ComponentClassification.RankTwoOddLie.modelCenterPPrime t k 3 1 Nat.prime_three
    (by norm_num) (ih8_isFundTag_mf M.isFundTag) M.admissible x (M.ker_le_center hx) hx3

end Model

section Twin

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem ih8_twin_data3 {K : Type} [Group K] (hΩ : HypOmegaModU (.sl2 3 1) Ω)
    (hex : ExactMembers Ω) {ψ : K →* G} (hker : ψ.ker ≤ Subgroup.center K)
    (hk3 : ∀ x ∈ ψ.ker, x ^ 3 = 1 → x = 1) {R R' : Subgroup K} (hR : Gen3 R)
    (hK : R.map ψ ∈ Ω) (hL : R'.map ψ ∈ Ω) (hne : R.map ψ ≠ R'.map ψ) {z : G}
    (hzK : IsUniqueInvolution (R.map ψ) z) (hzL : IsUniqueInvolution (R'.map ψ) z) :
    Commutes R R' ∧ ∃ x ∈ R, ∃ x' ∈ R', ψ x = z ∧ ψ x' = z ∧ x' ≠ 1 ∧
      x' * x⁻¹ ∈ Subgroup.center K := by
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hzK.sq) hzK.ne_one
  have hzmem : z ∈ R.map ψ ⊓ R'.map ψ := ⟨hzK.mem, hzL.mem⟩
  have hdvd : 2 ∣ Nat.card ↥(R.map ψ ⊓ R'.map ψ) := by
    have := Subgroup.orderOf_dvd_natCard (R.map ψ ⊓ R'.map ψ) hzmem
    rwa [hz2] at this
  obtain ⟨h41, h4⟩ := hΩ.omega4_commutes hex hK hL hne
  have hv : padicValNat 2 (Nat.card ↥(R.map ψ ⊓ R'.map ψ)) = 1 := by
    have hpos : 0 < Nat.card ↥(R.map ψ ⊓ R'.map ψ) := Nat.card_pos
    have hge : 1 ≤ padicValNat 2 (Nat.card ↥(R.map ψ ⊓ R'.map ψ)) :=
      one_le_padicValNat_of_dvd hpos.ne' hdvd
    omega
  have hcomm : Commutes (R.map ψ) (R'.map ψ) := h4 hv
  have hRR : Commutes R R' := by
    intro a ha b hb
    exact commute_of_map_commute_of_gen3 ψ hker hk3 hR (b := b)
      (fun a' ha' => hcomm _ (Subgroup.mem_map_of_mem ψ ha') _ (Subgroup.mem_map_of_mem ψ hb))
      a ha
  refine ⟨hRR, ?_⟩
  obtain ⟨x, hx, hxz⟩ := hzK.mem
  obtain ⟨x', hx', hx'z⟩ := hzL.mem
  refine ⟨x, hx, x', hx', hxz, hx'z, ?_, ?_⟩
  · intro h
    apply hzK.ne_one
    rw [← hx'z, h, map_one]
  · apply hker
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxz, hx'z, mul_inv_cancel]

end Twin

section Eq

variable {K G : Type} [Group K] [Finite K] [Group G]

theorem eq_of_map_eq_of_gen3 (ψ : K →* G) (hker : ψ.ker ≤ Subgroup.center K)
    (hk3 : ∀ x ∈ ψ.ker, x ^ 3 = 1 → x = 1) {A B : Subgroup K}
    (hA : Gen3 A) (hB : Gen3 B)
    (h : A.map ψ = B.map ψ) : A = B := by
  have key : ∀ {A B : Subgroup K}, Gen3 A → A.map ψ ≤ B.map ψ → A ≤ B := by
    intro A B hA hAB
    obtain ⟨S, hSA, hS3, hAS⟩ := hA
    refine hAS.trans ((Subgroup.closure_le _).2 fun s hs => ?_)
    obtain ⟨b, hb, hbs⟩ := hAB (Subgroup.mem_map_of_mem ψ (hSA hs))
    set c : K := b⁻¹ * s with hc
    have hcker : c ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, hc, map_mul, map_inv, hbs, inv_mul_cancel]
    have hcc : ∀ y : K, y * c = c * y := fun y => Subgroup.mem_center_iff.mp (hker hcker) y
    have hsbc : s = b * c := by rw [hc]; group
    have hc3B : c ^ 3 ∈ B := by
      have h1 : b ^ 3 * c ^ 3 = 1 := by
        rw [← (Commute.mul_pow (show Commute b c from hcc b) 3), ← hsbc]
        exact hS3 s hs
      have : c ^ 3 = (b ^ 3)⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [this]
      exact B.inv_mem (B.pow_mem hb 3)
    have hcB : c ∈ B := by
      have hcop : Nat.Coprime 3 (orderOf c) := by
        rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
        intro h3
        obtain ⟨r, hr⟩ := h3
        set c' : K := c ^ r with hc'
        have hc'ker : c' ∈ ψ.ker := Subgroup.pow_mem _ hcker r
        have hc'3 : c' ^ 3 = 1 := by
          rw [hc', ← pow_mul, mul_comm, ← hr]
          exact pow_orderOf_eq_one c
        have hc'1 := hk3 c' hc'ker hc'3
        have hr0 : 0 < r := by
          rcases Nat.eq_zero_or_pos r with h0 | h0
          · have := orderOf_pos c
            rw [h0] at hr
            omega
          · exact h0
        have hdvd := orderOf_dvd_of_pow_eq_one (hc'1 : c ^ r = 1)
        have := Nat.le_of_dvd hr0 hdvd
        have := orderOf_pos c
        omega
      obtain ⟨u, hu⟩ := exists_pow_eq_self_of_coprime hcop
      rw [← hu]
      exact B.pow_mem hc3B u
    rw [hsbc]
    exact B.mul_mem hb hcB
  exact le_antisymm (key hA h.le) (key hB h.ge)

end Eq

section Std

open CFSG.ClassicalInvolution.Asc77.T3CII (center_sl3_eq_bot center_su3_eq_bot)
open CFSG.ClassicalInvolution.Models (suMat det_suMat)

theorem linearPair_eq_one_of_centralizes3 {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 3) {X : Type} [Group X] {W U V : Subgroup X}
    (h : WeakCT.LinearBlockStandardPair F W U V) {x : X} (hx : x ∈ U)
    (hc : ∀ y ∈ V, x * y = y * x) : x = 1 := by
  obtain ⟨θ, -, hker, hU, hV⟩ := WeakCT.pair_normalize h
  have hinj : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    intro c hc1
    have := hker (MonoidHom.mem_ker.2 hc1)
    rwa [center_sl3_eq_bot hF, Subgroup.mem_bot] at this
  rw [← hU] at hx
  obtain ⟨b, hb, rfl⟩ := hx
  have hcomm : ∀ g ∈ WeakCT.B23 F, b * g = g * b := by
    intro g hg
    apply hinj
    rw [map_mul, map_mul]
    exact hc (θ g) (hV ▸ Subgroup.mem_map_of_mem θ hg)
  obtain ⟨A, rfl⟩ := hb
  have hr : WeakCT.blockSL F 3 2 1 (by omega) (WeakCT.rotSL) ∈ WeakCT.B23 F := ⟨_, rfl⟩
  have h1 := congrArg (fun z : SL(3, F) => (z : Matrix (Fin 3) (Fin 3) F))
    (hcomm _ hr)
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_blockSL_zero, coe_blockSL_one] at h1
  have hA : (A : Matrix (Fin 2) (Fin 2) F) = 1 :=
    embPair_two_eq_one_of_commute_rot _ A.2 h1
  have : A = 1 := Subtype.ext hA
  rw [this, map_one, map_one]

theorem unitaryPair_eq_one_of_centralizes3 {K : Type} [Field K] [Finite K] {p f : ℕ}
    [Fact p.Prime] [CharP K p] (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f = 3) {X : Type}
    [Group X] {W U V : Subgroup X} (h : Phan.UnitaryBlockStandardPair K p f W U V) {x : X}
    (hx : x ∈ U) (hc : ∀ y ∈ V, x * y = y * x) : x = 1 := by
  obtain ⟨θ, -, hker, hU, hV⟩ := Phan.pair_normalize h
  have hinj : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    intro c hc1
    have := hker (MonoidHom.mem_ker.2 hc1)
    rwa [center_su3_eq_bot hK hq, Subgroup.mem_bot] at this
  rw [← hU] at hx
  obtain ⟨b, hb, rfl⟩ := hx
  have hcomm : ∀ g ∈ Phan.B23 K p f, b * g = g * b := by
    intro g hg
    apply hinj
    rw [map_mul, map_mul]
    exact hc (θ g) (hV ▸ Subgroup.mem_map_of_mem θ hg)
  obtain ⟨A, rfl⟩ := hb
  have hr : embSUid (unitaryInvolution K p f) 0 (Phan.rotSU (unitaryInvolution K p f)) ∈
      Phan.B23 K p f := ⟨_, rfl⟩
  have h1 := congrArg suMat (hcomm _ hr)
  simp only [Models.suMat_mul] at h1
  have hA : suMat A = 1 := embPair_two_eq_one_of_commute_rot _ (det_suMat A) h1
  have : A = 1 := Models.suMat_injective (by rw [hA, Models.suMat_one])
  rw [this, map_one, map_one]

end Std

end CFSG.ClassicalInvolution.Uniform
