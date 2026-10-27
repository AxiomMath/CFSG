module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmallFive
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmallMain
public import CFSG.ClassicalInvolution.Q3.TA3FrameU5

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmall

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Models.Transfer CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg CFSG.LieType.BorelTits CFSG.Blueprint
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TA3
open CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
open CFSG.ClassicalInvolution.Balance.StrongBalance.Linear (coordSet ker_comp_conj_le_center)
open CFSG.CGT.PushingUpLit.SolKNA.R4
open scoped MatrixGroups

section Su5

variable {X : Type} [Group X] {K : Type} [Field K] [Finite K] {p f : ℕ}
  [Fact p.Prime] [CharP K p]

theorem twoBlock_of_su5 (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (θ : Su K p f 5 →* X) (hsurj : Function.Surjective θ)
    (hker : θ.ker ≤ Subgroup.center (Su K p f 5)) {z : Su K p f 5} (hz : z * z = 1)
    (hz1 : z ≠ 1) :
    ∃ B₁ B₂ I₁ I₂ : Subgroup X, CFSG.Open.IsComponentOf B₁ (Subgroup.centralizer ({θ z} : Set X)) ∧
      CFSG.Open.IsComponentOf B₂ (Subgroup.centralizer ({θ z} : Set X)) ∧ I₁ ≤ B₁ ∧ I₂ ≤ B₂ ∧
      (∀ a ∈ I₁, ∀ b ∈ I₂, a * b = b * a) ∧ Nonempty (↥I₁ ≃* SL(2, fixedSubfield K p f)) ∧
      Nonempty (↥I₂ ≃* SL(2, fixedSubfield K p f)) := by
  have h2 := two_ne_zero_of_charP_ne_two (K := K) hp
  obtain ⟨a, ha, g, hg⟩ := ModelFacts.exists_su_conj_negBlock hK h2 (by norm_num) hz
  rw [ModelFacts.negBlockK_zero_eq_diagonal] at hg
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hz1
    have h1 : z * g = 1 * g := suMat_injective (by
      rw [suMat_mul, hg, suMat_mul, suMat_one, Matrix.one_mul]
      simp)
    exact mul_right_cancel h1
  have hprod : ∏ j : Fin 5, (if j.val < a then (-1 : K) else 1) = 1 := by
    have := congrArg Matrix.det hg
    rw [Matrix.det_mul, Matrix.det_mul, det_suMat, det_suMat, one_mul, one_mul,
      Matrix.det_diagonal] at this
    exact this.symm
  have ha24 := Frame.FL5.eq_two_or_four h2 ha ha0 hprod
  set σ : Fin 5 → Bool := fun j => decide (a ≤ j.val) with hσ
  have hD : (((g⁻¹ * z * g : Su K p f 5) : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      Matrix.diagonal fun i => signOf K (σ i) := by
    change suMat (g⁻¹ * z * g) = _
    rw [suMat_mul, suMat_mul, Matrix.mul_assoc, hg, ← Matrix.mul_assoc, ← suMat_mul,
      inv_mul_cancel, suMat_one, Matrix.one_mul]
    congr 1
    funext j
    simp only [signOf, hσ, decide_eq_true_eq]
    split_ifs <;> first | rfl | omega
  have hf : ∀ y, θ z * (θ.comp (MulAut.conj g).toMonoidHom) y * (θ z)⁻¹ =
      (θ.comp (MulAut.conj g).toMonoidHom) (g⁻¹ * z * g * y * (g⁻¹ * z * g)⁻¹) := by
    intro y
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulAut.conj_apply]
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    group
  have hk := ker_comp_conj_le_center θ hker g
  have hs : Function.Surjective (θ.comp (MulAut.conj g).toMonoidHom) :=
    hsurj.comp (MulAut.conj g).surjective
  have hJ₁ := Frame.FL5.mem_coordSet_zero ha24
  have hJ₂ := Frame.FL5.mem_coordSet_two ha24
  obtain ⟨e₁⟩ := IsLongRootSU2Image.nonempty_mulEquiv hK hp hq (by norm_num) hk
    ⟨_, _, isLongRootSU2_range_blockEmb hK hp (by norm_num : 0 + 2 ≤ 5), rfl, rfl⟩
  obtain ⟨e₂⟩ := IsLongRootSU2Image.nonempty_mulEquiv hK hp hq (by norm_num) hk
    ⟨_, _, isLongRootSU2_range_blockEmb hK hp (by norm_num : 2 + 2 ≤ 5), rfl, rfl⟩
  have hB₁ := isComponentOf_block_centralizer_su hK hq h2 _ hk _ σ _ hD hf false
    (Frame.FL5.two_le_card (by norm_num) hJ₁)
  have hB₂ := isComponentOf_block_centralizer_su hK hq h2 _ hk _ σ _ hD hf (decide (a ≤ 2))
    (Frame.FL5.two_le_card (by norm_num) hJ₂)
  rw [MonoidHom.range_eq_top.mpr hs, top_inf_eq] at hB₁ hB₂
  refine ⟨_, _, _, _, hB₁, hB₂, Subgroup.map_mono (Frame.FU5.range_blockEmb_le _ hJ₁),
    Subgroup.map_mono (Frame.FU5.range_blockEmb_le _ hJ₂), ?_, ⟨e₁⟩, ⟨e₂⟩⟩
  rintro _ ⟨_, ⟨A, rfl⟩, rfl⟩ _ ⟨_, ⟨B, rfl⟩, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  exact blockEmb_comm (K := K) (p := p) (f := f) (by norm_num : 0 + 2 ≤ 5)
    (by norm_num : 2 + 2 ≤ 5) (Or.inl le_rfl) A B

end Su5

theorem twoBlockShape_u5 {F : Type} [Group F] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h5 : 5 ≤ p ^ f) (hm : LieModel F .PSU 5 p f) : TwoBlockShape F := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := Q5L5U5.statedClassicalModel_of_lieModel_psu hm
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := ClassicalGroups.Unitary.charP_of_card_sq hK
  let θ : Su K p f 5 →* F := e.symm.toMonoidHom.comp
    ((QuotientGroup.mk' ((StatedScalars (Fin 5) K).subgroupOf (StatedSU 5 (p ^ f) K))).comp
      (MulEquiv.subgroupCongr (SUid_eq_statedSU hK 5)).toMonoidHom)
  have hsurj : Function.Surjective θ :=
    e.symm.surjective.comp ((QuotientGroup.mk'_surjective _).comp
      (MulEquiv.subgroupCongr (SUid_eq_statedSU hK 5)).surjective)
  have hker : θ.ker ≤ Subgroup.center (Su K p f 5) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx' : MulEquiv.subgroupCongr (SUid_eq_statedSU hK 5) x ∈
        (StatedScalars (Fin 5) K).subgroupOf (StatedSU 5 (p ^ f) K) := by
      simpa [θ, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] using hx
    rw [Subgroup.mem_subgroupOf, StatedScalars,
      ← Matrix.GeneralLinearGroup.center_eq_range_scalar] at hx'
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.mp hx' (g : GL (Fin 5) K))
  have hq := card_fixedSubfield hK
  have hodd : Odd (Nat.card (fixedSubfield K p f)) := by
    rw [hq]
    exact ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  have h4 : 4 ≤ Nat.card (fixedSubfield K p f) := by rw [hq]; omega
  intro t ht
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  obtain ⟨z, hz, rfl⟩ := exists_sq_eq_one_lift_of_pow_five θ hker (center_pow_five_su hK h5)
    (MonoidHom.mem_range.mpr (hsurj t)) ht2
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [map_one, orderOf_one] at ht
    exact absurd ht (by norm_num)
  obtain ⟨B₁, B₂, I₁, I₂, hB₁, hB₂, hI₁, hI₂, hc, ⟨e₁⟩, ⟨e₂⟩⟩ :=
    twoBlock_of_su5 hK hp2 h5 θ hsurj hker hz hz1
  exact ⟨↥(fixedSubfield K p f), ↥(fixedSubfield K p f), inferInstance, inferInstance,
    inferInstance, inferInstance, B₁, B₂, I₁, I₂, hodd, hodd, h4, h4, hB₁, hB₂, hI₁, hI₂, hc,
    ⟨e₁⟩, ⟨e₂⟩⟩


theorem false_of_u5 {r n : ℕ} (hr : 4 ≤ r) {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y}
    {S : Sylow 2 R} {t : Y} (h : PerpHypR r n Y R S t)
    (hsmall : TwoSubgroupsFourGenerated ↥(genFittingFStar Y))
    (hF : SmallU5 ↥(genFittingFStar Y)) : False := by
  haveI := h.core.simple
  obtain ⟨p, f, hp, hp2, hf, h4, hm⟩ := hF
  have hsm := Q5L5U5.statedClassicalModel_of_lieModel_psu hm
  have hg : Odd (Nat.gcd 5 (p ^ f + 1)) :=
    (by decide : Odd 5).of_dvd_nat (Nat.gcd_dvd_left 5 _)
  have h5 : 5 ≤ p ^ f := by
    have hle : p ≤ p ^ f := Nat.le_self_pow (by omega) p
    have := hp.two_le
    omega
  exact not_twinPair_of_twoBlockShape (twoBlockShape_u5 hp hp2 h5 hm) hsmall
    (exists_twinPair_of_perp hr h (socleComm2_of_outTwoCyclic (outTwoCyclic_PSU hsm hg)))

theorem twinLeafR_u5 {r n : ℕ} (hr : 4 ≤ r) : TwinLeafR r n SmallU5 :=
  fun _ _ _ _ _ _ hP hsmall hF => false_of_u5 hr hP hsmall hF

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmall
