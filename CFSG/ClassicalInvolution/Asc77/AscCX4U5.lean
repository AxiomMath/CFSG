module

public import CFSG.ClassicalInvolution.Asc77.AscCX4A
public import CFSG.ClassicalInvolution.Asc77.AscCX4L3
public import CFSG.ClassicalInvolution.Asc77.AscCX4U4

public section

namespace CFSG.ClassicalInvolution.Asc77.CX.CX4.U4

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU
  CFSG.ClassicalGroups.Unitary CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterU4
  CFSG.ClassicalInvolution.Generic
open CFSG.Open (classicalInvolutionOddCore)
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem eq_one_of_mem_longRootU_of_mem_center (hK : Nat.card K = (p ^ f) ^ 2)
    {R : Subgroup (Su K p f 4)} {i : Su K p f 4}
    (hR : IsLongRootSU2 K p f (show 2 ≤ 4 by norm_num) R i) {x : Su K p f 4} (hxR : x ∈ R)
    (hxZ : x ∈ Subgroup.center (Su K p f 4)) : x = 1 := by
  obtain ⟨g, rfl, -⟩ := hR
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hxR
  obtain ⟨B, rfl⟩ := MonoidHom.mem_range.mp hy
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hxZ ⊢
  have hcomm := Subgroup.mem_center_iff.mp hxZ g
  have hyx : g * blockEmb K p f 4 2 0 (by norm_num) B * g⁻¹ =
      blockEmb K p f 4 2 0 (by norm_num) B :=
    mul_left_cancel (a := g) (by rw [hcomm]; group)
  rw [hyx] at hxZ ⊢
  obtain ⟨u, hu⟩ := exists_scalar_of_mem_center (isUnitaryInvolution_unitaryInvolution hK)
    (by norm_num : 3 ≤ 4) hxZ
  have hu' : suMat (blockEmb K p f 4 2 0 (by norm_num) B) = Matrix.scalar (Fin 4) (u : K) := hu
  have e := congrFun (congrFun hu' 3) 3
  rw [suMat_blockEmb_zero] at e
  simp at e
  apply suMat_injective
  rw [hu', ← e, map_one, suMat_one]

theorem oddCoreOf_map_longRootU_eq_bot (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) {Y : Type}
    [Group Y] (θ : Su K p f 4 →* Y) (hker : θ.ker ≤ Subgroup.center (Su K p f 4))
    {R : Subgroup (Su K p f 4)} {i : Su K p f 4}
    (hR : IsLongRootSU2 K p f (show 2 ≤ 4 by norm_num) R i) : oddCoreOf (R.map θ) = ⊥ := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two (K := K) hp
  have h2' : (2 : CFSG.LieType.Steinberg.fixedSubfield K p f) ≠ 0 := by
    intro h
    apply h2
    have h' := congrArg (CFSG.LieType.Steinberg.fixedSubfield K p f).subtype h
    rwa [map_ofNat, map_zero] at h'
  have hinj : Function.Injective (θ.comp R.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hxk : (x : Su K p f 4) ∈ θ.ker := hx
    exact Subgroup.mem_bot.mpr (Subtype.ext
      (eq_one_of_mem_longRootU_of_mem_center hK hR x.2 (hker hxk)))
  have hrange : (θ.comp R.subtype).range = R.map θ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  obtain ⟨e⟩ := (hR.isClassicalSL2 hK hp).nonempty_mulEquiv
  let e₁ : ↥(R.map θ) ≃* SL(2, CFSG.LieType.Steinberg.fixedSubfield K p f) :=
    ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).symm.trans e
  have hO : classicalInvolutionOddCore ↥(R.map θ) = ⊥ := by
    have h1 : (classicalInvolutionOddCore ↥(R.map θ)).map e₁.toMonoidHom =
        classicalInvolutionOddCore SL(2, CFSG.LieType.Steinberg.fixedSubfield K p f) :=
      CFSG.ComponentClassification.OddCore.equiv_invariant e₁
    rw [L4.oddCore_sl2_eq_bot_odd h2'] at h1
    rwa [Subgroup.map_eq_bot_iff_of_injective _ e₁.injective] at h1
  unfold oddCoreOf
  rw [hO, Subgroup.map_bot]

theorem center_le_ker (hK : Nat.card K = (p ^ f) ^ 2) (hq1 : p ^ f % 4 = 1) {X : Type} [Group X]
    (θ : Su K p f 4 →* X) (hneg : ∀ x : Su K p f 4, suMat x = -1 → θ x = 1) :
    Subgroup.center (Su K p f 4) ≤ θ.ker := by
  intro c hc
  obtain ⟨u, hu⟩ := exists_scalar_of_mem_center (isUnitaryInvolution_unitaryInvolution hK)
    (by norm_num : 3 ≤ 4) hc
  have hu' : suMat c = Matrix.scalar (Fin 4) (u : K) := hu
  have hdet : (u : K) ^ (2 ^ 2) = 1 := by
    have h := det_suMat c
    rw [hu'] at h
    simpa [Matrix.scalar_apply] using h
  have hN : unitaryInvolution K p f (u : K) * u = 1 := by
    have h1 : conjTr (unitaryInvolution K p f) (suMat c) * suMat c = 1 := c.2.2
    rw [hu'] at h1
    have e := congrFun (congrFun h1 0) 0
    simpa [conjTr, Matrix.mul_apply, Fin.sum_univ_four, Matrix.scalar_apply,
      Matrix.diagonal_apply] using e
  have h2 := sq_eq_one_of_norm hq1 hN hdet
  have h' : ((u : K) - 1) * ((u : K) + 1) = 0 := by linear_combination h2
  rw [MonoidHom.mem_ker]
  rcases mul_eq_zero.mp h' with h | h
  · have hc1 : c = 1 := suMat_injective (by
      rw [hu', show (u : K) = 1 by linear_combination h, map_one, suMat_one])
    rw [hc1, map_one]
  · exact hneg c (by rw [hu', show (u : K) = -1 by linear_combination h, map_neg, map_one])

theorem twin_data (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) {Y : Type} [Group Y]
    (θ : Su K p f 4 →* Y) (hker : θ.ker ≤ Subgroup.center (Su K p f 4))
    {R : Subgroup (Su K p f 4)} {i : Su K p f 4}
    (hi : IsLongRootSU2 K p f (show 2 ≤ 4 by norm_num) R i) {z' : Y}
    (hz : IsUniqueInvolution (R.map θ) z') : i ∈ R ∧ i * i = 1 ∧ i ≠ 1 ∧ θ i = z' := by
  have hcl := hi.isClassicalSL2 hK hp
  have hio := hcl.orderOf_eq_two
  have hi2 : i * i = 1 := by
    have := pow_orderOf_eq_one i
    rwa [hio, sq] at this
  have hi1 : i ≠ 1 := fun h => by rw [h, orderOf_one] at hio; omega
  refine ⟨hcl.mem, hi2, hi1, ?_⟩
  rcases hz.unique (θ i) ⟨i, hcl.mem, rfl⟩ (by rw [← map_mul, hi2, map_one]) with h | h
  · exact absurd (eq_one_of_mem_longRootU_of_mem_center hK hi hcl.mem (hker h)) hi1
  · exact h

theorem layerTwinFacts_psu4 (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hq1 : p ^ f % 4 = 1) {Y : Type} [Group Y]
    (θ : Su K p f 4 →* Y) (hker : θ.ker ≤ Subgroup.center (Su K p f 4))
    (hsurj : Function.Surjective θ) {R R' : Subgroup (Su K p f 4)}
    (hR : R ∈ longRootSetU (K := K) (p := p) (f := f) (show 2 ≤ 4 by norm_num))
    (hR' : R' ∈ longRootSetU (K := K) (p := p) (f := f) (show 2 ≤ 4 by norm_num))
    (hne : R.map θ ≠ R'.map θ) {z' : Y} (hz : IsUniqueInvolution (R.map θ) z')
    (hz' : IsUniqueInvolution (R'.map θ) z') : LayerTwinFacts (R.map θ) (R'.map θ) z' := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two (K := K) hp
  have hperf : Group.IsPerfect (Su K p f 4) :=
    isPerfect_SUid (isUnitaryInvolution_unitaryInvolution hK) (by norm_num) (fun h => by omega)
  obtain ⟨i, hi⟩ := hR
  obtain ⟨i', hi'⟩ := hR'
  have hRR : R ≠ R' := fun h => hne (by rw [h])
  obtain ⟨hiR, hi2, hi1, hθi⟩ := twin_data hK hp θ hker hi hz
  obtain ⟨hi'R, hi'2, hi'1, hθi'⟩ := twin_data hK hp θ hker hi' hz'
  have hc : i' * i⁻¹ ∈ Subgroup.center (Su K p f 4) := hker (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hθi, hθi', mul_inv_cancel])
  obtain ⟨g, hRg, hR'g, hig⟩ :=
    twin_std_u hK hp ⟨i, hi⟩ ⟨i', hi'⟩ hRR hiR hi2 hi1 hi'R hi'2 hi'1 hc
  have hi'neg : i' = ModelFacts.Orth15.InnerSu.zneg K p f * i :=
    ModelFacts.Orth15.InnerSu.twin_neg_su h2 hig hR'g hi'R hi'2 hi'1
  have hzneg : θ (ModelFacts.Orth15.InnerSu.zneg K p f) = 1 := by
    have h1 : θ i' = θ (ModelFacts.Orth15.InnerSu.zneg K p f) * θ i := by rw [hi'neg, map_mul]
    rw [hθi, hθi'] at h1
    exact mul_eq_right.mp h1.symm
  have hneg : ∀ x : Su K p f 4, suMat x = -1 → θ x = 1 := fun x hx => by
    rw [show x = ModelFacts.Orth15.InnerSu.zneg K p f from
      suMat_injective (by rw [hx, ModelFacts.Orth15.InnerSu.suMat_zneg])]
    exact hzneg
  set θ' : Su K p f 4 →* Y := θ.comp (MulAut.conj g).toMonoidHom with hθ'
  have hθ'surj : Function.Surjective θ' := hsurj.comp (MulAut.conj g).surjective
  have hθ'ker : θ'.ker ≤ Subgroup.center (Su K p f 4) := by
    intro x hx
    have hx' : g * x * g⁻¹ ∈ θ.ker := hx
    exact ModelFacts.Orth15.InnerL4.mem_center_of_conj_mem_center (hker hx')
  have hθ'neg : ∀ x : Su K p f 4, suMat x = -1 → θ' x = 1 := by
    intro x hx
    show θ (g * x * g⁻¹) = 1
    apply hneg
    rw [suMat_mul, suMat_mul, hx, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul,
      suMat_mul_suMat_inv]
  have hA : R.map θ = (blockEmb K p f 4 2 0 (by norm_num)).range.map θ' := by
    rw [hRg, Subgroup.map_map]
  have hA' : R'.map θ = (blockEmb K p f 4 2 2 (by norm_num)).range.map θ' := by
    rw [hR'g, Subgroup.map_map]
  have hzz : z' = θ' (rootInvSU K p f (show 2 ≤ 4 by norm_num)) := by
    show z' = θ (g * rootInvSU K p f (show 2 ≤ 4 by norm_num) * g⁻¹)
    rw [← hig, hθi]
  have hkerc : θ.ker = Subgroup.center (Su K p f 4) :=
    le_antisymm hker (center_le_ker hK hq1 θ hneg)
  have hcen : Subgroup.center Y = ⊥ :=
    CX4.center_eq_bot_of_mulEquiv ((QuotientGroup.quotientMulEquivOfEq hkerc.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective θ hsurj))
      (Group.IsPerfect.center_quotient_center_eq_bot (Su K p f 4))
  have hmem0 : ∀ B : Su K p f 2, θ' (blockEmb K p f 4 2 0 (by norm_num) B) ∈ R.map θ :=
    fun B => by
      rw [hA]
      exact Subgroup.mem_map_of_mem θ' (MonoidHom.mem_range.mpr ⟨B, rfl⟩)
  have hmem2 : ∀ B : Su K p f 2, θ' (blockEmb K p f 4 2 2 (by norm_num) B) ∈ R'.map θ :=
    fun B => by
      rw [hA']
      exact Subgroup.mem_map_of_mem θ' (MonoidHom.mem_range.mpr ⟨B, rfl⟩)
  refine ⟨hcen, oddCoreOf_map_longRootU_eq_bot hK hp θ hker hi,
    oddCoreOf_map_longRootU_eq_bot hK hp θ hker hi', fun P hP hfix => ?_,
    fun β hβ hβ' hβ2 hβ1 hβz => ?_⟩
  · exact fix_pgroup hK hp hq hq1 θ' hθ'surj hθ'ker P hP fun s hs =>
      ⟨fun B => (hfix s hs).1 _ (hmem0 B), fun B => (hfix s hs).2 _ (hmem2 B)⟩
  · rw [hzz] at hβz ⊢
    exact fix_invol hK hp hq hq1 θ' hθ'surj hθ'ker hθ'neg β (fun B => hβ _ (hmem0 B))
      (fun B => hβ' _ (hmem2 B)) hβ2 hβ1 hβz

end CFSG.ClassicalInvolution.Asc77.CX.CX4.U4
