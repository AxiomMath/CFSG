module

public import CFSG.ClassicalInvolution.Asc77.AscCX9Z8
public import CFSG.ClassicalInvolution.Asc77.AscCX9W
public import CFSG.ClassicalInvolution.Asc77.AscCX4U5
public import CFSG.ClassicalInvolution.Asc77.AscCX9Z5

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.CX.MF2U

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.LieType.Universal.Unitary CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits
  CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.ClassicalInvolution.Asc77.CX.MF2L (spForm uT orderOf_upT_one)
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem theta_inj_block0 (hK : Nat.card K = (p ^ f) ^ 2) {Y : Type} [Group Y]
    (θ : Su K p f 4 →* Y) (hker : θ.ker ≤ Subgroup.center (Su K p f 4)) {x y : Su K p f 4}
    (hx : x ∈ (blockEmb K p f 4 2 0 (by norm_num)).range)
    (hy : y ∈ (blockEmb K p f 4 2 0 (by norm_num)).range) (h : θ x = θ y) : x = y := by
  have hxy : x⁻¹ * y ∈ θ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  have h1 := CX4.U4.eq_one_of_mem_longRootU_of_mem_center hK
    (isLongRootSU2_standard (K := K) (p := p) (f := f) (show 2 ≤ 4 by norm_num))
    (Subgroup.mul_mem _ (Subgroup.inv_mem _ hx) hy) (hker hxy)
  exact inv_mul_eq_one.mp h1

variable {Y : Type} [Group Y] [Finite Y]

theorem diagWit_U (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) {F : Type} [Field F] [CharP F p]
    (hsq : IsSquare (-1 : F)) (D : DescData (unitaryInvolution K p f) F)
    (hσt : unitaryInvolution K p f D.t = -D.t) (θ : Su K p f 4 →* Y)
    (hθ : Function.Surjective θ) (hker : θ.ker = Subgroup.center (Su K p f 4)) (β β' : MulAut Y)
    (hX₁ : Goldschmidt75.perfRes (fixSubgroup β) = (spU (spForm D.m D.n)).map θ)
    (hX₂ : Goldschmidt75.perfRes (fixSubgroup β') = (spU (spForm (-D.m) D.n)).map θ)
    (hA : (blockEmb K p f 4 2 0 (by norm_num)).range.map θ ≤
      Goldschmidt75.perfRes (fixSubgroup β))
    (hA' : (blockEmb K p f 4 2 2 (by norm_num)).range.map θ ≤
      Goldschmidt75.perfRes (fixSubgroup β))
    (hB : (blockEmb K p f 4 2 0 (by norm_num)).range.map θ ≤
      Goldschmidt75.perfRes (fixSubgroup β'))
    (hB' : (blockEmb K p f 4 2 2 (by norm_num)).range.map θ ≤
      Goldschmidt75.perfRes (fixSubgroup β')) :
    DiagWit p (centTG _ _ β hA hA') (centTG _ _ β' hB hB') := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two (K := K) hp2
  have hmapX : (Goldschmidt75.perfRes (fixSubgroup β)).map (cHatU θ hθ hker).toMonoidHom =
      Goldschmidt75.perfRes (fixSubgroup β') := by
    rw [hX₁, hX₂, map_cHatU, map_d0SU_spU]
  set φ : ↥(Goldschmidt75.perfRes (fixSubgroup β)) ≃*
      ↥(Goldschmidt75.perfRes (fixSubgroup β')) :=
    ((cHatU θ hθ hker).subgroupMap (Goldschmidt75.perfRes (fixSubgroup β))).trans
      (MulEquiv.subgroupCongr hmapX) with hφ
  have hφv : ∀ x, (φ x : Y) = cHatU θ hθ hker x := fun x => rfl
  have h0 : ((blockEmb K p f 4 2 0 (by norm_num)).range.map θ).map
      (cHatU θ hθ hker).toMonoidHom = (blockEmb K p f 4 2 0 (by norm_num)).range.map θ := by
    rw [map_cHatU, map_d0SU_block0]
  have hfix2 : ∀ y ∈ (blockEmb K p f 4 2 2 (by norm_num)).range.map θ,
      cHatU θ hθ hker y = y := by
    rintro _ ⟨_, ⟨B, rfl⟩, rfl⟩
    rw [cHatU_apply, d0SU_block2]
  have hφA : (((blockEmb K p f 4 2 0 (by norm_num)).range.map θ).subgroupOf
      (Goldschmidt75.perfRes (fixSubgroup β))).map (φ : _ →* _) =
      ((blockEmb K p f 4 2 0 (by norm_num)).range.map θ).subgroupOf
        (Goldschmidt75.perfRes (fixSubgroup β')) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : (x : Y) ∈ (blockEmb K p f 4 2 0 (by norm_num)).range.map θ := hx
      refine Subgroup.mem_subgroupOf.mpr ?_
      show (φ x : Y) ∈ _
      rw [hφv, ← h0]
      exact Subgroup.mem_map_of_mem _ hx'
    · intro hy
      rw [Subgroup.mem_subgroupOf, ← h0] at hy
      obtain ⟨x, hx, hxy⟩ := hy
      exact ⟨⟨x, hA hx⟩, Subgroup.mem_subgroupOf.mpr hx, Subtype.ext hxy⟩
  have hφA' : (((blockEmb K p f 4 2 2 (by norm_num)).range.map θ).subgroupOf
      (Goldschmidt75.perfRes (fixSubgroup β))).map (φ : _ →* _) =
      ((blockEmb K p f 4 2 2 (by norm_num)).range.map θ).subgroupOf
        (Goldschmidt75.perfRes (fixSubgroup β')) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : (x : Y) ∈ (blockEmb K p f 4 2 2 (by norm_num)).range.map θ := hx
      refine Subgroup.mem_subgroupOf.mpr ?_
      show (φ x : Y) ∈ _
      rw [hφv, hfix2 _ hx']
      exact hx'
    · intro hy
      rw [Subgroup.mem_subgroupOf] at hy
      exact ⟨⟨y, hA' hy⟩, Subgroup.mem_subgroupOf.mpr hy, Subtype.ext (hfix2 _ hy)⟩
  refine ⟨φ, hφA, hφA', fun hiff => ?_⟩
  have hr' : DiagTriv p (TwinGroup.restr' (L₁ := centTG _ _ β hA hA')
      (L₂ := centTG _ _ β' hB hB') φ hφA') := by
    intro u _
    refine ⟨1, ?_⟩
    rw [one_mul, inv_one, mul_one]
    apply Subtype.ext
    exact (congrArg Subtype.val (TwinGroup.restr'_apply (L₁ := centTG _ _ β hA hA')
      (L₂ := centTG _ _ β' hB hB') φ hφA' u)).trans (hfix2 _ u.2)
  have hr := hiff.mpr hr'
  have hker' : θ.ker ≤ Subgroup.center (Su K p f 4) := hker.le
  have hinj : Function.Injective (θ.comp (D.kU.comp (longBlock F 2 0))) := fun a b hab =>
    longBlock_injective 0 (D.kU_injective (theta_inj_block0 hK θ hker'
      (D.kU_longBlock0_mem a) (D.kU_longBlock0_mem b) hab))
  set u : ↥((blockEmb K p f 4 2 0 (by norm_num)).range.map θ) :=
    ⟨θ (D.kU (longBlock F 2 0 (uT 1))), Subgroup.mem_map_of_mem θ (D.kU_longBlock0_mem _)⟩
    with hu
  have hou : orderOf u = p := by
    rw [← Subgroup.orderOf_coe, hu]
    show orderOf ((θ.comp (D.kU.comp (longBlock F 2 0))) (uT 1)) = p
    rw [orderOf_injective _ hinj, orderOf_upT_one p]
  obtain ⟨g, hg⟩ := hr u hou
  have hg2 : (g : Y) ∈ ((longRootSp2 F 2 0).map D.kU).map θ := by
    rw [D.map_kU_longRoot0 hK]
    exact g.2
  rw [Subgroup.map_map] at hg2
  obtain ⟨_, ⟨b, rfl⟩, hgb⟩ := hg2
  have e1 : (TwinGroup.restr (L₁ := centTG _ _ β hA hA') (L₂ := centTG _ _ β' hB hB') φ hφA u :
      Y) = θ (d0SU (D.kU (longBlock F 2 0 (uT 1)))) := by
    show cHatU θ hθ hker (θ (D.kU (longBlock F 2 0 (uT 1)))) = _
    rw [cHatU_apply]
  have e2 := congrArg Subtype.val hg
  rw [e1] at e2
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, hu] at e2
  rw [← hgb] at e2
  simp only [MonoidHom.coe_comp, Function.comp_apply] at e2
  rw [← map_inv, ← map_mul, ← map_mul, ← map_inv, ← map_mul, ← map_mul, ← map_inv,
    ← map_mul, ← map_mul] at e2
  exact D.d0_kU_ne hσt h2 hsq b (theta_inj_block0 hK θ hker'
    (d0SU_mem_block0 (D.kU_longBlock0_mem _)) (D.kU_longBlock0_mem _) e2)

end CFSG.ClassicalInvolution.Asc77.CX.MF2U
