module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneX10TwFrame
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneX10TwRoot
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneX10T1Iso

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.X10

open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatLeafProof CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

theorem center_projectiveSL_eq_bot' {m : ℕ} (hm : 2 ≤ m) (K : Type) [Field K] :
    Subgroup.center (LinearFlag.projectiveSL (m + 1) K) = ⊥ := by
  have : Group.IsPerfect (SL(m + 1, K)) := (SpecialLinear.isQuasisimple m K hm).1
  have hc := ComponentClassification.Quasisimple.center_comap_of_central_kernel
    (LinearFlag.proj (m + 1) K) (LinearFlag.proj_surjective _ _)
    (by rw [LinearFlag.ker_proj, LinearFlag.scalars_eq_center])
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨g, rfl⟩ := LinearFlag.proj_surjective _ _ z
  have hg : g ∈ Subgroup.center (SL(m + 1, K)) := by
    rw [← hc]
    exact hz
  rw [← LinearFlag.scalars_eq_center] at hg
  exact Subgroup.mem_bot.mpr (LinearFlag.proj_eq_one_iff.mpr hg)

theorem exists_pairSpan_projectiveSL_of_frame
    {τ : Tag} {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) {m : ℕ} (hm : 2 ≤ m) {S : Set (Fin τ.rank → ℤ)}
    {β₀ : Fin τ.rank → ℤ} (hβ₀ : IsRoot τ β₀) (hβS : β₀ ∈ S) (k₀ : Fin m)
    (Ψ : SL(m + 1, K) →* adjointGroup τ K) (hker : Ψ.ker ≤ Subgroup.center (SL(m + 1, K)))
    (hrange : Ψ.range.map (adjointGroup τ K).subtype = pairSpan τ K S)
    (hrk : (CurtisTits.rankOne (SpecialLinear.rootDatum m K).rootGroup k₀).map Ψ =
      (adjDatum (rootOperatorFamily τ) K).rootGroup β₀ ⊔
        (adjDatum (rootOperatorFamily τ) K).rootGroup (-β₀)) :
    ∃ θ : pairSpan τ K S →* LinearFlag.projectiveSL (m + 1) K,
      Function.Surjective θ ∧ θ.ker = Subgroup.center _ ∧
      ∃ (N : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (r : K → SL(m + 1, K)),
        N * N = 0 ∧ N ≠ 0 ∧
        (∀ c, ((r c : SL(m + 1, K)) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) = 1 + c • N) ∧
        (∀ c, ∃ d, θ ⟨rootSL2 τ K β₀ (uSL c), rootSL2_uSL_mem_pairSpan hβS c⟩ =
          LinearFlag.proj (m + 1) K (r d)) ∧
        ∀ d, ∃ c, θ ⟨rootSL2 τ K β₀ (uSL c), rootSL2_uSL_mem_pairSpan hβS c⟩ =
          LinearFlag.proj (m + 1) K (r d) := by
  have hij : (k₀.castSucc : Fin (m + 1)) ≠ k₀.succ := Fin.castSucc_lt_succ.ne
  set X := SpecialLinear.fundamentalRootSubgroup m K k₀ true with hX
  have hXR : X ≤ CurtisTits.rankOne (SpecialLinear.rootDatum m K).rootGroup k₀ := by
    change X ≤ CurtisTits.rankOne (SpecialLinear.rootGroup m K) k₀
    rw [SpecialLinear.rankOne_rootGroup]
    exact le_sup_left
  have hXeq : X = (Matrix.SpecialLinearGroup.transvectionHom (A := K) hij).range := rfl
  have hpX : IsPGroup p X := by
    have hM : IsPGroup p (Multiplicative K) := IsPGroup.of_card (n := f) hK
    rw [hXeq]
    exact hM.of_surjective (Matrix.SpecialLinearGroup.transvectionHom (A := K) hij).rangeRestrict
      (MonoidHom.rangeRestrict_surjective _)
  obtain ⟨y, hy⟩ := exists_conj_le_rootGroup hp hp2 hK hβ₀ Ψ hrk hXR hpX
  set ΨM := (adjointGroup τ K).subtype.comp Ψ with hΨM
  have hrangeM : ΨM.range = pairSpan τ K S := by
    rw [hΨM, MonoidHom.range_comp, hrange]
  have hkerM : ΨM.ker ≤ Subgroup.center _ := fun x hx => hker (by
    rw [MonoidHom.mem_ker] at hx ⊢
    exact Subtype.ext hx)
  obtain ⟨θ, hθs, hθk, hθ⟩ := exists_quotient_of_frame ΨM hrangeM hkerM
    (LinearFlag.proj (m + 1) K) (LinearFlag.proj_surjective _ _)
    (by rw [LinearFlag.ker_proj, LinearFlag.scalars_eq_center]) (center_projectiveSL_eq_bot' hm K)
  set Y := ((y : SL(m + 1, K)) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) with hY
  set Yi := ((y⁻¹ : SL(m + 1, K)) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) with hYi
  have hYYi : Y * Yi = 1 := by
    rw [hY, hYi, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hYiY : Yi * Y = 1 := by
    rw [hY, hYi, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  set E := Matrix.single (k₀.castSucc : Fin (m + 1)) k₀.succ (1 : K) with hE
  have hE2 : E * E = 0 := by
    rw [hE]
    simp [hij.symm]
  have hE0 : E ≠ 0 := fun h => by
    have := congrFun (congrFun h k₀.castSucc) k₀.succ
    rw [hE, Matrix.single_apply_same] at this
    exact one_ne_zero this
  set N := Y * E * Yi with hN
  set r : K → SL(m + 1, K) := fun d =>
    y * Matrix.SpecialLinearGroup.transvection hij d * y⁻¹ with hr
  have hN2 : N * N = 0 := by
    calc N * N = Y * (E * (Yi * Y) * E) * Yi := by simp only [hN, Matrix.mul_assoc]
      _ = 0 := by rw [hYiY, Matrix.mul_one, hE2, Matrix.mul_zero, Matrix.zero_mul]
  have hN0 : N ≠ 0 := fun h => by
    apply hE0
    calc E = Yi * (Y * E * Yi) * Y := by
          simp only [← Matrix.mul_assoc, hYiY, Matrix.one_mul]
          rw [Matrix.mul_assoc, hYiY, Matrix.mul_one]
      _ = 0 := by rw [← hN, h, Matrix.mul_zero, Matrix.zero_mul]
  have hrc : ∀ c, ((r c : SL(m + 1, K)) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) = 1 + c • N := by
    intro c
    have hs : Matrix.single (k₀.castSucc : Fin (m + 1)) k₀.succ c = c • E := by
      rw [hE, Matrix.smul_single, smul_eq_mul, mul_one]
    rw [hr, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.transvection_coe, hs, ← hY, ← hYi, Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_one, hYYi, Matrix.mul_smul, Matrix.smul_mul]
  have hxU : ∀ d, ΨM (r d) ∈ rootSubgroup τ K β₀ := by
    intro d
    rw [← map_subtype_rootGroup _ hβ₀]
    refine ⟨Ψ (r d), hy ⟨_, ⟨Matrix.SpecialLinearGroup.transvection hij d, ?_, rfl⟩, rfl⟩, rfl⟩
    exact SpecialLinear.transvection_mem_rootSubgroup hij d
  have hsup : ∀ d, ∃ c, θ ⟨rootSL2 τ K β₀ (uSL c), rootSL2_uSL_mem_pairSpan hβS c⟩ =
      LinearFlag.proj (m + 1) K (r d) := by
    intro d
    obtain ⟨c, hc⟩ := exists_rootSL2_uSL_eq (hxU d)
    refine ⟨c, ?_⟩
    have h1 : (⟨rootSL2 τ K β₀ (uSL c), rootSL2_uSL_mem_pairSpan hβS c⟩ : pairSpan τ K S) =
        ⟨ΨM (r d), by rw [← hrangeM]; exact ⟨r d, rfl⟩⟩ := Subtype.ext hc
    rw [h1, hθ]
  refine ⟨θ, hθs, hθk, N, r, hN2, hN0, hrc, ?_, hsup⟩
  choose cf hcf using hsup
  have hinj : Function.Injective cf := fun d₁ d₂ h =>
    rootClass_injective_psl (by omega) hN2 hN0 r hrc (by rw [← hcf, ← hcf, h])
  have hsurj := Finite.injective_iff_surjective.mp hinj
  intro c
  obtain ⟨d, rfl⟩ := hsurj c
  exact ⟨d, hcf d⟩

end CFSG.ComponentClassification.Burgoyne.X10
