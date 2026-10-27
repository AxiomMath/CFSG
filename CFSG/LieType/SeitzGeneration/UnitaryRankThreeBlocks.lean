module

public import CFSG.LieType.SeitzGeneration.HyperAnisoBlocks
public import CFSG.LieType.SeitzGeneration.UnitaryNonsplit
public import CFSG.Foundations
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.URankThree

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary HyperBlocks

section General

variable {K : Type*} [Field K] {σ : K ≃+* K} {n : ℕ}

variable (σ n) in
abbrev act : SUid σ n →* Module.End K (Fin n → K) := DistribMulAction.toModuleEnd K (Fin n → K)

theorem act_apply (g : SUid σ n) (v : Fin n → K) : act σ n g v = g • v := rfl

theorem herm_sumOp (B : Subgroup (SUid σ n)) [Fintype B] (u v : Fin n → K) :
    herm σ (sumOp (act σ n) B u) v = herm σ u (sumOp (act σ n) B v) := by
  unfold sumOp
  simp only [LinearMap.sum_apply, act_apply, Centers.herm_sum_left, Centers.herm_sum_right]
  have h : ∀ b : B, herm σ ((b : SUid σ n) • u) v = herm σ u (((b⁻¹ : B) : SUid σ n) • v) :=
    fun b => by
      rw [← herm_smul_smul σ ((b : SUid σ n)⁻¹) _ v, inv_smul_smul]
      rfl
  rw [Finset.sum_congr rfl fun b _ => h b]
  exact Fintype.sum_equiv (Equiv.inv B) _ _ (fun b => rfl)

theorem herm_fix_sumOp {B : Subgroup (SUid σ n)} [Fintype B] {u : Fin n → K}
    (hu : u ∈ fixSub (act σ n) B) (v : Fin n → K) :
    herm σ u (sumOp (act σ n) B v) = (Fintype.card B : K) * herm σ u v := by
  rw [← herm_sumOp, sumOp_apply_of_fix _ B hu, herm_smul_left, map_natCast]

theorem eq_zero_of_fixSub {B : Subgroup (SUid σ n)} [Fintype B] (hB : (Fintype.card B : K) ≠ 0)
    {u : Fin n → K} (hu : u ∈ fixSub (act σ n) B)
    (h : ∀ w ∈ fixSub (act σ n) B, herm σ u w = 0) : u = 0 := by
  refine eq_zero_of_herm σ fun v => ?_
  have h1 := herm_fix_sumOp hu v
  rw [h _ (sumOp_mem_fixSub _ B v)] at h1
  exact (mul_eq_zero.mp h1.symm).resolve_left hB

theorem herm_fixSub_block {A F : Subgroup (SUid σ n)} [Fintype A]
    (hA : (Fintype.card A : K) ≠ 0) {u v : Fin n → K} (hu : u ∈ fixSub (act σ n) A)
    (hv : v ∈ HyperBlocks.block (act σ n) A F) : herm σ u v = 0 := by
  have h1 := herm_fix_sumOp hu v
  rw [LinearMap.mem_ker.mp hv.2, herm_zero_right] at h1
  exact (mul_eq_zero.mp h1.symm).resolve_left hA

theorem sumOp_eq_zero_of_block {Y V : Type*} [Group Y] [AddCommGroup V] [Module K V]
    (ρ : Y →* Module.End K V) {A F F' : Subgroup Y} [Fintype A] [Fintype F]
    (hA : (Fintype.card A : K) ≠ 0) (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hFA : F ≤ A) (hF'A : F' ≤ A) (hgen : F ⊔ F' = A) {w : V} (hw : w ∈ HyperBlocks.block ρ A F') :
    sumOp ρ F w = 0 := by
  have hcF : ∀ f' ∈ F', ρ f' * sumOp ρ F = sumOp ρ F * ρ f' := fun f' hf' => by
    unfold sumOp
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [← map_mul, ← map_mul, hcomm f' (hF'A hf') f (hFA f.2)]
  have h1 : sumOp ρ F w ∈ fixSub ρ A := by
    have hA' : A ≤ stabVec ρ (sumOp ρ F w) := by
      rw [← hgen]
      refine sup_le (sumOp_mem_fixSub ρ F w) (fun f' hf' => ?_)
      show ρ f' (sumOp ρ F w) = sumOp ρ F w
      rw [← Module.End.mul_apply, hcF f' hf', Module.End.mul_apply, hw.1 f' hf']
    exact hA'
  have h2 : sumOp ρ A (sumOp ρ F w) = 0 := by
    have hSS : sumOp ρ A * sumOp ρ F = (Fintype.card F : K) • sumOp ρ A := by
      unfold sumOp
      rw [Finset.mul_sum]
      have : ∀ f : F, sumOp ρ A * ρ (f : Y) = sumOp ρ A := fun f => sumOp_mul ρ A (hFA f.2)
      unfold sumOp at this
      simp_rw [this]
      simp [Nat.cast_smul_eq_nsmul]
    rw [← Module.End.mul_apply, hSS, LinearMap.smul_apply, LinearMap.mem_ker.mp hw.2, smul_zero]
  have h3 := sumOp_apply_of_fix ρ A h1
  rw [h2] at h3
  have h4 := congrArg (fun z => ((Fintype.card A : ℕ) : K)⁻¹ • z) h3.symm
  simpa [smul_smul, inv_mul_cancel₀ hA] using h4

theorem herm_block_block {A F F' : Subgroup (SUid σ n)} [Fintype A] [Fintype F]
    (hA : (Fintype.card A : K) ≠ 0) (hF : (Fintype.card F : K) ≠ 0)
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hFA : F ≤ A) (hF'A : F' ≤ A)
    (hgen : F ⊔ F' = A) {v w : Fin n → K} (hv : v ∈ HyperBlocks.block (act σ n) A F)
    (hw : w ∈ HyperBlocks.block (act σ n) A F') : herm σ v w = 0 := by
  have h1 := herm_fix_sumOp hv.1 w
  rw [sumOp_eq_zero_of_block (act σ n) hA hcomm hFA hF'A hgen hw, herm_zero_right] at h1
  exact (mul_eq_zero.mp h1.symm).resolve_left hF

theorem eq_zero_of_block (hσ : ∀ c, σ (σ c) = c) {A F : Subgroup (SUid σ n)} [Fintype A]
    [Fintype F] (hA : (Fintype.card A : K) ≠ 0) (hF : (Fintype.card F : K) ≠ 0) (hFA : F ≤ A)
    {u : Fin n → K} (hu : u ∈ HyperBlocks.block (act σ n) A F)
    (h : ∀ w ∈ HyperBlocks.block (act σ n) A F, herm σ u w = 0) : u = 0 := by
  refine eq_zero_of_herm σ fun v => ?_
  have h1 := herm_fix_sumOp hu.1 v
  have hmem : sumOp (act σ n) F v ∈ fixSub (act σ n) A ⊔ HyperBlocks.block (act σ n) A F := by
    rw [← fixSub_eq_sup _ hA hFA]
    exact sumOp_mem_fixSub _ F v
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hmem
  rw [← hab, herm_add_right, herm_eq_zero_comm σ hσ (herm_fixSub_block hA ha hu), h b hb,
    add_zero] at h1
  exact (mul_eq_zero.mp h1.symm).resolve_left hF

theorem smul_mem_fixSub {A B : Subgroup (SUid σ n)} (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hBA : B ≤ A) {a : SUid σ n} (ha : a ∈ A) {v : Fin n → K} (hv : v ∈ fixSub (act σ n) B) :
    a • v ∈ fixSub (act σ n) B := fun b hb => by
  change b • a • v = a • v
  rw [← mul_smul, hcomm b (hBA hb) a ha, mul_smul]
  exact congrArg (a • ·) (hv b hb)

end General

section Dimension

open CFSG.RankThree.PartOne.KCUnitaryPlane CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.BorelTits Nonsplit

variable {ℓ f n : ℕ} {K : Type} [Field K] [Finite K] [Fact ℓ.Prime] [CharP K ℓ]

local notation "σ₀" => unitaryInvolution K ℓ f

theorem ordNegQ_dvd_finrank_block (hU : UnitaryFieldData ℓ f K) {p : ℕ} (hp : p.Prime)
    (hpℓ : p ≠ ℓ) {A F : Subgroup (SUid σ₀ n)} [Fintype A] [Fintype F]
    (hA : (Fintype.card A : K) ≠ 0) (hF0 : (Fintype.card F : K) ≠ 0)
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hFA : F ≤ A) (hF : F.relIndex A = p)
    {x : SUid σ₀ n} (hxA : x ∈ A) (hxF : x ∉ F) (hxp : x ^ p = 1) :
    ordNegQ ℓ f p ∣ Module.finrank K (HyperBlocks.block (act σ₀ n) A F) := by
  classical
  have hσ : IsUnitaryInvolution σ₀ := isUnitaryInvolution hU
  let W := HyperBlocks.block (act σ₀ n) A F
  have hW : ∀ y ∈ A, ∀ w ∈ W, act σ₀ n y w ∈ W := fun y hy w hw =>
    block_invariant (act σ₀ n) hFA hcomm hy hw
  let xW : W →ₗ[K] W := (act σ₀ n x).restrict (hW x hxA)
  let yW : W →ₗ[K] W := (act σ₀ n x⁻¹).restrict (hW _ (A.inv_mem hxA))
  have hxy : xW * yW = 1 := LinearMap.ext fun w => Subtype.ext (by
    change x • x⁻¹ • (w : Fin n → K) = w
    rw [smul_inv_smul])
  have hyx : yW * xW = 1 := LinearMap.ext fun w => Subtype.ext (by
    change x⁻¹ • x • (w : Fin n → K) = w
    rw [inv_smul_smul])
  let g : LinearMap.GeneralLinearGroup K W := ⟨xW, yW, hxy, hyx⟩
  have hB : ((idForm hU n).domRestrict₁₂ W W).IsSymm := (idForm_isSymm hU n).domRestrict W
  have hBl : ((idForm hU n).domRestrict₁₂ W W).SeparatingLeft := by
    intro w hw
    refine Subtype.ext (eq_zero_of_block hσ.invol hA hF0 hFA w.2 fun w' hw' => ?_)
    have := hw ⟨w', hw'⟩
    rw [LinearMap.domRestrict₁₂_apply, idForm_eq_herm] at this
    exact this
  have hg : g ∈ sesqUnitaryGroup ((idForm hU n).domRestrict₁₂ W W) := by
    intro v w
    change idForm hU n (x • (v : Fin n → K)) (x • (w : Fin n → K)) = idForm hU n v w
    rw [idForm_eq_herm, idForm_eq_herm]
    exact herm_smul_smul σ₀ x v w
  have hpow : ∀ (k : ℕ) (w : W), (((g : Module.End K W) ^ k) w : Fin n → K) = x ^ k • (w : _) := by
    intro k
    induction k with
    | zero => intro w; simp
    | succ k ih =>
      intro w
      rw [pow_succ, Module.End.mul_apply, ih, pow_succ, mul_smul]
      rfl
  have hgp : (g : Module.End K W) ^ p = 1 := LinearMap.ext fun w => Subtype.ext (by
    rw [hpow, hxp, one_smul]
    rfl)
  have hker : LinearMap.ker ((g : Module.End K W) - 1) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro w hw
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hw
    have hfix : act σ₀ n x w = w := congrArg Subtype.val hw
    exact Subtype.ext (block_fixed_eq_zero (act σ₀ n) hA
      (sup_zpowers_eq hp hFA hF hxA hxF) w.2 hfix)
  have h := ordNegQ_dvd_finrank_sub hU hp hpℓ hB hBl hg hgp
  rwa [hker, finrank_bot, Nat.sub_zero] at h

end Dimension

end CFSG.LieType.SeitzGeneration.URankThree
