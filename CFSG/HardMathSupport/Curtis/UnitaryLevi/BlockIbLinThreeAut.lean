module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbLinThreeAlg
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.AGLEmbedding.LinearThreeKitParab
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeAbstract

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi.LinA

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.AGLEmbedding.LinearThreeKit
open scoped commutatorElement

section Blk

variable {K : Type} [Field K]

def blk (M : Matrix (Fin 3) (Fin 3) K) : Matrix (Fin 2) (Fin 2) K := fun i j => M i.succ j.succ

def LZ (M : Matrix (Fin 3) (Fin 3) K) : Prop := M 1 0 = 0 ∧ M 2 0 = 0

theorem LZ.one : LZ (1 : Matrix (Fin 3) (Fin 3) K) := by
  constructor <;> simp

theorem LZ.mul {M N : Matrix (Fin 3) (Fin 3) K} (hM : LZ M) (hN : LZ N) : LZ (M * N) := by
  obtain ⟨hM1, hM2⟩ := hM
  obtain ⟨hN1, hN2⟩ := hN
  constructor <;> simp [Matrix.mul_apply, Fin.sum_univ_three, hM1, hM2, hN1, hN2]

theorem LZ.pow {M : Matrix (Fin 3) (Fin 3) K} (hM : LZ M) (m : ℕ) : LZ (M ^ m) := by
  induction m with
  | zero => simpa using LZ.one
  | succ m ih => rw [pow_succ]; exact ih.mul hM

theorem blk_mul {M : Matrix (Fin 3) (Fin 3) K} (hM : LZ M) (N : Matrix (Fin 3) (Fin 3) K) :
    blk (M * N) = blk M * blk N := by
  obtain ⟨h1, h2⟩ := hM
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, h1, h2]

theorem blk_one : blk (1 : Matrix (Fin 3) (Fin 3) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk]

theorem blk_pow {M : Matrix (Fin 3) (Fin 3) K} (hM : LZ M) (m : ℕ) : blk (M ^ m) = blk M ^ m := by
  induction m with
  | zero => simpa using blk_one
  | succ m ih => rw [pow_succ, pow_succ, blk_mul (hM.pow m), ih]

theorem blk_map (M : Matrix (Fin 3) (Fin 3) K) (f : K → K) :
    blk (M.map f) = (blk M).map f := by
  ext i j; simp [blk]

theorem det_of_LZ {M : Matrix (Fin 3) (Fin 3) K} (hM : LZ M) :
    M.det = M 0 0 * (blk M).det := by
  obtain ⟨h1, h2⟩ := hM
  simp [Matrix.det_fin_three, Matrix.det_fin_two, blk, h1, h2]
  ring

end Blk

section Lift

variable {K : Type} [Field K]

theorem exists_lift_perfect (D : Subgroup (projectiveSL 3 K)) (hDp : ⁅D, D⁆ = D)
    (hDP : D ≤ projStabilizer (flagSpace 3 K 1)) :
    ∃ Dt : Subgroup (SpecialLinearGroup (Fin 3) K), ⁅Dt, Dt⁆ = Dt ∧ Dt.map (proj 3 K) = D ∧
      Dt ≤ stabilizer (flagSpace 3 K 1) := by
  obtain ⟨W, hW, hWle, hWmap⟩ := CFSG.AGLEmbedding.ParabPrime.exists_perfect_map_eq (proj 3 K)
    ((ker_proj 3 K).le.trans (scalars_le_center 3 K)) hDp
    (by rw [MonoidHom.range_eq_top.2 (proj_surjective 3 K)]; exact le_top)
  refine ⟨W, hW, hWmap, ?_⟩
  intro g hg
  have h1 := hWle hg
  rw [Subgroup.mem_comap] at h1
  rw [← comap_projStabilizer (n := 3) (K := K) (flagSpace 3 K 1), Subgroup.mem_comap]
  exact hDP h1

theorem LZ_of_mem_stabilizer {g : SpecialLinearGroup (Fin 3) K}
    (hg : g ∈ stabilizer (flagSpace 3 K 1)) : LZ (g : Matrix (Fin 3) (Fin 3) K) :=
  ⟨apply_zero_eq_zero_of_mem_stabilizer_one hg (by decide),
    apply_zero_eq_zero_of_mem_stabilizer_one hg (by decide)⟩

theorem entry_zero_of_perfect {V : Subgroup (SpecialLinearGroup (Fin 3) K)}
    (hV : V ≤ stabilizer (flagSpace 3 K 1)) (hVp : ⁅V, V⁆ = V)
    {g : SpecialLinearGroup (Fin 3) K} (hg : g ∈ V) : (g : Matrix (Fin 3) (Fin 3) K) 0 0 = 1 := by
  have := mulVec_single_zero_of_perfect hV hVp hg
  have h0 := congrFun this 0
  simpa [Matrix.mulVec_single_one] using h0

end Lift

section Order

variable {K : Type} [Field K] [CharP K 2]

theorem mul_self_eq_one_of_blk {M : Matrix (Fin 3) (Fin 3) K} (hM : LZ M) (h00 : M 0 0 = 1)
    (hb : blk M = 1) : M * M = 1 := by
  obtain ⟨h1, h2⟩ := hM
  have b11 : M 1 1 = 1 := by simpa [blk] using congrFun (congrFun hb 0) 0
  have b12 : M 1 2 = 0 := by simpa [blk] using congrFun (congrFun hb 0) 1
  have b21 : M 2 1 = 0 := by simpa [blk] using congrFun (congrFun hb 1) 0
  have b22 : M 2 2 = 1 := by simpa [blk] using congrFun (congrFun hb 1) 1
  have h2' : (2 : K) = 0 := CharP.cast_eq_zero K 2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, h1, h2, h00, b11, b12, b21, b22] <;>
    (try first | linear_combination (M 0 1) * h2' | linear_combination (M 0 2) * h2')

theorem order_facts (Dt : Subgroup (SpecialLinearGroup (Fin 3) K)) (hDp : ⁅Dt, Dt⁆ = Dt)
    (hDQ : Dt ≤ stabilizer (flagSpace 3 K 1)) {b : ℕ} {st : SpecialLinearGroup (Fin 3) K}
    (hst : st ∈ Dt) (hord : orderOf (proj 3 K st) = 3 ^ b) :
    (blk (st : Matrix (Fin 3) (Fin 3) K)) ^ (3 ^ b) = 1 ∧
      (∀ m : ℕ, (blk (st : Matrix (Fin 3) (Fin 3) K)) ^ m = 1 → 3 ^ b ∣ m) ∧
      (blk (st : Matrix (Fin 3) (Fin 3) K)).det = 1 := by
  have hLZ : ∀ g ∈ Dt, LZ (g : Matrix (Fin 3) (Fin 3) K) := fun g hg => LZ_of_mem_stabilizer (hDQ hg)
  have h00 : ∀ g ∈ Dt, (g : Matrix (Fin 3) (Fin 3) K) 0 0 = 1 := fun g hg =>
    entry_zero_of_perfect hDQ hDp hg
  have hs3 : st ^ 3 ^ b = 1 := by
    have h1 : proj 3 K (st ^ 3 ^ b) = 1 := by
      rw [map_pow, ← hord]; exact pow_orderOf_eq_one _
    obtain ⟨c, -, hc⟩ := mem_scalars.1 (proj_eq_one_iff.1 h1)
    have hmem : st ^ 3 ^ b ∈ Dt := Subgroup.pow_mem _ hst _
    have h0 := h00 _ hmem
    rw [hc] at h0
    simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h0
    apply Subtype.ext
    rw [hc]
    have : (c : K) = 1 := h0
    simp [this]
  have hdvd : orderOf st = 3 ^ b := by
    refine Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one hs3) ?_
    rw [← hord]; exact orderOf_map_dvd (proj 3 K) st
  have hcoe : ∀ m : ℕ, ((st ^ m : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (st : Matrix (Fin 3) (Fin 3) K) ^ m := fun m => Matrix.SpecialLinearGroup.coe_pow st m
  refine ⟨?_, ?_, ?_⟩
  · rw [← blk_pow (hLZ st hst), ← hcoe, hs3]
    simpa using blk_one
  · intro m hm
    set g := st ^ m with hg
    have hgD : g ∈ Dt := Subgroup.pow_mem _ hst _
    have hb1 : blk (g : Matrix (Fin 3) (Fin 3) K) = 1 := by
      rw [hg, hcoe, blk_pow (hLZ st hst), hm]
    have hgg : g * g = 1 := Subtype.ext (by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
      exact mul_self_eq_one_of_blk (hLZ g hgD) (h00 g hgD) hb1)
    have hg3 : g ^ 3 ^ b = 1 := by
      rw [hg, ← pow_mul, mul_comm, pow_mul, hs3, one_pow]
    have hodd : Odd (3 ^ b) := Odd.pow (by decide)
    obtain ⟨k, hk⟩ := hodd
    have : g = 1 := by
      have e : g ^ (2 * k + 1) = g := by
        rw [pow_succ, pow_mul, sq, hgg, one_pow, one_mul]
      rw [← e, ← hk, hg3]
    rw [← hdvd]
    exact orderOf_dvd_of_pow_eq_one (by rw [← hg]; exact this)
  · have := det_of_LZ (hLZ st hst)
    rw [h00 st hst, one_mul] at this
    rw [← this]
    exact st.2

end Order

section Rel

variable {K : Type} [Field K]

theorem eq_of_inv_mul_mem_center' {H G : Type*} [Group H] [Group G] [Group.IsPerfect H]
    (f₁ f₂ : H →* G) (hc : ∀ g, (f₁ g)⁻¹ * f₂ g ∈ Subgroup.center G) : f₁ = f₂ := by
  let δ : H →* G := MonoidHom.mk' (fun g => (f₁ g)⁻¹ * f₂ g) (fun a b => by
    have h := Subgroup.mem_center_iff.mp (hc a) (f₁ b)⁻¹
    simp only [map_mul, _root_.mul_inv_rev]
    calc (f₁ b)⁻¹ * (f₁ a)⁻¹ * (f₂ a * f₂ b)
        = ((f₁ b)⁻¹ * ((f₁ a)⁻¹ * f₂ a)) * f₂ b := by group
      _ = (f₁ a)⁻¹ * f₂ a * ((f₁ b)⁻¹ * f₂ b) := by rw [h]; group)
  have hker : ⁅(⊤ : Subgroup H), ⊤⁆ ≤ δ.ker := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp (hc a) (δ b)).symm
  have htop : ⁅(⊤ : Subgroup H), ⊤⁆ = ⊤ := Group.isPerfect_def.mp inferInstance
  rw [htop] at hker
  ext g
  have := hker (Subgroup.mem_top g)
  rw [MonoidHom.mem_ker] at this
  exact inv_mul_eq_one.mp this

theorem rel_of_fixes {n : ℕ} (Dt : Subgroup (SpecialLinearGroup (Fin n) K)) (hDp : ⁅Dt, Dt⁆ = Dt)
    (A : GL (Fin n) K) (σ : K ≃+* K) (α : MulAut (projectiveSL n K))
    (hα : α = conjAut n K A * fieldAut n K σ) (hfix : ∀ g ∈ Dt, α (proj n K g) = proj n K g) :
    ∀ g ∈ Dt, (A : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K).map σ =
      (g : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K) := by
  have : Group.IsPerfect ↥Dt := Subgroup.isPerfect_iff.2 hDp
  set φ : SpecialLinearGroup (Fin n) K →* SpecialLinearGroup (Fin n) K :=
    (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n K A).toMonoidHom.comp
      (SpecialLinearGroup.map σ.toRingHom) with hφ
  have hkey : φ.comp Dt.subtype = Dt.subtype := by
    refine eq_of_inv_mul_mem_center' _ _ fun g => ?_
    have h1 := hfix g g.2
    rw [hα, MulAut.mul_apply, fieldAut_proj, conjAut_proj] at h1
    have h2 := proj_eq_proj_iff.1 h1
    rw [← scalars_eq_center]
    exact h2
  intro g hg
  have h1 := congrArg (fun f : ↥Dt →* SpecialLinearGroup (Fin n) K => (f ⟨g, hg⟩ : SpecialLinearGroup (Fin n) K)) hkey
  simp only [MonoidHom.comp_apply, Subgroup.subtype_apply] at h1
  have h2 := congrArg (fun x : SpecialLinearGroup (Fin n) K => (x : Matrix (Fin n) (Fin n) K)) h1
  simp only [hφ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation_matrix,
    Matrix.SpecialLinearGroup.map_apply_coe] at h2
  rw [RingHom.mapMatrix_apply] at h2
  calc (A : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K).map σ
      = ((A : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K).map σ *
          ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) * (A : Matrix (Fin n) (Fin n) K) := by
        rw [mul_assoc _ ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K), Units.inv_mul, mul_one]
    _ = (g : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K) := by
        rw [show (σ.toRingHom : K →+* K) = (σ : K →+* K) from rfl] at h2
        simpa using congrArg (fun M => M * (A : Matrix (Fin n) (Fin n) K)) h2

end Rel

section Analyze

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem LZ_of_rel (Dt : Subgroup (SpecialLinearGroup (Fin 3) K)) (hDp : ⁅Dt, Dt⁆ = Dt)
    (hDQ : Dt ≤ stabilizer (flagSpace 3 K 1)) {b : ℕ} (hb1 : 1 ≤ b)
    {st : SpecialLinearGroup (Fin 3) K} (hst : st ∈ Dt) (hord : orderOf (proj 3 K st) = 3 ^ b)
    (A : GL (Fin 3) K) (σ : K ≃+* K)
    (hrel : ∀ g ∈ Dt, (A : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K).map σ =
      (g : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K)) :
    LZ (A : Matrix (Fin 3) (Fin 3) K) := by
  obtain ⟨hM3, hMord, hdet⟩ := order_facts Dt hDp hDQ hst hord
  set M := blk (st : Matrix (Fin 3) (Fin 3) K) with hM
  have hMne : M ≠ 1 := by
    intro h
    have := hMord 1 (by rw [h, pow_one])
    have h3b : 3 ≤ 3 ^ b := by
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ b := Nat.pow_le_pow_right (by norm_num) hb1
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have hLZ := LZ_of_mem_stabilizer (hDQ hst)
  have h00 := entry_zero_of_perfect hDQ hDp hst
  obtain ⟨h10, h20⟩ := hLZ
  have hr := hrel st hst
  have E1 := congrFun (congrFun hr 1) 0
  have E2 := congrFun (congrFun hr 2) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.map_apply, h10, h20, h00, map_one,
    map_zero, mul_zero, mul_one, zero_mul, add_zero, zero_add] at E1 E2
  have hw : M *ᵥ ![(A : Matrix (Fin 3) (Fin 3) K) 1 0, (A : Matrix (Fin 3) (Fin 3) K) 2 0] =
      ![(A : Matrix (Fin 3) (Fin 3) K) 1 0, (A : Matrix (Fin 3) (Fin 3) K) 2 0] := by
    ext i
    fin_cases i
    · simp [hM, blk, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      linear_combination -E1
    · simp [hM, blk, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      linear_combination -E2
  have hzero := LinA.fixed_eq_zero hdet hMne (Odd.pow (by decide : Odd 3)) hM3 hw
  constructor
  · simpa using congrFun hzero 0
  · simpa using congrFun hzero 1

theorem blk_rel (Dt : Subgroup (SpecialLinearGroup (Fin 3) K))
    (hDQ : Dt ≤ stabilizer (flagSpace 3 K 1)) (A : GL (Fin 3) K) (σ : K ≃+* K)
    (hA : LZ (A : Matrix (Fin 3) (Fin 3) K))
    (hrel : ∀ g ∈ Dt, (A : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K).map σ =
      (g : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K)) :
    ∀ g ∈ Dt, blk (A : Matrix (Fin 3) (Fin 3) K) * (blk (g : Matrix (Fin 3) (Fin 3) K)).map σ =
      blk (g : Matrix (Fin 3) (Fin 3) K) * blk (A : Matrix (Fin 3) (Fin 3) K) := by
  intro g hg
  have h := congrArg blk (hrel g hg)
  rw [blk_mul hA, blk_mul (LZ_of_mem_stabilizer (hDQ hg)), blk_map (K := K)] at h
  exact h

theorem det_blk_ne_zero (A : GL (Fin 3) K) (hA : LZ (A : Matrix (Fin 3) (Fin 3) K)) :
    (blk (A : Matrix (Fin 3) (Fin 3) K)).det ≠ 0 := by
  intro h
  have hd := det_of_LZ hA
  rw [h, mul_zero] at hd
  exact (Matrix.isUnit_iff_isUnit_det _).1 A.isUnit |>.ne_zero hd

theorem fixed_pow {σ : K ≃+* K} {x : K} (h : σ x = x) (k : ℕ) : (σ ^ k) x = x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ']; exact (congrArg σ ih).trans h

theorem not_three_dvd_orderOf (Dt : Subgroup (SpecialLinearGroup (Fin 3) K)) (hDp : ⁅Dt, Dt⁆ = Dt)
    (hDQ : Dt ≤ stabilizer (flagSpace 3 K 1)) {b : ℕ}
    (hb : b = padicValNat 3 (Nat.card K ^ 2 - 1)) (hb1 : 1 ≤ b)
    {st : SpecialLinearGroup (Fin 3) K} (hst : st ∈ Dt) (hord : orderOf (proj 3 K st) = 3 ^ b)
    (A : GL (Fin 3) K) (σ : K ≃+* K)
    (hrel : ∀ g ∈ Dt, (A : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K).map σ =
      (g : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K)) :
    ¬ 3 ∣ orderOf σ := by
  intro h3
  obtain ⟨hM3, hMord, hdet⟩ := order_facts Dt hDp hDQ hst hord
  have hA := LZ_of_rel Dt hDp hDQ hb1 hst hord A σ hrel
  have hbr := blk_rel Dt hDQ A σ hA hrel st hst
  set M := blk (st : Matrix (Fin 3) (Fin 3) K) with hM
  set Ab := blk (A : Matrix (Fin 3) (Fin 3) K) with hAb
  have hdetA : IsUnit Ab.det := isUnit_iff_ne_zero.2 (det_blk_ne_zero A hA)
  have hMσ : M.map σ = Ab⁻¹ * M * Ab := by
    have : Ab⁻¹ * (Ab * M.map σ) = Ab⁻¹ * (M * Ab) := by rw [hbr]
    rw [← mul_assoc, Matrix.nonsing_inv_mul _ hdetA, one_mul, ← mul_assoc] at this
    exact this
  have htr : σ M.trace = M.trace := by
    have h1 : (M.map σ).trace = σ M.trace := by simp [Matrix.trace]
    rw [← h1, hMσ, Matrix.trace_mul_comm, ← mul_assoc, Matrix.mul_nonsing_inv _ hdetA, one_mul]
  haveI : Finite (K ≃+* K) := Finite.of_injective (fun σ : K ≃+* K => (σ : K → K))
    DFunLike.coe_injective
  have hm : 0 < orderOf σ := orderOf_pos σ
  set m := orderOf σ with hmdef
  obtain ⟨m', hm'⟩ := h3
  set σ' := σ ^ m' with hσ'
  have hσ'3 : σ' ^ 3 = 1 := by
    rw [hσ', ← pow_mul, mul_comm, ← hm', hmdef]; exact pow_orderOf_eq_one σ
  have hσ'1 : σ' ≠ 1 := by
    intro h
    have : m ∣ m' := orderOf_dvd_of_pow_eq_one h
    have hm'pos : 0 < m' := by
      rcases Nat.eq_zero_or_pos m' with h0 | h0
      · rw [h0, mul_zero] at hm'; omega
      · exact h0
    have := Nat.le_of_dvd hm'pos this
    omega
  exact LinA.false_of_fixed_trace hb hb1 σ' hσ'3 hσ'1 M hdet hMord (fixed_pow htr m')

end Analyze

section Eps

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem map_toMonoidHom_mul' {G : Type*} [Group G] (α β : MulAut G) (H : Subgroup G) :
    H.map (α * β).toMonoidHom = (H.map β.toMonoidHom).map α.toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

theorem finrank_coordImage' {n : ℕ} (σ : K ≃+* K) (W : Submodule K (Fin n → K)) :
    Module.finrank K (coordImage σ W) = Module.finrank K W := by
  let j : W ≃+ coordImage σ W :=
    { toFun := fun w => ⟨fun i => σ (w.1 i), coord_mem_coordImage w.2⟩
      invFun := fun v => ⟨fun i => σ.symm (v.1 i), v.2⟩
      left_inv := fun w => by ext i; simp
      right_inv := fun v => by ext i; simp
      map_add' := fun v w => by ext i; simp }
  have h := rank_eq_of_equiv_equiv (σ : K → K) j σ.bijective (fun r w => by ext i; simp [j])
  rw [Module.finrank, Module.finrank, h]

theorem finrank_map_mulVecLin' {n : ℕ} (A : GL (Fin n) K) (W : Submodule K (Fin n → K)) :
    Module.finrank K (W.map (mulVecLin (A : Matrix (Fin n) (Fin n) K))) = Module.finrank K W := by
  have hinj : Function.Injective (mulVecLin (A : Matrix (Fin n) (Fin n) K)) :=
    Matrix.mulVec_injective_iff_isUnit.2 A.isUnit
  exact (Submodule.equivMapOfInjective _ hinj W).finrank_eq.symm

theorem not_typeExchanging (A : GL (Fin 3) K) (σ : K ≃+* K) :
    (projStabilizer (flagSpace 3 K 1)).map
      (conjAut 3 K A * fieldAut 3 K σ * dualAut 3 K).toMonoidHom ≠
      projStabilizer (flagSpace 3 K 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htrans := standard_automorphism_transport (K := K) (n := 3)
  have h7 : ∀ (B : GL (Fin 3) K) (W : Submodule K (Fin 3 → K)),
      (projStabilizer W).map (conjAut 3 K B).toMonoidHom =
        projStabilizer (W.map (mulVecLin (B : Matrix (Fin 3) (Fin 3) K))) :=
    htrans.2.2.2.2.2.2.1
  have h8 : ∀ (τ : K ≃+* K) (W : Submodule K (Fin 3 → K)),
      (projStabilizer W).map (fieldAut 3 K τ).toMonoidHom = projStabilizer (coordImage τ W) :=
    htrans.2.2.2.2.2.2.2.1
  have h9 : ∀ W : Submodule K (Fin 3 → K),
      (projStabilizer W).map (dualAut 3 K).toMonoidHom = projStabilizer (dotOrth W) :=
    htrans.2.2.2.2.2.2.2.2.1
  intro h
  set W₁ := flagSpace 3 K 1 with hW₁
  have hW₁rank : Module.finrank K W₁ = 1 := by
    rw [hW₁, flagSpace_one_eq_span]
    exact finrank_span_singleton (by
      intro h0
      have := congrFun h0 0
      simp at this)
  set W' := (coordImage σ (dotOrth W₁)).map (mulVecLin (A : Matrix (Fin 3) (Fin 3) K)) with hW'
  have hmap : (projStabilizer W₁).map
      (conjAut 3 K A * fieldAut 3 K σ * dualAut 3 K).toMonoidHom = projStabilizer W' := by
    rw [map_toMonoidHom_mul', map_toMonoidHom_mul', h9, h8, h7]
  have hrank : Module.finrank K W' = 2 := by
    rw [hW', finrank_map_mulVecLin', finrank_coordImage', finrank_dotOrth, hW₁rank]
  obtain ⟨-, hdisj, -⟩ := intrinsic_extremal_parabolics (K := K) (n := 3) 2 (le_refl 3)
  rw [hmap] at h
  have hm1 : projStabilizer W₁ ∈ projStabilizer ''
      {L : Submodule K (Fin 3 → K) | Module.finrank K L = 1} := ⟨W₁, hW₁rank, rfl⟩
  have hm2 : projStabilizer W₁ ∈ projStabilizer ''
      {H : Submodule K (Fin 3 → K) | Module.finrank K H = 3 - 1} :=
    ⟨W', by simpa using hrank, h⟩
  exact Set.disjoint_left.1 hdisj hm1 hm2

end Eps

section Scalar

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem map_one_ringEquiv (M : Matrix (Fin 3) (Fin 3) K) : M.map (⇑(1 : K ≃+* K)) = M := by
  ext i j; rfl

theorem map_one_ringEquiv2 (M : Matrix (Fin 2) (Fin 2) K) : M.map (⇑(1 : K ≃+* K)) = M := by
  ext i j; rfl

theorem exists_noncomm_blk (Dt : Subgroup (SpecialLinearGroup (Fin 3) K)) (hDp : ⁅Dt, Dt⁆ = Dt)
    (hDQ : Dt ≤ stabilizer (flagSpace 3 K 1)) {b : ℕ} (hb1 : 1 ≤ b)
    {st : SpecialLinearGroup (Fin 3) K} (hst : st ∈ Dt) (hord : orderOf (proj 3 K st) = 3 ^ b) :
    ∃ g ∈ Dt, ∃ h ∈ Dt, blk (g : Matrix (Fin 3) (Fin 3) K) * blk (h : Matrix (Fin 3) (Fin 3) K) ≠
      blk (h : Matrix (Fin 3) (Fin 3) K) * blk (g : Matrix (Fin 3) (Fin 3) K) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hM3, hMord, hdet⟩ := order_facts Dt hDp hDQ hst hord
  have hLZ : ∀ g ∈ Dt, LZ (g : Matrix (Fin 3) (Fin 3) K) := fun g hg => LZ_of_mem_stabilizer (hDQ hg)
  let K₁ : Subgroup (SpecialLinearGroup (Fin 3) K) :=
    { carrier := {x | x ∈ Dt ∧ blk (x : Matrix (Fin 3) (Fin 3) K) = 1}
      mul_mem' := by
        rintro x y ⟨hx, hx1⟩ ⟨hy, hy1⟩
        refine ⟨Dt.mul_mem hx hy, ?_⟩
        rw [Matrix.SpecialLinearGroup.coe_mul, blk_mul (hLZ x hx), hx1, hy1, one_mul]
      one_mem' := ⟨Dt.one_mem, by simpa using blk_one⟩
      inv_mem' := by
        rintro x ⟨hx, hx1⟩
        refine ⟨Dt.inv_mem hx, ?_⟩
        have h := congrArg blk (congrArg (fun y : SpecialLinearGroup (Fin 3) K =>
          (y : Matrix (Fin 3) (Fin 3) K)) (mul_inv_cancel x))
        simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at h
        rw [blk_mul (hLZ x hx), hx1, one_mul, blk_one] at h
        exact h }
  have hle : ⁅Dt, Dt⁆ ≤ K₁ := by
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    have ha' := hLZ a ha
    have hb' := hLZ b hb
    have hai := hLZ _ (Dt.inv_mem ha)
    have hbi := hLZ _ (Dt.inv_mem hb)
    refine ⟨Dt.mul_mem (Dt.mul_mem (Dt.mul_mem ha hb) (Dt.inv_mem ha)) (Dt.inv_mem hb), ?_⟩
    have hA : blk (a : Matrix (Fin 3) (Fin 3) K) * blk ((a⁻¹ : SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = 1 := by
      rw [← blk_mul ha', ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel]; simpa using blk_one
    have hB : blk (b : Matrix (Fin 3) (Fin 3) K) * blk ((b⁻¹ : SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = 1 := by
      rw [← blk_mul hb', ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel]; simpa using blk_one
    show blk (((a * b * a⁻¹ * b⁻¹ : SpecialLinearGroup (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) = 1
    simp only [Matrix.SpecialLinearGroup.coe_mul]
    rw [blk_mul (ha'.mul hb' |>.mul hai), blk_mul (ha'.mul hb'), blk_mul ha', hcon a ha b hb]
    calc _ = blk (b : Matrix (Fin 3) (Fin 3) K) * (blk (a : Matrix (Fin 3) (Fin 3) K) *
          blk ((a⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) *
          blk ((b⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
          simp only [mul_assoc]
      _ = 1 := by rw [hA, mul_one, hB]
  have hst1 : st ∈ K₁ := hle (by rw [hDp]; exact hst)
  have hb1' : blk (st : Matrix (Fin 3) (Fin 3) K) = 1 := hst1.2
  have := hMord 1 (by rw [hb1', pow_one])
  have h3b : 3 ≤ 3 ^ b := by
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ b := Nat.pow_le_pow_right (by norm_num) hb1
  have := Nat.le_of_dvd (by norm_num) this
  omega

theorem scalar_of_rel (Dt : Subgroup (SpecialLinearGroup (Fin 3) K)) (hDp : ⁅Dt, Dt⁆ = Dt)
    (hDQ : Dt ≤ stabilizer (flagSpace 3 K 1)) {b : ℕ} (hb1 : 1 ≤ b)
    {st : SpecialLinearGroup (Fin 3) K} (hst : st ∈ Dt) (hord : orderOf (proj 3 K st) = 3 ^ b)
    (B : GL (Fin 3) K)
    (hrel : ∀ g ∈ Dt, (B : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K) =
      (g : Matrix (Fin 3) (Fin 3) K) * (B : Matrix (Fin 3) (Fin 3) K)) :
    LZ (B : Matrix (Fin 3) (Fin 3) K) ∧ ∃ μ : K, blk (B : Matrix (Fin 3) (Fin 3) K) = μ • 1 := by
  have hrel' : ∀ g ∈ Dt, (B : Matrix (Fin 3) (Fin 3) K) *
      (g : Matrix (Fin 3) (Fin 3) K).map (⇑(1 : K ≃+* K)) =
      (g : Matrix (Fin 3) (Fin 3) K) * (B : Matrix (Fin 3) (Fin 3) K) := by
    intro g hg; rw [map_one_ringEquiv]; exact hrel g hg
  have hLZ := LZ_of_rel Dt hDp hDQ hb1 hst hord B 1 hrel'
  refine ⟨hLZ, ?_⟩
  have hbr := blk_rel Dt hDQ B 1 hLZ hrel'
  simp only [map_one_ringEquiv2] at hbr
  by_contra hno
  push Not at hno
  obtain ⟨g, hg, h, hh, hne⟩ := exists_noncomm_blk Dt hDp hDQ hb1 hst hord
  exact hne (LinA.commute_of_commute_nonscalar _ _ _ hno (hbr g hg) (hbr h hh))

end Scalar

section Main

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem fieldAut_mul_conjAut (σ : K ≃+* K) (A : GL (Fin 3) K) :
    fieldAut 3 K σ * conjAut 3 K A =
      conjAut 3 K (GeneralLinearGroup.map (σ : K →+* K) A) * fieldAut 3 K σ := by
  have h := (standard_automorphism_transport (K := K) (n := 3)).2.2.1 σ A
  calc fieldAut 3 K σ * conjAut 3 K A
      = fieldAut 3 K σ * conjAut 3 K A * (fieldAut 3 K σ)⁻¹ * fieldAut 3 K σ := by group
    _ = _ := by rw [h]

theorem pow_conj_field (A : GL (Fin 3) K) (σ : K ≃+* K) (m : ℕ) :
    ∃ B : GL (Fin 3) K, (conjAut 3 K A * fieldAut 3 K σ) ^ m =
      conjAut 3 K B * fieldAut 3 K (σ ^ m) := by
  induction m with
  | zero => exact ⟨1, by simp⟩
  | succ m ih =>
    obtain ⟨B, hB⟩ := ih
    refine ⟨B * GeneralLinearGroup.map ((σ ^ m : K ≃+* K) : K →+* K) A, ?_⟩
    rw [pow_succ, hB, map_mul, map_pow]
    calc conjAut 3 K B * (fieldAut 3 K σ) ^ m * (conjAut 3 K A * fieldAut 3 K σ)
        = conjAut 3 K B * ((fieldAut 3 K σ) ^ m * conjAut 3 K A) * fieldAut 3 K σ := by group
      _ = _ := by
        rw [← map_pow, fieldAut_mul_conjAut, pow_succ, map_mul]
        group

theorem exists_conj_of_fixes (Dt : Subgroup (SpecialLinearGroup (Fin 3) K)) (hDp : ⁅Dt, Dt⁆ = Dt)
    (hDQ : Dt ≤ stabilizer (flagSpace 3 K 1)) {b : ℕ}
    (hb : b = padicValNat 3 (Nat.card K ^ 2 - 1)) (hb1 : 1 ≤ b)
    {st : SpecialLinearGroup (Fin 3) K} (hst : st ∈ Dt) (hord : orderOf (proj 3 K st) = 3 ^ b)
    (α : MulAut (projectiveSL 3 K)) (k : ℕ) (hαk : α ^ 3 ^ k = 1)
    (hJ : (projStabilizer (flagSpace 3 K 1)).map α.toMonoidHom = projStabilizer (flagSpace 3 K 1))
    (hfix : ∀ g ∈ Dt, α (proj 3 K g) = proj 3 K g) :
    ∃ B : GL (Fin 3) K, α = conjAut 3 K B := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨A, σ, ε, hε, hαeq⟩ := (automorphism_generation (K := K) (n := 3) le_rfl).2 α
  have hε0 : ε = 0 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hε with h | h
    · exact h
    · exfalso
      subst h
      rw [pow_one] at hαeq
      rw [hαeq] at hJ
      exact not_typeExchanging A σ hJ
  subst hε0
  rw [pow_zero, mul_one] at hαeq
  have hrel := rel_of_fixes Dt hDp A σ α hαeq hfix
  have hn3 := not_three_dvd_orderOf Dt hDp hDQ hb hb1 hst hord A σ hrel
  haveI : Finite (K ≃+* K) := Finite.of_injective (fun σ : K ≃+* K => (σ : K → K))
    DFunLike.coe_injective
  set m := orderOf σ with hm
  obtain ⟨B₁, hB₁⟩ := pow_conj_field A σ m
  rw [← hαeq, hm, pow_orderOf_eq_one, map_one, mul_one] at hB₁
  have hcop : Nat.Coprime m (3 ^ k) := by
    refine Nat.Coprime.pow_right _ ?_
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hn3 |>.symm
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · subst hk0
    refine ⟨1, ?_⟩
    simpa using hαk
  obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (by
    calc 1 < 3 := by norm_num
      _ = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk0)
  refine ⟨B₁ ^ u, ?_⟩
  rw [map_pow, ← hB₁, ← pow_mul]
  have : α ^ (m * u) = α := by
    have h1 : m * u = 3 ^ k * (m * u / 3 ^ k) + 1 := by
      have := Nat.div_add_mod (m * u) (3 ^ k)
      rw [hu] at this
      omega
    rw [h1, pow_add, pow_mul, hαk, one_pow, one_mul, pow_one]
  exact this.symm

theorem shape_facts (B : GL (Fin 3) K) (hLZ : LZ (B : Matrix (Fin 3) (Fin 3) K)) {μ : K}
    (hblk : blk (B : Matrix (Fin 3) (Fin 3) K) = μ • 1) :
    (B : Matrix (Fin 3) (Fin 3) K) 1 1 = μ ∧ (B : Matrix (Fin 3) (Fin 3) K) 2 2 = μ ∧
      (B : Matrix (Fin 3) (Fin 3) K) 1 2 = 0 ∧ (B : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 ∧
      (B : Matrix (Fin 3) (Fin 3) K) 0 0 ≠ 0 ∧ μ ≠ 0 := by
  have e00 := congrFun (congrFun hblk 0) 0
  have e01 := congrFun (congrFun hblk 0) 1
  have e10 := congrFun (congrFun hblk 1) 0
  have e11 := congrFun (congrFun hblk 1) 1
  simp [blk] at e00 e01 e10 e11
  have hdet := det_of_LZ hLZ
  rw [hblk] at hdet
  have hu : (B : Matrix (Fin 3) (Fin 3) K).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 B.isUnit).ne_zero
  refine ⟨e00, e11, e01, e10, ?_, ?_⟩
  · intro h0
    apply hu
    rw [hdet, h0, zero_mul]
  · intro h0
    apply hu
    rw [hdet, h0]
    simp [Matrix.det_fin_two]

theorem three_dvd_card_sq_sub_one : 3 ∣ Nat.card K ^ 2 - 1 := by
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨f, -, hf⟩ := FiniteField.card K 2
  rw [Nat.card_eq_fintype_card, hf, ← pow_mul, mul_comm, pow_mul]
  simpa using Nat.sub_dvd_pow_sub_pow 4 1 f

theorem conjAut_scalar (c : Kˣ) :
    conjAut 3 K (Matrix.GeneralLinearGroup.scalar (Fin 3) c) = 1 := by
  simp [conjAut, CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation_scalar]

theorem cyclic_of_fixing_perfect (D : Subgroup (projectiveSL 3 K)) (hDp : ⁅D, D⁆ = D)
    (hDP : D ≤ projStabilizer (flagSpace 3 K 1)) (s : projectiveSL 3 K) (hsD : s ∈ D)
    (hs : orderOf s = 3 ^ padicValNat 3 (Nat.card K ^ 2 - 1))
    (U : Subgroup (MulAut (projectiveSL 3 K))) (hU3 : IsPGroup 3 U)
    (hJ : ∀ α ∈ U, (projStabilizer (flagSpace 3 K 1)).map α.toMonoidHom =
      projStabilizer (flagSpace 3 K 1))
    (hD : ∀ α ∈ U, ∀ d ∈ D, α d = d) : IsCyclic U := by
  classical
  set b := padicValNat 3 (Nat.card K ^ 2 - 1) with hb
  have hb1 : 1 ≤ b := by
    rw [hb]
    exact one_le_padicValNat_of_dvd (by
      have : 1 < Nat.card K := Finite.one_lt_card
      have : 1 < Nat.card K ^ 2 := by nlinarith
      omega) three_dvd_card_sq_sub_one
  obtain ⟨Dt, hDtp, hDtmap, hDtQ⟩ := exists_lift_perfect D hDp hDP
  obtain ⟨st, hst, hstmap⟩ : ∃ st ∈ Dt, proj 3 K st = s := by
    rw [← hDtmap] at hsD
    obtain ⟨st, hst, h⟩ := hsD
    exact ⟨st, hst, h⟩
  have hord : orderOf (proj 3 K st) = 3 ^ b := by rw [hstmap]; exact hs
  have hfixD : ∀ α ∈ U, ∀ g ∈ Dt, α (proj 3 K g) = proj 3 K g := fun α hα g hg =>
    hD α hα _ (hDtmap ▸ ⟨g, hg, rfl⟩)
  have hconj : ∀ α ∈ U, ∃ B : GL (Fin 3) K, α = conjAut 3 K B := by
    intro α hα
    obtain ⟨k, hk⟩ := hU3 ⟨α, hα⟩
    have hk' : α ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact exists_conj_of_fixes Dt hDtp hDtQ hb hb1 hst hord α k hk' (hJ α hα) (hfixD α hα)
  let G : Subgroup (GL (Fin 3) K) := U.comap (conjAut 3 K)
  have hshape : ∀ B ∈ G, LZ (B : Matrix (Fin 3) (Fin 3) K) ∧
      ∃ μ : K, blk (B : Matrix (Fin 3) (Fin 3) K) = μ • 1 := by
    intro B hB
    have hfix := hfixD _ hB
    have hrel := rel_of_fixes Dt hDtp B 1 (conjAut 3 K B) (by simp) hfix
    have hrel' : ∀ g ∈ Dt, (B : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K) =
        (g : Matrix (Fin 3) (Fin 3) K) * (B : Matrix (Fin 3) (Fin 3) K) := by
      intro g hg
      have := hrel g hg
      rwa [map_one_ringEquiv] at this
    exact scalar_of_rel Dt hDtp hDtQ hb1 hst hord B hrel'
  have hfacts : ∀ B : G, (B.1 : Matrix (Fin 3) (Fin 3) K) 1 1 ≠ 0 ∧
      (B.1 : Matrix (Fin 3) (Fin 3) K) 0 0 ≠ 0 := fun B => by
    obtain ⟨hLZ, μ, hμ⟩ := hshape B.1 B.2
    obtain ⟨h11, -, -, -, h00, hμ0⟩ := shape_facts B.1 hLZ hμ
    exact ⟨by rw [h11]; exact hμ0, h00⟩
  let χ : G →* Kˣ := MonoidHom.mk'
    (fun B => Units.mk0 ((B.1 : Matrix (Fin 3) (Fin 3) K) 0 0 / (B.1 : Matrix (Fin 3) (Fin 3) K) 1 1)
      (div_ne_zero (hfacts B).2 (hfacts B).1))
    (fun B C => by
      obtain ⟨hLZB, μB, hμB⟩ := hshape B.1 B.2
      obtain ⟨hLZC, μC, hμC⟩ := hshape C.1 C.2
      obtain ⟨hB11, hB22, hB12, hB21, hB00, hμB0⟩ := shape_facts B.1 hLZB hμB
      obtain ⟨hC11, hC22, hC12, hC21, hC00, hμC0⟩ := shape_facts C.1 hLZC hμC
      obtain ⟨hB10, hB20⟩ := hLZB
      obtain ⟨hC10, hC20⟩ := hLZC
      apply Units.ext
      simp only [Units.val_mul, Units.val_mk0, Subgroup.coe_mul, Units.val_mul,
        Matrix.mul_apply, Fin.sum_univ_three, hB10, hB20, hB12, hB21, hC10, hC20, hC12, hC21]
      simp only [mul_zero, zero_mul, add_zero, zero_add]
      rw [div_mul_div_comm])
  have hχval : ∀ B : G, ((χ B : Kˣ) : K) =
      (B.1 : Matrix (Fin 3) (Fin 3) K) 0 0 / (B.1 : Matrix (Fin 3) (Fin 3) K) 1 1 := fun B => rfl
  let c : G →* U := (conjAut 3 K).subgroupComap U
  have hcsurj : Function.Surjective c := by
    intro α
    obtain ⟨B, hB⟩ := hconj α.1 α.2
    have hBG : B ∈ G := by
      show conjAut 3 K B ∈ U
      rw [← hB]; exact α.2
    exact ⟨⟨B, hBG⟩, Subtype.ext hB.symm⟩
  have hcval : ∀ B : G, ((c B : U) : MulAut (projectiveSL 3 K)) = conjAut 3 K B.1 := fun B => rfl
  have hker : χ.ker ≤ c.ker := by
    intro B hB
    rw [MonoidHom.mem_ker] at hB ⊢
    have h1 : ((χ B : Kˣ) : K) = 1 := by rw [hB]; rfl
    rw [hχval] at h1
    obtain ⟨hLZ, μ, hμ⟩ := hshape B.1 B.2
    obtain ⟨h11, h22, h12, h21, h00, hμ0⟩ := shape_facts B.1 hLZ hμ
    obtain ⟨h10, h20⟩ := hLZ
    have h11' : (B.1 : Matrix (Fin 3) (Fin 3) K) 1 1 ≠ 0 := by rw [h11]; exact hμ0
    have heq : (B.1 : Matrix (Fin 3) (Fin 3) K) 0 0 = (B.1 : Matrix (Fin 3) (Fin 3) K) 1 1 :=
      (div_eq_one_iff_eq h11').1 h1
    have h2' : (2 : K) = 0 := CharP.cast_eq_zero K 2
    have hBB : (B.1 * B.1 : GL (Fin 3) K) = Matrix.GeneralLinearGroup.scalar (Fin 3)
        (Units.mk0 (((B.1 : Matrix (Fin 3) (Fin 3) K) 0 0) ^ 2) (pow_ne_zero 2 h00)) := by
      apply Units.ext
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_three, h10, h20, h12, h21, h22, ← h11, ← heq, sq] <;>
        (try linear_combination (B.1 : Matrix (Fin 3) (Fin 3) K) 0 0 *
          (B.1 : Matrix (Fin 3) (Fin 3) K) 0 1 * h2') <;>
        (try linear_combination (B.1 : Matrix (Fin 3) (Fin 3) K) 0 0 *
          (B.1 : Matrix (Fin 3) (Fin 3) K) 0 2 * h2')
    have hsq : (conjAut 3 K B.1) ^ 2 = 1 := by
      rw [sq, ← map_mul, hBB, conjAut_scalar]
    have hα2 : ((c B : U)) ^ 2 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, hcval]; exact hsq)
    obtain ⟨k, hk⟩ := hU3 (c B)
    have hdvd2 : orderOf (c B) ∣ 2 := orderOf_dvd_of_pow_eq_one hα2
    have hdvd3 : orderOf (c B) ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
    have hcop : Nat.Coprime 2 (3 ^ k) := Nat.Coprime.pow_right _ (by norm_num)
    have : orderOf (c B) ∣ 1 := by
      have := Nat.dvd_gcd hdvd2 hdvd3
      rwa [hcop] at this
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 this)
  haveI : IsCyclic (χ.range) := inferInstance
  have hsurjχ : Function.Surjective χ.rangeRestrict := χ.rangeRestrict_surjective
  let ψ : χ.range →* U := MonoidHom.liftOfRightInverse χ.rangeRestrict
    (Function.surjInv hsurjχ) (Function.rightInverse_surjInv hsurjχ) ⟨c, by
      intro B hB
      apply hker
      rw [MonoidHom.mem_ker] at hB ⊢
      have : (χ.rangeRestrict B : χ.range) = 1 := hB
      simpa using congrArg Subtype.val this⟩
  have hψ : Function.Surjective ψ := by
    intro α
    obtain ⟨B, rfl⟩ := hcsurj α
    refine ⟨χ.rangeRestrict B, ?_⟩
    show (MonoidHom.liftOfRightInverse χ.rangeRestrict (Function.surjInv hsurjχ)
      (Function.rightInverse_surjInv hsurjχ) _) (χ.rangeRestrict B) = c B
    rw [MonoidHom.liftOfRightInverse_comp_apply]
  exact isCyclic_of_surjective ψ hψ

end Main

end CFSG.HardMathSupport.Curtis.UnitaryLevi.LinA
