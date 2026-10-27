module

public import CFSG.RankThree.SteinbergR3ELinearThreePlaneCore
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycGroup

public section

namespace CFSG.AGLEmbedding.BlockCyc

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.LinearThreePlane CFSG.RankThree.PartOne.OutStructure

section L3E9

variable {K : Type} [Field K] {ω : K}

@[expose] def diagA (ω : K) : Matrix (Fin 3) (Fin 3) K := Matrix.diagonal ![1, ω, ω ^ 2]

@[expose] def permB : Matrix (Fin 3) (Fin 3) K := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

theorem det_diagA (hω : ω ^ 3 = 1) : (diagA ω).det = 1 := by
  simp only [diagA, Matrix.det_diagonal, Fin.prod_univ_three]
  simp
  rw [← pow_succ']
  exact hω

theorem det_permB : (permB : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  simp [permB, Matrix.det_fin_three]

theorem ne_zero_of_pow_three (hω : ω ^ 3 = 1) : ω ≠ 0 := by
  rintro rfl
  norm_num at hω

@[expose] def slA (hω : ω ^ 3 = 1) : SpecialLinearGroup (Fin 3) K := ⟨diagA ω, det_diagA hω⟩

@[expose] def slB : SpecialLinearGroup (Fin 3) K := ⟨permB, det_permB⟩

theorem coe_slA (hω : ω ^ 3 = 1) : ((slA hω : SpecialLinearGroup (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) K) = diagA ω := rfl

theorem coe_slB : ((slB : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = permB :=
  rfl

theorem slA_pow_three (hω : ω ^ 3 = 1) : (slA hω : SpecialLinearGroup (Fin 3) K) ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_slA, diagA, Matrix.diagonal_pow,
    Matrix.SpecialLinearGroup.coe_one, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i
  · simp
  · simpa using hω
  · simp
    rw [← pow_mul, mul_comm, pow_mul, hω, one_pow]

@[expose] def omegaSq (hω : ω ^ 3 = 1) : Kˣ :=
  Units.mk0 (ω ^ 2) (pow_ne_zero 2 (ne_zero_of_pow_three hω))

theorem omegaSq_pow (hω : ω ^ 3 = 1) : omegaSq hω ^ 3 = 1 := by
  apply Units.ext
  simp only [omegaSq, Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
  rw [← pow_mul, mul_comm, pow_mul, hω, one_pow]

theorem slB_pow_three : (slB : SpecialLinearGroup (Fin 3) K) ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_slB, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, permB, Matrix.mul_apply, Fin.sum_univ_three]

theorem slB_mul_slA (hω : ω ^ 3 = 1) :
    (slB : SpecialLinearGroup (Fin 3) K) * slA hω =
      scalarElement (n := 3) (omegaSq hω) (omegaSq_pow hω) * (slA hω * slB) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, coe_slA, coe_slB, coe_scalarElement]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [omegaSq, diagA, permB, Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
  · linear_combination (-1 : K) * hω
  · linear_combination (-ω) * hω

theorem eq_zero_of_mem_scalars (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) {s t : ℕ} (hs : s < 3)
    (ht : t < 3)
    (h : (slA hω : SpecialLinearGroup (Fin 3) K) ^ s * (slB : SpecialLinearGroup (Fin 3) K) ^ t ∈
      scalars 3 K) : s = 0 ∧ t = 0 := by
  obtain ⟨c, -, hm⟩ := h
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_pow,
    Matrix.SpecialLinearGroup.coe_pow, coe_slA, coe_slB] at hm
  have h00 := congrFun (congrFun hm 0) 0
  have h11 := congrFun (congrFun hm 1) 1
  interval_cases s <;> interval_cases t
  · exact ⟨rfl, rfl⟩
  all_goals
    exfalso
    simp [diagA, permB, pow_succ, Matrix.mul_apply, Fin.sum_univ_three, Matrix.scalar_apply,
      Matrix.diagonal_apply] at h00 h11
    first
      | exact c.ne_zero h00.symm
      | exact hω1 (h11.trans h00.symm)
      | exact hω1 (by linear_combination hω - ω * (h11.trans h00.symm))

theorem hasE9_projectiveSL_three (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) : HasE9 (projectiveSL 3 K) := by
  refine hasE9_of_two_elements (e₁ := proj 3 K (slA hω)) (e₂ := proj 3 K slB) ?_ ?_ ?_ ?_
  · have h1 : proj 3 K (slB * slA hω) = proj 3 K (slA hω * slB) := by
      rw [slB_mul_slA hω, map_mul, proj_eq_one_iff.2 (scalarElement_mem_scalars _ _), one_mul]
    show proj 3 K (slA hω) * proj 3 K slB = proj 3 K slB * proj 3 K (slA hω)
    rw [← map_mul, ← map_mul, h1]
  · rw [← map_pow, slA_pow_three, map_one]
  · rw [← map_pow, slB_pow_three, map_one]
  · intro s t hs ht h
    rw [← map_pow, ← map_pow, ← map_mul, proj_eq_one_iff] at h
    exact eq_zero_of_mem_scalars hω hω1 hs ht h

end L3E9


section L3Aut

theorem four_pow_mod_five (k : ℕ) : 4 ^ k % 5 = 1 ∨ 4 ^ k % 5 = 4 := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    omega

variable {K : Type} [Field K] [Finite K]

theorem not_five_dvd_card_SL_three {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : Odd f) :
    ¬ 5 ∣ Nat.card (SpecialLinearGroup (Fin 3) K) := by
  rw [card_SL_eq (by norm_num), hK]
  obtain ⟨k, rfl⟩ := hf
  have hq : (2 ^ (2 * k + 1)) % 5 = 2 ∨ (2 ^ (2 * k + 1)) % 5 = 3 := by
    have h4 : (2 ^ (2 * k + 1)) = 2 * 4 ^ k := by
      rw [pow_succ, pow_mul]; norm_num; ring
    rw [h4]
    have := four_pow_mod_five k
    omega
  set q := 2 ^ (2 * k + 1) with hqdef
  have hq1 : 1 ≤ q := Nat.one_le_two_pow
  have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq1
  have hq3 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ hq1
  have h2 : q ^ 2 % 5 = 4 := by
    rw [Nat.pow_mod]; rcases hq with h | h <;> rw [h]
  have h3 : q ^ 3 % 5 = 3 ∨ q ^ 3 % 5 = 2 := by
    rw [Nat.pow_mod]; rcases hq with h | h <;> rw [h] <;> simp
  intro hdvd
  have hprod : ∏ j ∈ Finset.Icc 2 3, (q ^ j - 1) = (q ^ 2 - 1) * (q ^ 3 - 1) := by
    rw [show Finset.Icc 2 3 = {2, 3} from rfl, Finset.prod_pair (by norm_num)]
  rw [hprod] at hdvd
  have hp : (5 : ℕ).Prime := by norm_num
  have hq5 : ¬ 5 ∣ q := by
    intro h
    have := hp.dvd_of_dvd_pow (show 5 ∣ 2 ^ (2 * k + 1) from h)
    omega
  rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h
  · exact hq5 (hp.dvd_of_dvd_pow h)
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · omega
    · omega

omit [Field K] [Finite K] in
theorem isCyclic_quotient_of_gen {A : Type*} [Group A] {D E : Subgroup A}
    [(D.subgroupOf E).Normal] (hE : ∃ g ∈ E, ∀ x ∈ E, ∃ k : ℤ, g ^ k * x ∈ D) :
    IsCyclic (↥E ⧸ D.subgroupOf E) := by
  obtain ⟨g, hgE, hg⟩ := hE
  set ρ : ↥E →* ↥E ⧸ D.subgroupOf E := QuotientGroup.mk' _ with hρ
  refine ⟨ρ ⟨g, hgE⟩, fun q => ?_⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨k, hk⟩ := hg x.1 x.2
  refine ⟨-k, ?_⟩
  change (ρ ⟨g, hgE⟩) ^ (-k) = ρ x
  rw [← map_zpow]
  refine (QuotientGroup.eq).2 ?_
  rw [Subgroup.mem_subgroupOf]
  simpa [mul_assoc] using hk

theorem aut5Le_projectiveSL_three (h5 : ¬ 5 ∣ Nat.card (projectiveSL 3 K)) :
    Aut5Le (projectiveSL 3 K) := by
  intro W hW
  have hWpow : ∀ x ∈ W, x ^ 5 = 1 := hW.2
  obtain ⟨hgenTop, -⟩ := automorphism_generation (K := K) (n := 3) le_rfl
  obtain ⟨-, -, hDn, -, -, hE, -, hidx, -, -⟩ := standard_outer_quotients (n := 3) (K := K)
  set D := linearAutGroup 3 K with hD
  set E := semilinearAutGroup 3 K with hE'
  have hDnorm : D.Normal := by
    refine ⟨fun d hd γ => ?_⟩
    have hγ : γ ∈ standardAutGroup 3 K := hgenTop ▸ Subgroup.mem_top γ
    have hd' : d ∈ standardAutGroup 3 K := hgenTop ▸ Subgroup.mem_top d
    have := hDn.conj_mem ⟨d, hd'⟩ (Subgroup.mem_subgroupOf.mpr hd) ⟨γ, hγ⟩
    exact Subgroup.mem_subgroupOf.mp this
  have hidx' : E.index ≤ 2 := by
    have h2 : E.relIndex (standardAutGroup 3 K) ≤ 2 := hidx
    rwa [hgenTop, Subgroup.relIndex_top_right] at h2
  have hWE : W ≤ E := fun x hx =>
    mem_of_pow_mem_of_index_le_two E hidx' (N := 5) (by decide)
      (by rw [hWpow x hx]; exact one_mem _)
  have : (D.subgroupOf E).Normal := Subgroup.Normal.subgroupOf hDnorm E
  have : IsCyclic (↥E ⧸ D.subgroupOf E) := isCyclic_quotient_of_gen (D := D) (E := E) hE
  have hcard := card_le_mul_card_inf_of_cyclic_quotient (p := 5) (D := D) (by norm_num) hWE hWpow
  have hbot : W ⊓ D = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hinner := mem_inner_of_mem_linearAutGroup (p := 5) (by norm_num) hx.2 (hWpow x hx.1)
    have h1 : orderOf x ∣ 5 := orderOf_dvd_of_pow_eq_one (hWpow x hx.1)
    have h2 : orderOf x ∣ Nat.card (projectiveSL 3 K) :=
      (Subgroup.orderOf_dvd_natCard _ hinner).trans (Subgroup.card_range_dvd _)
    have h5' : Nat.Coprime 5 (Nat.card (projectiveSL 3 K)) := (Nat.Prime.coprime_iff_not_dvd
      (by norm_num)).2 h5
    have h3 : orderOf x ∣ 1 := h5'.gcd_eq_one ▸ Nat.dvd_gcd h1 h2
    exact Subgroup.mem_bot.2 (orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3))
  rw [hbot, Subgroup.card_bot] at hcard
  omega

end L3Aut


end CFSG.AGLEmbedding.BlockCyc
