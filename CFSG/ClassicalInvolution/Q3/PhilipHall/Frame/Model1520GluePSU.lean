module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520GlueSUFix
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520Orth
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520GlueCover
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520Core
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520GlueSUAut

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520U

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterU4
  CFSG.LieType.Steinberg CFSG.ClassicalGroups.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Universal.Unitary CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520Aux
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem sl2_unitri_cube {F : Type} [Field F] (h3 : (3 : F) = 0) (c : F) :
    sl2Upper c ^ 3 = 1 ∧ sl2Lower c ^ 3 = 1 := by
  constructor
  · apply Subtype.ext
    rw [pow_three, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_one]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Sp.coe_sl2Upper, Matrix.mul_apply, Fin.sum_univ_two] <;> linear_combination c * h3
  · apply Subtype.ext
    rw [pow_three, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_one]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Sp.coe_sl2Lower, Matrix.mul_apply, Fin.sum_univ_two] <;> linear_combination c * h3

theorem su2_mem_closure_cube (hK : Nat.card K = (p ^ f) ^ 2) (h3 : p ^ f = 3) (A : Su K p f 2) :
    A ∈ Subgroup.closure {B : Su K p f 2 | B ^ 3 = 1} := by
  obtain ⟨e⟩ := nonempty_sl2_mulEquiv_su_two hK
  have hc : Nat.card (fixedSubfield K p f) = 3 := by
    rw [card_fixedSubfield hK, h3]
  have h30 : (3 : fixedSubfield K p f) = 0 := three_eq_zero_of_card_eq_three hc
  obtain ⟨y, rfl⟩ := e.surjective A
  have hle : Subgroup.closure (Set.range (sl2Upper (k := fixedSubfield K p f)) ∪
      Set.range sl2Lower) ≤ (Subgroup.closure {B : Su K p f 2 | B ^ 3 = 1}).comap e.toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro x (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact Subgroup.subset_closure (by
        show (e (sl2Upper c)) ^ 3 = 1
        rw [← map_pow, (sl2_unitri_cube h30 c).1, map_one])
    · exact Subgroup.subset_closure (by
        show (e (sl2Lower c)) ^ 3 = 1
        rw [← map_pow, (sl2_unitri_cube h30 c).2, map_one])
  exact hle (Sp.mem_closure_sl2 y)

theorem su4_rigid3 (hK : Nat.card K = (p ^ f) ^ 2) (h3 : p ^ f = 3) (hp2 : p ≠ 2) {X : Type}
    [Group X] (θ : Su K p f 4 →* X) (hθ : Function.Surjective θ)
    (hker : θ.ker ≤ Subgroup.center (Su K p f 4)) (σ : MulAut X) (hσ : ∃ k : ℕ, σ ^ (3 ^ k) = 1)
    (hfix0 : ∀ A : Su K p f 2, A ^ 3 = 1 →
      σ (θ (blockEmb K p f 4 2 0 (by norm_num) A)) = θ (blockEmb K p f 4 2 0 (by norm_num) A))
    (hfix2 : ∀ A : Su K p f 2, A ^ 3 = 1 →
      σ (θ (blockEmb K p f 4 2 2 (by norm_num) A)) = θ (blockEmb K p f 4 2 2 (by norm_num) A)) :
    σ = 1 := by
  obtain ⟨k, hk⟩ := hσ
  obtain ⟨α, g, φ, hlift, hmat, -, -⟩ :=
    unitaryAutClassification_isometry_of_card_three hK hp2 h3 (d := 4) (by norm_num) X θ hθ hker σ
  have hσU : IsUnitaryInvolution (unitaryInvolution K p f) :=
    isUnitaryInvolution_unitaryInvolution hK
  have hexact : ∀ b : Su K p f 4, b ^ 3 = 1 → σ (θ b) = θ b → α b = b := by
    intro b hb hσb
    have hz0 : α b * b⁻¹ ∈ Subgroup.center (Su K p f 4) :=
      hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, hlift, hσb, mul_inv_cancel])
    obtain ⟨z, hzdef⟩ : ∃ z, z = α b * b⁻¹ := ⟨_, rfl⟩
    have hz : z ∈ Subgroup.center (Su K p f 4) := by rw [hzdef]; exact hz0
    have hαb : α b = z * b := by rw [hzdef]; group
    have hcomm : Commute z b := (Subgroup.mem_center_iff.mp hz b).symm
    have hz3 : z ^ 3 = 1 := by
      have h1 : (α b) ^ 3 = 1 := by rw [← map_pow, hb, map_one]
      rw [hαb, hcomm.mul_pow, hb, mul_one] at h1
      exact h1
    obtain ⟨c, hc⟩ := exists_scalar_of_mem_center hσU (by norm_num : 3 ≤ 4) hz
    have hzM : suMat z = Matrix.scalar (Fin 4) (c : K) := hc
    have hdet := det_suMat z
    rw [hzM] at hdet
    have hz3M : suMat (z ^ 3) = (Matrix.scalar (Fin 4) (c : K)) ^ 3 := by
      rw [pow_three, suMat_mul, suMat_mul, hzM, pow_three]
    rw [hz3, suMat_one, ← map_pow] at hz3M
    have hc3 : (c : K) ^ 3 = 1 := by
      have := congrFun (congrFun hz3M 0) 0
      simpa using this.symm
    have hc4 : (c : K) ^ 4 = 1 := by
      simpa [Matrix.scalar_apply, Matrix.det_diagonal] using hdet
    have hc1 : (c : K) = 1 := by
      calc (c : K) = (c : K) ^ 4 / (c : K) ^ 3 := by
            field_simp [c.ne_zero]
        _ = 1 := by rw [hc4, hc3]; norm_num
    have hz1 : z = 1 := by
      apply suMat_injective
      rw [hzM, hc1, suMat_one]
      simp
    rw [hαb, hz1, one_mul]
  have hblock : ∀ (i : ℕ) (hi : i + 2 ≤ 4), (∀ A : Su K p f 2, A ^ 3 = 1 →
      σ (θ (blockEmb K p f 4 2 i hi A)) = θ (blockEmb K p f 4 2 i hi A)) →
      ∀ A : Su K p f 2, α (blockEmb K p f 4 2 i hi A) = blockEmb K p f 4 2 i hi A := by
    intro i hi hfix A
    have hle : Subgroup.closure {B : Su K p f 2 | B ^ 3 = 1} ≤
        MonoidHom.eqLocus (α.comp (blockEmb K p f 4 2 i hi)) (blockEmb K p f 4 2 i hi) := by
      rw [Subgroup.closure_le]
      intro B hB
      exact hexact _ (by rw [← map_pow, hB, map_one]) (hfix B hB)
    exact hle (su2_mem_closure_cube hK h3 A)
  have hα2 : ∀ x, α (α x) = x := by
    refine su4_fixing_odd hK h3 hp2 α g φ (fun x => hmat x) (hblock 0 (by norm_num) hfix0)
      (hblock 2 (by norm_num) hfix2) (m := 3 ^ k) (Odd.pow (by decide)) ?_
    intro x
    apply hker
    have hit : ∀ n x, θ ((⇑α)^[n] x) = (σ ^ n) (θ x) := by
      intro n
      induction n with
      | zero => intro x; simp
      | succ n ih =>
        intro x
        rw [Function.iterate_succ_apply', hlift, ih, pow_succ', MulAut.mul_apply]
    have hmul : (⇑(α.comp α))^[3 ^ k] = (⇑α)^[2 * 3 ^ k] := by
      rw [Function.iterate_mul]
      rfl
    rw [MonoidHom.mem_ker, map_mul, map_inv, hmul, hit, pow_mul', hk, one_pow]
    simp
  have hσσ : σ * σ = 1 := by
    ext y
    obtain ⟨x, rfl⟩ := hθ y
    have := congrArg θ (hα2 x)
    rw [hlift, hlift] at this
    simpa using this
  have h2 : orderOf σ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hσσ)
  have h3' : orderOf σ ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hg := Nat.dvd_gcd h2 h3'
  rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right k (by norm_num))] at hg
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hg)

theorem blockEmb_comm_rootInv (i : ℕ) (hi : i = 0 ∨ i = 2) (hi4 : i + 2 ≤ 4) (A : Su K p f 2) :
    blockEmb K p f 4 2 i hi4 A * rootInvSU K p f (show 2 ≤ 4 by norm_num) =
      rootInvSU K p f (show 2 ≤ 4 by norm_num) * blockEmb K p f 4 2 i hi4 A := by
  apply suMat_injective
  rw [suMat_mul, suMat_mul, suMat_rootInvSU_four]
  rcases hi with rfl | rfl
  · rw [suMat_blockEmb_zero]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_four]
  · rw [suMat_blockEmb_two]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

theorem model1520_su4_std (hK : Nat.card K = (p ^ f) ^ 2) (h3 : p ^ f = 3) (hp2 : p ≠ 2)
    {G : Type} [Group G] [Finite G] {X : Subgroup G} (ψ : Su K p f 4 →* ↥X)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center (Su K p f 4)) :
    Model1520 X ((ψ (rootInvSU K p f (show 2 ≤ 4 by norm_num)) : ↥X) : G) := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · simp at h3
    · exact hf
  have hUF : UnitaryFieldData p f K := ⟨Fact.out, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hperf : Group.IsPerfect (Su K p f 4) := by
    obtain ⟨hp, -⟩ := isPerfect_and_center_unitarySU_three hUF h3 (d := 4) (by norm_num)
    exact Group.IsPerfect.ofSurjective (f := (suEquivUnitarySU K p f hK 4).symm.toMonoidHom)
      (suEquivUnitarySU K p f hK 4).symm.surjective
  let t0 := rootInvSU K p f (show 2 ≤ 4 by norm_num)
  have ht2 : ((ψ t0 : ↥X) : G) * ((ψ t0 : ↥X) : G) = 1 := by
    rw [← Subgroup.coe_mul, ← map_mul, rootInvSU_mul_self_four, map_one, Subgroup.coe_one]
  let θ : Su K p f 4 →* ↥X ⧸ Subgroup.center ↥X := (QuotientGroup.mk' _).comp ψ
  have hθ : Function.Surjective θ := fun y => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨k, rfl⟩ := hψ x
    exact ⟨k, rfl⟩
  have hθker : θ.ker ≤ Subgroup.center (Su K p f 4) := by
    intro k hk
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hk
    refine mem_center_of_commutators_central hperf fun y => hker ?_
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv]
    have := Subgroup.mem_center_iff.mp hk (ψ y)
    calc ψ k * ψ y * (ψ k)⁻¹ * (ψ y)⁻¹ = (ψ y * ψ k) * (ψ k)⁻¹ * (ψ y)⁻¹ := by rw [this]
      _ = 1 := by group
  refine model1520_of_rigid3 (ψ t0).2 ht2 (P := ↥X ⧸ Subgroup.center ↥X) ?_ (MulEquiv.refl _)
    (τ := QuotientGroup.mk (ψ t0)) rfl ?_
  ·
    have := hperf
    exact Group.IsPerfect.ofSurjective hθ
  · refine ⟨{s | ∃ (i : ℕ) (hi : i = 0 ∨ i = 2) (hi4 : i + 2 ≤ 4) (A : Su K p f 2), A ^ 3 = 1 ∧
      s = θ (blockEmb K p f 4 2 i hi4 A)}, ?_, ?_⟩
    · rintro _ ⟨i, hi, hi4, A, hA, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [← map_pow, ← map_pow, hA, map_one, map_one]
      · show θ _ * θ t0 = θ t0 * θ _
        rw [← map_mul, ← map_mul, blockEmb_comm_rootInv i hi hi4 A]
    · intro σ hσ hfix
      exact su4_rigid3 hK h3 hp2 θ hθ hθker σ hσ
        (fun A hA => hfix _ ⟨0, Or.inl rfl, by norm_num, A, hA, rfl⟩)
        (fun A hA => hfix _ ⟨2, Or.inr rfl, by norm_num, A, hA, rfl⟩)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520U
