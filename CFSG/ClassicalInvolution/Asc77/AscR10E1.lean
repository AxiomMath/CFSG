module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ClassicalInvolution.Phan.Defs
public import CFSG.LieType.Steinberg.CentralExt.UnitaryThreeLift
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.CentralSL2Semilinear

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.LieType.Universal CFSG.ClassicalInvolution.Phan
open scoped MatrixGroups commutatorElement

section Basic

theorem eq_three_of_pow_eq_three {p e : ℕ} [Fact p.Prime] (h3 : p ^ e = 3) : p = 3 ∧ e = 1 := by
  have he : e ≠ 0 := by
    rintro rfl
    simp at h3
  have hp : p ∣ 3 := h3 ▸ dvd_pow_self p he
  have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_three).1 hp
  subst hp3
  exact ⟨rfl, Nat.pow_right_injective (by norm_num : 2 ≤ 3) (h3.trans (pow_one 3).symm)⟩

theorem ne_two_of_pow_eq_three {p e : ℕ} [Fact p.Prime] (h3 : p ^ e = 3) : p ≠ 2 := by
  rw [(eq_three_of_pow_eq_three h3).1]
  norm_num

theorem neZero_of_pow_eq_three {p e : ℕ} (h3 : p ^ e = 3) : NeZero e :=
  ⟨by
    rintro rfl
    simp at h3⟩

end Basic

section GenSq

variable {K G : Type*} [Group K] [Group G]

@[expose] def GenSq (P : Subgroup K) : Prop :=
  P ≤ Subgroup.closure {x | ∃ a ∈ P, x = a * a}

theorem GenSq.map {P : Subgroup K} (h : GenSq P) (f : K →* G) : GenSq (P.map f) := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := hy
  have h1 := Subgroup.mem_map_of_mem f (h hx)
  rw [MonoidHom.map_closure] at h1
  refine Subgroup.closure_mono ?_ h1
  rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
  exact ⟨f a, Subgroup.mem_map_of_mem f ha, by simp⟩

theorem genSq_of_pow_three {P : Subgroup K} {S : Set K} (hS : S ⊆ P) (h3 : ∀ s ∈ S, s ^ 3 = 1)
    (hP : P ≤ Subgroup.closure S) : GenSq P := by
  refine hP.trans (Subgroup.closure_mono fun s hs => ⟨s * s, P.mul_mem (hS hs) (hS hs), ?_⟩)
  have := h3 s hs
  calc s = s ^ 3 * s := by rw [this, one_mul]
    _ = s * s * (s * s) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]

theorem genSq_top_sl2 {F : Type} [Field F] [CharP F 3] : GenSq (⊤ : Subgroup SL(2, F)) := by
  have h3 : (3 : F) = 0 := by
    have := CharP.cast_eq_zero F 3
    simpa using this
  refine genSq_of_pow_three (S := Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Upper F) ∪
    Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Lower F)) (fun _ _ => trivial) ?_
    (CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower (K := F) ▸ le_rfl)
  rintro s (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · rw [pow_succ, pow_two, ← CFSG.LocalAnalysis.ComponentInitial.sl2Upper_add,
      ← CFSG.LocalAnalysis.ComponentInitial.sl2Upper_add]
    have : c + c + c = 0 := by linear_combination c * h3
    rw [this, CFSG.LocalAnalysis.ComponentInitial.sl2Upper_zero]
  · rw [pow_succ, pow_two, ← CFSG.LocalAnalysis.ComponentInitial.sl2Lower_add,
      ← CFSG.LocalAnalysis.ComponentInitial.sl2Lower_add]
    have : c + c + c = 0 := by linear_combination c * h3
    rw [this, CFSG.LocalAnalysis.ComponentInitial.sl2Lower_zero]

theorem genSq_of_equiv_sl2 {F : Type} [Field F] [CharP F 3] {R : Subgroup K}
    (e : R ≃* SL(2, F)) : GenSq R := by
  have h1 : GenSq (⊤ : Subgroup ↥R) := by
    have := (genSq_top_sl2 (F := F)).map e.symm.toMonoidHom
    rwa [← MonoidHom.range_eq_map, MonoidHom.range_eq_top.2 e.symm.surjective] at this
  have h2 := h1.map R.subtype
  rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h2

theorem eq_of_map_eq_of_genSq (ψ : K →* G) (hker : ψ.ker ≤ Subgroup.center K)
    (hk2 : ∀ x ∈ ψ.ker, x * x = 1) {R R' : Subgroup K} (hR : GenSq R) (hR' : GenSq R')
    (h : R.map ψ = R'.map ψ) : R = R' := by
  have key : ∀ {A B : Subgroup K}, GenSq A → A.map ψ ≤ B.map ψ → A ≤ B := by
    intro A B hA hAB x hx
    refine ((Subgroup.closure_le _).2 ?_) (hA hx)
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨b, hb, hab⟩ := hAB (Subgroup.mem_map_of_mem ψ ha)
    have hk : b⁻¹ * a ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hab]
      group
    obtain ⟨k, hkd⟩ : ∃ k, k = b⁻¹ * a := ⟨_, rfl⟩
    rw [← hkd] at hk
    have hc := Subgroup.mem_center_iff.1 (hker hk)
    have h2 := hk2 k hk
    have hak : a = b * k := by
      rw [hkd]
      group
    have hbb : a * a = b * b := by
      calc a * a = b * k * (b * k) := by rw [← hak]
        _ = b * (k * b) * k := by simp only [mul_assoc]
        _ = b * (b * k) * k := by rw [← hc b]
        _ = b * b * (k * k) := by simp only [mul_assoc]
        _ = b * b := by rw [h2, mul_one]
    rw [hbb]
    exact B.mul_mem hb hb
  exact le_antisymm (key hR h.le) (key hR' h.ge)

theorem commute_of_map_commute_of_genSq (ψ : K →* G) (hker : ψ.ker ≤ Subgroup.center K)
    (hk2 : ∀ x ∈ ψ.ker, x * x = 1) {R : Subgroup K} (hR : GenSq R) {b : K}
    (h : ∀ a ∈ R, ψ a * ψ b = ψ b * ψ a) : ∀ a ∈ R, a * b = b * a := by
  have hle : R ≤ Subgroup.centralizer ({b} : Set K) := by
    refine fun x hx => ((Subgroup.closure_le _).2 ?_) (hR hx)
    rintro _ ⟨a, ha, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    have hk : a * b * a⁻¹ * b⁻¹ ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, h a ha]
      group
    obtain ⟨k, hkd⟩ : ∃ k, k = a * b * a⁻¹ * b⁻¹ := ⟨_, rfl⟩
    rw [← hkd] at hk
    have hc := Subgroup.mem_center_iff.1 (hker hk)
    have h2 := hk2 k hk
    have e1 : a * b = k * (b * a) := by
      rw [hkd]
      group
    calc a * a * b = a * (a * b) := mul_assoc a a b
      _ = a * (k * (b * a)) := by rw [e1]
      _ = k * (a * (b * a)) := by rw [← mul_assoc a k, hc a, mul_assoc k a]
      _ = k * ((a * b) * a) := by rw [mul_assoc a b a]
      _ = k * (k * (b * a) * a) := by rw [e1]
      _ = (k * k) * (b * a * a) := by simp only [mul_assoc]
      _ = b * a * a := by rw [h2, one_mul]
      _ = b * (a * a) := mul_assoc b a a
  intro a ha
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle ha)

end GenSq

section NegOne

theorem neg_one_commutator_sl2_three {F : Type} [Field F] [Finite F] (hF : Nat.card F = 3) :
    ∃ A B : SL(2, F), ⁅A, B⁆ = (-1 : SL(2, F)) := by
  have h3 : (3 : F) = 0 := by
    have h : Nat.card F • (1 : F) = 0 := card_nsmul_eq_zero'
    rw [hF] at h
    simpa using h
  obtain ⟨A, hA⟩ : ∃ A : SL(2, F), (A : Matrix (Fin 2) (Fin 2) F) = !![0, -1; 1, 0] :=
    ⟨⟨_, by simp [Matrix.det_fin_two]⟩, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : SL(2, F), (B : Matrix (Fin 2) (Fin 2) F) = !![1, 1; 1, -1] :=
    ⟨⟨_, by simp [Matrix.det_fin_two]; linear_combination (-1 : F) * h3⟩, rfl⟩
  have hAi : ((A⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; -1, 0] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, hA, Matrix.adjugate_fin_two]
    simp
  have hBi : ((B⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![-1, -1; -1, 1] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, hB, Matrix.adjugate_fin_two]
    simp
  refine ⟨A, B, ?_⟩
  apply Subtype.ext
  rw [commutatorElement_def]
  simp only [Matrix.SpecialLinearGroup.coe_mul, hA, hB, hAi, hBi, Matrix.SpecialLinearGroup.coe_neg,
    Matrix.SpecialLinearGroup.coe_one, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> linear_combination (1 : F) * h3

end NegOne

section SU3

variable {E : Type} [Field E] [Finite E] {p e : ℕ} [Fact p.Prime] [CharP E p]

theorem su_three_perfect_odd (hK : Nat.card E = (p ^ e) ^ 2) (hp2 : p ≠ 2) :
    (⊤ : Subgroup (Su E p e 3)) ≤ ⁅(⊤ : Subgroup (Su E p e 3)), ⊤⁆ := by
  have h : Group.IsPerfect (Su E p e 3) := CFSG.ClassicalGroups.Unitary.isPerfect_SUid
    (CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hK) le_rfl
    fun _ => CFSG.ClassicalGroups.Unitary.exists_norm_ne_one hK
      (CFSG.LieType.Steinberg.pow_ne_two_of_ne_two Fact.out hp2 e)
  exact h.commutator_eq_top.ge

theorem su_range_le_commutator_odd {Y : Type*} [Group Y] (hK : Nat.card E = (p ^ e) ^ 2)
    (hp2 : p ≠ 2) (α : Su E p e 3 →* Y) : α.range ≤ ⁅α.range, α.range⁆ := by
  have h := su_three_perfect_odd (E := E) (p := p) (e := e) hK hp2
  rw [MonoidHom.range_eq_map]
  have h2 := Subgroup.map_mono (f := α) h
  rwa [Subgroup.map_commutator] at h2

end SU3

end CFSG.ClassicalInvolution.Asc77.T3CII
