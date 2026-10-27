module

public import CFSG.LargeExtraspecial.Asc611IMatF4
public import CFSG.LargeExtraspecial.Asc611IStepB

public section

namespace CFSG.LargeExtraspecial.Asc611I

open Subgroup Matrix CFSG.Fischer CFSG.Fischer.Classification.Unitary
open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LargeExtraspecial.AS35L
open CFSG.Blueprint.Fischer (K)

variable {m : ℕ} {e : SUid frob m} {U : Subgroup (PG m)} {r : ℕ} {q : Fin r → Fin m → K}

theorem herm_sum_p_self (he : e * e = 1) (d : Fin r → K) :
    herm frob (∑ l, d l • invN e (q l)) (∑ l, d l • invN e (q l)) = 0 := by
  rw [herm_sum_right']
  simp only [herm_smul_right, herm_sum_left', herm_smul_left, herm_invN_invN he, mul_zero,
    Finset.sum_const_zero]

theorem false_of_rank_one (S : Setup e U) (F : IsFrame e q) {g : SUid frob m}
    (hg : (QuotientGroup.mk g : PG m) ∈ U) {d : Fin r → F4} (hd : d ≠ 0)
    (hact : ActsBy e q ((rk1F d).map eF4) g) : False := by
  rw [map_rk1F] at hact
  have heq := hact.eq_tvU S.invol
  have hd' : (fun l => eF4 (d l)) ≠ 0 := fun h0 => hd (funext fun l => by
    have := congrFun h0 l
    simpa using this)
  apply S.noTransv _ hg
  rw [heq]
  exact tq_mem_DG (sum_ne_zero_of_frame F hd') (herm_sum_p_self S.invol _)

theorem step_mem (S : Setup e U) (F : IsFrame e q) {u : SUid frob m}
    (hu : (QuotientGroup.mk u : PG m) ∈ U) {M : Matrix (Fin r) (Fin r) F4}
    (hact : ActsBy e q (M.map eF4) u) {c : Fin r → F4} (hc : ∑ i, c i ^ 2 * c i = 0) :
    (QuotientGroup.mk (u * cv e (∑ i, eF4 (c i) • q i) * u⁻¹ *
        (cv e (∑ i, eF4 (c i) • q i))⁻¹) : PG m) ∈ U ∧
      ActsBy e q ((stepF M c).map eF4) (u * cv e (∑ i, eF4 (c i) • q i) * u⁻¹ *
        (cv e (∑ i, eF4 (c i) • q i))⁻¹) := by
  have hc' := norm_eF4 hc
  refine ⟨mk_comm_mem S.normal hu (cv_comm S.invol (iso_sum F _) (isoN_sum F _ hc')), ?_⟩
  rw [map_stepF]
  exact ActsBy.comm_cv S.invol F _ hc' hact

theorem map_add_eF4 (A B : Matrix (Fin r) (Fin r) F4) :
    A.map eF4 + B.map eF4 = (A + B).map eF4 :=
  (Matrix.map_add _ (fun a b => map_add eF4 a b) A B).symm

theorem map_one_eF4 : (1 : Matrix (Fin r) (Fin r) F4).map eF4 = 1 :=
  Matrix.map_one _ (map_zero eF4) (map_one eF4)

theorem false_of_chain3 (S : Setup e U) (F : IsFrame e q) {u₀ : SUid frob m}
    (hu₀ : (QuotientGroup.mk u₀ : PG m) ∈ U) {M₀ : Matrix (Fin r) (Fin r) F4}
    (hact : ActsBy e q (M₀.map eF4) u₀) {c₁ c₂ c₃ d : Fin r → F4}
    (h₁ : ∑ i, c₁ i ^ 2 * c₁ i = 0) (h₂ : ∑ i, c₂ i ^ 2 * c₂ i = 0)
    (h₃ : ∑ i, c₃ i ^ 2 * c₃ i = 0) (hch : stepF (stepF M₀ c₁ + stepF M₀ c₂) c₃ = rk1F d)
    (hd : d ≠ 0) : False := by
  obtain ⟨hu₁, ha₁⟩ := step_mem S F hu₀ hact h₁
  obtain ⟨hu₂, ha₂⟩ := step_mem S F hu₀ hact h₂
  have ha₁₂ := ha₁.mul S.invol ha₂
  rw [map_add_eF4] at ha₁₂
  obtain ⟨hu₃, ha₃⟩ := step_mem S F (by rw [QuotientGroup.mk_mul]; exact U.mul_mem hu₁ hu₂)
    ha₁₂ h₃
  rw [hch] at ha₃
  exact false_of_rank_one S F hu₃ hd ha₃

theorem false_of_chain2e (S : Setup e U) (F : IsFrame e q)
    (hEU : (QuotientGroup.mk e : PG m) ∈ U) (he1 : ActsBy e q 1 e) {u₀ : SUid frob m}
    (hu₀ : (QuotientGroup.mk u₀ : PG m) ∈ U) {M₀ : Matrix (Fin r) (Fin r) F4}
    (hact : ActsBy e q (M₀.map eF4) u₀) {c₁ c₂ d : Fin r → F4}
    (h₁ : ∑ i, c₁ i ^ 2 * c₁ i = 0) (h₂ : ∑ i, c₂ i ^ 2 * c₂ i = 0)
    (hch : stepF (stepF M₀ c₁) c₂ + 1 = rk1F d) (hd : d ≠ 0) : False := by
  obtain ⟨hu₁, ha₁⟩ := step_mem S F hu₀ hact h₁
  obtain ⟨hu₂, ha₂⟩ := step_mem S F hu₁ ha₁ h₂
  rw [← map_one_eF4] at he1
  have ha := ha₂.mul S.invol he1
  rw [map_add_eF4, hch] at ha
  exact false_of_rank_one S F (by rw [QuotientGroup.mk_mul]; exact U.mul_mem hu₂ hEU) hd ha

theorem false_of_chain0e (S : Setup e U) (F : IsFrame e q)
    (hEU : (QuotientGroup.mk e : PG m) ∈ U) (he1 : ActsBy e q 1 e) {u₀ : SUid frob m}
    (hu₀ : (QuotientGroup.mk u₀ : PG m) ∈ U) {M₀ : Matrix (Fin r) (Fin r) F4}
    (hact : ActsBy e q (M₀.map eF4) u₀) {d : Fin r → F4} (hch : M₀ + 1 = rk1F d)
    (hd : d ≠ 0) : False := by
  rw [← map_one_eF4] at he1
  have ha := hact.mul S.invol he1
  rw [map_add_eF4, hch] at ha
  exact false_of_rank_one S F (by rw [QuotientGroup.mk_mul]; exact U.mul_mem hu₀ hEU) hd ha

end CFSG.LargeExtraspecial.Asc611I
