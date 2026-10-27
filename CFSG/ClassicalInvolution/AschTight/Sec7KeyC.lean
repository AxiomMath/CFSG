module

public import CFSG.ClassicalInvolution.AschTight.Sec7KeyB
public import CFSG.ClassicalInvolution.AschTight.E2StarTargets
public import CFSG.ClassicalInvolution.AschTight.Sec7Basic

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

omit [Finite G] in
theorem mem_normalizer_inf {A B : Subgroup G} {n : G} (hA : n ∈ Subgroup.normalizer (A : Set G))
    (hB : n ∈ Subgroup.normalizer (B : Set G)) :
    n ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro y
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hA y, hB y]

omit [Finite G] in
theorem oddCoreOf_eq_oddCoreIn (X : Subgroup G) : oddCoreOf X = Balance.oddCoreIn X := rfl

theorem mem_oddCoreOf_of_odd (hΩ : HypOmegaMod p f Ω) {J W : Subgroup G} (hJ : J ∈ Ω) {u : G}
    (huJ : u ∈ J) (huW : u ∈ W) (hu2 : IsPGroup 2 (Subgroup.zpowers u)) (huu : u * u ≠ 1)
    {d : G} (hdC : d ∈ J ⊓ Subgroup.centralizer (W : Set G)) (hodd : Odd (orderOf d)) :
    d ∈ oddCoreOf (J ⊓ Subgroup.centralizer (W : Set G)) := by
  set C := J ⊓ Subgroup.centralizer (W : Set G) with hCdef
  set D := C ⊓ oddCoreOf J with hDdef
  have hCJ : C ≤ J := inf_le_left
  have hCu : ∀ c ∈ C, c * u = u * c := fun c hc =>
    ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2) u huW).symm
  have hDodd : Odd (Nat.card D) :=
    (oddCoreOf_odd_natCard J).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)
  have hCND : C ≤ Subgroup.normalizer (D : Set G) := fun c hc =>
    mem_normalizer_inf (Subgroup.le_normalizer hc)
      (mem_normalizer_oddCoreOf_of_mem_normalizer (Subgroup.le_normalizer (hCJ hc)))
  have hE : Odd (Nat.card ↥(Subgroup.zpowers d ⊔ D)) :=
    odd_card_sup_of_le_normalizer' (Subgroup.zpowers_le.mpr (hCND hdC))
      (by rw [Nat.card_zpowers]; exact hodd) hDodd
  have hEC : Subgroup.zpowers d ⊔ D ≤ C := sup_le (Subgroup.zpowers_le.mpr hdC) inf_le_left
  have hCNE : C ≤ Subgroup.normalizer ((Subgroup.zpowers d ⊔ D : Subgroup G) : Set G) := by
    intro c hc
    rw [mem_normalizer_iff_conjSub_eq]
    refine conjSub_eq_of_le_self ?_
    rw [conjSub, Subgroup.map_sup, ← conjSub, ← conjSub]
    refine sup_le ?_ ?_
    · rw [conjSub, MonoidHom.map_zpowers, Subgroup.zpowers_le]
      have hcomm : d⁻¹ * c * d⁻¹⁻¹ * c⁻¹ ∈ D := by
        refine ⟨?_, commutator_mem_oddCoreOf_of_commute hΩ hJ huJ hu2 huu
          (J.inv_mem (hCJ hdC)) (hCJ hc) (hCu _ (C.inv_mem hdC)) (hCu c hc)⟩
        exact C.mul_mem (C.mul_mem (C.mul_mem (C.inv_mem hdC) hc) (C.inv_mem (C.inv_mem hdC)))
          (C.inv_mem hc)
      have e : (MulAut.conj c).toMonoidHom d = d * (d⁻¹ * c * d⁻¹⁻¹ * c⁻¹) := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers d))
        (Subgroup.mem_sup_right hcomm)
    · rw [mem_normalizer_iff_conjSub_eq.mp (hCND hc)]
      exact le_sup_right
  have h1 := Balance.le_oddCoreIn_of_normalizes hEC hCNE hE
  rw [← oddCoreOf_eq_oddCoreIn] at h1
  exact h1 (Subgroup.mem_sup_left (Subgroup.mem_zpowers d))

theorem exists_pow_two_pow_mem (hΩ : HypOmegaMod p f Ω) {J W : Subgroup G} (hJ : J ∈ Ω)
    (hWJ : W ≤ Subgroup.normalizer (J : Set G)) (hUc : IsCyclic ↥(J ⊓ W))
    (hU2 : IsPGroup 2 ↥(J ⊓ W)) {u : G} (huU : u ∈ J ⊓ W) (huu : u * u ≠ 1) {h : G}
    (hhJ : h ∈ J) (hhW : h ∈ Subgroup.normalizer (W : Set G)) :
    ∃ n : ℕ, h ^ (2 ^ n) ∈ oddCoreOf (J ⊓ Subgroup.centralizer (W : Set G)) := by
  obtain ⟨n, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos h).ne'
  refine ⟨n, ?_⟩
  have hdvd : 2 ^ n ∣ orderOf h := ⟨m, hnm⟩
  have hord : orderOf (h ^ (2 ^ n)) = m := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) hdvd, hnm,
      Nat.mul_div_cancel_left _ (pow_pos two_pos n)]
  have hodd : Odd (orderOf (h ^ (2 ^ n))) := hord ▸ hm
  have hJ' : h ^ (2 ^ n) ∈ J := J.pow_mem hhJ _
  have hW' : h ^ (2 ^ n) ∈ Subgroup.normalizer (W : Set G) := Subgroup.pow_mem _ hhW _
  have hC := mem_centralizer_of_odd hWJ hUc hU2 hJ' hW' hodd
  exact mem_oddCoreOf_of_odd hΩ hJ (Subgroup.mem_inf.mp huU).1 (Subgroup.mem_inf.mp huU).2
    (hU2.to_le (Subgroup.zpowers_le.mpr huU)) huu ⟨hJ', hC⟩ hodd

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7
