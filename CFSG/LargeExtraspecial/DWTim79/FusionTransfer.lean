module

public import CFSG.LargeExtraspecial.DWNormalFour

public section

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module QuadraticMap CFSG.RankThree.Literature.FSmith
open scoped commutatorElement

theorem transfer_eq_one_of_O2 {G : Type*} [Group G] [Finite G] {S : Setting G}
    (hO2 : ∀ (N : Subgroup G) [N.Normal], IsPGroup 2 (G ⧸ N) → N = ⊤)
    (ϕ : S.M →* Multiplicative (ZMod 2)) (g : G) : ϕ.transfer g = 1 := by
  have hrange : IsPGroup 2 (ϕ.transfer).range := by
    refine IsPGroup.of_card_dvd_pow (n := 1) ?_
    have hdvd := Subgroup.card_subgroup_dvd_card (ϕ.transfer).range
    have hcard : Nat.card (Multiplicative (ZMod 2)) = 2 := by
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    simpa [hcard] using hdvd
  haveI : (ϕ.transfer).ker.Normal := (ϕ.transfer).normal_ker
  have hquot : IsPGroup 2 (G ⧸ (ϕ.transfer).ker) :=
    hrange.of_equiv (QuotientGroup.quotientKerEquivRange ϕ.transfer).symm
  have hker : (ϕ.transfer).ker = ⊤ := hO2 _ hquot
  exact (MonoidHom.mem_ker).mp (by rw [hker]; exact Subgroup.mem_top g)

theorem eq_one_or_z_of_forall_conj_of_O2 {G : Type*} [Group G] [Finite G] {S : Setting G}
    (hO2 : ∀ (N : Subgroup G) [N.Normal], IsPGroup 2 (G ⧸ N) → N = ⊤) (h2 : 2 ≤ S.width)
    {c : G} (hcQ : c ∈ S.QG)
    (hc : ∀ m ∈ S.M, m * c * m⁻¹ = c ∨ m * c * m⁻¹ = c * S.z) : c = 1 ∨ c = S.z := by
  by_contra hne
  push Not at hne
  obtain ⟨hc1, hcz⟩ := hne
  have hv : S.cl c ≠ 0 := fun h => by
    rcases (S.cl_eq_zero_iff hcQ).mp h with h | h
    exacts [hc1 h, hcz h]
  obtain ⟨w, hwv, hwq⟩ := Sm77.exists_polar_eq_one_q_eq_zero S h2 hv
  obtain ⟨a, haQ, rfl⟩ := S.exists_cl w
  have ha2 : a ^ 2 = 1 := (S.q_cl_eq_zero_iff haQ).mp hwq
  have hac : a * c ≠ c * a := (S.polar_cl_eq_one_iff haQ hcQ).mp hwv
  have haca : a * c * a⁻¹ = c * S.z := by
    rcases S.mul_comm_or haQ hcQ with h | h
    · exact absurd h hac
    · calc a * c * a⁻¹ = S.z * (c * a) * a⁻¹ := by rw [h]
        _ = S.z * c := by group
        _ = c * S.z := (S.z_comm (S.QG_le_M hcQ)).symm
  have ha1 : a ≠ 1 := by
    rintro rfl
    exact hac (by rw [one_mul, mul_one])
  have haz : a ≠ S.z := by
    rintro rfl
    exact hac (S.z_comm (S.QG_le_M hcQ)).symm
  have hva : S.cl a ≠ 0 := fun h => by
    rcases (S.cl_eq_zero_iff haQ).mp h with h | h
    exacts [ha1 h, haz h]
  obtain ⟨c₁, hc₁Q, hc₁a, c₂, hc₂Q, hc₂a, h12⟩ : ∃ c₁ ∈ S.QG, c₁ * a = a * c₁ ∧
      ∃ c₂ ∈ S.QG, c₂ * a = a * c₂ ∧ c₁ * c₂ ≠ c₂ * c₁ := by
    obtain ⟨u₁, hu₁, u₂, hu₂, h⟩ := Sm77.exists_polar_eq_one_of_width_lt S
      (U := perp S (Submodule.span (ZMod 2) {S.cl a}))
      (by
        have hdim : Module.finrank (ZMod 2) (perp S (Submodule.span (ZMod 2) {S.cl a})) =
            2 * S.width - 1 :=
          Sm77.finrank_orthogonal_span_singleton S hva
        rw [hdim]
        omega)
    obtain ⟨c₁, hc₁, rfl⟩ := S.exists_cl u₁
    obtain ⟨c₂, hc₂, rfl⟩ := S.exists_cl u₂
    refine ⟨c₁, hc₁, ?_, c₂, hc₂, ?_, (S.polar_cl_eq_one_iff hc₁ hc₂).mp h⟩
    · exact ((S.polar_cl_eq_zero_iff haQ hc₁).mp
        (Sm77.polar_eq_zero_of_mem_orthogonal S hu₁)).symm
    · exact ((S.polar_cl_eq_zero_iff haQ hc₂).mp
        (Sm77.polar_eq_zero_of_mem_orthogonal S hu₂)).symm
  have hcomm : ⁅c₁, c₂⁆ = S.z := by
    rw [commutatorElement_def]
    rcases S.commutator_eq_one_or_z hc₁Q hc₂Q with h | h
    · exfalso
      apply h12
      calc c₁ * c₂ = c₁ * c₂ * c₁⁻¹ * c₂⁻¹ * (c₂ * c₁) := by group
        _ = c₂ * c₁ := by rw [h, one_mul]
    · exact h
  refine smith_transfer (fixHom S hc) S.z_ne_one S.z_mul_z (F := S.QG) S.QG_le_M S.isPGroup_QG
    ?_ haQ (by rw [← pow_two]; exact ha2) ?_
    (transfer_eq_one_of_O2 (S := S) hO2 (fixHom S hc) a) ?_
    (S.exists_conj_eq_mul_z haQ ha1 haz) ⟨c₁, hc₁Q, c₂, hc₂Q, hc₁a, hc₂a, hcomm⟩
  · intro c' hc'
    have hc'M : c' ∈ S.M := S.mem_M_iff.mpr (hc' S.z S.z_mem_QG)
    exact S.eq_one_or_z_of_commute (S.mem_QG_of_commute hc'M hc') hc'
  · rw [fixHom_apply]
    have hne : a * c * a⁻¹ ≠ c := by
      rw [haca]
      exact fun h => S.z_ne_one (by simpa using h)
    rw [ite_eq_right hne]
    decide
  · intro f hf
    rcases S.mul_comm_or hf haQ with h | h
    · left
      rw [h]
      group
    · right
      calc f * a * f⁻¹ = S.z * (a * f) * f⁻¹ := by rw [h]
        _ = S.z * a := by group
        _ = a * S.z := (S.z_comm (S.QG_le_M haQ)).symm

theorem eq_zero_of_forall_ρ_apply_eq_of_O2 {G : Type*} [Group G] [Finite G] {S : Setting G}
    (hO2 : ∀ (N : Subgroup G) [N.Normal], IsPGroup 2 (G ⧸ N) → N = ⊤) (h2 : 2 ≤ S.width)
    {v : S.Qt} (hv : ∀ m : S.M, (S.ρ m : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) : v = 0 := by
  obtain ⟨c, hcQ, rfl⟩ := S.exists_cl v
  have hc : ∀ m ∈ S.M, m * c * m⁻¹ = c ∨ m * c * m⁻¹ = c * S.z := fun m hm => by
    have h := hv ⟨m, hm⟩
    rw [S.ρ_cl ⟨m, hm⟩ hcQ] at h
    exact (S.cl_eq_cl_iff hcQ (S.conj_mem_QG hm hcQ)).mp h.symm
  rcases eq_one_or_z_of_forall_conj_of_O2 (S := S) hO2 h2 hcQ hc with rfl | rfl
  · exact S.cl_one
  · exact S.cl_z

theorem not_normal_order_four_of_O2 {G : Type*} [Group G] [Finite G] {S : Setting G}
    (hO2 : ∀ (N : Subgroup G) [N.Normal], IsPGroup 2 (G ⧸ N) → N = ⊤) (h2 : 2 ≤ S.width)
    {T : Subgroup G} (hTM : T ≤ S.M) (hT : ∀ m ∈ S.M, ∀ x ∈ T, m * x * m⁻¹ ∈ T)
    (hcard : Nat.card T = 4) (hz : S.z ∈ T) : False := by
  obtain ⟨t, -, -, hw0, -, hfix⟩ := exists_fixed_of_normal_order_four hTM hT hcard hz
  exact hw0 (eq_zero_of_forall_ρ_apply_eq_of_O2 (S := S) hO2 h2 hfix)

end CFSG.LargeExtraspecial.DW
