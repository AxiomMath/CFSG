module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PGroup.NormalSubgroups

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem c16_comm_of_rho {Q K : Subgroup G} {rho : G} (hQ : IsPGroup 2 Q) (hKQ : K ≤ Q)
    (hcard : Nat.card K = 4) (hQK : ∀ q ∈ Q, ∀ k ∈ K, q * k * q⁻¹ ∈ K)
    (hrQ : ∀ q ∈ Q, rho * q * rho⁻¹ ∈ Q) (hrK : ∀ k ∈ K, rho * k * rho⁻¹ ∈ K)
    (hr3 : rho ^ 3 = 1) (hmove : ∀ k ∈ K, k ≠ 1 → rho * k * rho⁻¹ ≠ k) :
    ∀ q ∈ Q, ∀ k ∈ K, q * k = k * q := by
  have hQnorm : Q ≤ Subgroup.normalizer (K : Set G) := by
    intro q hq
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · intro hk; exact hQK q hq k hk
    · intro hk
      have h := hQK q⁻¹ (Q.inv_mem hq) (q * k * q⁻¹) hk
      have h' : q⁻¹ * (q * k * q⁻¹) * (q⁻¹)⁻¹ = k := by group
      rwa [h'] at h
  haveI hNn : (K.subgroupOf Q).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hQnorm
  have hcardSub : Nat.card (K.subgroupOf Q) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKQ).toEquiv, hcard]
  haveI hNt : Nontrivial (K.subgroupOf Q) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hcardSub]; norm_num)
  haveI : Fact (IsPGroup 2 ↥Q) := ⟨hQ⟩
  obtain ⟨x, hx1, hxc⟩ :=
    CFSG.exists_nontrivial_center_mem_normal (N := K.subgroupOf Q) (p := 2)
  let k : G := ((x : ↥Q) : G)
  have hkK : k ∈ K := x.2
  have hk1 : k ≠ 1 := by
    intro h
    exact hx1 (Subtype.ext (Subtype.ext h))
  have hkCent : k ∈ Subgroup.centralizer (Q : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have h := Subgroup.mem_center_iff.mp hxc (⟨q, hq⟩ : ↥Q)
    simpa using congrArg (fun y : ↥Q => (y : G)) h
  let C : Subgroup G := K ⊓ Subgroup.centralizer (Q : Set G)
  have hkC : k ∈ C := Subgroup.mem_inf.mpr ⟨hkK, hkCent⟩
  have hCKle : C ≤ K := inf_le_left
  have hrho_inv : rho⁻¹ = rho * rho := by
    have h : rho * (rho * rho) = 1 := by simpa [pow_succ, mul_assoc] using hr3
    exact inv_eq_of_mul_eq_one_right h
  have hrho_sq : rho * rho = rho⁻¹ := hrho_inv.symm
  have hrho_ii : rho⁻¹ * rho⁻¹ = rho := by
    rw [hrho_inv]
    calc (rho * rho) * (rho * rho) = rho ^ 4 := by
          rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add, pow_two]
      _ = rho := by rw [show rho ^ 4 = rho ^ 3 * rho by rw [pow_succ], hr3, one_mul]
  have hCnorm : ∀ c ∈ C, rho * c * rho⁻¹ ∈ C := by
    intro c hc
    obtain ⟨hcK, hcCent⟩ := Subgroup.mem_inf.mp hc
    refine Subgroup.mem_inf.mpr ⟨hrK c hcK, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hq' : rho⁻¹ * q * rho ∈ Q := by
      have h1 : rho * q * rho⁻¹ ∈ Q := hrQ q hq
      have h2 : rho * (rho * q * rho⁻¹) * rho⁻¹ ∈ Q := hrQ _ h1
      have he : rho * (rho * q * rho⁻¹) * rho⁻¹ = rho⁻¹ * q * rho := by
        calc rho * (rho * q * rho⁻¹) * rho⁻¹
            = (rho * rho) * q * (rho⁻¹ * rho⁻¹) := by group
          _ = rho⁻¹ * q * rho := by rw [hrho_sq, hrho_ii]
      rwa [he] at h2
    have hcomm := (Subgroup.mem_centralizer_iff.mp hcCent) (rho⁻¹ * q * rho) hq'
    calc q * (rho * c * rho⁻¹)
        = rho * ((rho⁻¹ * q * rho) * c) * rho⁻¹ := by group
      _ = rho * (c * (rho⁻¹ * q * rho)) * rho⁻¹ := by rw [hcomm]
      _ = (rho * c * rho⁻¹) * q := by group
  let k' : G := rho * k * rho⁻¹
  have hk'C : k' ∈ C := hCnorm k hkC
  have hk'ne : k' ≠ k := hmove k hkK hk1
  have hk'1 : k' ≠ 1 := by
    intro h
    apply hk1
    calc k = rho⁻¹ * k' * rho := by dsimp only [k']; group
      _ = rho⁻¹ * 1 * rho := by rw [h]
      _ = 1 := by group
  have h3 : 3 ≤ Nat.card C := by
    have hsub : ({1, k, k'} : Set G) ⊆ (C : Set G) := by
      intro a ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl | rfl
      · exact Subgroup.one_mem C
      · exact hkC
      · exact hk'C
    have hcard3 : ({1, k, k'} : Set G).ncard = 3 := by
      rw [Set.ncard_eq_three]
      exact ⟨1, k, k', hk1.symm, hk'1.symm, hk'ne.symm, rfl⟩
    calc 3 = ({1, k, k'} : Set G).ncard := hcard3.symm
      _ ≤ (C : Set G).ncard := Set.ncard_le_ncard hsub
      _ = Nat.card C := by rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe]
  have hdvd : Nat.card C ∣ 4 := by
    rw [← hcard]
    exact Subgroup.card_dvd_of_le hCKle
  have hcardC : Nat.card C = 4 := by
    have hle : Nat.card C ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases h : Nat.card C
    · norm_num at hdvd
    · rfl
  have hCK : C = K := Subgroup.eq_of_le_of_card_ge hCKle (by omega)
  intro q hq k hk
  have hkC' : k ∈ C := by rw [hCK]; exact hk
  exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hkC').2) q hq

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
