module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13a3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13aAb
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutHS29

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

private theorem conj_eq_of_comm {g x : G} (h : g * x = x * g) : g * x * g⁻¹ = x := by
  rw [h, mul_assoc, mul_inv_cancel, mul_one]

private theorem conj_inv_eq {g x : G} (h : g * x = x * g) : g * x⁻¹ * g⁻¹ = x⁻¹ := by
  have hx : g * x * g⁻¹ = x := conj_eq_of_comm h
  calc g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    _ = x⁻¹ := by rw [hx]

private theorem q13a_x₁_ne_one_aux (h : Q13Om t L S x₁ x₂ lam rho tau om) : x₁ ≠ 1 := by
  intro h1
  have h4 := h.c11.wreath.ord_x₁
  rw [h1, orderOf_one] at h4
  exact absurd h4 (by norm_num)

private theorem q13a_x₁_ne_x₂_aux (h : Q13Om t L S x₁ x₂ lam rho tau om) : x₁ ≠ x₂ := by
  intro hEq
  have hmem : x₁ ∈ (⊥ : Subgroup G) := by
    rw [← h.c11.wreath.inf_eq_bot]
    exact Subgroup.mem_inf.mpr
      ⟨Subgroup.mem_zpowers x₁, by rw [hEq]; exact Subgroup.mem_zpowers x₂⟩
  exact q13a_x₁_ne_one_aux h (by simpa using hmem)

private theorem q13a_tlam_sq_aux (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    (t * lam) * (t * lam) = 1 := by
  have htl : t * lam = lam * t := (q13a_t_comm h).1
  calc (t * lam) * (t * lam) = t * (lam * t) * lam := by group
    _ = t * (t * lam) * lam := by rw [← htl]
    _ = (t * t) * (lam * lam) := by group
    _ = 1 := by rw [q13a_t_mul_self h, q13a_lam_mul_self h, one_mul]

private theorem q13a_tlam_rho_aux (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    (t * lam) * rho * (t * lam)⁻¹ = rho⁻¹ := by
  have htr : t * rho = rho * t := (q13a_t_comm h).2.1
  calc (t * lam) * rho * (t * lam)⁻¹ = t * (lam * rho * lam⁻¹) * t⁻¹ := by group
    _ = t * rho⁻¹ * t⁻¹ := by rw [h.c11.lam_rho]
    _ = rho⁻¹ := conj_inv_eq htr

theorem q13a_card_CQ_tlam (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    Nat.card ↥(ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t * lam} : Set G)) = 8 := by
  set Q : Subgroup G := ctxQ t tau x₁ x₂ rho with hQ
  have hρ : rho ∈ normalizer (Q : Set G) := by rw [hQ]; exact q13a_rho_norm_Q h
  have htM : t ∈ ctxM t tau x₁ x₂ := (q13a_mem_M h).1
  have hlamM : lam ∈ ctxM t tau x₁ x₂ := (q13a_mem_M h).2.2.2.1
  have hx : t * lam ∈ normalizer (Q : Set G) := by
    rw [hQ]
    exact Subgroup.mem_normalizer_fintype (fun a ha => q13a_conj_Q h (mul_mem htM hlamM) ha)
  have hx₁Q' : x₁ ∈ ctxQ t tau x₁ x₂ rho :=
    h.c11.base_le_Q (Subgroup.subset_closure (by simp))
  have hx₁Q : x₁ ∈ Q := hQ ▸ hx₁Q'
  have hconj_tlam_x₁ : (t * lam) * x₁ * (t * lam)⁻¹ = x₂ := by
    have hx₂base : x₂ ∈ baseGrp x₁ x₂ := Subgroup.subset_closure (by simp)
    have htx₂ : t * x₂ = x₂ * t := by
      have hmem : x₂ ∈ ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t} : Set G) := by
        rw [l12_CQ_t h.c11]; exact hx₂base
      exact (Subgroup.mem_centralizer_singleton_iff.mp hmem.2).symm
    calc (t * lam) * x₁ * (t * lam)⁻¹ = t * (lam * x₁ * lam⁻¹) * t⁻¹ := by group
      _ = t * x₂ * t⁻¹ := by rw [h.c11.wreath.conj_x₁]
      _ = x₂ := by rw [htx₂, mul_assoc, mul_inv_cancel, mul_one]
  have hfρ : ∃ h ∈ Q, rho * h ≠ h * rho :=
    ⟨x₁, hx₁Q, fun hconj => q13a_x₁_ne_one_aux h (l12_cent_Q_rho h.c11 x₁ hx₁Q' hconj.symm)⟩
  have hfx : ∃ h ∈ Q, (t * lam) * h ≠ h * (t * lam) := by
    refine ⟨x₁, hx₁Q, fun hconj => ?_⟩
    have h1 : (t * lam) * x₁ * (t * lam)⁻¹ = x₁ := by
      rw [hconj, mul_assoc, mul_inv_cancel, mul_one]
    exact q13a_x₁_ne_x₂_aux h (h1.symm.trans hconj_tlam_x₁)
  have h2 : orderOf (t * lam) = 2 := by
    apply orderOf_eq_prime (by simpa [pow_two] using q13a_tlam_sq_aux h)
    intro h1
    have h3 := hconj_tlam_x₁
    rw [h1, one_mul, inv_one, mul_one] at h3
    exact q13a_x₁_ne_x₂_aux h h3
  have hs : Outside.Sigma3Rel (Outside.conjAut Q rho hρ) (Outside.conjAut Q (t * lam) hx) :=
    Outside.sigma3Rel_conjAut Q hρ hx h.c11.ord_rho h2 (q13a_tlam_rho_aux h) hfρ hfx
  have hfpf : ∀ g : ↥Q, Outside.conjAut Q rho hρ g = g → g = 1 := by
    intro g hg
    have h1 : rho * (g : G) * rho⁻¹ = (g : G) := by
      have := congrArg (fun x : ↥Q => (x : G)) hg
      simpa [Outside.conjAut_coe] using this
    have h2' : rho * (g : G) = (g : G) * rho := (mul_inv_eq_iff_eq_mul).mp h1
    exact Subtype.ext (l12_cent_Q_rho h.c11 (g : G) (hQ ▸ g.2) h2'.symm)
  have hnab : ∃ a b : ↥Q, a * b ≠ b * a := by
    obtain ⟨a, b, ha, hb, hab⟩ := q13a_Q_nonab h
    exact ⟨⟨a, hQ ▸ ha⟩, ⟨b, hQ ▸ hb⟩, fun hc => hab (congrArg Subtype.val hc)⟩
  have hcard : Nat.card ↥Q = 64 := by rw [hQ, l12_card_Q h.c11]; norm_num
  obtain ⟨-, hfix⟩ := Outside.HS29 hcard hnab hs hfpf
  have hcard_fix : Nat.card ↥(Outside.fixSub (Outside.conjAut Q (t * lam) hx)) = 8 := by
    rcases hfix with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · calc Nat.card ↥(Outside.fixSub (Outside.conjAut Q (t * lam) hx))
          = Nat.card (DihedralGroup 4) := Nat.card_congr e.toEquiv
        _ = 8 := by rw [DihedralGroup.nat_card]
    · calc Nat.card ↥(Outside.fixSub (Outside.conjAut Q (t * lam) hx))
          = Nat.card (QuaternionGroup 2) := Nat.card_congr e.toEquiv
        _ = 8 := by rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hgoal : Nat.card ↥((Outside.fixSub (Outside.conjAut Q (t * lam) hx)).map Q.subtype) = 8 := by
    rw [Subgroup.card_map_of_injective Q.subtype_injective, hcard_fix]
  rw [Outside.map_fixSub_conjAut Q hx] at hgoal
  exact hgoal

theorem q13a_card_CA_tlam (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    Nat.card ↥(q13A t tau x₁ x₂ rho ⊓ centralizer ({t * lam} : Set G)) = 4 := by
  have hrA : ∀ a ∈ q13A t tau x₁ x₂ rho, rho * a * rho⁻¹ ∈ q13A t tau x₁ x₂ rho :=
    fun a ha => (q13a_A_inv h a ha).1
  have hsA : ∀ a ∈ q13A t tau x₁ x₂ rho,
      (t * lam) * a * (t * lam)⁻¹ ∈ q13A t tau x₁ x₂ rho := by
    intro a ha
    have h1 : (t * lam) * a * (t * lam)⁻¹ = t * (lam * a * lam⁻¹) * t⁻¹ := by group
    rw [h1]
    exact q13a_t_norm_A h (lam * a * lam⁻¹) (q13a_A_inv h a ha).2.1
  have hfpf : ∀ a ∈ q13A t tau x₁ x₂ rho, rho * a * rho⁻¹ = a → a = 1 := by
    intro a ha hfix
    exact l12_cent_Q_rho h.c11 a (Subgroup.mem_inf.mp ha).1
      (mul_inv_eq_iff_eq_mul.mp hfix).symm
  have hmain := card_eq_sq_card_inf_centralizer (A := q13A t tau x₁ x₂ rho) (q13a_A_comm h)
    hrA hsA (q13a_rho_cube h) hfpf (q13a_tlam_sq_aux h) (q13a_tlam_rho_aux h)
  have hcardA : Nat.card (q13A t tau x₁ x₂ rho) = 16 := by rw [q13a_card_A h]; norm_num
  have hx : Nat.card ↥(q13A t tau x₁ x₂ rho ⊓ centralizer ({t * lam} : Set G)) ^ 2 = 16 := by
    rw [← hmain, hcardA]
  have hx4 : Nat.card ↥(q13A t tau x₁ x₂ rho ⊓ centralizer ({t * lam} : Set G)) ^ 2
      = 4 ^ 2 := by rw [hx]; norm_num
  exact Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) hx4

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
