module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13a4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13b0
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

theorem q13d_gam_sq (h : Q13Om t L S x₁ x₂ lam rho tau om) : (t * om) ^ 2 = tau := by
  have hom : om⁻¹ = om := inv_eq_of_mul_eq_one_right h.om_sq
  have htom : om * t * om = t * tau := by
    have h1 := h.t_om
    rwa [hom] at h1
  calc (t * om) ^ 2 = t * om * t * om := by rw [pow_two]; group
    _ = t * (om * t * om) := by group
    _ = t * (t * tau) := by rw [htom]
    _ = tau := by rw [← mul_assoc, q13a_t_mul_self h, one_mul]

theorem q13d_orderOf_gam (h : Q13Om t L S x₁ x₂ lam rho tau om) : orderOf (t * om) = 4 := by
  have h4 : (t * om) ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, q13d_gam_sq h, pow_two]
    exact q13a_tau_mul_self h
  have hnot : ¬ (t * om) ^ 2 ^ 1 = 1 := by
    rw [pow_one, q13d_gam_sq h]
    exact q13b_tau_ne_one h
  have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := t * om) hnot (by simpa using h4)
  simpa using h

theorem q13d_tau_not_mem_Q (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    tau ∉ ctxQ t tau x₁ x₂ rho := by
  intro hQ
  have hCO : tau ∈ ctxCO t tau x₁ x₂ rho :=
    Subgroup.mem_inf.mpr ⟨q13b_N_le_O h (q13b_tau_mem_N h),
      Subgroup.mem_centralizer_singleton_iff.mpr h.c11.tau_rho⟩
  exact q13b_tau_ne_one h (q13b_Q_inf_CO h tau hQ hCO)

theorem q13d_A_le_Q (_h : Q13Om t L S x₁ x₂ lam rho tau om) :
    q13A t tau x₁ x₂ rho ≤ ctxQ t tau x₁ x₂ rho :=
  inf_le_left

theorem q13d_A_cent_tau (_h : Q13Om t L S x₁ x₂ lam rho tau om) :
    ∀ a ∈ q13A t tau x₁ x₂ rho, a * tau = tau * a := by
  intro a ha
  exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp ha).2

theorem q13d_tau_not_mem_A (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    tau ∉ q13A t tau x₁ x₂ rho := by
  intro hA
  exact q13d_tau_not_mem_Q h (q13d_A_le_Q h hA)

theorem q13d_A_inf_CO (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    ∀ g ∈ q13A t tau x₁ x₂ rho, g ∈ closure ({t, om} : Set G) → g = 1 := by
  intro g hgA hgC
  have hQ : g ∈ ctxQ t tau x₁ x₂ rho := q13d_A_le_Q h hgA
  have hCO : g ∈ ctxCO t tau x₁ x₂ rho := by rw [h.CO_eq]; exact hgC
  exact q13b_Q_inf_CO h g hQ hCO

theorem q13d_CO_norm_A (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    ∀ c ∈ closure ({t, om} : Set G), ∀ a ∈ q13A t tau x₁ x₂ rho,
      c * a * c⁻¹ ∈ q13A t tau x₁ x₂ rho := by
  intro c hc a ha
  have htN : t ∈ Subgroup.normalizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) :=
    Subgroup.mem_normalizer_fintype (fun a ha => by
      rw [q13a_t_inv_A h a ha]
      exact Subgroup.inv_mem _ ha)
  have homN : om ∈ Subgroup.normalizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) :=
    Subgroup.mem_normalizer_fintype (fun a ha => (q13a_A_inv h a ha).2.2)
  have hle : closure ({t, om} : Set G) ≤
      Subgroup.normalizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact htN
    · exact homN
  exact (Subgroup.mem_normalizer_iff.mp (hle hc) a).mp ha

theorem q13d_card_CO (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    Nat.card ↥(closure ({t, om} : Set G)) = 8 := by
  rw [← h.CO_eq]
  obtain ⟨e⟩ := h.c11.CO_dihedral
  rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]

theorem q13d_A_cent_N (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    ∀ a ∈ q13A t tau x₁ x₂ rho, ∀ n ∈ ctxN tau x₁ x₂, a * n = n * a := by
  intro a ha n hn
  have hle : ctxN tau x₁ x₂ ≤ Subgroup.centralizer ({a} : Set G) := by
    rw [ctxN, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (q13d_A_cent_tau h a ha).symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (q13a_A_comm h a ha (x₁ ^ 2)
          (q13a_V_le_A h (Subgroup.subset_closure (by simp)))).symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (q13a_A_comm h a ha ((x₁ * x₂) ^ 2)
          (q13a_V_le_A h (Subgroup.subset_closure (by simp)))).symm
  exact Subgroup.mem_centralizer_iff.mp (hle hn) a (Set.mem_singleton a)

theorem q13d_CO_cent_N (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    ∀ c ∈ closure ({t, om} : Set G), ∀ n ∈ ctxN tau x₁ x₂, c * n = n * c := by
  intro c hc n hn
  have ht : t ∈ Subgroup.centralizer ((ctxN tau x₁ x₂ : Subgroup G) : Set G) :=
    Subgroup.mem_centralizer_iff.mpr (fun n hn =>
      (q13a_X_comm h t (Subgroup.subset_closure (by simp)) n
        ((p0_V_le_N_le_X t tau x₁ x₂).2 hn)).symm)
  have hNle : ctxN tau x₁ x₂ ≤ Subgroup.centralizer ({om} : Set G) := by
    rw [ctxN, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (q13a_om_comm h).1.symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        ((q13a_om_comm h).2.2 (x₁ ^ 2) (Subgroup.subset_closure (by simp))).symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        ((q13a_om_comm h).2.2 ((x₁ * x₂) ^ 2)
          (Subgroup.subset_closure (by simp))).symm
  have hom : om ∈ Subgroup.centralizer ((ctxN tau x₁ x₂ : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    exact Subgroup.mem_centralizer_singleton_iff.mp (hNle hn)
  have hle : closure ({t, om} : Set G) ≤
      Subgroup.centralizer ((ctxN tau x₁ x₂ : Subgroup G) : Set G) := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ht
    · exact hom
  exact (Subgroup.mem_centralizer_iff.mp (hle hc) n hn).symm

theorem q13d_A_le_U (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    q13A t tau x₁ x₂ rho ≤ ctxU t tau x₁ x₂ lam :=
  (q13d_A_le_Q h).trans (q13b_Q_normal_U h).1

theorem q13d_CO_le_U (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    closure ({t, om} : Set G) ≤ ctxU t tau x₁ x₂ lam := by
  rw [← h.CO_eq]
  exact (inf_le_left : ctxCO t tau x₁ x₂ rho ≤ ctxO t tau x₁ x₂).trans (q13b_O_le_U h)

theorem q13d_N_le_U (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    ctxN tau x₁ x₂ ≤ ctxU t tau x₁ x₂ lam :=
  (q13b_N_le_O h).trans (q13b_O_le_U h)

theorem q13d_mem_N (h : Q13Om t L S x₁ x₂ lam rho tau om) {n : G} :
    n ∈ ctxN tau x₁ x₂ ↔ n ∈ fourGrp x₁ x₂ ∨ ∃ v ∈ fourGrp x₁ x₂, n = tau * v := by
  constructor
  · intro hn
    rcases l12_N_cases h.c11.toCtx10.toCtx4 hn with hV | hV
    · exact Or.inl hV
    · refine Or.inr ⟨tau * n, hV, ?_⟩
      rw [← mul_assoc, q13a_tau_mul_self h, one_mul]
  · rintro (hV | ⟨v, hv, rfl⟩)
    · exact q13b_V_le_N h hV
    · exact Subgroup.mul_mem _ (q13b_tau_mem_N h) (q13b_V_le_N h hv)

theorem q13d_conj_mem_of_charIn {A B : Subgroup G} (hAB : CharIn A B) {g : G}
    (hg : g ∈ normalizer (B : Set G)) : ∀ a ∈ A, g * a * g⁻¹ ∈ A := by
  obtain ⟨hABle, hABchar⟩ := hAB
  intro a ha
  let φ : MulAut B := Outside.conjAut B g hg
  have hmap : (A.subgroupOf B).map φ.toMonoidHom = A.subgroupOf B :=
    (Subgroup.characteristic_iff_map_eq.mp hABchar) φ
  have hφ : φ ⟨a, hABle ha⟩ ∈ A.subgroupOf B := by
    have h1 : φ ⟨a, hABle ha⟩ ∈ (A.subgroupOf B).map φ.toMonoidHom :=
      Subgroup.mem_map.mpr ⟨⟨a, hABle ha⟩, ha, rfl⟩
    rwa [hmap] at h1
  have hcoe : ((φ ⟨a, hABle ha⟩ : B) : G) = g * a * g⁻¹ :=
    Outside.conjAut_coe B g hg ⟨a, hABle ha⟩
  have := (Subgroup.mem_subgroupOf (H := A) (K := B)).mp hφ
  rwa [hcoe] at this

theorem q13d_normalizer_le_of_charIn {A B : Subgroup G} (hAB : CharIn A B) :
    normalizer (B : Set G) ≤ normalizer (A : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro a
  refine ⟨fun ha => q13d_conj_mem_of_charIn hAB hg a ha, fun ha => ?_⟩
  have h2 := q13d_conj_mem_of_charIn hAB (inv_mem hg) _ ha
  simpa [mul_assoc] using h2

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
