module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC13KCharU
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC13KInv
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34Aux

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

theorem c13K_conj_R (hc : Ctx13M t L S x₁ x₂ lam rho tau om) {g : G}
    (hg : g ∈ normalizer ((ctxU t tau x₁ x₂ lam : Subgroup G) : Set G)) :
    ∀ r ∈ ctxR t tau x₁ x₂, g * r * g⁻¹ ∈ ctxR t tau x₁ x₂ := by
  have hR := (c13K_lemma4_12a hc).2.2.2.2.1
  have hQ := L34.conj_mem_of_charIn (c13K_charIn_Q_U hc).1 hg
  have hQt := L34.conj_mem_of_charIn (c13K_charIn_Q_U hc).2 hg
  have hO := L34.conj_mem_of_charIn (c13K_charIn_O_U hc) hg
  have hQR : ctxQ t tau x₁ x₂ rho ≤ ctxR t tau x₁ x₂ := by
    rw [hR]
    exact le_sup_left
  have hcl_t : t ∈ closure ({t, tau} : Set G) := Subgroup.subset_closure (by simp)
  have hcl_tau : tau ∈ closure ({t, tau} : Set G) := Subgroup.subset_closure (by simp)
  have htR : t ∈ ctxR t tau x₁ x₂ := by
    rw [hR]
    exact Subgroup.mem_sup_right hcl_t
  have htauR : tau ∈ ctxR t tau x₁ x₂ := by
    rw [hR]
    exact Subgroup.mem_sup_right hcl_tau
  have h1 : g * t * g⁻¹ ∈ ctxR t tau x₁ x₂ := c13K_tG_O hc (hO t (hc.R_le_O htR))
  have h2 : g * tau * g⁻¹ ∈ ctxR t tau x₁ x₂ := by
    have h : g * tau * g⁻¹ ∈ ctxQ t tau x₁ x₂ rho ⊔ zpowers tau :=
      hQt tau (Subgroup.mem_sup_right (Subgroup.mem_zpowers tau))
    exact (sup_le hQR (Subgroup.zpowers_le.mpr htauR)) h
  have hcl : ∀ x ∈ closure ({t, tau} : Set G), g * x * g⁻¹ ∈ ctxR t tau x₁ x₂ := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with h | h
      · rw [h]
        exact h1
      · rw [h]
        exact h2
    | one => simpa using (ctxR t tau x₁ x₂).one_mem
    | mul y z _ _ hy hz =>
      have e : g * (y * z) * g⁻¹ = (g * y * g⁻¹) * (g * z * g⁻¹) := by group
      rw [e]
      exact mul_mem hy hz
    | inv y _ hy =>
      have e : g * y⁻¹ * g⁻¹ = (g * y * g⁻¹)⁻¹ := by group
      rw [e]
      exact inv_mem hy
  let f : G →* G := (MulAut.conj g).toMonoidHom
  have hle : ctxQ t tau x₁ x₂ rho ⊔ closure ({t, tau} : Set G) ≤
      (ctxR t tau x₁ x₂).comap f := by
    refine sup_le (fun q hq => ?_) (fun x hx => ?_)
    · exact hQR (hQ q hq)
    · exact hcl x hx
  intro r hr
  rw [hR] at hr
  exact hle hr

theorem c13K_N_U_le_K (hc : Ctx13M t L S x₁ x₂ lam rho tau om) :
    normalizer ((ctxU t tau x₁ x₂ lam : Subgroup G) : Set G) ≤ ctxK t tau x₁ x₂ rho := by
  intro g hg
  have hR := (c13K_lemma4_12a hc).2.2.2.2.1
  unfold ctxK
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [← hR]
  refine ⟨fun hh => c13K_conj_R hc hg h hh, fun hh => ?_⟩
  have h2 := c13K_conj_R hc (inv_mem hg) _ hh
  have e : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
  rwa [e] at h2

theorem c13K_exists_not_M (hG : Sec4Glob G) (hc : Ctx13M t L S x₁ x₂ lam rho tau om) :
    ∃ k ∈ ctxK t tau x₁ x₂ rho, k ∉ ctxM t tau x₁ x₂ := by
  by_contra hcon
  push Not at hcon
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU2 : IsPGroup 2 (ctxU t tau x₁ x₂ lam) := hc.U_sylow.2.1
  obtain ⟨P, hUP⟩ := hU2.exists_le_sylow
  have hPcard : Nat.card ↥(P : Subgroup G) = 2 ^ (Nat.card G).factorization 2 :=
    Sylow.card_eq_multiplicity P
  have h11 : 11 ≤ (Nat.card G).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp hG.dvd
  have hUne : ctxU t tau x₁ x₂ lam ≠ (P : Subgroup G) := by
    intro h
    have h10 := c13K_card_U hc
    rw [h, hPcard] at h10
    have hlt : (2 : ℕ) ^ 10 < 2 ^ ((Nat.card G).factorization 2) :=
      Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hex : ∃ n ∈ (P : Subgroup G), (∀ x ∈ ctxU t tau x₁ x₂ lam,
      n * x * n⁻¹ ∈ ctxU t tau x₁ x₂ lam) ∧ n ∉ ctxU t tau x₁ x₂ lam := by
    by_contra hno
    push Not at hno
    exact hUne (eq_of_forall_normalizes P.isPGroup' hUP hno)
  obtain ⟨n, hnP, hnU, hnnU⟩ := hex
  have hnorm : n ∈ normalizer ((ctxU t tau x₁ x₂ lam : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨x, hx, rfl⟩
      exact hnU x hx
    · rw [Subgroup.card_map_of_injective (MulAut.conj n).injective]
  have hnM : n ∈ ctxM t tau x₁ x₂ := hcon n (c13K_N_U_le_K hc hnorm)
  have hVP : ctxU t tau x₁ x₂ lam ⊔ zpowers n ≤ (P : Subgroup G) :=
    sup_le hUP (Subgroup.zpowers_le.mpr hnP)
  have hVM : ctxU t tau x₁ x₂ lam ⊔ zpowers n ≤ ctxM t tau x₁ x₂ :=
    sup_le (c13K_O_le_U_le_M hc).2 (Subgroup.zpowers_le.mpr hnM)
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := 2)).mp (P.isPGroup'.to_le hVP)
  have hdvd : 2 ^ a ∣ 2 ^ 10 := by
    have h1 : 2 ^ a ∣ 3 * 2 ^ 10 := by
      rw [← ha, ← hc.card_M]
      exact Subgroup.card_dvd_of_le hVM
    rw [mul_comm] at h1
    exact (Nat.Coprime.pow_left a (by norm_num : Nat.Coprime 2 3)).dvd_of_dvd_mul_right h1
  have hle : Nat.card ↥(ctxU t tau x₁ x₂ lam ⊔ zpowers n) ≤ Nat.card ↥(ctxU t tau x₁ x₂ lam) := by
    rw [ha, c13K_card_U hc]
    exact Nat.le_of_dvd (by positivity) hdvd
  have hEq := Subgroup.eq_of_le_of_card_ge (le_sup_left : ctxU t tau x₁ x₂ lam ≤
    ctxU t tau x₁ x₂ lam ⊔ zpowers n) hle
  exact hnnU (hEq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers n))

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
