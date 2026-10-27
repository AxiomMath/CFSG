module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSixE32Frame
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSixE32Frat

public section

namespace CFSG.ComponentClassification.SolMax.Sig36.E32

open CFSG Subgroup Equiv

variable {X : Type} [Group X] [Finite X] {M : Subgroup X}
  {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 9)}
  {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 9)} {t s : X} {H Q : Subgroup X}

private theorem isPGroup_zpowers_t' (Z : Ctx M θ ρ t s H Q) : IsPGroup 2 (zpowers t) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact Z.ht2) Z.ht1
  exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h2, pow_one])

private theorem rhoX_eq_one_of_mem_zpowers' (Z : Ctx M θ ρ t s H Q) {g : X}
    (hg : g ∈ zpowers t) : rhoX ρ g = 1 := by
  have hk : (⟨t, Z.t_mem_N⟩ : ↥(normalizer (M : Set X))) ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, ← rhoX_of_mem Z.t_mem_N]
    exact Z.rho_t
  have h1 : zpowers t ≤ ρ.ker.map (normalizer (M : Set X)).subtype :=
    zpowers_le.mpr ⟨_, hk, rfl⟩
  obtain ⟨k, hk', hkg⟩ := h1 hg
  have hkg' : (k : X) = g := hkg
  subst hkg'
  rw [rhoX_of_mem k.2]
  exact MonoidHom.mem_ker.mp hk'

private theorem exists_lift_even (Z : Ctx M θ ρ t s H Q) (π : Perm (Fin 9))
    (hπ : π ∈ alternatingGroup (Fin 9)) :
    ∃ c ∈ M, c ∈ centralizer ({t} : Set X) ∧ rhoX ρ c = π := by
  have hBN : zpowers t ≤ normalizer (M : Set X) := zpowers_le.mpr Z.t_mem_N
  obtain ⟨x, hxC, hxθ⟩ := Z.hρ.exists_lift_of_isPGroup (b := ⟨π, hπ⟩) hBN
    (isPGroup_zpowers_t' Z)
    (fun g hg => by
      have h1 : ρ ⟨g, hBN hg⟩ = 1 := by
        rw [← rhoX_of_mem (hBN hg)]
        exact rhoX_eq_one_of_mem_zpowers' Z hg
      rw [h1, mul_one, one_mul])
  refine ⟨x, x.2, centralizer_le (Set.singleton_subset_iff.mpr (mem_zpowers t)) hxC, ?_⟩
  rw [rhoX_of_mem (le_normalizer x.2), Z.hρ.apply_of_mem (by norm_num) x, hxθ]

private theorem C_le_normalizer_N0 (Z : Ctx M θ ρ t s H Q) {c : X}
    (hc : c ∈ centralizer ({t} : Set X)) : c ∈ normalizer (N0 M t : Set X) := by
  refine mem_normalizer_iff.mpr fun n => ⟨fun hn => Z.N0_conj hc hn, fun h => ?_⟩
  have h1 := Z.N0_conj (inv_mem hc) h
  have e : c⁻¹ * (c * n * c⁻¹) * c⁻¹⁻¹ = n := by group
  rwa [e] at h1

namespace IsFrame

variable {Z : Ctx M θ ρ t s H Q} {w₀ w₁ x : X} (F : IsFrame Z w₀ w₁ x)
include F

private theorem rhoX_aF (i : Fin 4) : rhoX ρ (aF s w₀ w₁ x i) = p i := by
  have hs := Z.s_mem_N
  have h0 : w₀ ∈ normalizer (M : Set X) := le_normalizer F.w₀M
  have h1 : w₁ ∈ normalizer (M : Set X) := le_normalizer F.w₁M
  have hx : x ∈ normalizer (M : Set X) := le_normalizer F.xM
  fin_cases i
  · change rhoX ρ (s * w₀) = p 0
    rw [rhoX_mul hs h0, Z.hρs, F.ρw₀]
    decide
  · change rhoX ρ (s * w₁) = p 1
    rw [rhoX_mul hs h1, Z.hρs, F.ρw₁]
    decide
  · change rhoX ρ (s * (w₀ * w₁)) = p 2
    rw [rhoX_mul hs (mul_mem h0 h1), rhoX_mul h0 h1, Z.hρs, F.ρw₀, F.ρw₁]
    decide
  · change rhoX ρ (s * x) = p 3
    rw [rhoX_mul hs hx, Z.hρs, F.ρx]
    decide

private theorem aF_mem_C (i : Fin 4) : aF s w₀ w₁ x i ∈ centralizer ({t} : Set X) := by
  have h0 : w₀ ∈ centralizer ({t} : Set X) := mem_centralizer_singleton_iff.mpr (F.E5.comm 2 1)
  have h1 : w₁ ∈ centralizer ({t} : Set X) := mem_centralizer_singleton_iff.mpr (F.E5.comm 3 1)
  have hx : x ∈ centralizer ({t} : Set X) := mem_centralizer_singleton_iff.mpr (F.E5.comm 4 1)
  fin_cases i
  · exact mul_mem Z.s_mem_C h0
  · exact mul_mem Z.s_mem_C h1
  · exact mul_mem Z.s_mem_C (mul_mem h0 h1)
  · exact mul_mem Z.s_mem_C hx

private theorem inv_s_mul_aF_mem (i : Fin 4) : s⁻¹ * aF s w₀ w₁ x i ∈ M := by
  fin_cases i
  · change s⁻¹ * (s * w₀) ∈ M
    rw [inv_mul_cancel_left]
    exact F.w₀M
  · change s⁻¹ * (s * w₁) ∈ M
    rw [inv_mul_cancel_left]
    exact F.w₁M
  · change s⁻¹ * (s * (w₀ * w₁)) ∈ M
    rw [inv_mul_cancel_left]
    exact mul_mem F.w₀M F.w₁M
  · change s⁻¹ * (s * x) ∈ M
    rw [inv_mul_cancel_left]
    exact F.xM

private theorem ratio_mem_N0 (α : Perm (Fin 4)) {y : X} (hyM : y ∈ M)
    (hyC : y ∈ centralizer ({t} : Set X)) (hyρ : rhoX ρ y = hat α) (i : Fin 4) :
    (aF s w₀ w₁ x (α i))⁻¹ * (y * aF s w₀ w₁ x i * y⁻¹) ∈ N0 M t := by
  have hyN : y ∈ normalizer (M : Set X) := le_normalizer hyM
  have hsN := Z.s_mem_N
  have haN : ∀ j, aF s w₀ w₁ x j ∈ normalizer (M : Set X) := fun j =>
    Z.mem_normalizer_of_mem_C (F.aF_mem_C j)
  refine Z.mem_N0 ?_ ?_ ?_
  · have e : (aF s w₀ w₁ x (α i))⁻¹ * (y * aF s w₀ w₁ x i * y⁻¹) =
        (s⁻¹ * aF s w₀ w₁ x (α i))⁻¹ * (s⁻¹ * y * s) * (s⁻¹ * aF s w₀ w₁ x i) * y⁻¹ := by
      group
    rw [e]
    have hconj : s⁻¹ * y * s ∈ M := by
      have h := (mem_normalizer_iff.mp (inv_mem hsN) y).mp hyM
      rwa [inv_inv] at h
    exact mul_mem (mul_mem (mul_mem (inv_mem (F.inv_s_mul_aF_mem (α i))) hconj)
      (F.inv_s_mul_aF_mem i)) (inv_mem hyM)
  · exact mul_mem (inv_mem (F.aF_mem_C (α i)))
      (mul_mem (mul_mem hyC (F.aF_mem_C i)) (inv_mem hyC))
  · rw [rhoX_mul (inv_mem (haN (α i))) (mul_mem (mul_mem hyN (haN i)) (inv_mem hyN)),
      rhoX_inv (haN (α i)), rhoX_conj hyN (haN i), F.rhoX_aF, F.rhoX_aF, hyρ, hat_conj,
      inv_mul_cancel]

theorem exists_symm (α : Perm (Fin 4)) :
    ∃ c ∈ centralizer ({t} : Set X), c * t * c⁻¹ = t ∧
      ∀ i, c * aF s w₀ w₁ x i * c⁻¹ = aF s w₀ w₁ x (α i) := by
  obtain ⟨y, hyM, hyC, hyρ⟩ := exists_lift_even Z (hat α) (hat_mem_alt α)
  set A : Subgroup X := Subgroup.closure (Set.range (aF s w₀ w₁ x)) with hA
  have hAC : A ≤ centralizer ({t} : Set X) := by
    rw [hA, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact F.aF_mem_C i
  have hA2 : IsPGroup 2 A := by
    refine F.E5.isPGroup_closure.to_le ?_
    rw [hA, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    have hs' : s ∈ Subgroup.closure (Set.range ![s, t, w₀, w₁, x]) :=
      Subgroup.subset_closure ⟨0, rfl⟩
    have h0 : w₀ ∈ Subgroup.closure (Set.range ![s, t, w₀, w₁, x]) :=
      Subgroup.subset_closure ⟨2, rfl⟩
    have h1 : w₁ ∈ Subgroup.closure (Set.range ![s, t, w₀, w₁, x]) :=
      Subgroup.subset_closure ⟨3, rfl⟩
    have hx : x ∈ Subgroup.closure (Set.range ![s, t, w₀, w₁, x]) :=
      Subgroup.subset_closure ⟨4, rfl⟩
    fin_cases i
    · exact mul_mem hs' h0
    · exact mul_mem hs' h1
    · exact mul_mem hs' (mul_mem h0 h1)
    · exact mul_mem hs' hx
  have haA : ∀ i, aF s w₀ w₁ x i ∈ A := fun i => Subgroup.subset_closure ⟨i, rfl⟩
  have hyA : ∀ a ∈ A, y * a * y⁻¹ ∈ A ⊔ N0 M t := by
    have hle : A ≤ (A ⊔ N0 M t).comap (MulAut.conj y).toMonoidHom := by
      rw [hA, Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      have e : (MulAut.conj y).toMonoidHom (aF s w₀ w₁ x i) =
          aF s w₀ w₁ x (α i) *
            ((aF s w₀ w₁ x (α i))⁻¹ * (y * aF s w₀ w₁ x i * y⁻¹)) := by
        simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply]
        group
      rw [e]
      exact mul_mem (Subgroup.mem_sup_left (haA _))
        (Subgroup.mem_sup_right (F.ratio_mem_N0 α hyM hyC hyρ i))
    intro a ha
    have h := hle ha
    rwa [Subgroup.mem_comap, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      MulAut.conj_apply] at h
  obtain ⟨n, hn, -, hfix⟩ := exists_mul_normalizes_of_odd hA2 Z.N0_odd
    (fun a ha => C_le_normalizer_N0 Z (hAC ha)) (C_le_normalizer_N0 Z hyC) hyA
  have hnC : n ∈ centralizer ({t} : Set X) := (Subgroup.mem_inf.mp hn).1
  have hcC : y * n ∈ centralizer ({t} : Set X) := mul_mem hyC hnC
  refine ⟨y * n, hcC, ?_, fun i => hfix _ (haA i) _ (haA (α i)) (F.ratio_mem_N0 α hyM hyC hyρ i)⟩
  have h := mem_centralizer_singleton_iff.mp hcC
  rw [h, mul_inv_cancel_right]

end IsFrame

end CFSG.ComponentClassification.SolMax.Sig36.E32
