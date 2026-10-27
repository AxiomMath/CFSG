module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSixE32Perm
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxEightD
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveN

public section

namespace CFSG.ComponentClassification.SolMax.Sig36.E32

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

open Classical in
@[expose] noncomputable def rhoX {M : Subgroup X} (ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 9))
    (x : X) : Perm (Fin 9) :=
  if h : x ∈ normalizer (M : Set X) then ρ ⟨x, h⟩ else 1

section rhoX

variable {M : Subgroup X} {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 9)}

theorem rhoX_of_mem {x : X} (hx : x ∈ normalizer (M : Set X)) : rhoX ρ x = ρ ⟨x, hx⟩ := by
  unfold rhoX
  rw [dif_pos hx]

theorem rhoX_mul {x y : X} (hx : x ∈ normalizer (M : Set X)) (hy : y ∈ normalizer (M : Set X)) :
    rhoX ρ (x * y) = rhoX ρ x * rhoX ρ y := by
  rw [rhoX_of_mem hx, rhoX_of_mem hy, rhoX_of_mem (mul_mem hx hy)]
  exact map_mul ρ ⟨x, hx⟩ ⟨y, hy⟩

theorem rhoX_one : rhoX ρ (1 : X) = 1 := by
  rw [rhoX_of_mem (one_mem _)]
  exact map_one ρ

theorem rhoX_inv {x : X} (hx : x ∈ normalizer (M : Set X)) : rhoX ρ x⁻¹ = (rhoX ρ x)⁻¹ := by
  rw [rhoX_of_mem hx, rhoX_of_mem (inv_mem hx)]
  exact map_inv ρ ⟨x, hx⟩

theorem rhoX_conj {g x : X} (hg : g ∈ normalizer (M : Set X)) (hx : x ∈ normalizer (M : Set X)) :
    rhoX ρ (g * x * g⁻¹) = rhoX ρ g * rhoX ρ x * (rhoX ρ g)⁻¹ := by
  rw [rhoX_mul (mul_mem hg hx) (inv_mem hg), rhoX_mul hg hx, rhoX_inv hg]

end rhoX

structure Ctx [Finite X] (M : Subgroup X)
    (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 9))
    (ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 9)) (t s : X) (H Q : Subgroup X) : Prop where
  hρ : IsPermAction θ ρ
  hHN : H ≤ normalizer (M : Set X)
  hCt : centralizer ({t} : Set X) ≤ H
  ht2 : t * t = 1
  ht1 : t ≠ 1
  hsH : s ∈ H
  hs2 : s * s = 1
  hst : s * t = t * s
  hρs : rhoX ρ s = σ₀
  hQK : Q ≤ H ⊓ UnbalancedLayer.coreActionKernel M
  hQ2 : IsPGroup 2 Q
  hQcard : Nat.card Q = 2 ^ (Nat.card ↥(H ⊓ UnbalancedLayer.coreActionKernel M)).factorization 2
  htQ : t ∈ Q
  hQt : ∀ q ∈ Q, q * t = t * q
  hsQ : s ∉ Q
  hsNQ : s ∈ normalizer (Q : Set X)
  hR : Q ⊓ centralizer ({s} : Set X) ≤ zpowers t
  hy : ∃ y ∈ Q, y * y = 1 ∧ y ≠ 1 ∧ y ≠ t

namespace Ctx

variable [Finite X] {M : Subgroup X} {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 9)}
  {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 9)} {t s : X} {H Q : Subgroup X}
  (Z : Ctx M θ ρ t s H Q)
include Z

theorem mem_normalizer_of_mem_C {x : X} (hx : x ∈ centralizer ({t} : Set X)) :
    x ∈ normalizer (M : Set X) := Z.hHN (Z.hCt hx)

theorem t_mem_C : t ∈ centralizer ({t} : Set X) := mem_centralizer_singleton_iff.mpr rfl

theorem s_mem_C : s ∈ centralizer ({t} : Set X) :=
  mem_centralizer_singleton_iff.mpr Z.hst

theorem t_mem_N : t ∈ normalizer (M : Set X) := Z.mem_normalizer_of_mem_C Z.t_mem_C

theorem s_mem_N : s ∈ normalizer (M : Set X) := Z.mem_normalizer_of_mem_C Z.s_mem_C

theorem rho_t : rhoX ρ t = 1 := by
  rw [rhoX_of_mem Z.t_mem_N]
  exact IsPermAction.eq_one_of_mem_coreActionKernel Z.hρ (by norm_num)
    (Z.hQK Z.htQ).2

theorem rho_mem_alt {m : X} (hm : m ∈ M) : rhoX ρ m ∈ alternatingGroup (Fin 9) := by
  rw [rhoX_of_mem (le_normalizer hm), Z.hρ.apply_of_mem (by norm_num) ⟨m, hm⟩]
  exact (θ _).2

private theorem orderOf_t : orderOf t = 2 :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  orderOf_eq_prime (by rw [pow_two]; exact Z.ht2) Z.ht1

private theorem isPGroup_zpowers_t : IsPGroup 2 (zpowers t) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Z.orderOf_t, pow_one])

private theorem rhoX_eq_one_of_mem_zpowers {g : X} (hg : g ∈ zpowers t) : rhoX ρ g = 1 := by
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

private theorem exists_rho_even (π : Perm (Fin 9)) (hπ : π ∈ alternatingGroup (Fin 9)) :
    ∃ c ∈ M, c ∈ centralizer ({t} : Set X) ∧ rhoX ρ c = π := by
  have hBN : zpowers t ≤ normalizer (M : Set X) := zpowers_le.mpr Z.t_mem_N
  obtain ⟨x, hxC, hxθ⟩ := Z.hρ.exists_lift_of_isPGroup (b := ⟨π, hπ⟩) hBN Z.isPGroup_zpowers_t
    (fun g hg => by
      have h1 : ρ ⟨g, hBN hg⟩ = 1 := by
        rw [← rhoX_of_mem (hBN hg)]
        exact Z.rhoX_eq_one_of_mem_zpowers hg
      rw [h1, mul_one, one_mul])
  refine ⟨x, x.2, centralizer_le (Set.singleton_subset_iff.mpr (mem_zpowers t)) hxC, ?_⟩
  rw [rhoX_of_mem (le_normalizer x.2), Z.hρ.apply_of_mem (by norm_num) x, hxθ]

theorem exists_rho_surj (π : Perm (Fin 9)) :
    ∃ c ∈ centralizer ({t} : Set X), rhoX ρ c = π := by
  by_cases hπ : π ∈ alternatingGroup (Fin 9)
  · obtain ⟨c, -, hcC, hc⟩ := Z.exists_rho_even π hπ
    exact ⟨c, hcC, hc⟩
  · have hσ : Perm.sign σ₀ = -1 := by
      have h := σ₀_not_mem_alt
      rw [Perm.mem_alternatingGroup] at h
      exact (Int.units_eq_one_or _).resolve_left h
    have hπ' : Perm.sign π = -1 := by
      rw [Perm.mem_alternatingGroup] at hπ
      exact (Int.units_eq_one_or _).resolve_left hπ
    have hev : π * σ₀ ∈ alternatingGroup (Fin 9) := by
      rw [Perm.mem_alternatingGroup, map_mul, hπ', hσ]
      decide
    obtain ⟨y, hyM, hyC, hy⟩ := Z.exists_rho_even _ hev
    refine ⟨y * s, mul_mem hyC Z.s_mem_C, ?_⟩
    rw [rhoX_mul (le_normalizer hyM) Z.s_mem_N, hy, Z.hρs, mul_assoc, σ₀_mul_self, mul_one]

theorem t_not_mem_M : t ∉ M := by
  intro htM
  have h1 : ρ ⟨t, le_normalizer htM⟩ = 1 :=
    (rhoX_of_mem Z.t_mem_N).symm.trans Z.rho_t
  have hodd := odd_orderOf_of_rho_eq_one Z.hρ htM h1
  rw [Z.orderOf_t] at hodd
  exact absurd hodd (by decide)

end Ctx

@[expose] def N0 (M : Subgroup X) (t : X) : Subgroup X :=
  centralizer ({t} : Set X) ⊓ (M ⊓ UnbalancedLayer.coreActionKernel M)

namespace Ctx

variable [Finite X] {M : Subgroup X} {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 9)}
  {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 9)} {t s : X} {H Q : Subgroup X}
  (Z : Ctx M θ ρ t s H Q)
include Z

theorem N0_odd : Odd (Nat.card (N0 M t)) := by
  refine odd_card_of_forall_mem_odd_orderOf fun n hn => ?_
  simp only [N0, Subgroup.mem_inf] at hn
  obtain ⟨-, hnM, hnK⟩ := hn
  exact odd_orderOf_of_rho_eq_one Z.hρ hnM (Z.hρ.eq_one_of_mem_coreActionKernel (by norm_num) hnK)

theorem N0_conj {c n : X} (hc : c ∈ centralizer ({t} : Set X)) (hn : n ∈ N0 M t) :
    c * n * c⁻¹ ∈ N0 M t := by
  simp only [N0, Subgroup.mem_inf] at hn ⊢
  obtain ⟨hnC, hnM, hnK⟩ := hn
  have hcN : c ∈ normalizer (M : Set X) := Z.mem_normalizer_of_mem_C hc
  exact ⟨mul_mem (mul_mem hc hnC) (inv_mem hc), (mem_normalizer_iff.mp hcN n).mp hnM,
    Z.hρ.conj_mem_coreActionKernel (by norm_num) hcN hnK⟩

theorem mem_N0 {z : X} (hzM : z ∈ M) (hzC : z ∈ centralizer ({t} : Set X))
    (h1 : rhoX ρ z = 1) : z ∈ N0 M t := by
  simp only [N0, Subgroup.mem_inf]
  exact ⟨hzC, hzM, Z.hρ.mem_coreActionKernel (le_normalizer hzM)
    ((rhoX_of_mem (le_normalizer hzM)).symm.trans h1)⟩

theorem rhoX_pow {x : X} (hx : x ∈ normalizer (M : Set X)) (n : ℕ) :
    rhoX ρ (x ^ n) = rhoX ρ x ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, rhoX_one]
  | succ n ih => rw [pow_succ, pow_succ, rhoX_mul (pow_mem hx n) hx, ih]

end Ctx

end CFSG.ComponentClassification.SolMax.Sig36.E32
