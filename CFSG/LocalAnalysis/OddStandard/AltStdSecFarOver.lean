module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecFarSecPerm

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup Equiv Equiv.Perm CFSG.Permutation.SymmetricCoxeter

structure OverData (G : Type*) [Group G] (z : G) (m : ℕ) where
  D : NearData z (m + 1)
  M : Subgroup G
  eM : Perm (Fin (m + 3)) ≃* M
  hC : centralizer ({z} : Set G) ≤ M
  hz : (eM (adjSwap (m + 2) (m + 1)) : G) = z
  hcompat : ∀ σ : Perm (Fin (m + 1)), (eM (inclPerm m σ) : G) = D.ι σ
  hconj : ∀ ρ : Perm (Fin (m + 3)), ρ.IsSwap → IsConj z (eM ρ : G)

namespace OverData

variable {G : Type*} [Group G] {z : G} {m : ℕ} (O : OverData G z m)

@[expose] noncomputable def φ : Perm (Fin (m + 3)) →* G := O.M.subtype.comp O.eM.toMonoidHom

theorem φ_apply (x : Perm (Fin (m + 3))) : O.φ x = (O.eM x : G) := rfl

theorem φ_injective : Function.Injective O.φ := Subtype.coe_injective.comp O.eM.injective

theorem φ_mem (x : Perm (Fin (m + 3))) : O.φ x ∈ O.M := (O.eM x).2

@[expose] def tau (m : ℕ) : Perm (Fin (m + 3)) := swap ⟨m + 1, by omega⟩ ⟨m + 2, by omega⟩

theorem tau_eq : tau m = adjSwap (m + 2) (m + 1) := by
  rw [adjSwap_of_lt (by omega)]; rfl

theorem φ_tau : O.φ (tau m) = z := by rw [tau_eq]; exact O.hz

theorem exists_eq_φ {g : G} (hg : g ∈ O.M) : ∃ x, O.φ x = g :=
  ⟨O.eM.symm ⟨g, hg⟩, by rw [φ_apply, MulEquiv.apply_symm_apply]⟩

theorem φ_comm_iff {x y : Perm (Fin (m + 3))} : O.φ x * O.φ y = O.φ y * O.φ x ↔ x * y = y * x := by
  rw [← map_mul, ← map_mul]
  exact O.φ_injective.eq_iff

theorem centralizer_conj_le {g : G} (hg : g ∈ O.M) :
    centralizer ({g * z * g⁻¹} : Set G) ≤ O.M := by
  intro x hx
  have h1 : g⁻¹ * x * g ∈ centralizer ({z} : Set G) := by
    rw [mem_centralizer_singleton_iff] at hx ⊢
    calc g⁻¹ * x * g * z = g⁻¹ * (x * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * z * g⁻¹) * x) * g := by rw [hx]
      _ = z * (g⁻¹ * x * g) := by group
  have h2 := O.hC h1
  have : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
  rw [this]
  exact mul_mem (mul_mem hg h2) (inv_mem hg)

theorem centralizer_φ_conj_le (γ : Perm (Fin (m + 3))) :
    centralizer ({O.φ (γ * tau m * γ⁻¹)} : Set G) ≤ O.M := by
  rw [map_mul, map_mul, map_inv, O.φ_tau]
  exact O.centralizer_conj_le (O.φ_mem γ)

theorem exists_of_mem_centralizer_z {g : G} (hg : g ∈ centralizer ({z} : Set G)) :
    ∃ x : Perm (Fin (m + 3)), O.φ x = g ∧ x * tau m = tau m * x := by
  obtain ⟨x, rfl⟩ := O.exists_eq_φ (O.hC hg)
  refine ⟨x, rfl, ?_⟩
  rw [← O.φ_comm_iff, O.φ_tau]
  exact mem_centralizer_singleton_iff.1 hg

theorem eq_one_of_isConj_mul {r : Perm (Fin (m + 3))}
    (h1 : r ⟨m + 1, by omega⟩ = ⟨m + 1, by omega⟩) (h2 : r ⟨m + 2, by omega⟩ = ⟨m + 2, by omega⟩)
    (hsupp : r.support.card + 7 ≤ m + 1) (hns : ¬ r.IsSwap) (hconj : IsConj z (z * O.φ r)) :
    r = 1 := by
  classical
  by_contra hr1
  obtain ⟨r', hr'⟩ := exists_inclPerm_eq h1 h2
  have hφr : O.φ r = O.D.ι r' := by rw [← hr', φ_apply, O.hcompat]
  have hmemC : z * O.φ r ∈ centralizer ({z} : Set G) := by
    rw [hφr]
    exact mul_mem (NearData.self_mem_centralizer z) (O.D.ι_mem r')
  have hne : z * O.φ r ≠ z := by
    intro h
    apply hr1
    apply O.φ_injective
    rw [map_one]
    calc O.φ r = z⁻¹ * (z * O.φ r) := by group
      _ = 1 := by rw [h, inv_mul_cancel]
  have hP : z * O.φ r ∈ Partners z := ⟨hconj, hne, mem_centralizer_singleton_iff.1 hmemC⟩
  have hπ : O.D.π ⟨z * O.φ r, hmemC⟩ = r' := by
    have : (⟨z * O.φ r, hmemC⟩ : centralizer ({z} : Set G)) =
        ⟨z, NearData.self_mem_centralizer z⟩ * ⟨O.D.ι r', O.D.ι_mem r'⟩ :=
      Subtype.ext (show z * O.φ r = z * (O.D.ι r' : G) by rw [hφr])
    rw [this, O.D.π_z_mul, O.D.π_ι]
  have hsupp' : r'.support.card + 7 ≤ m + 1 := by
    have := Perm.card_support_extend_domain (finIncl m) (g := r')
    rw [show r'.extendDomain (finIncl m) = r from hr'] at this
    omega
  have hns' : ¬ r'.IsSwap := fun h => hns (by rw [← hr']; exact inclPerm_isSwap h)
  have hnear : IsNearPerm (O.D.π ⟨z * O.φ r, hmemC⟩) := by
    rw [hπ]
    have := NearData.fixFin_card_add_support_card r'
    constructor <;> omega
  have := (O.D.near _ hP hnear).1
  rw [hπ] at this
  exact hns' this

end OverData

end CFSG.OddStandard.AltStdSec
