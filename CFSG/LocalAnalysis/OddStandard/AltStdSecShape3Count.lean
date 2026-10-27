module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecShape3Roots
public import CFSG.LocalAnalysis.OddStandard.AltStdSecShape3Sigma
public import CFSG.LocalAnalysis.OddStandard.AltStdSecSylowDef

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup Equiv CFSG.OddStandard.AltStdBal

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z : G}

theorem false_of_shape_three_of_count (hcount : OddRootCount n) (h : Setting G L n)
    (d : Cyc L Q z) (hQ2 : Nat.card Q = 2) {u : G} (hu : u ∈ centralizer ({z} : Set G))
    (huL : u ∉ L ⊔ Q) (hu2 : u ^ 2 = z) : False := by
  obtain ⟨e⟩ := h.iso
  obtain ⟨R, hRC, hR, hRmax⟩ := exists_maximal_two_subgroup (centralizer ({z} : Set G))
  have hzR : z ∈ R := mem_of_maximal d hRC hR hRmax
  obtain ⟨x, y₀, hx, hx', hy₀R, hy₀L, hy₀ne, hy₀sq, hy₀c, hxz⟩ :=
    exists_growth_shape3 h d hQ2 hu huL hu2 hRC hR hRmax
  have hyz : y₀ * z = z * y₀ :=
    mem_centralizer_singleton_iff.1 (le_centralizer_single h d hy₀L)
  have h1 := card_roots_conj hx hx' z
  rw [hxz, hyz] at h1
  have e1 : Nat.card {r : R // (r : G) ^ 2 = z} =
      2 * Nat.card {s : (rhoR e h d R hRC).range //
        Perm.sign (s : Perm (Fin n)) = -1 ∧ (s : Perm (Fin n)) ^ 2 = 1} := by
    have := card_roots_eq_two_mul e h d hQ2 hu huL hu2 hRC hzR (1 : L)
    simpa using this
  have e2 : Nat.card {r : R // (r : G) ^ 2 = z * y₀} =
      2 * Nat.card {s : (rhoR e h d R hRC).range //
        Perm.sign (s : Perm (Fin n)) = -1 ∧
          (s : Perm (Fin n)) ^ 2 = ((e ⟨y₀, hy₀L⟩ : alternatingGroup (Fin n)) : Perm (Fin n))} :=
    card_roots_eq_two_mul e h d hQ2 hu huL hu2 hRC hzR ⟨y₀, hy₀L⟩
  obtain ⟨hP2, hPmax⟩ := range_rhoR_maximal e h d hQ2 hu huL hRC hR hRmax
  have hρy : rhoR e h d R hRC ⟨y₀, hy₀R⟩ =
      ((e ⟨y₀, hy₀L⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) :=
    rho_of_mem e h.hn ⟨y₀, hy₀L⟩ (Subgroup.le_normalizer hy₀L)
  have hlt := hcount _ hP2 hPmax ((e ⟨y₀, hy₀L⟩ : alternatingGroup (Fin n)) : Perm (Fin n))
    ⟨⟨y₀, hy₀R⟩, hρy⟩
    (by
      rintro s ⟨r, rfl⟩
      rw [← hρy]
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hy₀c r r.2))
    (Equiv.Perm.mem_alternatingGroup.1 (e ⟨y₀, hy₀L⟩).2)
    (by
      intro h0
      apply hy₀ne
      have h2 : e ⟨y₀, hy₀L⟩ = 1 := Subtype.ext (by simpa using h0)
      have h3 : (⟨y₀, hy₀L⟩ : L) = 1 := e.injective (by simpa using h2)
      exact congrArg Subtype.val h3)
    (by
      have h2 : e ⟨y₀, hy₀L⟩ * e ⟨y₀, hy₀L⟩ = 1 := by
        rw [← map_mul, ← map_one e]
        congr 1
        exact Subtype.ext hy₀sq
      exact congrArg Subtype.val h2)
  omega

end CFSG.OddStandard.AltStdSec
