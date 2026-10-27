module

public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoShape3Roots
public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoShape3Sigma
public import CFSG.LocalAnalysis.OddStandard.AltStdSecSylowModel
public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoDefs

public section

namespace CFSG.OddStandard.AltStdCycTwo

open Subgroup Equiv
open AltStdBal (Cyc rho_of_mem)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z : G}

namespace Shape3

theorem false_of_shape_three (hS : StandardSetting G L) (θ : L ≃* alternatingGroup (Fin n))
    (hn : 8 ≤ n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2) {u : G}
    (hu : u ∈ centralizer ({z} : Set G)) (huO : u ∉ L ⊔ centralizer (L : Set G))
    (hu2 : u ^ 2 = z) : False := by
  obtain ⟨R, hRC, hR, hRmax⟩ :=
    AltStdBal.exists_maximal_two_subgroup (centralizer ({z} : Set G))
  have hzR : z ∈ R := AltStdBal.mem_of_maximal d hRC hR hRmax
  obtain ⟨x, y₀, hx, hx', hy₀R, hy₀L, hy₀ne, hy₀sq, hy₀c, hxz⟩ :=
    exists_growth hS θ hn d hQ2 hu huO hu2 hRC hR hRmax
  have hyz : y₀ * z = z * y₀ := mem_centralizer_singleton_iff.1 (le_cent_single hS d hy₀L)
  have h1 := AltStdSec.card_roots_conj hx hx' z
  rw [hxz, hyz] at h1
  have e1 : Nat.card {r : R // (r : G) ^ 2 = z} =
      2 * Nat.card {s : (rhoR hS θ hn d R hRC).range //
        Perm.sign (s : Perm (Fin n)) = -1 ∧ (s : Perm (Fin n)) ^ 2 = 1} := by
    have := card_roots_eq_two_mul hS θ hn d hQ2 hu huO hu2 hRC hR hzR (1 : L)
    simpa using this
  have e2 : Nat.card {r : R // (r : G) ^ 2 = z * y₀} =
      2 * Nat.card {s : (rhoR hS θ hn d R hRC).range //
        Perm.sign (s : Perm (Fin n)) = -1 ∧
          (s : Perm (Fin n)) ^ 2 = ((θ ⟨y₀, hy₀L⟩ : alternatingGroup (Fin n)) : Perm (Fin n))} :=
    card_roots_eq_two_mul hS θ hn d hQ2 hu huO hu2 hRC hR hzR ⟨y₀, hy₀L⟩
  obtain ⟨hP2, hPmax⟩ := range_rhoR_maximal hS θ hn d hu huO hRC hR hRmax
  have hρy : rhoR hS θ hn d R hRC ⟨y₀, hy₀R⟩ =
      ((θ ⟨y₀, hy₀L⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) :=
    rho_of_mem θ hn ⟨y₀, hy₀L⟩ (Subgroup.le_normalizer hy₀L)
  have hlt := AltStdSec.oddRootCount_of_le n hn _ hP2 hPmax
    ((θ ⟨y₀, hy₀L⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) ⟨⟨y₀, hy₀R⟩, hρy⟩
    (by
      rintro s ⟨r, rfl⟩
      rw [← hρy, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hy₀c r r.2))
    (Equiv.Perm.mem_alternatingGroup.1 (θ ⟨y₀, hy₀L⟩).2)
    (by
      intro h0
      apply hy₀ne
      have h2 : θ ⟨y₀, hy₀L⟩ = 1 := Subtype.ext (by simpa using h0)
      have h3 : (⟨y₀, hy₀L⟩ : L) = 1 := θ.injective (by simpa using h2)
      exact congrArg Subtype.val h3)
    (by
      have h2 : θ ⟨y₀, hy₀L⟩ * θ ⟨y₀, hy₀L⟩ = 1 := by
        rw [← map_mul, ← map_one θ]
        congr 1
        exact Subtype.ext hy₀sq
      exact congrArg Subtype.val h2)
  omega

end Shape3

theorem cycTwoShapeThreeFalse_holds : CycTwoShapeThreeFalse := by
  intro G _ _ L Q n θ z u hT hu huO hu2
  exact Shape3.false_of_shape_three hT.std θ (by have := hT.hn; omega) hT.cyc hT.card hu huO hu2

end CFSG.OddStandard.AltStdCycTwo
