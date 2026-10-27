module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.AltCocycle

public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0

open CFSG.RankThree.PartTwo CFSG.HardMathSupport.Cooperstein.Coordinator Equiv Equiv.Perm

variable {N : ℕ} {W : Type*} [AddCommGroup W] {M : Type*} [Group M]

structure PiFrame (θ : M →* Perm (Fin N)) (ρ : M →* AddMonoid.End W) (U : AddSubgroup W)
    (π : U →+ altHeart N) (L S : Subgroup M) : Prop where
  two : ∀ w : W, w + w = 0
  ker : ∀ m : M, θ m = 1 → ρ m = 1
  stable : ∀ (m : M), ∀ u ∈ U, ρ m u ∈ U
  equiv : ∀ (m : M) (u : U), π ⟨ρ m u, stable m u u.2⟩ = altAct (θ m) (π u)
  surj : Function.Surjective π
  alt : ∀ σ ∈ alternatingGroup (Fin N), ∃ l ∈ L, θ l = σ
  lTriv : ∀ l ∈ L, ∀ w : W, ρ l w - w ∈ U
  sTriv : ∀ s ∈ S, ∀ w : W, ρ s w - w ∈ U
  sK : ∀ s ∈ S, ∀ u : U, π u = 0 → ρ s u = u

variable {θ : M →* Perm (Fin N)} {ρ : M →* AddMonoid.End W} {U : AddSubgroup W}
  {π : U →+ altHeart N} {L S : Subgroup M}

namespace PiFrame

theorem sub_mem_U (F : PiFrame θ ρ U π L S) (m : M) {u : W} (hu : u ∈ U) : ρ m u - u ∈ U :=
  U.sub_mem (F.stable m u hu) hu

theorem pi_sub (F : PiFrame θ ρ U π L S) (m : M) (u : U) :
    π ⟨ρ m u - u, F.sub_mem_U m u.2⟩ = altAct (θ m) (π u) - π u := by
  have : (⟨ρ m u - u, F.sub_mem_U m u.2⟩ : U) = ⟨ρ m u, F.stable m u u.2⟩ - u := rfl
  rw [this, map_sub, F.equiv]

theorem comm (F : PiFrame θ ρ U π L S) {m n : M} (h : θ m * θ n = θ n * θ m) :
    ρ m * ρ n = ρ n * ρ m := by
  have h1 : θ ((n * m)⁻¹ * (m * n)) = 1 := by
    rw [map_mul, map_inv, map_mul, map_mul, h]; group
  have h2 := F.ker _ h1
  have h3 : ρ (m * n) = ρ (n * m) := by
    have e : m * n = (n * m) * ((n * m)⁻¹ * (m * n)) := by group
    rw [e, map_mul ρ (n * m), h2, mul_one]
  rw [← map_mul, ← map_mul, h3]

end PiFrame

theorem altHeartCoord_rebase {n : ℕ} (k r : Fin n) (v : altHeart n) (j : Fin n) :
    altHeartCoord k v j = altHeartCoord r v j + altHeartCoord r v k := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective v
  rw [altHeartCoord_mk, altHeartCoord_mk, altHeartCoord_mk]
  generalize (x : Fin n → ZMod 2) j = a
  generalize (x : Fin n → ZMod 2) k = b
  generalize (x : Fin n → ZMod 2) r = c
  revert a b c
  decide

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0
