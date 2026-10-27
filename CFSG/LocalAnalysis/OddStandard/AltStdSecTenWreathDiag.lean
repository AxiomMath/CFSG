module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSwapTwist
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSwapReps
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenWreathPerm

public section

namespace CFSG.OddStandard.AltStdSec.SwapPattern

open Subgroup Equiv Equiv.Perm

variable {G : Type} [Group G] [Finite G] {z : G} {ι : Perm (Fin 10) →* G} {x : G}

theorem z_mem_centralizer_of_eq (hC : CentData z ι) (hx : x = ι τ₀) :
    z ∈ centralizer ({x} : Set G) := by
  rw [hx, mem_centralizer_singleton_iff]
  exact hC.comm τ₀

@[expose] noncomputable def zbar (hC : CentData z ι) (hx : x = ι τ₀) : TwoSec x :=
  QuotientGroup.mk ⟨z, z_mem_centralizer_of_eq hC hx⟩

@[expose] noncomputable def sigmaX (hx : x = ι τ₀) : Perm (Fin 8) →* TwoSec x :=
  (QuotientGroup.mk' (zpowers (selfC x))).comp (liftS8Centralizer (ι := ι) hx)

@[expose] noncomputable def diagSub (hx : x = ι τ₀) : Subgroup (TwoSec x) :=
  (alternatingGroup (Fin 8)).map (sigmaX (ι := ι) hx)

theorem sigmaX_injective (hC : CentData z ι) (hx : x = ι τ₀) :
    Function.Injective (sigmaX (ι := ι) hx) := by
  have hx2 : x * x = 1 := by rw [hx, ← map_mul, τ₀_mul_self, map_one]
  rw [injective_iff_map_eq_one]
  intro ρ hρ
  have hmem : liftS8Centralizer (ι := ι) hx ρ ∈ zpowers (selfC x) := by
    rw [← QuotientGroup.eq_one_iff]
    exact hρ
  rcases (mem_zpowers_selfC_iff hx2).1 hmem with h1 | h1
  · have h1' : ι (liftS8 ρ) = 1 := by
      rw [← liftS8Centralizer_apply (ι := ι) hx ρ]; exact h1
    have h2 : liftS8 ρ = 1 := hC.inj (h1'.trans (map_one ι).symm)
    exact liftS8_injective (by rw [h2, map_one])
  · exfalso
    have h2 : liftS8 ρ = τ₀ := hC.inj (by
      rw [← liftS8Centralizer_apply (ι := ι) hx ρ, h1, hx])
    have h3 := congrArg (fun f : Perm (Fin 10) => f 8) h2
    rw [liftS8_apply_eight] at h3
    simp [τ₀] at h3

theorem zbar_comm_sigmaX (hC : CentData z ι) (hx : x = ι τ₀) (ρ : Perm (Fin 8)) :
    zbar hC hx * sigmaX (ι := ι) hx ρ = sigmaX (ι := ι) hx ρ * zbar hC hx := by
  change QuotientGroup.mk (⟨z, z_mem_centralizer_of_eq hC hx⟩ :
      ↥(centralizer ({x} : Set G))) *
      QuotientGroup.mk (liftS8Centralizer (ι := ι) hx ρ) =
    QuotientGroup.mk (liftS8Centralizer (ι := ι) hx ρ) *
      QuotientGroup.mk (⟨z, z_mem_centralizer_of_eq hC hx⟩ :
        ↥(centralizer ({x} : Set G)))
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, liftS8Centralizer_apply]
  exact hC.comm (liftS8 ρ)

theorem card_diagSub_inf_centralizer_swap (hC : CentData z ι) (hx : x = ι τ₀) {ρ : Perm (Fin 8)}
    (hρ : ρ.IsSwap) :
    Nat.card ↥(diagSub (ι := ι) hx ⊓
        centralizer ({sigmaX (ι := ι) hx ρ} : Set (TwoSec x))) = 720 := by
  have hset : diagSub (ι := ι) hx ⊓ centralizer ({sigmaX (ι := ι) hx ρ} : Set (TwoSec x)) =
      (alternatingGroup (Fin 8) ⊓ centralizer ({ρ} : Set (Perm (Fin 8)))).map
        (sigmaX (ι := ι) hx) := by
    apply le_antisymm
    · rintro y ⟨hyD, hyC⟩
      obtain ⟨a, ha, hay⟩ := Subgroup.mem_map.1 (show y ∈ (alternatingGroup (Fin 8)).map
        (sigmaX (ι := ι) hx) from hyD)
      rw [← hay] at hyC ⊢
      refine Subgroup.mem_map.2 ⟨a, ⟨ha, ?_⟩, rfl⟩
      refine mem_centralizer_singleton_iff.mpr ?_
      exact sigmaX_injective hC hx (by
        rw [map_mul, map_mul]
        exact mem_centralizer_singleton_iff.mp hyC)
    · rintro y ⟨a, ⟨ha, haC⟩, rfl⟩
      refine ⟨Subgroup.mem_map.2 ⟨a, ha, rfl⟩, ?_⟩
      refine mem_centralizer_singleton_iff.mpr ?_
      rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp haC]
  rw [hset, Subgroup.card_map_of_injective (sigmaX_injective hC hx)]
  exact card_alt_inf_centralizer_swap hρ

theorem card_diagSub_inf_centralizer_zbar_mul_swap (hC : CentData z ι) (hx : x = ι τ₀)
    {ρ : Perm (Fin 8)} (hρ : ρ.IsSwap) :
    Nat.card ↥(diagSub (ι := ι) hx ⊓
        centralizer ({zbar hC hx * sigmaX (ι := ι) hx ρ} : Set (TwoSec x))) = 720 := by
  have hset : diagSub (ι := ι) hx ⊓
        centralizer ({zbar hC hx * sigmaX (ι := ι) hx ρ} : Set (TwoSec x)) =
      diagSub (ι := ι) hx ⊓ centralizer ({sigmaX (ι := ι) hx ρ} : Set (TwoSec x)) := by
    apply le_antisymm
    · rintro y ⟨hyD, hyC⟩
      obtain ⟨a, ha, hay⟩ := Subgroup.mem_map.1 (show y ∈ (alternatingGroup (Fin 8)).map
        (sigmaX (ι := ι) hx) from hyD)
      rw [← hay] at hyC ⊢
      have hzy : zbar hC hx * sigmaX (ι := ι) hx a = sigmaX (ι := ι) hx a * zbar hC hx :=
        zbar_comm_sigmaX hC hx a
      refine ⟨Subgroup.mem_map.2 ⟨a, ha, rfl⟩, ?_⟩
      refine mem_centralizer_singleton_iff.mpr ?_
      have hc := mem_centralizer_singleton_iff.mp hyC
      exact mul_left_cancel (by
        calc zbar hC hx * (sigmaX (ι := ι) hx a * sigmaX (ι := ι) hx ρ)
            = (zbar hC hx * sigmaX (ι := ι) hx a) * sigmaX (ι := ι) hx ρ := by group
          _ = (sigmaX (ι := ι) hx a * zbar hC hx) * sigmaX (ι := ι) hx ρ := by rw [hzy]
          _ = sigmaX (ι := ι) hx a * (zbar hC hx * sigmaX (ι := ι) hx ρ) := by group
          _ = (zbar hC hx * sigmaX (ι := ι) hx ρ) * sigmaX (ι := ι) hx a := hc
          _ = zbar hC hx * (sigmaX (ι := ι) hx ρ * sigmaX (ι := ι) hx a) := by group)
    · rintro y ⟨hyD, hyC⟩
      obtain ⟨a, ha, hay⟩ := Subgroup.mem_map.1 (show y ∈ (alternatingGroup (Fin 8)).map
        (sigmaX (ι := ι) hx) from hyD)
      rw [← hay] at hyC ⊢
      have hzy : zbar hC hx * sigmaX (ι := ι) hx a = sigmaX (ι := ι) hx a * zbar hC hx :=
        zbar_comm_sigmaX hC hx a
      refine ⟨Subgroup.mem_map.2 ⟨a, ha, rfl⟩, ?_⟩
      refine mem_centralizer_singleton_iff.mpr ?_
      have hc := mem_centralizer_singleton_iff.mp hyC
      calc sigmaX (ι := ι) hx a * (zbar hC hx * sigmaX (ι := ι) hx ρ)
          = (sigmaX (ι := ι) hx a * zbar hC hx) * sigmaX (ι := ι) hx ρ := by group
        _ = (zbar hC hx * sigmaX (ι := ι) hx a) * sigmaX (ι := ι) hx ρ := by rw [← hzy]
        _ = zbar hC hx * (sigmaX (ι := ι) hx a * sigmaX (ι := ι) hx ρ) := by group
        _ = zbar hC hx * (sigmaX (ι := ι) hx ρ * sigmaX (ι := ι) hx a) := by rw [hc]
        _ = (zbar hC hx * sigmaX (ι := ι) hx ρ) * sigmaX (ι := ι) hx a := by group
  rw [hset]
  exact card_diagSub_inf_centralizer_swap hC hx hρ

end CFSG.OddStandard.AltStdSec.SwapPattern
