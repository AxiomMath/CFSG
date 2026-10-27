module

public import CFSG.LieType.BorelTits.Flag
public import CFSG.LieType.BorelTits.CentralQuotient
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup Matrix CFSG.LieType.BorelTits CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

section Rep

variable (n : ℕ) (F : Type) [Field F]

@[expose] noncomputable def slRep : SL(n, F) →* Module.End F (Fin n → F) where
  toFun g := Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) F)
  map_one' := by
    simp only [Matrix.SpecialLinearGroup.coe_one]
    exact Matrix.mulVecLin_one
  map_mul' g h := by
    simp only [Matrix.SpecialLinearGroup.coe_mul]
    rw [Matrix.mulVecLin_mul]
    rfl

variable {n F}

theorem slRep_apply (g : SL(n, F)) (v : Fin n → F) :
    slRep n F g v = (g : Matrix (Fin n) (Fin n) F) *ᵥ v := rfl

end Rep

section Fixed

variable {F : Type} [Field F] [Finite F]

theorem exists_fixed_vector_sl3 (r : ℕ) [Fact r.Prime] [CharP F r] (R : Subgroup SL(3, F))
    (hR : IsPGroup r R) :
    ∃ v : Fin 3 → F, v ≠ 0 ∧ ∀ g ∈ R, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v := by
  obtain ⟨v, hv0, hv⟩ := exists_fixed_ne_zero (slRep 3 F) r R hR
  exact ⟨v, hv0, fun g hg => hv g hg⟩

end Fixed

section Lift

variable {F : Type} [Field F] [Finite F]

theorem coprime_card_scalars (r : ℕ) [Fact r.Prime] [CharP F r] :
    Nat.Coprime (Nat.card (scalars 3 F)) r := by
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Fact.out]
  intro hdvd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' r hdvd
  have hxr : x ^ r = 1 := hx ▸ pow_orderOf_eq_one x
  obtain ⟨c, -, hc⟩ := x.2
  have hxr' : ((x : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) ^ r = 1 := by
    have := congrArg (fun y : ↥(scalars 3 F) => ((y : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)) hxr
    simpa using this
  rw [hc, ← map_pow] at hxr'
  have h00 := congrFun (congrFun hxr' 0) 0
  simp at h00
  have hc1 : (c : F) = 1 := frobenius_inj F r (by simpa [frobenius_def] using h00)
  have hx1 : x = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    rw [hc, hc1]
    simp
  rw [hx1, orderOf_one] at hx
  exact (Fact.out : r.Prime).one_lt.ne hx

theorem exists_lift_isPGroup_proj (r : ℕ) [Fact r.Prime] [CharP F r]
    (Y : Subgroup (projectiveSL 3 F)) (hY : IsPGroup r Y) :
    ∃ Yh : Subgroup SL(3, F), IsPGroup r Yh ∧ Yh.map (proj 3 F) = Y ∧
      ∀ g : SL(3, F), proj 3 F g ∈ normalizer (Y : Set (projectiveSL 3 F)) →
        g ∈ normalizer (Yh : Set SL(3, F)) := by
  obtain ⟨Yh, hYh, hmap⟩ := exists_isPGroup_map_eq (scalars 3 F) hY
  refine ⟨Yh, hYh, hmap, fun g hg => ?_⟩
  rw [normalizer_eq_comap_normalizer_map (scalars 3 F) (scalars_le_center 3 F)
    (coprime_card_scalars r) hYh, Subgroup.mem_comap, hmap]
  exact hg

end Lift

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
