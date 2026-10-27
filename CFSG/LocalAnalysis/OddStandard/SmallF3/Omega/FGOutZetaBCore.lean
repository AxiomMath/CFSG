module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGOutZetaBDefs
public import CFSG.LieType.Multipliers.U43

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.U43

theorem zetaCore_of_parts (h1 : ZetaPermSide) (h4 : ZetaPresentation) (h5 : ZetaLift)
    (h6 : ZetaCount) : ZetaCore := by
  intro E S _ _ q hq hker hperf hmodel eh hrel hne hwg hc
  let s : Fin 2 → S := fun i => q (eh i)
  have hP : IsPresentation s (wordSet rels) := h4 S s hmodel hrel hne
  obtain ⟨lam, hlamof, hlamq, hlamsurj⟩ :=
    h5 (S := S) (E := E) q hq hker hperf s hP hwg eh (fun _ => rfl)
  have hw : ∀ i, zW i ∈ commutator (FreeGroup (Fin 2)) := fun i =>
    mk_commWords_mem_commutator (coverPairs i)
  let π : ZetaCover →* S := coverMap (w := zW) hP hwg
  have hlam_mk : ∀ f : FreeGroup (Fin 2),
      lam (PresentedGroup.mk (coverRelators (wordSet rels) zW) f) =
        FreeGroup.lift (zCanon eh) f := by
    have hcomp : lam.comp (PresentedGroup.mk (coverRelators (wordSet rels) zW)) =
        FreeGroup.lift (zCanon eh) :=
      FreeGroup.ext_hom _ _ fun i => by
        change lam (PresentedGroup.of i) = FreeGroup.lift (zCanon eh) (FreeGroup.of i)
        rw [hlamof i, FreeGroup.lift_apply_of]
    intro f
    exact DFunLike.congr_fun hcomp f
  have hcommP : ∀ k, lam (zCommP k) = zComm (zCanon eh) k := by
    intro k
    simp only [zCommP, zComm]
    rw [hlam_mk, map_commutatorElement]
  have hmem : ∀ k, zCommP k ∈ π.ker := by
    intro k
    rw [MonoidHom.mem_ker, ← hlamq (zCommP k), hcommP k]
    exact hc k
  let M : Subgroup ZetaCover := π.ker
  let c₀ : M := ⟨zCommP 0, hmem 0⟩
  let c₁ : M := ⟨zCommP 1, hmem 1⟩
  obtain ⟨-, ⟨hM⟩⟩ := multiplier_PSU_four_three S hmodel
  have hequiv : CFSG.Open.griessHopfMultiplier S ≃* M :=
    griessHopfMultiplierEquivKer hP hw hwg
  let e : M ≃* Multiplicative (ZMod 4 × ZMod 3 × ZMod 3) := hequiv.symm.trans hM
  have h12 : ∀ a : Multiplicative (ZMod 4 × ZMod 3 × ZMod 3), a ^ 12 = 1 := by decide
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨p, hp⟩ := hlamsurj x
    have hpker : p ∈ π.ker := by
      rw [MonoidHom.mem_ker, ← hlamq p, hp]
      exact hx
    have h12p : (e ⟨p, hpker⟩) ^ 12 = 1 := h12 _
    have hp12 : p ^ 12 = 1 := by
      have hM12 : (⟨p, hpker⟩ : M) ^ 12 = 1 :=
        (e.map_eq_one_iff (x := (⟨p, hpker⟩ : M) ^ 12)).mp (by rw [map_pow]; exact h12p)
      simpa using congrArg (fun z : M => (z : ZetaCover)) hM12
    rw [← hp, ← map_pow, hp12, map_one]
  · intro x hx hx3
    obtain ⟨p, hp⟩ := hlamsurj x
    have hpker : p ∈ π.ker := by
      rw [MonoidHom.mem_ker, ← hlamq p, hp]
      exact hx
    let m : M := ⟨p, hpker⟩
    obtain ⟨ρ, hρ0, hρ1, -, hρindep⟩ := h1
    have hρc0 : (ρ.comp M.subtype) c₀ ^ 3 = 1 := by simpa [c₀] using hρ0
    have hρc1 : (ρ.comp M.subtype) c₁ ^ 3 = 1 := by simpa [c₁] using hρ1
    have hindep : ∀ i j : Fin 3,
        (ρ.comp M.subtype) c₀ ^ (i : ℕ) * (ρ.comp M.subtype) c₁ ^ (j : ℕ) = 1 →
          i = 0 ∧ j = 0 := by
      intro i j hij
      exact hρindep i j (by simpa [c₀, c₁] using hij)
    obtain ⟨i, j, hij⟩ := h6 e (ρ.comp M.subtype) c₀ c₁ hρc0 hρc1 hindep m
    refine ⟨i, j, ?_⟩
    have hlam_m : (lam.comp M.subtype) m = x := by
      change lam (m : ZetaCover) = x
      simpa using hp
    have hlam_0 : (lam.comp M.subtype) c₀ = zComm (zCanon eh) 0 := by
      change lam (zCommP 0) = zComm (zCanon eh) 0
      exact hcommP 0
    have hlam_1 : (lam.comp M.subtype) c₁ = zComm (zCanon eh) 1 := by
      change lam (zCommP 1) = zComm (zCanon eh) 1
      exact hcommP 1
    have hpow : x ^ 4 = (zComm (zCanon eh) 0) ^ (4 * (i : ℕ)) *
        (zComm (zCanon eh) 1) ^ (4 * (j : ℕ)) := by
      rw [← hlam_m, ← map_pow, hij, map_mul, map_pow, map_pow, hlam_0, hlam_1]
    have hx4 : x ^ 4 = x := by
      rw [show (4 : ℕ) = 3 + 1 from rfl, pow_add, hx3, one_mul, pow_one]
    exact hx4.symm.trans hpow

end CFSG.OddStandard.SmallF3.Omega
