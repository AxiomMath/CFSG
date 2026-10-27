module

public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.L32Tools
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.OddExact
public import CFSG.RankThree.FFModules.ChiefFactors
import CFSG.CharacterTheory.Semidihedral.Principal.CompositionMultiplicity
public import Mathlib.Topology.Sheaves.Presheaf

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.DynkinA2

open Module Polynomial
open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542 CFSG.RankThree.FFModules

private theorem factorRep_eq_mapQ {K V : Type*} [Group K] [AddCommGroup V]
    [Module (ZMod 2) V] {ρ : Representation (ZMod 2) K V}
    (U U' : Subrepresentation ρ) (k : K) :
    (factorSub U U').mapQ (factorSub U U')
      ((ρ k).restrict (fun _ hx => U'.apply_mem_toSubmodule k hx))
      (fun _ hz => U.apply_mem_toSubmodule k hz) =
    factorRep U U' k := by
  apply LinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | H z =>
    erw [Submodule.mapQ_apply]

theorem finrank_ker_aeval_eq_sum {K V : Type*} [Group K] [AddCommGroup V] [Module (ZMod 2) V]
    [Finite V] {ρ : Representation (ZMod 2) K V} {r : ℕ} {Vs : Fin (r + 1) → Subrepresentation ρ}
    (hmono : ∀ i : Fin r, Vs i.castSucc ≤ Vs i.succ) (h0 : Vs 0 = ⊥)
    (hlast : Vs (Fin.last r) = ⊤) {f h : (ZMod 2)[X]} (hcop : IsCoprime f h) {k : K}
    (hk : aeval (ρ k) (f * h) = 0) :
    finrank (ZMod 2) ↥(LinearMap.ker (aeval (ρ k) f)) =
      ∑ i : Fin r, finrank (ZMod 2)
        ↥(LinearMap.ker (aeval (factorRep (Vs i.castSucc) (Vs i.succ) k) f)) := by
  classical
  have : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
  let d : Fin (r + 1) → ℕ := fun j =>
    finrank (ZMod 2) ↥((Vs j).toSubmodule ⊓ LinearMap.ker (aeval (ρ k) f))
  let a : Fin r → ℕ := fun i =>
    finrank (ZMod 2) ↥(LinearMap.ker (aeval (factorRep (Vs i.castSucc) (Vs i.succ) k) f))
  have hmap : ∀ i : Fin r,
      (((Vs i.castSucc).toSubmodule.comap (Vs i.succ).toSubmodule.subtype).mapQ
        ((Vs i.castSucc).toSubmodule.comap (Vs i.succ).toSubmodule.subtype)
        ((ρ k : Module.End (ZMod 2) V).restrict
          (fun x hx => (Vs i.succ).apply_mem_toSubmodule k hx))
        (fun _ hz => (Vs i.castSucc).apply_mem_toSubmodule k hz)) =
      factorRep (Vs i.castSucc) (Vs i.succ) k := fun i =>
    factorRep_eq_mapQ (Vs i.castSucc) (Vs i.succ) k
  have hstep : ∀ i : Fin r, d i.succ = d i.castSucc + a i := by
    intro i
    dsimp only [d, a]
    have hi := finrank_inf_ker_aeval_eq (K := ZMod 2) (M := V)
      (T := (ρ k : Module.End (ZMod 2) V)) hcop hk (hmono i)
      (fun x hx => (Vs i.castSucc).apply_mem_toSubmodule k hx)
      (fun x hx => (Vs i.succ).apply_mem_toSubmodule k hx)
    rw [hi, hmap i]
    rfl
  have htel := CFSG.Semidihedral.Principal.fin_telescope d a hstep
  have hd0 : d 0 = 0 := by
    dsimp only [d]
    have hbot : (Vs 0).toSubmodule = (⊥ : Submodule (ZMod 2) V) := by
      rw [h0]
      rfl
    rw [hbot]
    simp
  have hdlast : d (Fin.last r) = finrank (ZMod 2) ↥(LinearMap.ker (aeval (ρ k) f)) := by
    dsimp only [d]
    have htop : (Vs (Fin.last r)).toSubmodule = (⊤ : Submodule (ZMod 2) V) := by
      rw [hlast]
      rfl
    rw [htop, top_inf_eq]
  rw [hd0, hdlast] at htel
  simpa only [a, zero_add] using htel

theorem finrank_ker_aeval_fL_eq_sum {K V : Type*} [Group K] [AddCommGroup V] [Module (ZMod 2) V]
    [Finite V] {ρ : Representation (ZMod 2) K V} {r : ℕ} {Vs : Fin (r + 1) → Subrepresentation ρ}
    (hmono : ∀ i : Fin r, Vs i.castSucc ≤ Vs i.succ) (h0 : Vs 0 = ⊥)
    (hlast : Vs (Fin.last r) = ⊤) {k : K} (hk : k ^ 7 = 1) :
    finrank (ZMod 2) ↥(LinearMap.ker (aeval (ρ k) fL)) =
      ∑ i : Fin r, finrank (ZMod 2)
        ↥(LinearMap.ker (aeval (factorRep (Vs i.castSucc) (Vs i.succ) k) fL)) :=
  finrank_ker_aeval_eq_sum hmono h0 hlast isCoprime_fL_gL
    (aeval_fL_mul_gL_eq_zero (by rw [← map_pow, hk, map_one]))

theorem kerDim_eq_finrank_ker {G K W : Type*} [Group G] [Group K] [AddCommGroup W]
    [Module (ZMod 2) W] [Finite W] (ρ : Representation (ZMod 2) G W) (π : K →* G)
    (SU : Subrepresentation (ρ.comp π)) (k : K) (p : (ZMod 2)[X]) :
    kerDim ρ p (π k) SU.toSubmodule =
      finrank (ZMod 2) ↥(LinearMap.ker (aeval (SU.toRepresentation k) p)) := by
  have h : ∀ v : ↥SU.toSubmodule,
      SU.toSubmodule.subtype (SU.toRepresentation k v) =
        (ρ (π k)) (SU.toSubmodule.subtype v) := by
    intro v
    rfl
  have hmap : (LinearMap.ker (aeval (SU.toRepresentation k) p)).map
        SU.toSubmodule.subtype =
      SU.toSubmodule ⊓ LinearMap.ker (aeval (ρ (π k)) p) := by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨v.2, ?_⟩
      have hv' := apply_aeval_of_intertwine SU.toSubmodule.subtype h p v
      have hv0 : SU.toSubmodule.subtype (aeval (SU.toRepresentation k) p v) = 0 := by
        rw [hv, map_zero]
      rw [hv'] at hv0
      exact hv0
    · rintro ⟨hw, hwker⟩
      refine ⟨⟨w, hw⟩, ?_, rfl⟩
      apply Subtype.ext
      have hw' := apply_aeval_of_intertwine SU.toSubmodule.subtype h p ⟨w, hw⟩
      exact hw'.trans hwker
  unfold kerDim
  rw [← hmap, Submodule.finrank_map_subtype_eq]

end CFSG.LocalAnalysis.RankThreeUC.S15.DynkinA2

end
