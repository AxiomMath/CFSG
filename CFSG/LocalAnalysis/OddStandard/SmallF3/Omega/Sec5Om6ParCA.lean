module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGAutCentLin
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5CoverAct

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {hQ : Q.Nondegenerate} {φ : ↥L →* omegaGroup hQ}

theorem om6par_coverAct_mul {s s' : G} {x x' : simGroup Q} (h : CoverAct L φ s x)
    (h' : CoverAct L φ s' x') : CoverAct L φ (s * s') (x * x') := by
  refine ⟨Subgroup.mul_mem _ h.1 h'.1, fun l l' hl => ?_⟩
  let l'' : ↥L := ⟨s' * (l : G) * s'⁻¹, (Subgroup.mem_normalizer_iff.mp h'.1 (l : G)).mp l.2⟩
  have e1 : ((φ l'' : omegaGroup hQ) : OGroup Q) =
      simAct Q x' ((φ l : omegaGroup hQ) : OGroup Q) := h'.2 l l'' rfl
  have e2 : ((φ l' : omegaGroup hQ) : OGroup Q) =
      simAct Q x ((φ l'' : omegaGroup hQ) : OGroup Q) :=
    h.2 l'' l' (by rw [hl]; show _ = s * (s' * (l : G) * s'⁻¹) * s⁻¹; group)
  rw [e2, e1, map_mul, MulAut.mul_apply]

theorem om6par_coverAct_inv {s : G} {x : simGroup Q} (h : CoverAct L φ s x) :
    CoverAct L φ s⁻¹ x⁻¹ := by
  refine ⟨Subgroup.inv_mem _ h.1, fun l l' hl => ?_⟩
  have e := h.2 l' l (by rw [hl]; group)
  rw [e, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]

theorem om6par_coverAct_of_mem {z : G} (hz : z ∈ L) :
    CoverAct L φ z (orthToSim Q ((φ ⟨z, hz⟩ : omegaGroup hQ) : OGroup Q)) := by
  refine ⟨Subgroup.le_normalizer hz, fun l l' hl => ?_⟩
  have h : l' = (⟨z, hz⟩ : ↥L) * l * (⟨z, hz⟩ : ↥L)⁻¹ := Subtype.ext hl
  rw [h, map_mul, map_mul, map_inv, simAct_orthToSim]
  simp

theorem om6par_mem_piSim_of_fixed (hQ : Q.Nondegenerate) (h3 : 3 ≤ Module.finrank (ZMod 3) V)
    {x : simGroup Q} (hx : ∀ w ∈ omegaGroup hQ, simAct Q x w = w) : x ∈ piSim Q := by
  obtain ⟨c, hc⟩ := fg_eq_smul_of_commute_omega hQ h3
    (((x : V ≃ₗ[ZMod 3] V)) : V →ₗ[ZMod 3] V) (fun g hg => by
      ext v
      have h1 := congrArg (fun t : OGroup Q => (t : V ≃ₗ[ZMod 3] V)) (hx g hg)
      simp only [coe_simAct] at h1
      have h2 := congrArg (fun t : V ≃ₗ[ZMod 3] V => t v) (mul_inv_eq_iff_eq_mul.mp h1)
      simpa using h2)
  have hxv : ∀ v : V, (x : V ≃ₗ[ZMod 3] V) v = c • v := fun v => by
    have := LinearMap.congr_fun hc v
    simpa using this
  haveI : Nontrivial V := Module.finrank_pos_iff.mp (lt_of_lt_of_le (by norm_num) h3)
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hv
    apply (x : V ≃ₗ[ZMod 3] V).injective
    rw [hxv v, zero_smul, map_zero]
  rw [mem_piSim_iff]
  have hcc : c = 1 ∨ c = -1 := by
    revert hc0
    generalize c = c'
    revert c'
    decide
  rcases hcc with rfl | rfl
  · left
    apply Subtype.ext
    apply LinearEquiv.ext
    intro u
    rw [hxv u, one_smul]
    rfl
  · right
    apply Subtype.ext
    apply LinearEquiv.ext
    intro u
    rw [hxv u, neg_one_smul]
    change -u = (piOrth Q : V ≃ₗ[ZMod 3] V) u
    rw [coe_piOrth_apply]

theorem om6par_fixed_of_mem_piSim {x : simGroup Q} (hx : x ∈ piSim Q) (w : OGroup Q) :
    simAct Q x w = w := by
  rcases mem_piSim_iff.mp hx with rfl | rfl
  · simp
  · rw [simAct_orthToSim]
    have h := Subgroup.mem_center_iff.mp piOrth_mem_center w
    rw [← h, mul_inv_cancel_right]

theorem om6par_cent_iff (hφ : Function.Surjective φ) (hinj : Function.Injective φ)
    (h3 : 3 ≤ Module.finrank (ZMod 3) V) {s : G} {x : simGroup Q} (hx : CoverAct L φ s x) :
    s ∈ centralizer (L : Set G) ↔ x ∈ piSim Q := by
  constructor
  · intro hs
    refine om6par_mem_piSim_of_fixed hQ h3 (fun w hw => ?_)
    obtain ⟨l, hl⟩ := hφ ⟨w, hw⟩
    have hcomm : s * (l : G) = (l : G) * s :=
      (Subgroup.mem_centralizer_iff.mp hs (l : G) l.2).symm
    have := t5_cent_map_mem hx hcomm
    rw [hl] at this
    exact this
  · intro hs
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    let l₀ : ↥L := ⟨l, hl⟩
    let l' : ↥L := ⟨s * l * s⁻¹, (Subgroup.mem_normalizer_iff.mp hx.1 l).mp hl⟩
    have h1 : ((φ l' : omegaGroup hQ) : OGroup Q) =
        simAct Q x ((φ l₀ : omegaGroup hQ) : OGroup Q) := hx.2 l₀ l' rfl
    rw [om6par_fixed_of_mem_piSim hs] at h1
    have h2 : l' = l₀ := hinj (Subtype.ext h1)
    have h3' : s * l * s⁻¹ = l := congrArg Subtype.val h2
    calc l * s = (s * l * s⁻¹) * s := by rw [h3']
      _ = s * l := by group

end CFSG.OddStandard.SmallF3.Omega
