module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeB.Stable
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic.FixedVector
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherBorel
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherSylow

public noncomputable section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeB

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (flagStabilizer borelCuts)

variable {r : ℕ}

theorem false_of_sylow_normalizer_le_centralizer {J : Subgroup (StatedSp r (ZMod 2))}
    (hJ : J ≠ ⊤) (T : Sylow 2 (StatedSp r (ZMod 2)))
    (hNT : Subgroup.normalizer ((T : Subgroup (StatedSp r (ZMod 2))) : Set (StatedSp r (ZMod 2))) ≤ J)
    {v : StatedSp r (ZMod 2)} (hv : v ^ 3 = 1)
    (hC : ∀ g : StatedSp r (ZMod 2), g * v = v * g → g ∈ J) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U, hU⟩ := SymplecticFlag.exists_sylow_unipotent (K := ZMod 2) 2 r
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq (StatedSp r (ZMod 2)) U T
  have hTx : (T : Subgroup (StatedSp r (ZMod 2))) =
      (SymplecticFlag.unipotent r (ZMod 2)).map (MulAut.conj x).toMonoidHom := by
    have h1 : ((x • U : Sylow 2 (StatedSp r (ZMod 2))) : Subgroup (StatedSp r (ZMod 2))) = T := by
      rw [hx]
    rw [← h1, Sylow.coe_subgroup_smul, hU]
    rfl
  let e : StatedSp r (ZMod 2) ≃* StatedSp r (ZMod 2) := MulAut.conj x⁻¹
  have heT : (T : Subgroup (StatedSp r (ZMod 2))).map e.toMonoidHom =
      SymplecticFlag.unipotent r (ZMod 2) := by
    rw [hTx, Subgroup.map_map]
    have : e.toMonoidHom.comp (MulAut.conj x).toMonoidHom = MonoidHom.id _ := by
      refine MonoidHom.ext fun z => ?_
      show x⁻¹ * (x * z * x⁻¹) * x⁻¹⁻¹ = z
      group
    rw [this, Subgroup.map_id]
  have hNmap : (Subgroup.normalizer ((T : Subgroup (StatedSp r (ZMod 2))) :
      Set (StatedSp r (ZMod 2)))).map e.toMonoidHom = SymplecticFlag.borelSubgroup r (ZMod 2) := by
    rw [Subgroup.map_normalizer_eq_of_bijective _ e.bijective, heT]
    exact SymplecticHigher.normalizer_unipotent
  have hBJ : SymplecticFlag.borelSubgroup r (ZMod 2) ≤ J.map e.toMonoidHom := by
    rw [← hNmap]
    exact Subgroup.map_mono hNT
  obtain ⟨hJeq, -⟩ := SymplecticHigher.borel_overgroups (J.map e.toMonoidHom) hBJ
  have hIr := SymplecticHigher.borelCuts_le (K := ZMod 2) (J.map e.toMonoidHom)
  have hne : (borelCuts (ZMod 2) (J.map e.toMonoidHom)).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    rw [hemp, SymplecticHigher.flagStabilizer_empty] at hJeq
    apply hJ
    have := congrArg (Subgroup.comap e.toMonoidHom) hJeq
    rwa [Subgroup.comap_map_eq_self_of_injective e.injective, Subgroup.comap_top] at this
  obtain ⟨i, hi⟩ := hne
  have hir : i ≤ r := (hIr i hi).2
  have hi1 : 1 ≤ i := (hIr i hi).1
  have hr : 0 < r := by omega
  have hflag : ∀ g' : StatedSp r (ZMod 2), g' * e v = e v * g' →
      ∀ y ∈ SymplecticFlag.flag r (ZMod 2) i, spMat g' *ᵥ y ∈ SymplecticFlag.flag r (ZMod 2) i := by
    intro g' hg' y hy
    have hg : e.symm g' ∈ J := by
      apply hC
      have := congrArg e.symm hg'
      simpa using this
    have hg' : g' ∈ J.map e.toMonoidHom := ⟨e.symm g', hg, by simp⟩
    rw [hJeq] at hg'
    exact spMat_mulVec_mem_of_mem_stabilizer (SymplecticHigher.mem_flagStabilizer.1 hg' i hi) hy
  have hF0 : (Pi.single (Sum.inl ⟨0, hr⟩) 1 : Fin r ⊕ Fin r → ZMod 2) ∈
      SymplecticFlag.flag r (ZMod 2) i := single_mem_flag hir 0 hr (by omega)
  have hiso := SymplecticHigher.isCompleteIsotropicFlag_flag (r := r) (K := ZMod 2)
  refine false_of_stable_isotropic (v := e v) (by rw [← map_pow, hv, map_one])
    (SymplecticFlag.flag r (ZMod 2) i).toAddSubgroup
    (fun a ha b hb => hiso.2.2 i hir a ha b hb) hF0 ?_ hflag
  intro h0
  have := congrFun h0 (Sum.inl ⟨0, hr⟩)
  simp at this

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeB
