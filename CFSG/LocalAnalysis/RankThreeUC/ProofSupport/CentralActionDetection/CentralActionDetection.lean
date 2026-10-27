module

public import CFSG.LocalAnalysis.RankThreeUC.ProofSupport.BinaryCenterDecomposition.BinaryCenterDecomposition

public section

namespace CFSG.LocalAnalysis.RankThreeUC.ProofSupport.CentralActionDetection

open CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
  {W : Type*} [AddCommGroup W] [Module (ZMod p) W]

theorem exists_hyperplane (hp2 : p ≠ 2) (ρ : Representation (ZMod p) G W) (Z : Subgroup G)
    (hZ : CFSG.Open.IsElemAbelian 2 Z) {z : G} (hz : z ∈ Z) (hnt : ∃ v, ρ z v ≠ v) :
    ∃ H ∈ hyperplanes 2 Z, ∃ v ∈ (commSpace ρ Z ⊓ fixedSpace ρ H), ρ z v ≠ v := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  push Not at hcon
  have hc : ((Nat.card Z : ℕ) : ZMod p) ≠ 0 :=
    natCard_ne_zero_of_le (fun h => hp2 h.symm) hZ (le_refl Z)
  have hsplit := CoprimeCommSpaceAveraging.split ρ Z hZ.1 hc
  have hfix : ∀ v ∈ fixedSpace ρ Z, ρ z v = v := fun v hv =>
    (mem_fixedSpace_iff ρ Z v).1 hv z hz
  have hcomm : ∀ v ∈ commSpace ρ Z, ρ z v = v := by
    have hle : commSpace ρ Z ≤ LinearMap.ker (ρ z - LinearMap.id) := by
      rw [← BinaryCenterDecomposition.iSup_eq hp2 ρ Z hZ]
      refine iSup_le fun H => fun v hv => ?_
      have := hcon H.1 H.2 v hv
      simp [this]
    intro v hv
    have := hle hv
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at this
    exact this
  obtain ⟨v, hv⟩ := hnt
  have hv' : v ∈ commSpace ρ Z ⊔ fixedSpace ρ Z := by rw [hsplit]; trivial
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv'
  exact hv (by rw [map_add, hcomm a ha, hfix b hb])

end CFSG.LocalAnalysis.RankThreeUC.ProofSupport.CentralActionDetection
