module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE6C4Gens
public import CFSG.LieType.Chevalley.E6SignedGraphPerfect

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.Timmesfeld CFSG.LocalAnalysis.ComponentInitial
  CFSG.LieType.Chevalley.E6SignedGraph
open CFSG.ClassicalInvolution.WeakCT (blk spBlock edgeDown doubleBondDiagram_cartanC
  weylElement_sp_one)
open scoped MatrixGroups Matrix

variable {K : Type} [Field K]

@[expose] def e6C4W :
    Fin 4 → WeylGroup TwistTag.E6.tag :=
  ![e6C4Word, 1, 1, 1]

@[expose] def e6C4A : Fin 4 → Fin TwistTag.E6.foldedTag.rank :=
  ![⟨1, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩]


theorem e6C4Rho_eq_orbitSL2
    (k : Fin 4) : e6C4Rho K k = orbitSL2 K (e6C4W k) (e6C4A k) := by
  fin_cases k <;> rfl

theorem e6C4W_mem
    (k : Fin 4) : e6C4W k ∈ relWeylTwist TwistTag.E6 := by
  fin_cases k
  · exact e6C4Word_mem
  all_goals exact one_mem _

theorem orbitImage_e6C4
    (k : Fin 4) : orbitImage (e6C4W k) (e6C4A k) = simpleOrbit k := by
  fin_cases k
  · exact orbitImage_e6C4Word
  · change orbitImage 1 ⟨0, by decide⟩ = simpleOrbit 1
    rw [orbitImage_pair (by decide) 1, one_smul, one_smul, simpleOrbit, diagramOrbit_eq]
    decide
  · change orbitImage 1 ⟨1, by decide⟩ = simpleOrbit 2
    rw [orbitImage_pair (by decide) 1, one_smul, one_smul, simpleOrbit, diagramOrbit_eq]
    decide
  · change orbitImage 1 ⟨2, by decide⟩ = simpleOrbit 3
    rw [orbitImage_single (by decide) 1, one_smul, simpleOrbit, diagramOrbit_eq]
    decide

theorem orbitSign_e6C4
    (k : Fin 4) (h : TwistTag.E6.perm (TwistTag.E6.orbitMin (e6C4A k)) =
      TwistTag.E6.orbitMin (e6C4A k)) : orbitSign K (e6C4W k) (e6C4A k) = 1 := by
  fin_cases k
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · change orbitSign K 1 ⟨2, by decide⟩ = 1
    rw [orbitSign, one_smul, Pi.single_eq_of_ne (by decide), zpow_zero]

theorem orbitFixed_simpleOrbit_le_range
    (k : Fin 4) : orbitFixed K (simpleOrbit k) ≤ (e6C4Rho K k).range := by
  rw [← orbitImage_e6C4 k, ← SetLike.coe_subset_coe,
    ← (orbitFixed_orbitImage_upper (e6C4W_mem k) (orbitSign_e6C4 k)).2, e6C4Rho_eq_orbitSL2]
  rintro _ ⟨c, rfl⟩
  exact ⟨_, rfl⟩

theorem exists_lift_mem_iSup_e6C4Rho
    {w : WeylGroup TwistTag.E6.tag} (hw : w ∈ weylGroup) :
    ∃ z ∈ ⨆ k, (e6C4Rho K k).range, z ∈ monomialSubgroup TwistTag.E6.tag K ∧
      z ∈ fixedGroup K ∧ MapsRootLines z w := by
  have hw' : w ∈ Subgroup.closure (Set.range gen) := hw
  clear hw
  induction hw' using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨i, rfl⟩ := hw
    have h := mapsRootLines_orbitSL2_nSL (K := K) (e6C4W i) (e6C4A i) 1
    rw [orbitImage_e6C4] at h
    refine ⟨e6C4Rho K i (nSL 1), Subgroup.mem_iSup_of_mem i ⟨_, rfl⟩, ?_,
      e6C4Rho_mem_fixedGroup i _, ?_⟩
    · rw [e6C4Rho_eq_orbitSL2]
      exact orbitSL2_nSL_mem_monomialSubgroup _ _ 1
    · rw [e6C4Rho_eq_orbitSL2]
      exact h
  | one => exact ⟨1, one_mem _, one_mem _, one_mem _, mapsRootLines_one⟩
  | mul w w' _ _ ih ih' =>
    obtain ⟨z, hz, hzN, hzΓ, hzw⟩ := ih
    obtain ⟨z', hz', hzN', hzΓ', hzw'⟩ := ih'
    exact ⟨z * z', mul_mem hz hz', mul_mem hzN hzN', mul_mem hzΓ hzΓ', hzw.mul hzw'⟩
  | inv w _ ih =>
    obtain ⟨z, hz, hzN, hzΓ, hzw⟩ := ih
    exact ⟨z⁻¹, inv_mem hz, inv_mem hzN, inv_mem hzΓ, hzw.inv⟩

theorem iSup_e6C4Rho_range_eq
    (hK : ringChar K ≠ 2) : (⨆ k, (e6C4Rho K k).range) = rootGenerated K := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h13, h14, -, -, h17, -, -, -, -⟩ :=
    E6_signed_graph_root_system_and_Weyl_stabilizer
  refine le_antisymm (iSup_le fun k => ?_) ?_
  · rw [e6C4Rho_eq_orbitSL2]
    exact range_orbitSL2_le_rootGenerated (e6C4W_mem k)
      (by rw [orbitImage_e6C4]; exact (simpleOrbit_spec k).1)
  have hsmul : ∀ {O₀ : Finset E6Vec}, O₀ ∈ orbits →
      orbitFixed K O₀ ≤ ⨆ k, (e6C4Rho K k).range → ∀ {w : WeylGroup TwistTag.E6.tag},
      w ∈ weylGroup → ∀ {O : Finset E6Vec}, O ∈ orbits → w • orbitVec O₀ = orbitVec O →
      orbitFixed K O ≤ ⨆ k, (e6C4Rho K k).range := by
    intro O₀ hO₀ hQ w hw O hO hv
    obtain ⟨hP, hPv⟩ := smul_mem_orbits (weylGroup_le_parityGroup hw) hO₀
    rw [← injOn_orbitVec hP hO (hPv.trans hv)]
    obtain ⟨z, hz, hzN, hzΓ, hzw⟩ := exists_lift_mem_iSup_e6C4Rho (K := K) hw
    have hroots : ∀ α ∈ O₀, IsRoot TwistTag.E6.tag α := fun α hα => by
      obtain ⟨⟨β, hβ, rfl⟩, -⟩ := hO₀
      exact TwistTag.E6.isRoot_of_mem_diagramOrbit hβ hα
    rw [← map_orbitFixed_conj hzN hzw hzΓ hroots]
    rintro _ ⟨x, hx, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact mul_mem (mul_mem hz (hQ hx)) (inv_mem hz)
  have key : ∀ O ∈ orbits, orbitFixed K O ≤ ⨆ k, (e6C4Rho K k).range := by
    intro O hO
    have hv : orbitVec O ∈ vecs := ⟨O, hO, rfl⟩
    rw [h17] at hv
    rcases hv with ⟨-, h4⟩ | ⟨-, h8⟩
    · have hm : orbitVec O ∈ {v | ∃ w ∈ weylGroup, w • simpleVec 0 = v} := by
        rw [h13]
        exact ⟨⟨O, hO, rfl⟩, h4⟩
      obtain ⟨w, hw, hwv⟩ := hm
      exact hsmul (simpleOrbit_spec 0).1
        ((orbitFixed_simpleOrbit_le_range 0).trans (le_iSup (fun k => (e6C4Rho K k).range) 0))
        hw hO (by rw [(simpleOrbit_spec 0).2]; exact hwv)
    · have hm : orbitVec O ∈ {v | ∃ w ∈ weylGroup, w • simpleVec 3 = v} := by
        rw [h14]
        exact ⟨⟨O, hO, rfl⟩, h8⟩
      obtain ⟨w, hw, hwv⟩ := hm
      exact hsmul (simpleOrbit_spec 3).1
        ((orbitFixed_simpleOrbit_le_range 3).trans (le_iSup (fun k => (e6C4Rho K k).range) 3))
        hw hO (by rw [(simpleOrbit_spec 3).2]; exact hwv)
  calc rootGenerated K = ⨆ O ∈ orbits, orbitFixed K O := rootGenerated_eq_iSup hK
    _ ≤ ⨆ k, (e6C4Rho K k).range := iSup₂_le key

end CFSG.ComponentClassification.CatLeafProof
