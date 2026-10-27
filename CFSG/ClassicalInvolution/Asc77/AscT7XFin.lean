module

public import CFSG.ClassicalInvolution.Asc77.AscT7XTyp
public import CFSG.ClassicalInvolution.Asc77.AscT7XMem
public import CFSG.ClassicalInvolution.Asc77.AscT7BThmE

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.Assembly.LowTwoRank

namespace T7X

namespace Frame24

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W : Subgroup G} (D : Frame24 p f Ω W)

 in
theorem layer_shape [IsSimpleGroup G] {K K' : Subgroup G} {z : G}
    (hs : Hyp23Setting p f Ω K K' z) (hK : D.F.ρ.K = K) (hK' : D.F.ρ'.K = K') {c : ℕ}
    (hc : 2 * c = D.m) (hZ : W ⊓ centerIn (Subgroup.normalizer (W : Set G)) = ⊥) :
    (if piSign p f then LayerLieType p f Ω (D.eEl c) .PSL 3
        else LayerLieType p f Ω (D.eEl c) .PSU 3) ∨
      LayerLieType p f Ω (D.eEl c) .G2 0 ∨ LayerLieType p f Ω (D.eEl c) .trialityD4 0 := by
  have hst := hs.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hWab := Thompson.commutes_of_mem_WSet hp hq hΩ D.c.hW
  have he2 := D.eEl_sq hc hZ
  have he1 := D.eEl_ne_one hc
  have hnc : ¬ ({D.eEl c} : Set G) ⊆ Subgroup.center G := by
    intro hsub
    obtain ⟨z₀, hz₀⟩ := hΩ.classical K hst.mem
    obtain ⟨x, -, y, -, hxy⟩ := ih8_exists_noncomm hz₀
    have hcen : D.eEl c ∈ Subgroup.center G := hsub (Set.mem_singleton _)
    exact he1 (T7B.eq_one_of_central ⟨x, y, hxy⟩ (fun g' => Subgroup.mem_center_iff.mp hcen g'))
  have hzW : D.F.z ∈ W := D.z₁ ▸ W.pow_mem D.x₁_mem _
  have hjW : D.F.j ∈ W := D.z₃ ▸ W.pow_mem D.x₃_mem _
  have hne : D.F.z ≠ D.F.j := by
    intro h
    have hJ : D.F.ρ₃.K ∈ twinSet Ω D.F.ρ.K :=
      ⟨D.F.ρ₃.hK, D.F.z, D.F.hz, h ▸ D.F.hj⟩
    rw [hK, hs.twinSet_eq] at hJ
    rcases hJ with hJ | hJ
    · exact D.F.hne₁ (hK.trans hJ.symm)
    · exact D.F.hne₂ (hK'.trans hJ.symm)
  have hcyc : IsCyclic ↥(D.F.ρ₃.R ⊓ W) := by
    rw [← D.h₃]
    infer_instance
  have hUK : D.F.ρ₃.R ⊓ W ≤ Subgroup.normalizer (D.F.ρ.K : Set G) := fun u hu =>
    (Thompson.inf_W_le_normalizer_of_ne hp hq hΩ D.c.hW D.F.ρ.hK D.F.ρ₃.hK D.F.hne₁ D.F.ρ.hR
      D.F.ρ₃.hR D.F.ρ.hRK D.F.ρ₃.hRK).2 ⟨D.F.ρ₃.hRK.1 hu.1, hu.2⟩
  have hperp : KPerp Ω D.F.ρ.K = {D.F.ρ.K, D.F.ρ'.K} := by
    rw [hK, hK']
    exact hs.perp
  exact layer_shape_of_data hp hq hΩ hst.aEmpty (hst.below f hq) he2 hnc hperp
    (D.K_mem_tq hc hZ) (D.J_mem_tq hc hZ) (D.K'_not_mem_tq hc hZ) D.F.hz D.F.hj
    (hWab _ hzW _ hjW) hne D.F.ρ₃.hRK D.eEl_cent_R₃ inf_le_left hcyc
    (Thompson.D_card hp hq hΩ D.c.hW D.F.ρ₃.hR) hUK
    (fun u hu => hWab u hu.2 _ (D.eEl_mem c))

end Frame24

end T7X

end CFSG.ClassicalInvolution.Asc77
