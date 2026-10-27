module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S2A5
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Inputs25C
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma116
public import CFSG.LocalAnalysis.QuasithinUnique.BenderBranchBasic

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.A5.S2

theorem S2.exists_central_invol {G : Type} [Group G] [Finite G] {D : Subgroup G}
    (hD : IsPGroup 2 D) (hD1 : D ≠ ⊥) :
    ∃ z ∈ D, z ≠ 1 ∧ z ^ 2 = 1 ∧ ∀ y ∈ D, y * z = z * y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial ↥D := (Subgroup.nontrivial_iff_ne_bot D).mpr hD1
  have := hD.center_nontrivial
  obtain ⟨⟨c, hc⟩, hc1⟩ := exists_ne (1 : ↥(Subgroup.center ↥D))
  have hZ1 : (Subgroup.center ↥D).map D.subtype ≠ ⊥ := by
    intro h
    have : (c : G) ∈ (Subgroup.center ↥D).map D.subtype := ⟨c, hc, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact hc1 (Subtype.ext (Subtype.ext this))
  have hZ2 : IsPGroup 2 ↥((Subgroup.center ↥D).map D.subtype) :=
    hD.to_le (by intro x ⟨y, _, hy⟩; rw [← hy]; exact y.2)
  obtain ⟨z, hzZ, hz1, hz2⟩ := GammaExtra.exists_involution_of_ne_bot hZ2 hZ1
  obtain ⟨c', hc', rfl⟩ := Subgroup.mem_map.mp hzZ
  refine ⟨(c' : G), c'.2, hz1, hz2, fun y hy => ?_⟩
  have := Subgroup.mem_center_iff.mp hc' ⟨y, hy⟩
  exact congrArg Subtype.val this

theorem comp25List_of (hlist : Lemma115_3_List) (htab : TabKc3) : Comp25List := by
  intro G _ _ T M H S L cfg x hxT hxN hxU hB K hKc hLK
  have hset := cfg.cs.setting
  have hS2 : IsPGroup 2 ↥S := hset.isPGroup.to_le cfg.cs.le_T
  have hφS : s2Phi S L ≤ S := phi_le_I.trans (s2I_le_baum.trans (C1GN.baum_le S))
  have hφ2 : IsPGroup 2 ↥(s2Phi S L) := hS2.to_le hφS
  have hφ1 : s2Phi S L ≠ ⊥ := hB.phi_ne
  set Gi : Subgroup G := Subgroup.normalizer (s2Phi S L : Set G) with hGi
  obtain ⟨TI, hTI⟩ := exists_isSylowTwoOf Gi
  have hφTI : s2Phi S L ≤ TI :=
    pCoreOf_two_le_of_sylowIn hTI.1 hTI.2.1 hTI.2.2 |> fun h =>
      (le_pCoreOf_of_normalizes Subgroup.le_normalizer le_rfl hφ2).trans h
  obtain ⟨T', hTIT', hT'⟩ := exists_isSylowTwoOf_of_le (le_top : TI ≤ ⊤) hTI.2.1
  have hT'2 : IsPGroup 2 ↥T' := hT'.2.1
  have hT'1 : T' ≠ ⊥ := by
    intro h
    apply hφ1
    rw [eq_bot_iff]
    exact (hφTI.trans hTIT').trans h.le
  obtain ⟨z, hzT, hz1, hz2, hzc⟩ := S2.exists_central_invol hT'2 hT'1
  obtain ⟨M', hM', hCM'⟩ := exists_quasithinIsMaxTwoLocal_ge
    (Lin2.isTwoLocal_centralizer_of_sq_eq_one hz2 hz1)
  have hzC : z ∈ Subgroup.centralizer (T' : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun y hy => (hzc y hy)
  have hHyp : Lemma115Hyp Gi TI M' z :=
    lemma116 hset.qtke.2.1 hφ2 hφ1
      (sup_le Subgroup.le_normalizer (Subgroup.centralizer_le_normalizer _)) le_rfl hTI hT' hTIT'
      hzT hzC hz1 hz2 hM' hCM'
  have hK' : IsComponentIn K Gi := hKc
  obtain ⟨-, -, -, hcases⟩ := Lemma115_3_List.component_cases hlist hset.simple hset.nonabelian
    hset.qtke hHyp hK'
  exact htab G K L z (BenderBranch.isQuasisimple_of_isComponentIn hKc) hcases hLK
    cfg.cs.block.1.1 cfg.alt5

end CFSG.QuasithinUnique.A5
