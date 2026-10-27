module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S2List

public section

namespace CFSG.QuasithinUnique.A5.C25

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.A5.S2

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

theorem exists_inv_of_A5 (cfg : A5Cfg2 G T M H S L) {x : G} (hB : A5s2B T M H S L x) :
    ∃ (TI : Subgroup G) (z : G),
      IsSylowTwoOf TI (Subgroup.normalizer (s2Phi S L : Set G)) ∧ z ∈ TI ∧
      z ∈ Subgroup.centralizer (TI : Set G) ∧ z * z = 1 ∧
      ∀ y ∈ oddCoreIn (Subgroup.normalizer (s2Phi S L : Set G)), z⁻¹ * y * z = y⁻¹ := by
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
  exact ⟨TI, z, hTI, hHyp.z_mem, hHyp.z_central, by rw [← pow_two]; exact hHyp.z_sq,
    hHyp.inverts_oddCoreIn⟩

end CFSG.QuasithinUnique.A5.C25
