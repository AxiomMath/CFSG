module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisP313a
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisL310a
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisL312a

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup SCert CFSG.ABGLocalTools

theorem SCert.SE.not_conj_a1a4_a3a4 : ∀ c : SE, c⁻¹ * invRep 4 * c ≠ invRep 3 := by
  decide +kernel

variable {G : Type} [Group G] [Finite G]

namespace GHSylow

variable (D : GHSylow G)

theorem index_three_B (hC : GorensteinHaradaThmCInput) (hB : D.caseB) {g : G} (hg : g ∈ D.M)
    (h : g⁻¹ * D.a1a4 * g = D.a3a4) :
    ((D.toMb.sylowXt D.pPrimeCore_Mb D.z_comm_Mb : Sylow 2 D.toMb.Xt) :
      Subgroup D.toMb.Xt).index = 3 := by
  rcases (D.toMb.prop38B_of hC D.pPrimeCore_Mb D.z_comm_Mb hB).1 with h1 | h3
  · exfalso
    have hS := D.toMb.mem_S_of_index_one D.pPrimeCore_Mb D.z_comm_Mb h1 (D.piM ⟨g, hg⟩)
    change D.piM ⟨g, hg⟩ ∈ (D.sylowMb : Subgroup D.Mb) at hS
    rw [D.coe_sylowMb] at hS
    obtain ⟨s, hs, hsg⟩ := hS
    have hSs : (s : G) ∈ (D.S : Subgroup G) := mem_subgroupOf.mp hs
    have h4 : D.a1a4 ∈ D.M := D.S_le_M (D.toG_mem _)
    have h3' : D.a3a4 ∈ D.M := D.S_le_M (D.toG_mem _)
    have key : D.piM (s⁻¹ * ⟨D.a1a4, h4⟩ * s) = D.piM ⟨D.a3a4, h3'⟩ := by
      rw [map_mul, map_mul, map_inv, hsg, D.piM_conj hg h4]
      congr 1
      exact Subtype.ext h
    have hmem : s⁻¹ * ⟨D.a1a4, h4⟩ * s ∈ D.SM :=
      mem_subgroupOf.mpr (mul_mem (mul_mem (inv_mem hSs) (D.toG_mem _)) hSs)
    have hinj := D.piM_comp_injective (a₁ := ⟨_, hmem⟩)
      (a₂ := ⟨⟨D.a3a4, h3'⟩, mem_subgroupOf.mpr (D.toG_mem _)⟩) key
    have e : ((s⁻¹ * ⟨D.a1a4, h4⟩ * s : ↥D.M) : G) = D.a3a4 :=
      congrArg (fun w : D.SM => ((w : ↥D.M) : G)) hinj
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at e
    obtain ⟨s₀, hs₀⟩ := D.exists_toG hSs
    rw [← hs₀, ← map_inv, ← map_mul, ← map_mul] at e
    exact SE.not_conj_a1a4_a3a4 s₀ (D.toG_injective e)
  · exact h3

theorem conj_t_a1l_B (hC : GorensteinHaradaThmCInput) (hB : D.caseB)
    (h3 : ((D.toMb.sylowXt D.pPrimeCore_Mb D.z_comm_Mb : Sylow 2 D.toMb.Xt) :
      Subgroup D.toMb.Xt).index = 3) :
    ∃ m ∈ D.M, m⁻¹ * D.t * m = D.a1l := by
  obtain ⟨h, hh⟩ := D.toMb.exists_conj_t_a1l_Y hC D.pPrimeCore_Mb D.z_comm_Mb hB h3
  obtain ⟨m, hm⟩ := D.exists_conj_M_of_conj_Mb (u := ⟨D.t, D.S_le_M (D.toG_mem _)⟩)
    (v := ⟨D.a1l, D.S_le_M (D.toG_mem _)⟩) (Subtype.ext D.t_mul_t)
    (Subtype.ext (by
      change D.toG (SE.invRep 2) * D.toG (SE.invRep 2) = 1
      rw [← map_mul, SE.invRep_mul_self', map_one]))
    (g := (h : D.Mb)) (congrArg Subtype.val hh)
  exact ⟨m, m.2, congrArg Subtype.val hm⟩


theorem fusion_B (hC : GorensteinHaradaThmCInput)
    (hidx : ∀ N : Subgroup G, N.Normal → N.index ≠ 2) (hxa : ¬ ∃ g : G, g⁻¹ * D.x * g = D.a)
    (hB : D.caseB) :
    (∀ i < 9, D.FusN i ([0, 0, 0, 3, 3, 5, 6, 3, 5].getD i i)) ∧ ¬ D.FusN 3 0 ∧ ¬ D.FusN 3 2 ∧
      IsSylowOf 2 ((D.S : Subgroup G) ⊓ centralizer ({D.a3a4} : Set G))
        (centralizer ({D.a3a4} : Set G)) ∧
      (∃ g ∈ D.M, g⁻¹ * D.y * g = D.x) ∧ (∃ g ∈ D.M, g⁻¹ * D.a1a4 * g = D.a3a4) ∧
      (∃ m ∈ D.M, m⁻¹ * D.t * m = D.a1l) ∧
      ((D.toMb.sylowXt D.pPrimeCore_Mb D.z_comm_Mb : Sylow 2 D.toMb.Xt) :
        Subgroup D.toMb.Xt).index = 3 ∧
      ∃ n : G, n⁻¹ * D.a * n = D.a3a4 ∧ n⁻¹ * D.t * n = D.z ∧
        (n⁻¹ * D.z * n = D.t ∨ n⁻¹ * D.z * n = D.t * D.z) ∧
        ∃ s₁ ∈ (D.S : Subgroup G), ∃ s₂ ∈ (D.S : Subgroup G),
          n⁻¹ * (s₁⁻¹ * D.x * s₁) * n = s₂⁻¹ * D.al * s₂ ∨
            n⁻¹ * (s₁⁻¹ * D.al * s₁) * n = s₂⁻¹ * D.x * s₂ := by
  have hE : ∀ {g u : G}, g ∈ D.M → u ∈ D.E → g⁻¹ * u * g ∈ (D.S : Subgroup G) →
      g⁻¹ * u * g ∈ D.E := fun hg hu hS => D.conj_mem_E_of_M hC hg hu hS
  have hF : ∀ {g u : G}, g ∈ D.M → u ∈ D.F → g⁻¹ * u * g ∈ (D.S : Subgroup G) →
      g⁻¹ * u * g ∈ D.F := fun hg hu hS => D.conj_mem_F_of_M hC hB hg hu hS
  have e5 : SE.invRep (Fin.ofNat 9 5) = SE.gen 6 := by decide
  rcases D.a_fusion hidx hxa with ⟨g, hgu, hgood, hgC⟩ | ⟨g, hgu, hgood, hgC, hsyl⟩
  · exfalso
    obtain ⟨h17, h73, hedge, -⟩ := D.aZ_decode hgu hgC hgood
    have h70 : D.FusN 7 0 := D.fusN_of_conj_rep (i := 7) (j := 0)
      (by rw [show SE.invRep 0 = SE.gen 0 by decide]; exact hgu)
    have h58 : D.FusN 5 8 := D.fusN_of_edge (g := g) (by rw [e5]; exact hedge)
    refine D.false_of_aZ_B hidx hE hF fun i hi => ?_
    interval_cases i
    · exact D.fusN_refl 0
    · exact D.fusN_trans h17 h70
    · exact D.fusN_refl 2
    · exact D.fusN_trans (D.fusN_symm h73) h70
    · exact D.fusN_refl 4
    · exact D.fusN_refl 5
    · exact D.fusN_refl 6
    · exact h70
    · exact D.fusN_symm h58
  · obtain ⟨h10, hedge, s, hsS, hsa, hst, hsz, -⟩ := D.aA34_decode hgu hgC hgood
    have h73 : D.FusN 7 3 := D.fusN_of_conj_rep (i := 7) (j := 3) hgu
    have h85 : D.FusN 8 5 := by
      obtain ⟨s₁, hs₁, s₂, hs₂, h | h⟩ := hedge
      · exact D.fusN_symm (D.fusN_of_edge (g := g) ⟨s₁, hs₁, s₂, hs₂, by rw [e5]; exact h⟩)
      · exact D.fusN_of_edge (g := g) ⟨s₁, hs₁, s₂, hs₂, by rw [e5]; exact h⟩
    have h30 := (D.not_fusN_of_lt (i := 3) (j := 0) hsyl (by decide)).1
    have h32 := (D.not_fusN_of_lt (i := 3) (j := 2) hsyl (by decide)).1
    have hP1 : ∀ i < 9, D.FusN i ([0, 0, 2, 3, 4, 5, 6, 3, 5].getD i i) := fun i hi => by
      interval_cases i
      · exact D.fusN_refl 0
      · exact h10
      · exact D.fusN_refl 2
      · exact D.fusN_refl 3
      · exact D.fusN_refl 4
      · exact D.fusN_refl 5
      · exact D.fusN_refl 6
      · exact h73
      · exact h85
    obtain ⟨g₁, hg₁M, hg₁⟩ := D.a1a4_fusion_B hidx hE hF hP1 h30 h32
    have h3 := D.index_three_B hC hB hg₁M hg₁
    obtain ⟨m, hmM, hm⟩ := D.conj_t_a1l_B hC hB h3
    have h12 : D.FusN 1 2 := D.fusN_of_conj_rep (i := 1) (j := 2) hm
    have h43 : D.FusN 4 3 := D.fusN_of_conj_rep (i := 4) (j := 3) hg₁
    have hP2 : ∀ i < 9, D.FusN i ([0, 0, 0, 3, 3, 5, 6, 3, 5].getD i i) := fun i hi => by
      interval_cases i
      · exact D.fusN_refl 0
      · exact h10
      · exact D.fusN_trans (D.fusN_symm h12) h10
      · exact D.fusN_refl 3
      · exact h43
      · exact D.fusN_refl 5
      · exact D.fusN_refl 6
      · exact h73
      · exact h85
    refine ⟨hP2, h30, h32, hsyl, D.y_fusion_B hidx hE hF hP2 h30 h32, ⟨g₁, hg₁M, hg₁⟩,
      ⟨m, hmM, hm⟩, h3, g * s, hsa, hst, hsz, ?_⟩
    obtain ⟨s₁, hs₁, s₂, hs₂, h | h⟩ := hedge
    · refine ⟨s₁, hs₁, s₂ * s, mul_mem hs₂ hsS, Or.inl ?_⟩
      rw [conj_conj, h]
      group
    · refine ⟨s₁, hs₁, s₂ * s, mul_mem hs₂ hsS, Or.inr ?_⟩
      rw [conj_conj, h]
      group

end GHSylow

end CFSG.ComponentClassification.GHarris
