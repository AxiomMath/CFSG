module

public import CFSG.GroupTheory.SylowIntersectionControl.SingularSubgroup.Regular
import CFSG.GroupTheory.SylowIntersectionControl.Regular
import CFSG.GroupTheory.SylowIntersectionControl.GomiOverCore
import CFSG.Quasithin.Background.C1GNNotation
import CFSG.Quasithin.Background.C1PackSolvBasic
import CFSG.Quasithin.Background.SmithC27Setup
import CFSG.GroupTheory.NormalizerInfCentralizer
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Basic

public section

namespace CFSG.GroupTheory.GomiThm45Counterexample

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {Ω : Type} [Group Ω] [Finite Ω] {c : GNPairChoice Ω} {G S : Subgroup Ω}

omit [Finite Ω] in
private theorem le_normalizer_inf_centralizer_g45c :
    G ≤ Subgroup.normalizer
      ((G ⊓ Subgroup.centralizer (gomiV G : Set Ω) : Subgroup Ω) : Set Ω) := by
  intro g hg
  exact mem_normalizer_inf_centralizer ((gomiV_moduleSetting G).2 hg)
    (Subgroup.le_normalizer hg)

open scoped Pointwise in
private theorem frattini_mul_normalizer_g45c {N T : Subgroup Ω} (hNG : N ≤ G)
    (hN : G ≤ Subgroup.normalizer (N : Set Ω))
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T N) :
    (N : Set Ω) *
      ((G ⊓ Subgroup.normalizer (T : Set Ω) : Subgroup Ω) : Set Ω) = G := by
  have hsup : N ⊔ (G ⊓ Subgroup.normalizer (T : Set Ω)) = G :=
    le_antisymm (sup_le hNG inf_le_left)
      (CFSG.Quasithin.B6.frattini_two hNG hN
        (CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.mpr hT))
  have h := Subgroup.coe_mul_of_right_le_normalizer_left N
    (G ⊓ Subgroup.normalizer (T : Set Ω)) (inf_le_left.trans hN)
  rw [hsup] at h
  exact h.symm

private theorem centralizer_sup_sylow_ne_top_g45c (h : GomiThm45Counterexample c G S) :
    (G ⊓ Subgroup.centralizer (gomiV G : Set Ω)) ⊔ S ≠ G := by
  intro hCS
  have hVle : omegaOneCenterOf S ≤ gomiV G :=
    omegaOneCenterOf_le_gomiV_of_pCoreOf_le h.hyp43.charTwo h.isSylowTwoOf.1
      (CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf h.isSylowTwoOf)
  have hCnorm : G ⊓ Subgroup.centralizer (gomiV G : Set Ω) ≤
      Subgroup.normalizer (omegaOneCenterOf S : Set Ω) :=
    (inf_le_right : G ⊓ Subgroup.centralizer (gomiV G : Set Ω) ≤
        Subgroup.centralizer (gomiV G : Set Ω)).trans
      ((Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hVle)).trans
        (Subgroup.centralizer_le_normalizer (omegaOneCenterOf S : Set Ω)))
  have hSnorm : S ≤ Subgroup.normalizer (omegaOneCenterOf S : Set Ω) :=
    (Subgroup.le_centralizer_iff.mpr
      ((CFSG.Quasithin.C1GN.omegaOneCenterOf_le_centerOf S).trans
        (show CFSG.Quasithin.centerOf S ≤ Subgroup.centralizer (S : Set Ω) from
          inf_le_right))).trans
      (Subgroup.centralizer_le_normalizer (omegaOneCenterOf S : Set Ω))
  have hGnorm : G ≤ Subgroup.normalizer (omegaOneCenterOf S : Set Ω) := by
    rw [← hCS]
    exact sup_le hCnorm hSnorm
  refine h.not_isRegular (c.selection.isRegular_of_le_normalizer
    (CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.mp h.isSylowTwoOf) ?_ hGnorm)
  change omegaOneCenterOf S ∈
    ({c.C₁ S, c.C₂ S, omegaOneCenterOf S} : Set (Subgroup Ω))
  simp

open scoped Pointwise in
theorem isSylowTwoOf_pCoreOf_of_sup_ne (h : GomiThm45Counterexample c G S) {N : Subgroup Ω}
    (hNG : N ≤ G) (hN : G ≤ Subgroup.normalizer (N : Set Ω)) (hNS : N ⊔ S ≠ G) :
    IsSylowTwoOf (pCoreOf 2 N) N := by
  have hTN : CFSG.ABGLocalTools.IsSylowOf 2 (S ⊓ N) N :=
    (CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.mp
      h.isSylowTwoOf).inf_of_le_normalizer hNG hN
  have hfr := frattini_mul_normalizer_g45c hNG hN hTN
  have hSK : S ≤ G ⊓ Subgroup.normalizer ((S ⊓ N : Subgroup Ω) : Set Ω) := by
    intro s hs
    exact ⟨h.isSylowTwoOf.1 hs,
      Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hs, hN (h.isSylowTwoOf.1 hs)⟩⟩
  have hHK : ((N ⊔ S : Subgroup Ω) : Set Ω) *
      ((G ⊓ Subgroup.normalizer ((S ⊓ N : Subgroup Ω) : Set Ω) : Subgroup Ω) : Set Ω) =
        G := by
    refine Set.eq_of_subset_of_subset ?_ ?_
    · intro x hx
      rw [Set.mem_mul] at hx
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      exact G.mul_mem ((sup_le hNG h.isSylowTwoOf.1) ha) hb.1
    · intro g hg
      have hg' : g ∈ (N : Set Ω) *
          ((G ⊓ Subgroup.normalizer ((S ⊓ N : Subgroup Ω) : Set Ω) : Subgroup Ω) :
            Set Ω) := by
        rw [hfr]
        exact hg
      rw [Set.mem_mul] at hg'
      obtain ⟨n, hn, k, hk, rfl⟩ := hg'
      rw [Set.mem_mul]
      exact ⟨n, (le_sup_left : N ≤ N ⊔ S) hn, k, hk, rfl⟩
  rcases h.eq_or_eq_of_mul_eq (le_sup_right : S ≤ N ⊔ S) hSK hHK with hH | hK
  · exact absurd hH hNS
  · have hNT : N ≤ Subgroup.normalizer ((S ⊓ N : Subgroup Ω) : Set Ω) :=
      hNG.trans ((le_of_eq hK.symm).trans inf_le_right)
    have hleT : S ⊓ N ≤ pCoreOf 2 N :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right hNT hTN.isPGroup
    have hEq : pCoreOf 2 N = S ⊓ N :=
      hTN.eq_of_le hleT (CFSG.LieType.BorelTits.pCoreOf_le 2 N)
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N)
    rw [hEq]
    exact CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.mpr hTN

theorem isSylowTwoOf_pCoreOf_centralizer (h : GomiThm45Counterexample c G S) :
    IsSylowTwoOf (pCoreOf 2 G) (G ⊓ Subgroup.centralizer (gomiV G : Set Ω)) := by
  have hC_sylow : IsSylowTwoOf (pCoreOf 2 (G ⊓ Subgroup.centralizer (gomiV G : Set Ω)))
      (G ⊓ Subgroup.centralizer (gomiV G : Set Ω)) :=
    isSylowTwoOf_pCoreOf_of_sup_ne h inf_le_left le_normalizer_inf_centralizer_g45c
      (centralizer_sup_sylow_ne_top_g45c h)
  have hQ : pCoreOf 2 (G ⊓ Subgroup.centralizer (gomiV G : Set Ω)) = pCoreOf 2 G := by
    refine le_antisymm ?_ ?_
    · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer
        (N := pCoreOf 2 (G ⊓ Subgroup.centralizer (gomiV G : Set Ω))) (H := G) 2 ?_ ?_ ?_
      · exact (CFSG.LieType.BorelTits.pCoreOf_le 2
          (G ⊓ Subgroup.centralizer (gomiV G : Set Ω))).trans inf_le_left
      · refine le_normalizer_inf_centralizer_g45c.trans ?_
        exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2
          (G ⊓ Subgroup.centralizer (gomiV G : Set Ω))
      · exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2
          (G ⊓ Subgroup.centralizer (gomiV G : Set Ω))
    · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer (N := pCoreOf 2 G)
        (H := G ⊓ Subgroup.centralizer (gomiV G : Set Ω)) 2
        (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 G)
          (CFSG.Quasithin.SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf G)) ?_
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G)
      exact inf_le_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 G)
  simpa [hQ] using hC_sylow

theorem inf_centralizer_inf_le_pCoreOf
    (h : GomiThm45Counterexample c G S) :
    G ⊓ Subgroup.centralizer (gomiV G : Set Ω) ⊓ S ≤ pCoreOf 2 G := by
  have hC_sylow : IsSylowTwoOf (pCoreOf 2 G)
      (G ⊓ Subgroup.centralizer (gomiV G : Set Ω)) :=
    isSylowTwoOf_pCoreOf_centralizer h
  refine CFSG.Quasithin.B6.le_of_isPGroup_of_odd_relIndex inf_le_left ?_
    (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 G)
      (CFSG.Quasithin.SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf G)) ?_ ?_
  · exact h.isSylowTwoOf.2.1.to_inf_right
  · exact inf_le_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 G)
  · simpa only [Subgroup.relIndex] using hC_sylow.2.2

private theorem sup_sylow_ne_of_two_quotient_g45c (h : GomiThm45Counterexample c G S)
    {N : Subgroup Ω} (hCN : G ⊓ Subgroup.centralizer (gomiV G : Set Ω) ≤ N)
    (hNG : N ≤ G) (hN : G ≤ Subgroup.normalizer (N : Set Ω))
    (h2 : ∀ x ∈ N, ∃ k : ℕ, x ^ 2 ^ k ∈ Subgroup.centralizer (gomiV G : Set Ω)) :
    N ⊔ S ≠ G := by
  have hNC' : N ≤ Subgroup.normalizer
      ((G ⊓ Subgroup.centralizer (gomiV G : Set Ω) : Subgroup Ω) : Set Ω) :=
    hNG.trans le_normalizer_inf_centralizer_g45c
  have h2' : ∀ d ∈ N, ∃ k : ℕ, d ^ 2 ^ k ∈
      G ⊓ Subgroup.centralizer (gomiV G : Set Ω) := by
    intro d hd
    obtain ⟨k, hk⟩ := h2 d hd
    exact ⟨k, ⟨pow_mem (hNG hd) (2 ^ k), hk⟩⟩
  have hTN : IsSylowTwoOf (S ⊓ N) N :=
    CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.mpr
      ((CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.mp
        h.isSylowTwoOf).inf_of_le_normalizer hNG hN)
  have hsup : (G ⊓ Subgroup.centralizer (gomiV G : Set Ω)) ⊔ (S ⊓ N) = N :=
    CFSG.Quasithin.B6.sup_eq_of_isTwoQuotient hCN hNC' h2' hTN
  have hNS_eq : N ⊔ S = (G ⊓ Subgroup.centralizer (gomiV G : Set Ω)) ⊔ S := by
    have hS : (S ⊓ N) ⊔ S = S := sup_eq_right.mpr inf_le_left
    rw [← hsup, sup_assoc, hS]
  rw [hNS_eq]
  exact centralizer_sup_sylow_ne_top_g45c h

theorem eq_centralizer_of_isPGroup_quotient (h : GomiThm45Counterexample c G S)
    {N : Subgroup Ω} (hCN : G ⊓ Subgroup.centralizer (gomiV G : Set Ω) ≤ N) (hNG : N ≤ G)
    (hN : G ≤ Subgroup.normalizer (N : Set Ω))
    (h2 : ∀ x ∈ N, ∃ k : ℕ, x ^ 2 ^ k ∈ Subgroup.centralizer (gomiV G : Set Ω)) :
    N = G ⊓ Subgroup.centralizer (gomiV G : Set Ω) := by
  have hNC' : N ≤ Subgroup.normalizer
      ((G ⊓ Subgroup.centralizer (gomiV G : Set Ω) : Subgroup Ω) : Set Ω) :=
    hNG.trans le_normalizer_inf_centralizer_g45c
  have h2' : ∀ d ∈ N, ∃ k : ℕ, d ^ 2 ^ k ∈
      G ⊓ Subgroup.centralizer (gomiV G : Set Ω) := by
    intro d hd
    obtain ⟨k, hk⟩ := h2 d hd
    exact ⟨k, ⟨pow_mem (hNG hd) (2 ^ k), hk⟩⟩
  have hNS_ne : N ⊔ S ≠ G := sup_sylow_ne_of_two_quotient_g45c h hCN hNG hN h2
  have hN_sylow : IsSylowTwoOf (pCoreOf 2 N) N :=
    isSylowTwoOf_pCoreOf_of_sup_ne h hNG hN hNS_ne
  have hpc : pCoreOf 2 N ≤ G ⊓ Subgroup.centralizer (gomiV G : Set Ω) := by
    refine (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer (N := pCoreOf 2 N)
      (H := G) 2 ?_ ?_ ?_).trans (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 G)
        (CFSG.Quasithin.SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf G))
    · exact (CFSG.LieType.BorelTits.pCoreOf_le 2 N).trans hNG
    · refine hN.trans ?_
      exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 N
    · exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N
  obtain ⟨n, hn⟩ := CFSG.Quasithin.B6.exists_relIndex_eq_two_pow hNC' h2'
  have hdvd : (G ⊓ Subgroup.centralizer (gomiV G : Set Ω)).relIndex N ∣
      (pCoreOf 2 N).relIndex N :=
    ⟨(pCoreOf 2 N).relIndex (G ⊓ Subgroup.centralizer (gomiV G : Set Ω)), by
      rw [mul_comm]
      exact (Subgroup.relIndex_mul_relIndex (pCoreOf 2 N)
        (G ⊓ Subgroup.centralizer (gomiV G : Set Ω)) N hpc hCN).symm⟩
  have hodd : ¬ 2 ∣ (pCoreOf 2 N).relIndex N := by
    simpa only [Subgroup.relIndex] using hN_sylow.2.2
  have hn0 : n = 0 := by
    by_contra hne
    have h2n : 2 ∣ (G ⊓ Subgroup.centralizer (gomiV G : Set Ω)).relIndex N := by
      rw [hn]
      exact dvd_pow_self 2 hne
    exact hodd (h2n.trans hdvd)
  have hone : (G ⊓ Subgroup.centralizer (gomiV G : Set Ω)).relIndex N = 1 := by
    rw [hn, hn0, pow_zero]
  exact le_antisymm (Subgroup.relIndex_eq_one.mp hone) hCN

open scoped Pointwise in
theorem centralizer_le_of_isMaxSubgroupIn (h : GomiThm45Counterexample c G S)
    {H : Subgroup Ω} (hH : IsMaxSubgroupIn G H) (hSH : S ≤ H) :
    G ⊓ Subgroup.centralizer (gomiV G : Set Ω) ≤ H := by
  by_contra hnot
  have hCG : G ⊓ Subgroup.centralizer (gomiV G : Set Ω) ≤ G := inf_le_left
  have hlt : H < G ⊓ Subgroup.centralizer (gomiV G : Set Ω) ⊔ H :=
    lt_of_le_of_ne le_sup_right fun heq => hnot (by rw [heq]; exact le_sup_left)
  have hsup : G ⊓ Subgroup.centralizer (gomiV G : Set Ω) ⊔ H = G :=
    hH.2 _ hlt (sup_le hCG hH.1.le)
  have hprod : ((G ⊓ Subgroup.centralizer (gomiV G : Set Ω) ⊔ S : Subgroup Ω) : Set Ω) *
      H = G := by
    have h0 : ((G ⊓ Subgroup.centralizer (gomiV G : Set Ω) : Subgroup Ω) : Set Ω) * H = G := by
      have h := Subgroup.coe_mul_of_right_le_normalizer_left
        (G ⊓ Subgroup.centralizer (gomiV G : Set Ω)) H
        (hH.1.le.trans le_normalizer_inf_centralizer_g45c)
      rw [hsup] at h
      exact h.symm
    refine Set.eq_of_subset_of_subset ?_ ?_
    · intro x hx
      rw [Set.mem_mul] at hx
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      exact G.mul_mem ((sup_le hCG h.isSylowTwoOf.1) ha) (hH.1.le hb)
    · intro g hg
      have hg' : g ∈ (G ⊓ Subgroup.centralizer (gomiV G : Set Ω) : Set Ω) * H := by
        change g ∈ ((G ⊓ Subgroup.centralizer (gomiV G : Set Ω) : Subgroup Ω) : Set Ω) * H
        rw [h0]
        exact hg
      rw [Set.mem_mul] at hg'
      obtain ⟨a, ha, b, hb, rfl⟩ := hg'
      rw [Set.mem_mul]
      refine ⟨a, ?_, b, hb, rfl⟩
      exact Subgroup.mem_sup_left ha
  rcases h.eq_or_eq_of_mul_eq (le_sup_right : S ≤ _) hSH hprod with hH' | hH'
  · exact centralizer_sup_sylow_ne_top_g45c h hH'
  · exact absurd hH' (ne_of_lt hH.1)

theorem not_thompsonJ_le_centralizer (h : GomiThm45Counterexample c G S) :
    ¬ thompsonJ S ≤ Subgroup.centralizer (gomiV G : Set Ω) := by
  intro hJ
  have hC'SQ : G ⊓ Subgroup.centralizer (gomiV G : Set Ω) ⊓ S ≤ pCoreOf 2 G :=
    inf_centralizer_inf_le_pCoreOf h
  have hJQ : thompsonJ S ≤ pCoreOf 2 G := by
    have h1 : thompsonJ S ≤ G ⊓ Subgroup.centralizer (gomiV G : Set Ω) :=
      le_inf ((CFSG.Quasithin.B6.thompsonJ_le S).trans h.isSylowTwoOf.1) hJ
    exact (le_inf h1 (CFSG.Quasithin.B6.thompsonJ_le S)).trans hC'SQ
  have hQS : pCoreOf 2 G ≤ S :=
    CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf h.isSylowTwoOf
  have hJeq : thompsonJ (pCoreOf 2 G) = thompsonJ S :=
    CFSG.Quasithin.B6.thompsonJ_eq_of_le hJQ hQS
  have hVle : gomiV G ≤ omegaOneCenterOf (thompsonJ (pCoreOf 2 G)) := by
    simpa [gomiV] using
      CFSG.Quasithin.C1Pack.omegaOneCenterOf_le_omegaOneCenterOf_thompsonJ
        (pCoreOf 2 G)
  have hbaum_le : baum S ≤ pCoreOf 2 G := by
    have h1 : baum S ≤ S ⊓ Subgroup.centralizer (gomiV G : Set Ω) := by
      refine le_inf (show baum S ≤ S from inf_le_left) ?_
      refine (inf_le_right : baum S ≤
        Subgroup.centralizer (omegaOneCenterOf (thompsonJ S) : Set Ω)).trans ?_
      refine Subgroup.centralizer_le ?_
      rw [← hJeq]
      exact hVle
    have h2 : S ⊓ Subgroup.centralizer (gomiV G : Set Ω) ≤
        G ⊓ Subgroup.centralizer (gomiV G : Set Ω) :=
      le_inf (inf_le_left.trans h.isSylowTwoOf.1) inf_le_right
    exact (le_inf (h1.trans h2) (show baum S ≤ S from inf_le_left)).trans hC'SQ
  have hbaum_eq : baum S = baum (pCoreOf 2 G) :=
    CFSG.Quasithin.baum_eq_of_le hbaum_le hQS
  have hGNorm : G ≤ Subgroup.normalizer (baum (pCoreOf 2 G) : Set Ω) :=
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 G).trans
      (CFSG.Quasithin.normalizer_le_normalizer_baum (pCoreOf 2 G))
  have hGNormC1 : G ≤ Subgroup.normalizer (c.C₁ S : Set Ω) := by
    refine hGNorm.trans ?_
    rw [← hbaum_eq]
    exact c.normalizer_baum_le_normalizer_C₁ h.isSylowTwoOf.2.1
  refine h.not_isRegular (c.selection.isRegular_of_le_normalizer
    (CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.mp h.isSylowTwoOf) ?_ hGNormC1)
  change c.C₁ S ∈ ({c.C₁ S, c.C₂ S, omegaOneCenterOf S} : Set (Subgroup Ω))
  simp

omit [Finite Ω] in
theorem gomiV_le_pCoreOf (G : Subgroup Ω) : gomiV G ≤ pCoreOf 2 G :=
  CFSG.Quasithin.C1GN.omegaOneCenterOf_le_self (pCoreOf 2 G)

theorem gomiV_le_sylow (h : GomiThm45Counterexample c G S) : gomiV G ≤ S :=
  (gomiV_le_pCoreOf G).trans
    (CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf h.isSylowTwoOf)

theorem exists_isMaxElemAbelian_not_le_centralizer (h : GomiThm45Counterexample c G S) :
    ∃ A : Subgroup Ω, IsMaxElemAbelian S A ∧
      ¬ A ≤ Subgroup.centralizer (gomiV G : Set Ω) := by
  by_contra hcon
  push Not at hcon
  refine not_thompsonJ_le_centralizer h ?_
  rw [thompsonJ]
  exact iSup₂_le fun B hB => hcon B hB

end CFSG.GroupTheory.GomiThm45Counterexample
