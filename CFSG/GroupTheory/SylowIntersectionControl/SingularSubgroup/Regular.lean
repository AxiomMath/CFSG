module

public import CFSG.GroupTheory.SylowIntersectionControl.SingularSubgroup.Counterexample
import CFSG.GroupTheory.SylowIntersectionControl.GomiOverCore
import CFSG.GroupTheory.SylowIntersectionControl.Regular
import CFSG.Quasithin.Background.B6Basic
import CFSG.Quasithin.Background.C1GNNotation
import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCShort
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Basic

public section

namespace CFSG.GroupTheory.GomiThm45Counterexample

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped Pointwise

variable {Ω : Type} [Group Ω] [Finite Ω] {c : GNPairChoice Ω} {G S : Subgroup Ω}

private theorem pCoreOf_le_pCoreOf_g45r {G H : Subgroup Ω} (hQH : pCoreOf 2 G ≤ H)
    (hHG : H ≤ G) : pCoreOf 2 G ≤ pCoreOf 2 H :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hQH
    (hHG.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 G))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G)

omit [Finite Ω] in
theorem eq_top_of_isPGroup_quotient_of_twoResidual_eq {K : Subgroup Ω}
    (hK : twoResidual K = K) (N' : Subgroup ↥K) [hNn : N'.Normal]
    (hN' : IsPGroup 2 (↥K ⧸ N')) : N' = ⊤ := by
  have hmap : N'.map K.subtype ≤ K := fun x hx => by
    obtain ⟨y, -, rfl⟩ := hx
    exact y.2
  have hn : K ≤ Subgroup.normalizer ((N'.map K.subtype : Subgroup Ω) : Set Ω) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨⟨k, hk⟩ * y * ⟨k, hk⟩⁻¹, hNn.conj_mem y hy _, ?_⟩
      simp
    · rintro ⟨y, hy, hyx⟩
      have h1 : (⟨k, hk⟩ : ↥K)⁻¹ * y * (⟨k, hk⟩ : ↥K)⁻¹⁻¹ ∈ N' :=
        hNn.conj_mem y hy _
      rw [inv_inv] at h1
      refine ⟨_, h1, ?_⟩
      simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
      have hyx' : (y : Ω) = k * x * k⁻¹ := hyx
      rw [hyx']
      group
  have h2 : ∀ y ∈ K, ∃ k : ℕ, y ^ 2 ^ k ∈ N'.map K.subtype := by
    intro y hy
    obtain ⟨k, hk⟩ := hN' (QuotientGroup.mk ⟨y, hy⟩)
    refine ⟨k, ⟨⟨y, hy⟩ ^ 2 ^ k, ?_, rfl⟩⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk
    exact hk
  have h3 : K ≤ N'.map K.subtype :=
    hK.symm.le.trans (CFSG.Quasithin.twoResidual_le_of_isTwoQuotient hmap hn h2)
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, hy, hyx⟩ := h3 x.2
  have : y = x := Subtype.ext hyx
  rwa [this] at hy

open scoped commutatorElement in
private theorem commutator_gomiV_eq_g45r {G H T X : Subgroup Ω}
    (hcharG : CharTwo G) (hHG : H ≤ G) (hQH : pCoreOf 2 G ≤ H)
    (hX : IsGomiSingularSubgroup H T X) :
    ⁅gomiV H, X⁆ = ⁅gomiV G, X⁆ := by
  have hQ_le_QH : pCoreOf 2 G ≤ pCoreOf 2 H := pCoreOf_le_pCoreOf_g45r hQH hHG
  have hWleV : gomiV H ≤ gomiV G := gomiV_le_gomiV_of_pCoreOf_le hcharG hHG hQH
  have hVleP : gomiV G ≤ pCoreOf 2 G := CFSG.Quasithin.C1GN.omegaOneCenterOf_le_self _
  have hPX : ⁅pCoreOf 2 H, X⁆ ≤ gomiV H := hX.commutator_pCoreOf_le
  have hXP : X ≤ Subgroup.normalizer (pCoreOf 2 H : Set Ω) :=
    hX.le.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H)
  have hPXeq : ⁅pCoreOf 2 H, X⁆ = ⁅⁅pCoreOf 2 H, X⁆, X⁆ :=
    (CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.commutator_commutator_eq_of_twoResidual
      (eq_top_of_isPGroup_quotient_of_twoResidual_eq hX.twoResidual_eq)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H) hXP).symm
  apply le_antisymm
  · exact Subgroup.commutator_mono hWleV le_rfl
  · calc ⁅gomiV G, X⁆ ≤ ⁅pCoreOf 2 H, X⁆ :=
          Subgroup.commutator_mono (hVleP.trans hQ_le_QH) le_rfl
      _ = ⁅⁅pCoreOf 2 H, X⁆, X⁆ := hPXeq
      _ ≤ ⁅gomiV H, X⁆ := Subgroup.commutator_mono hPX le_rfl

open scoped commutatorElement in
private theorem isGomiSingularSubgroup_mono_g45r {G S H T X : Subgroup Ω}
    (hcharG : CharTwo G) (hHG : H ≤ G) (hQH : pCoreOf 2 G ≤ H)
    (hJT : thompsonJ T = thompsonJ S) (hX : IsGomiSingularSubgroup H T X) :
    IsGomiSingularSubgroup G S X := by
  have hQ_le_QH : pCoreOf 2 G ≤ pCoreOf 2 H := pCoreOf_le_pCoreOf_g45r hQH hHG
  have hWleV : gomiV H ≤ gomiV G := gomiV_le_gomiV_of_pCoreOf_le hcharG hHG hQH
  have hcomm : ⁅gomiV H, X⁆ = ⁅gomiV G, X⁆ := commutator_gomiV_eq_g45r hcharG hHG hQH hX
  refine ⟨hX.le.trans hHG, ?_, hX.twoResidual_eq, ?_, ?_⟩
  · simpa only [hJT] using hX.eq_commutator_thompsonJ
  · exact (Subgroup.commutator_mono hQ_le_QH le_rfl).trans
      (hX.commutator_pCoreOf_le.trans hWleV)
  · obtain ⟨C, n, hn, hnat⟩ := hX.natural
    exact ⟨C, n, hn, by simpa only [hcomm] using hnat⟩

private theorem exists_singular_of_lt_g45r (h : GomiThm45Counterexample c G S)
    {H : Subgroup Ω} (hHG : H < G) (hJH : thompsonJ S ⊔ pCoreOf 2 G ≤ H)
    (hnot : ¬ c.selection.IsRegular H) :
    ∃ X : Subgroup Ω, IsGomiSingularSubgroup G S X := by
  have hQH : pCoreOf 2 G ≤ H := le_sup_right.trans hJH
  have hGH : GomiHyp43 H := GomiHyp43.of_pCoreOf_le h.hyp43 hHG.le hQH
  have hJS : thompsonJ S ≤ S := B6.thompsonJ_le S
  have hQS : pCoreOf 2 G ≤ S := B6.pCoreOf_two_le_of_isSylowTwoOf h.isSylowTwoOf
  have hP2 : IsPGroup 2 (thompsonJ S ⊔ pCoreOf 2 G : Subgroup Ω) :=
    h.isSylowTwoOf.2.1.to_le (sup_le hJS hQS)
  obtain ⟨T, hT, hPT⟩ := B6.exists_isSylowTwoOf_ge hP2 hJH
  have hJT : thompsonJ T = thompsonJ S :=
    thompsonJ_eq_of_thompsonJ_le h.isSylowTwoOf (hT.1.trans hHG.le) hT.2.1
      (le_sup_left.trans hPT)
  obtain ⟨X, hX⟩ := h.minimal H hHG hGH hnot T hT
  exact ⟨X, isGomiSingularSubgroup_mono_g45r h.hyp43.charTwo hHG.le hQH hJT hX⟩

theorem isRegular_of_lt (h : GomiThm45Counterexample c G S) {H : Subgroup Ω} (hHG : H < G)
    (hJH : thompsonJ S ⊔ pCoreOf 2 G ≤ H) : c.selection.IsRegular H := by
  by_contra hnot
  obtain ⟨X, hX⟩ := exists_singular_of_lt_g45r h hHG hJH hnot
  exact h.not_isGomiSingularSubgroup X hX

theorem eq_or_eq_of_mul_eq (h : GomiThm45Counterexample c G S) {H K : Subgroup Ω}
    (hSH : S ≤ H) (hSK : S ≤ K) (hHK : (H : Set Ω) * K = G) : H = G ∨ K = G := by
  have hJS : thompsonJ S ≤ S := B6.thompsonJ_le S
  have hQS : pCoreOf 2 G ≤ S := B6.pCoreOf_two_le_of_isSylowTwoOf h.isSylowTwoOf
  have hJH : thompsonJ S ⊔ pCoreOf 2 G ≤ H := sup_le (hJS.trans hSH) (hQS.trans hSH)
  have hJK : thompsonJ S ⊔ pCoreOf 2 G ≤ K := sup_le (hJS.trans hSK) (hQS.trans hSK)
  have hHG : H ≤ G := fun x hx => by
    have : x ∈ (H : Set Ω) * K := ⟨x, hx, 1, K.one_mem, mul_one x⟩
    rwa [hHK] at this
  have hKG : K ≤ G := fun x hx => by
    have : x ∈ (H : Set Ω) * K := ⟨1, H.one_mem, x, hx, one_mul x⟩
    rwa [hHK] at this
  by_cases hH : H = G
  · exact Or.inl hH
  · by_cases hK : K = G
    · exact Or.inr hK
    · have hHlt : H < G := lt_of_le_of_ne hHG (fun h' => hH h')
      have hKlt : K < G := lt_of_le_of_ne hKG (fun h' => hK h')
      have hrH : c.selection.IsRegular H := h.isRegular_of_lt hHlt hJH
      have hrK : c.selection.IsRegular K := h.isRegular_of_lt hKlt hJK
      exact absurd
        (PSubgroupSelection.IsRegular.of_mul_eq (f := c.selection)
          (K := G) (G₁ := H) (G₂ := K) (S := S)
          (CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.mp h.isSylowTwoOf)
          hSH hSK hHK hrH hrK)
        h.not_isRegular

end CFSG.GroupTheory.GomiThm45Counterexample
