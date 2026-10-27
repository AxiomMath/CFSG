module

public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalRankThreeStabilizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBRankFourCoverage
import CFSG.LocalAnalysis.SectionRank.AmbientRank

public section

namespace CFSG.ComponentClassification.UnbalancedCorr

open Subgroup CFSG.LargeEvenClassification CFSG.ComponentClassification.LiteratureLocal

variable {G : Type*} [Group G] [Finite G]

theorem rankThree_path_of_four_le {A B V : Subgroup G} (hA : A ∈ E3 G) (hB : B ∈ E3 G)
    (hVA : V ≤ A) (hVB : V ≤ B) (hV : Nat.card V = 4) : RankThreeSubgroupPath A B := by
  have h1 : Nat.card ↥(A ⊓ B) ∣ 8 := hA.2 ▸ Subgroup.card_dvd_of_le inf_le_left
  have h2 : 4 ≤ Nat.card ↥(A ⊓ B) := hV ▸ Subgroup.card_le_of_le (le_inf hVA hVB)
  have h3 : Nat.card ↥(A ⊓ B) ≤ 8 := Nat.le_of_dvd (by norm_num) h1
  obtain ⟨d, hd⟩ : ∃ d, Nat.card ↥(A ⊓ B) = d := ⟨_, rfl⟩
  rw [hd] at h1 h2 h3
  interval_cases d
  · exact rankThree_path_of_intersection_four A B hA hB hd
  · norm_num at h1
  · norm_num at h1
  · norm_num at h1
  · have hAeq : A ⊓ B = A := eq_of_le_of_card_ge inf_le_left (by rw [hd, hA.2])
    have hBeq : A ⊓ B = B := eq_of_le_of_card_ge inf_le_right (by rw [hd, hB.2])
    rw [← hAeq, hBeq]
    exact rankThree_path_refl B hB

omit [Finite G] in
theorem centralizer_le_normalizer_set (V : Subgroup G) :
    centralizer (V : Set G) ≤ normalizer (V : Set G) := by
  intro x hx
  rw [mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have h1 : h * x = x * h := mem_centralizer_iff.mp hx h hh
    rwa [show x * h * x⁻¹ = h by rw [← h1, mul_inv_cancel_right]]
  · intro hh
    have h1 : x * h * x⁻¹ * x = x * (x * h * x⁻¹) := mem_centralizer_iff.mp hx _ hh
    have h2 : x * h * x⁻¹ = h := by
      have h3 : x * h = x * (x * h * x⁻¹) := by
        rw [← h1]
        group
      exact (mul_left_cancel h3).symm
    rwa [h2] at hh

omit [Finite G] in
theorem isElemAbelian_two_of_le {E E' : Subgroup G} (hE : Open.IsElemAbelian 2 E)
    (hle : E' ≤ E) : Open.IsElemAbelian 2 E' := by
  obtain ⟨hc, hpow⟩ := hE
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => hpow x (hle hx)⟩
  have h1 := congrArg Subtype.val (hc.is_comm.comm ⟨x, hle x.2⟩ ⟨y, hle y.2⟩)
  exact h1

theorem pRank_two_eq_open (X : Subgroup G) : CFSG.pRank 2 ↥X = Open.pRank 2 X :=
  CFSG.SectionRank.pRank_coe_eq_openPRank 2 X

theorem exists_four_le_of_two_le_pRank {Q : Subgroup G} (hQ : 2 ≤ CFSG.pRank 2 ↥Q) :
    ∃ V : Subgroup G, V ≤ Q ∧ Open.IsElemAbelian 2 V ∧ Nat.card V = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E, hEQ, hE, hEcard⟩ := SectionRank.exists_pRank (p := 2) one_lt_two Q
  rw [← pRank_two_eq_open] at hEcard
  have hdvd : 2 ^ 2 ∣ Nat.card E := hEcard ▸ pow_dvd_pow 2 hQ
  obtain ⟨W, hW⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥E) 2 hdvd
  refine ⟨W.map E.subtype, (map_subtype_le W).trans hEQ, isElemAbelian_two_of_le hE
    (map_subtype_le W), ?_⟩
  rw [card_map_of_injective E.subtype_injective, hW]
  norm_num

theorem perfect_group_full_core_or_isolated_four_escape {G : Type} [Group G] [Finite G]
    (hperf : commutator G = ⊤) (hrank : 3 ≤ CFSG.pRank 2 G) (hconn : ¬ Conn3 G)
    (S : Sylow 2 G) {Estar : Subgroup G} (hEstar : Estar ∈ E3 G) (hEstarS : Estar ≤ S)
    {K : Subgroup G}
    (hK : K = ⨆ (Q : Subgroup G) (_ : Q ≤ (S : Subgroup G)) (_ : 2 ≤ CFSG.pRank 2 ↥Q),
      normalizer (Q : Set G)) :
    rankThreeClassStabilizer Estar < ⊤ ∧
    Xor (K ≤ rankThreeClassStabilizer Estar)
      (∃ V : Subgroup G, V ≤ S ∧ IsElementaryAbelian 2 V ∧ Nat.card V = 4 ∧
        CFSG.pRank 2 ↥((S : Subgroup G) ⊓ centralizer (V : Set G)) = 2 ∧
        ∃ x : G, orderOf x = 2 ∧ x ∈ centralizer (V : Set G) ∧
          x ∉ rankThreeClassStabilizer Estar) ∧
    (K ≤ rankThreeClassStabilizer Estar → K < ⊤) ∧
    ((∃ V : Subgroup G, V ≤ S ∧ IsElementaryAbelian 2 V ∧ Nat.card V = 4 ∧
        CFSG.pRank 2 ↥((S : Subgroup G) ⊓ centralizer (V : Set G)) = 2 ∧
        ∃ x : G, orderOf x = 2 ∧ x ∈ centralizer (V : Set G) ∧
          x ∉ rankThreeClassStabilizer Estar) →
      ∃ V : Subgroup G, V ≤ S ∧ IsElementaryAbelian 2 V ∧ Nat.card V = 4 ∧
        CFSG.pRank 2 ↥((S : Subgroup G) ⊓ centralizer (V : Set G)) = 2 ∧
        (∃ x : G, orderOf x = 2 ∧ x ∈ centralizer (V : Set G) ∧
          x ∉ rankThreeClassStabilizer Estar) ∧
        (∀ E ∈ E3 G, V ≤ E → ¬ E ≤ rankThreeClassStabilizer Estar) ∧
        ¬ normalizer (V : Set G) ≤ rankThreeClassStabilizer Estar) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := rankThreeClassStabilizer Estar with hMdef
  obtain ⟨-, -, hΔ, -, -, hMtop⟩ :=
    SymmetricLocal.rank_three_component_stabilizer_vertices hrank S hEstar hEstarS
  obtain ⟨-, hctrl⟩ := rank_three_component_normalizer_control hrank S
  obtain ⟨-, -, -, hVctrl, -, -⟩ := hctrl Estar hEstar hEstarS
  have hMlt : M < ⊤ := lt_top_iff_ne_top.mpr fun h => hconn (hMtop.mp h)
  have hrank' : 3 ≤ CFSG.Assembly.twoRank G := by
    have h1 := hrank
    rw [SectionRank.pRank_eq_open_pRank_top] at h1
    exact h1
  have hel : ∀ V : Subgroup G, IsElementaryAbelian 2 V ↔ Open.IsElemAbelian 2 V := fun V =>
    SectionRank.isElementaryAbelian_iff_isElemAbelian 2 V
  have hcover : ∀ V : Subgroup G, Open.IsElemAbelian 2 V → Nat.card V = 4 →
      ∃ E ∈ E3 G, V ≤ E := by
    intro V hV hV4
    obtain ⟨E, hE, hE8, hVE⟩ := UnbalancedGS.perfect_four_rank_three_coverage G hperf hrank' V
      hV hV4
    exact ⟨E, ⟨hE, hE8⟩, hVE⟩
  have hEC : ∀ E ∈ E3 G, ∀ V : Subgroup G, V ≤ E → E ≤ centralizer (V : Set G) := by
    intro E hE V hVE x hx
    rw [mem_centralizer_iff]
    intro v hv
    exact congrArg Subtype.val (hE.1.1.is_comm.comm (⟨v, hVE hv⟩ : E) ⟨x, hx⟩)
  have hNV : ∀ V : Subgroup G, Nat.card V = 4 → ∀ E ∈ rankThreeClass Estar, V ≤ E →
      normalizer (V : Set G) ≤ M := by
    intro V hV4 E hE hVE g hg
    apply mem_rankThreeClassStabilizer_of_mem hE
    have hVg : CFSG.conjugate V g = V := conjugate_eq_of_mem_normalizer hg
    have hVEg : V ≤ CFSG.conjugate E g := hVg ▸ conjugate_mono' g hVE
    exact ⟨conjugate_mem_E3 hE.1 g, rankThree_path_trans
      (rankThree_path_of_four_le (conjugate_mem_E3 hE.1 g) hE.1 hVEg hVE hV4) hE.2⟩
  have hstepA : (∀ V : Subgroup G, V ≤ S → Open.IsElemAbelian 2 V → Nat.card V = 4 →
      normalizer (V : Set G) ≤ M) → K ≤ M := by
    intro hall
    have hΔV : ∀ V : Subgroup G, V ≤ S → Open.IsElemAbelian 2 V → Nat.card V = 4 →
        ∃ E ∈ rankThreeClass Estar, V ≤ E := by
      intro V hVS hV hV4
      obtain ⟨E, hE, hVE⟩ := hcover V hV hV4
      refine ⟨E, ?_, hVE⟩
      rw [hΔ]
      exact ⟨hE, (hEC E hE V hVE).trans
        ((centralizer_le_normalizer_set V).trans (hall V hVS hV hV4))⟩
    rw [hK]
    refine iSup₂_le fun Q hQS => iSup_le fun hQ2 => ?_
    obtain ⟨V, hVQ, hV, hV4⟩ := exists_four_le_of_two_le_pRank hQ2
    intro g hg
    obtain ⟨E, hE, hVE⟩ := hΔV V (hVQ.trans hQS) hV hV4
    have hVgS : CFSG.conjugate V g ≤ S :=
      (conjugate_mono' g hVQ).trans ((conjugate_eq_of_mem_normalizer hg).le.trans hQS)
    have hVgE3 : CFSG.conjugate V g ∈ {V' : Subgroup G | Open.IsElemAbelian 2 V' ∧
        Nat.card V' = 4} :=
      ⟨Helpers.elementary_map V hV _, (card_conjugate' V g).trans hV4⟩
    obtain ⟨F, hF, hVgF⟩ := hΔV (CFSG.conjugate V g) hVgS hVgE3.1 hVgE3.2
    apply mem_rankThreeClassStabilizer_of_mem hE
    exact ⟨conjugate_mem_E3 hE.1 g, rankThree_path_trans
      (rankThree_path_of_four_le (conjugate_mem_E3 hE.1 g) hF.1 (conjugate_mono' g hVE) hVgF
        hVgE3.2) hF.2⟩
  have hstepB : ¬ K ≤ M → ∃ V : Subgroup G, V ≤ S ∧ IsElementaryAbelian 2 V ∧ Nat.card V = 4 ∧
      CFSG.pRank 2 ↥((S : Subgroup G) ⊓ centralizer (V : Set G)) = 2 ∧
      (∃ x : G, orderOf x = 2 ∧ x ∈ centralizer (V : Set G) ∧ x ∉ M) ∧
      (∀ E ∈ E3 G, V ≤ E → ¬ E ≤ M) ∧ ¬ normalizer (V : Set G) ≤ M := by
    intro hnot
    obtain ⟨V, hVS, hV, hV4, hVN⟩ : ∃ V : Subgroup G, V ≤ S ∧ Open.IsElemAbelian 2 V ∧
        Nat.card V = 4 ∧ ¬ normalizer (V : Set G) ≤ M := by
      by_contra h
      push Not at h
      exact hnot (hstepA fun V hVS hV hV4 => h V hVS hV hV4)
    have hle2 : CFSG.pRank 2 ↥((S : Subgroup G) ⊓ centralizer (V : Set G)) ≤ 2 := by
      by_contra h3
      push Not at h3
      exact hVN (hVctrl V hVS ((hel V).mpr hV) hV4 h3)
    have hge2 : 2 ≤ CFSG.pRank 2 ↥((S : Subgroup G) ⊓ centralizer (V : Set G)) := by
      rw [pRank_two_eq_open]
      exact SectionRank.le_pRank one_lt_two
        (le_inf hVS (UnbalancedGS.RankFourCoverage.le_centralizer_of_isElemAbelian hV)) hV
        (by rw [hV4]; norm_num)
    have hnoE : ∀ E ∈ E3 G, V ≤ E → ¬ E ≤ M := by
      intro E hE hVE hEM
      have hEΔ : E ∈ rankThreeClass Estar := by
        rw [hΔ]
        exact ⟨hE, hEM⟩
      exact hVN (hNV V hV4 E hEΔ hVE)
    obtain ⟨E, hE, hVE⟩ := hcover V hV hV4
    obtain ⟨x, hxE, hxM⟩ := IsConcreteLE.not_le_iff_exists.mp (hnoE E hE hVE)
    have hx1 : x ≠ 1 := fun h => hxM (h ▸ one_mem M)
    have hx2 : orderOf x = 2 := orderOf_eq_prime (hE.1.2 x hxE) hx1
    exact ⟨V, hVS, (hel V).mpr hV, hV4, le_antisymm hle2 hge2,
      ⟨x, hx2, hEC E hE V hVE hxE, hxM⟩, hnoE, hVN⟩
  have hstepC : K ≤ M → ¬ ∃ V : Subgroup G, V ≤ S ∧ IsElementaryAbelian 2 V ∧ Nat.card V = 4 ∧
      CFSG.pRank 2 ↥((S : Subgroup G) ⊓ centralizer (V : Set G)) = 2 ∧
      ∃ x : G, orderOf x = 2 ∧ x ∈ centralizer (V : Set G) ∧ x ∉ M := by
    rintro hKM ⟨V, hVS, hV, hV4, -, x, -, hxC, hxM⟩
    apply hxM
    apply hKM
    have hV2 : 2 ≤ CFSG.pRank 2 ↥V := by
      rw [pRank_two_eq_open]
      exact SectionRank.le_pRank one_lt_two le_rfl ((hel V).mp hV) (by rw [hV4]; norm_num)
    rw [hK]
    exact mem_iSup_of_mem V (mem_iSup_of_mem hVS (mem_iSup_of_mem hV2
      (centralizer_le_normalizer_set V hxC)))
  refine ⟨hMlt, xor_iff_iff_not.mpr ⟨hstepC, fun hnb => ?_⟩,
    fun hKM => lt_of_le_of_lt hKM hMlt, fun hii => ?_⟩
  · by_contra hna
    obtain ⟨V, hVS, hV, hV4, h2, hx, -, -⟩ := hstepB hna
    exact hnb ⟨V, hVS, hV, hV4, h2, hx⟩
  · by_cases hKM : K ≤ M
    · exact absurd hii (hstepC hKM)
    · exact hstepB hKM

end CFSG.ComponentClassification.UnbalancedCorr
