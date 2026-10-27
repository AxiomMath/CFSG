module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8G2Gamma

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoExceptional

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull
open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.RankTwoClassical (Sec3)
open CFSG.Blueprint.Chevalley CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.Open (IsElemAbelian)

section Count

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G}
  {K : Type} [Field K] [Finite K] [CharP K 2]
  {ψ : normalizer (A : Set G) →* MulAut ↥(adjointGroup .G2 K)}

theorem le_sup_lift_of_conj
    (h4 : Asc75Theorem4) (h32 : Lemma32)
    (h184 : G2Centr184) (h184s : G2Centr184s) (hK4 : 4 ≤ Nat.card K) (hc : Sec3 A R T g)
    (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A))))
    (hZA : Odd (Nat.card (center A)))
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    (hnolong : ¬ ∃ (T' : Subgroup G) (g' : G), Sec3 A R T' g' ∧ G2Pinned ψ T' g2c ∧
      ActsIn ψ T' (rootSubgroup .G2 K g2c))
    {x : G} (hx : rightConjugate R x ≤ R ⊔ twoLift ψ (g2ShortRadical K))
    (hne : rightConjugate R x ≠ R) :
    ∃ α γ : K, rightConjugate R x ≤ R ⊔ twoLift ψ (g2YGroup K α γ) := by
  have h34 : Asc08Lemma34 := asc08Lemma34
  have hZ : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G)) := by
    rwa [RankTwoL3Even.card_inf_centralizer_eq]
  have hZC := LieType.Chevalley.center_adjointGroup_eq_bot (τ := .G2) (K := K)
  have hinj := RankTwoHypIIY.conj_injective_of_center_eq_bot hZC
  have hRBe := isElemAbelian_sup_twoLift h32 hc hZA hψ
  have hRBK := sup_twoLift_inf_centralizer hc hZA hψ
  have hxN : x ∉ normalizer (A : Set G) := by
    intro hxN
    apply hne
    have hKx : rightConjugate (centralizer (A : Set G)) x = centralizer (A : Set G) := by
      rw [← centralizer_rightConjugate, (rightConjugate_eq_self_iff A x).2 hxN]
    have h1 : rightConjugate R x ≤ (R ⊔ twoLift ψ (g2ShortRadical K)) ⊓
        centralizer (A : Set G) := le_inf hx (hKx ▸ map_mono hc.sylowR.le)
    rw [hRBK] at h1
    exact eq_of_le_of_card_ge h1 (by rw [rightConjugate_card])
  have hcx : Sec3 A R (rightConjugate R x) x := by
    refine ⟨hc.hyp, hc.sylowR, hxN, AschbacherTheorem3.isSylowOf_rightConjugate hc.sylowR x, ?_⟩
    exact hx.trans ((le_centralizer_self_of_isElemAbelian hRBe).trans
      (centralizer_le fun v hv => mem_sup_left hv))
  obtain ⟨a, ha, hlong | hshort⟩ := g2_exists_pinned h4 h32 h184 h184s hcx hOut hK4 hψ
  · exact absurd ⟨_, _, sec3_conj hcx ha, hlong.1, hlong.2⟩ hnolong
  have hca := sec3_conj hcx ha
  obtain ⟨c, hc'⟩ := hψ.map_mem a ha
  have key : ∀ r' ∈ rightConjugate R x, ∃ r ∈ R, ∃ b : G,
      ∃ hb : b ∈ twoLift ψ (g2ShortRadical K),
      r * b = r' ∧ ∃ s : K, ψ ⟨b, le_normalizer (twoLift_le hb)⟩ =
        MulAut.conj (c * g2Xc g2v s * c⁻¹) := by
    intro r' hr'
    obtain ⟨r, hr, b, hb, hrb⟩ := exists_mul_of_mem_sup_twoLift hc _ (hx hr')
    refine ⟨r, hr, b, hb, hrb, ?_⟩
    have hmem : a⁻¹ * r' * a ∈ rightConjugate (rightConjugate R x) a := by
      rw [mem_rightConjugate_iff]
      simpa [mul_assoc] using hr'
    have hN := hca.le_normalizer hmem
    obtain ⟨y, hy⟩ := exists_psi_eq_conj hca h32 h4 h34 hψ hmem hN
    obtain ⟨s, hs⟩ := mem_rootSubgroup.1 (hshort.2 _ hmem hN y hy)
    have hy' : y = g2Xc g2v s := Subtype.ext hs.symm
    refine ⟨s, ?_⟩
    have hbA := twoLift_le hb
    have hr'N : r' ∈ normalizer (A : Set G) := hcx.le_normalizer hr'
    have hrN : r ∈ normalizer (A : Set G) := centralizer_le_normalizer _ (hc.sylowR.le hr)
    have e1 : ψ ⟨b, le_normalizer hbA⟩ = ψ ⟨r', hr'N⟩ := by
      have e : (⟨r', hr'N⟩ : normalizer (A : Set G)) = ⟨r, hrN⟩ * ⟨b, le_normalizer hbA⟩ :=
        Subtype.ext hrb.symm
      rw [e, map_mul, (hψ.eq_one_iff ⟨r, hrN⟩).2 (hc.sylowR.le hr), one_mul]
    have e2 : (⟨r', hr'N⟩ : normalizer (A : Set G)) =
        ⟨a, le_normalizer ha⟩ * ⟨a⁻¹ * r' * a, hN⟩ * ⟨a, le_normalizer ha⟩⁻¹ :=
      Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group)
    rw [e1, e2, map_mul, map_mul, map_inv, ← hc', hy, hy']
    simp only [map_mul, map_inv]
  obtain ⟨⟨r'₀, hr'₀⟩, hne1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hcx.T_ne_bot
  have hne1' : r'₀ ≠ 1 := fun h => hne1 (Subtype.ext h)
  obtain ⟨r₀, hr₀, b₀, hb₀, hrb₀, s₀, hb₀ψ⟩ := key r'₀ hr'₀
  have hs₀ : s₀ ≠ 0 := by
    rintro rfl
    apply hne1'
    have h0 : g2Xc g2v (0 : K) = 1 := Subtype.ext (pinnedX_zero .G2 K g2v)
    rw [h0, mul_one, mul_inv_cancel, map_one] at hb₀ψ
    have hb1 : b₀ = 1 := eq_of_sq_eq_one hψ hZ (twoLift_le hb₀) (one_mem A)
      (sq_eq_one_of_mem_twoLift hψ hZ g2ShortRadical_comm hb₀) (one_pow 2)
      (by rw [hb₀ψ]; exact (map_one ψ).symm)
    rw [hb1, mul_one] at hrb₀
    have h1 : r'₀ ∈ R ⊓ rightConjugate R x := mem_inf.2 ⟨hrb₀ ▸ hr₀, hr'₀⟩
    rwa [hcx.inf_eq_bot, mem_bot] at h1
  have hmemAv : (c : ModGL .G2 K) * pinnedX .G2 K g2v s₀ * (c : ModGL .G2 K)⁻¹ ∈
      g2ShortRadical K := by
    obtain ⟨_, -, y₀, hy₀, hy₀U⟩ := (mem_twoLift hψ hZ g2ShortRadical_comm).1 hb₀
    rw [hb₀ψ] at hy₀
    have h1 := congrArg Subtype.val (hinj hy₀)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    rw [h1]
    exact hy₀U
  obtain ⟨α, γ, μ, -, hall⟩ := g2_conj_v_eq_of_mem_radical h184 hK4 c.2 hs₀ hmemAv
  refine ⟨α, γ, fun r' hr' => ?_⟩
  obtain ⟨r, hr, b, hb, hrb, s, hbψ⟩ := key r' hr'
  have hbY : b ∈ twoLift ψ (g2YGroup K α γ) := by
    refine mem_twoLift_of (twoLift_le hb)
      (sq_eq_one_of_mem_twoLift hψ hZ g2ShortRadical_comm hb) hbψ ?_
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hall s]
    exact ⟨μ * s, rfl⟩
  rw [← hrb]
  exact mul_mem (mem_sup_left hr) (mem_sup_right hbY)

end Count

section Count3

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G}
  {K : Type} [Field K] [Finite K] [CharP K 2]
  {ψ : normalizer (A : Set G) →* MulAut ↥(adjointGroup .G2 K)}

omit [Finite G] in
theorem map_conj_one (H : Subgroup G) : H.map (MulAut.conj (1 : G)).toMonoidHom = H := by
  ext y
  rw [mem_map_equiv, MulAut.conj_symm_apply, inv_one, one_mul, mul_one]

omit [Finite G] in
theorem map_conj_eq_rightConjugate (H : Subgroup G) (u : G) :
    H.map (MulAut.conj u).toMonoidHom = rightConjugate H u⁻¹ := by
  rw [rightConjugate, inv_inv]

end Count3

end CFSG.ComponentClassification.RankTwoExceptional
