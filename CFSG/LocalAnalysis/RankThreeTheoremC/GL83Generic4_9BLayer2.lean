module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_9Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Reduced3
public import CFSG.LocalAnalysis.AGLEmbedding.ReducedComponents

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools CFSG.AGLEmbedding Subgroup

namespace Gen49BHyp

variable {p : ℕ} [Fact p.Prime] {Y : Type} [Group Y] [Finite Y] {S R Γ : Subgroup Y} {x : Y}

theorem gen49bl_ne_two (h : Gen49BHyp p S R Γ x) : p ≠ 2 := h.ne_two

theorem gen49bl_pow_eq_one (h : Gen49BHyp p S R Γ x) : x ^ p = 1 := h.elemAbelian.2 x h.mem

theorem gen49bl_orderOf_eq (h : Gen49BHyp p S R Γ x) : orderOf x = p :=
  orderOf_eq_prime h.gen49bl_pow_eq_one h.ne_one

theorem gen49bl_commute (h : Gen49BHyp p S R Γ x) {a b : Y} (ha : a ∈ S) (hb : b ∈ S) :
    a * b = b * a :=
  congrArg Subtype.val ((isMulCommutative_iff.mp h.abelian) ⟨a, ha⟩ ⟨b, hb⟩)

theorem gen49bl_exists_sylow (h : Gen49BHyp p S R Γ x) :
    ∃ Q : Sylow p Y, (Q : Subgroup Y) = S := by
  refine ⟨Sylow.ofCard S ?_, Sylow.coe_ofCard _ _⟩
  rw [h.sylow.card_eq, card_top]

theorem gen49bl_mem_of_pow_eq_one (h : Gen49BHyp p S R Γ x) {t : Y} (ht : t ∈ S)
    (htp : t ^ p = 1) : t ∈ R := by
  have hp : p.Prime := Fact.out
  have hcomm : R ≤ centralizer ((zpowers t : Subgroup Y) : Set Y) := fun r hr => by
    rw [mem_centralizer_iff]
    intro c hc
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hc
    exact (Commute.zpow_left (h.gen49bl_commute ht (h.le_sylow hr)) k).eq
  have hE : IsElemAbelian p (R ⊔ zpowers t) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_sup_of_commuting p h.elemAbelian
      (isElemAbelian_zpowers htp) hcomm
  have heq : R = R ⊔ zpowers t :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_subgroup_eq_of_rank_bound p hp hE le_sup_left 2
      h.card_eq ((CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp le_top).trans h.pRank_le)
  have : t ∈ R ⊔ zpowers t := mem_sup_right (mem_zpowers t)
  rwa [← heq] at this

theorem gen49bl_center_eq_bot (h : Gen49BHyp p S R Γ x) (hR0 : CFSG.pCore p Y = ⊥)
    {K : Subgroup Y} (hK : IsComponentOf K ⊤) : center K = ⊥ :=
  center_eq_bot_of_centralizer_layer_eq_bot
    (centralizer_layer_eq_bot_of_pCore_eq_bot h.core_eq_bot hR0) hK

theorem gen49bl_inf_eq_bot (h : Gen49BHyp p S R Γ x) (hR0 : CFSG.pCore p Y = ⊥)
    {K K' : Subgroup Y} (hK : IsComponentOf K ⊤) (hK' : IsComponentOf K' ⊤) (hne : K ≠ K') :
    K ⊓ K' = ⊥ := by
  have hZ := h.gen49bl_center_eq_bot hR0 hK
  have hc : K' ≤ centralizer (K : Set Y) :=
    commutator_eq_bot_iff_le_centralizer.mp
      (CFSG.ComponentClassification.LocalComponents.commute_of_ne K' K hK' hK (Ne.symm hne))
  refine eq_bot_iff.mpr fun z hz => ?_
  have hzc : (⟨z, hz.1⟩ : K) ∈ center K := mem_center_iff.mpr fun k =>
    Subtype.ext (mem_centralizer_iff.mp (hc hz.2) k k.2)
  rw [hZ, mem_bot] at hzc
  exact congrArg Subtype.val hzc

theorem gen49bl_mem_normalizer (h : Gen49BHyp p S R Γ x) {K : Subgroup Y}
    (hK : IsComponentOf K ⊤) {s : Y} (hs : s ∈ S) : s ∈ normalizer (K : Set Y) := by
  by_contra hsK
  obtain ⟨Q, hQ⟩ := h.gen49bl_exists_sylow
  obtain ⟨t, ⟨htS, htK⟩, -, htC⟩ :=
    exists_mem_sylow_inf_component Fact.out h.gen49bl_ne_two h.core_eq_bot Q hK
  rw [hQ] at htS
  have hne : K.map (MulAut.conj s).toMonoidHom ≠ K := fun he =>
    hsK (mem_normalizer_iff_map_conj_eq.mpr he)
  have hK' : IsComponentOf (K.map (MulAut.conj s).toMonoidHom) ⊤ :=
    (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj s) K).mpr hK
  have hc : K.map (MulAut.conj s).toMonoidHom ≤ centralizer (K : Set Y) :=
    commutator_eq_bot_iff_le_centralizer.mp
      (CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ hK' hK hne)
  refine htC (hc ⟨t, htK, ?_⟩)
  change s * t * s⁻¹ = t
  rw [h.gen49bl_commute hs htS, mul_inv_cancel_right]

end Gen49BHyp

end CFSG.LocalAnalysis.RankThreeTheoremC
