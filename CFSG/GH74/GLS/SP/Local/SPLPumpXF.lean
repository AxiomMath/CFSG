module

public import CFSG.GH74.GLS.SP.Local.SPLPumpXE
public import CFSG.GH74.GLS.SP.Local.SPLRankTools

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin
open scoped commutatorElement

theorem center_eq_bot_of_simple_quasisimple {K : Type} [Group K] (hs : IsSimpleGroup K)
    (hq : IsQuasisimple K) : center K = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center K) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hq.2.2
    have : Subsingleton (K ⧸ center K) := by
      rw [h]
      exact QuotientGroup.subsingleton_quotient_top
    exact hab (Subsingleton.elim _ _)

namespace XCtx

variable {X : Type} [Group X] [Finite X] {z t : X} {A T₁ : Subgroup X}

theorem inf_eq_bot_of_comm (hX : XCtx X z t A T₁) {K : Subgroup X}
    (hK : ∀ k ∈ K, ∀ a ∈ A, k * a = a * k) : A ⊓ K = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  have hz : (⟨a, ha.1⟩ : ↥A) ∈ center ↥A := by
    rw [Subgroup.mem_center_iff]
    intro b
    exact Subtype.ext (hK a ha.2 b b.2).symm
  rw [hX.A_quasisimple.2, Subgroup.mem_bot] at hz
  exact (Subgroup.mem_bot).mpr (congrArg Subtype.val hz)

theorem A_rank_one (hX : XCtx X z t A T₁) : RankCertified ↥A 1 :=
  rankCertified_one_of_quasisimple hX.A_quasisimple.1

theorem other_not_mem (hX : XCtx X z t A T₁) {K : Subgroup X} (hK : OtherL z A K)
    (hq : IsQuasisimple ↥K) (ht : t ∉ K) : False := by
  have hd : A ⊓ K = ⊥ := hX.inf_eq_bot_of_comm hK.comm_A
  have hcomm : ∀ a ∈ A, ∀ k ∈ K, a * k = k * a := fun a ha k hk => (hK.comm_A k hk a ha).symm
  have h3 : RankCertified ↥(A ⊔ K) (1 + 1 + 1) :=
    rankCertified_sup_of_commute hcomm hd hX.A_rank_one (rankCertified_one_of_quasisimple hq)
  have htAK : t ∉ A ⊔ K := by
    intro hmem
    obtain ⟨a, ha, k, hk, hak⟩ := mem_sup_of_comm hcomm hmem
    apply ht
    have hka : ∀ a' ∈ A, k⁻¹ * a' = a' * k⁻¹ := fun a' ha' => by
      have h1 := hK.comm_A k hk a' ha'
      calc k⁻¹ * a' = k⁻¹ * (a' * k) * k⁻¹ := by group
        _ = k⁻¹ * (k * a') * k⁻¹ := by rw [← h1]
        _ = a' * k⁻¹ := by group
    have hat : a = t * k⁻¹ := by rw [← hak]; group
    have hz : (⟨a, ha⟩ : ↥A) ∈ center ↥A := by
      rw [Subgroup.mem_center_iff]
      intro b
      apply Subtype.ext
      show (b : X) * a = a * b
      rw [hat]
      calc (b : X) * (t * k⁻¹) = (b * t) * k⁻¹ := by group
        _ = (t * b) * k⁻¹ := by rw [hX.t_central b]
        _ = t * (b * k⁻¹) := by group
        _ = t * (k⁻¹ * b) := by rw [hka b b.2]
        _ = (t * k⁻¹) * b := by group
    rw [hX.A_quasisimple.2, Subgroup.mem_bot] at hz
    have ha1 : a = 1 := congrArg Subtype.val hz
    have : t = k := by rw [← hak, ha1, one_mul]
    rw [this]
    exact hk
  have h4 := h3.of_central_involution hX.t_central hX.t_sq htAK
  exact h4.not_gen4 (by norm_num) hX.gen4

theorem other_false_of_rank2 (hX : XCtx X z t A T₁) {K : Subgroup X} (hK : OtherL z A K)
    (hrank : RankCertified ↥K 2) : False := by
  have hd : A ⊓ K = ⊥ := hX.inf_eq_bot_of_comm hK.comm_A
  have hcomm : ∀ a ∈ A, ∀ k ∈ K, a * k = k * a := fun a ha k hk => (hK.comm_A k hk a ha).symm
  have h4 : RankCertified ↥(A ⊔ K) (1 + 2 + 1) :=
    rankCertified_sup_of_commute hcomm hd hX.A_rank_one hrank
  exact h4.of_subgroup.not_gen4 (by norm_num) hX.gen4

theorem other_False
    (hG : Generic.GenericKnownFacts) (hF : E2.E2ComponentFacts) (hOUI : OtherUniqueInvolution)
    (hX : XCtx X z t A T₁) {K : Subgroup X} (hK : OtherL z A K) (hq : IsQuasisimple ↥K)
    (hshape : InC2 ↥K ∨ InT2 ↥K) : False := by
  by_cases ht : t ∈ K
  · have htz : (⟨t, ht⟩ : ↥K) ∈ center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hX.t_central g)
    have hnb : center ↥K ≠ ⊥ := by
      intro h
      rw [h, Subgroup.mem_bot] at htz
      exact hX.t_ne_one (congrArg Subtype.val htz)
    rcases hshape with hC | hT
    · rcases c2ShapeG_of_inC2 hG hF hC (Gen4.subgroup K hX.gen4) with hz | h2M | h2S
      · exact hnb hz
      · exact hX.other_false_of_rank2 hK (rankCertified_two_of_2M12 h2M)
      · exact hX.other_false_of_rank2 hK (rankCertified_two_of_2Sz8 h2S)
    · obtain ⟨-, hcases⟩ := hT
      rcases hcases with ⟨p, f, hp, hf, ⟨hodd, hnfm⟩, hlie⟩ | hSL | hA7 | ⟨n, hn7, hn11, hn⟩ | ⟨hlq, hexp⟩
      · obtain ⟨-, -, F, _, _, hF', ⟨e⟩⟩ := Generic.lieModel_psl_data hlie
        have hp2 : 2 ≤ p ^ f := (hp.one_lt).trans_le (Nat.le_self_pow (by omega) p)
        have hL2F : IVK.L2Field F := ⟨hF' ▸ hodd, hF' ▸ three_lt_of_not_fm9 hodd hp2 hnfm⟩
        have hsimple : IsSimpleGroup ↥K := (MulEquiv.isSimpleGroup_congr e).mpr
          (IVK.Proofs2.isSimpleGroup_of_l2 hL2F (MulEquiv.refl _))
        exact hnb (center_eq_bot_of_simple_quasisimple hsimple hq)
      · exact hOUI X z t A T₁ K hX hK ht hq (Or.inl hSL)
      · obtain ⟨e⟩ := hA7
        have hsimple : IsSimpleGroup ↥K := (MulEquiv.isSimpleGroup_congr e).mpr
          (alternatingGroup.isSimpleGroup (by norm_num))
        exact hnb (center_eq_bot_of_simple_quasisimple hsimple hq)
      · by_cases h7 : n = 7
        · subst h7
          exact hOUI X z t A T₁ K hX hK ht hq (Or.inr hn)
        · exact hX.other_false_of_rank2 hK (rankCertified_two_of_doubleCoverAlt (by omega) hn)
      · exact hX.other_false_of_rank2 hK (rankCertified_two_of_L34Cover hlq)
  · exact hX.other_not_mem hK hq ht

end XCtx

end CFSG.GH74.GLS.SP.Local
