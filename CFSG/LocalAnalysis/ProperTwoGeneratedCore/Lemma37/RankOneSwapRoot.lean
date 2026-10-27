module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankOneSwap
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankOneNormal

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {H : Subgroup G} {z : G}
  {J : Subgroup (EscapingQuotient z)}

namespace RankOneSetting

variable (h : RankOneSetting G S H z J) {s : EscapingQuotient z}
  (hsS : s ∈ escapingSylowImage S z)
  (hs : s ∉ Subgroup.normalizer (J : Set (EscapingQuotient z)))
include h hs

theorem le_centralizer_swap :
    J ≤ Subgroup.centralizer ((swapComponent J s : Subgroup _) : Set (EscapingQuotient z)) := by
  intro j hj
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  exact (Subgroup.mem_centralizer_iff.mp (h.swap_le_centralizer hs hg) j hj).symm

theorem exists_mul_eq_of_mem_normalizer_sup {t : EscapingQuotient z}
    (htS : t ∈ escapingSylowImage S z)
    (htN : t ∈ Subgroup.normalizer (J : Set (EscapingQuotient z)))
    (htJJ : t ∈ J ⊔ swapComponent J s) :
    ∃ c ∈ escapingSylowImage S z, c ∈ J ∧ ∃ c' ∈ escapingSylowImage S z,
      c' ∈ swapComponent J s ∧ c * c' = t := by
  have hJJ : J ≤
      Subgroup.normalizer ((swapComponent J s : Subgroup _) : Set (EscapingQuotient z)) :=
    (h.le_centralizer_swap hs).trans (Subgroup.centralizer_le_normalizer _)
  have ht' : t ∈ ((J : Set (EscapingQuotient z)) *
      ((swapComponent J s : Subgroup _) : Set (EscapingQuotient z))) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hJJ]
    exact htJJ
  obtain ⟨c, hcJ, c', hc'J', rfl⟩ := ht'
  have hcc' : Commute c c' :=
    Subgroup.mem_centralizer_iff.mp (h.swap_le_centralizer hs hc'J') c hcJ
  obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp h.sylowImage_isPGroup) ⟨c * c', htS⟩
  rw [Subgroup.orderOf_mk] at hn
  have hpow : (c * c') ^ 2 ^ n = 1 := by rw [← hn, pow_orderOf_eq_one]
  rw [hcc'.mul_pow] at hpow
  have hc2 : c ^ 2 ^ (n + 1) = 1 := by
    have hmem : c ^ 2 ^ n ∈ swapComponent J s := by
      rw [eq_inv_of_mul_eq_one_left hpow]
      exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hc'J' _)
    rcases h.eq_of_mem_inf_of_ne h.component h.swap_isComponent (swapComponent_ne hs).symm
      (J.pow_mem hcJ _) hmem with h1 | h1
    · rw [pow_succ, pow_mul, h1, one_pow]
    · rw [pow_succ, pow_mul, h1, h.bar_sq]
  have hcN : c ∈ Subgroup.normalizer
      ((escapingSylowImage S z ⊓ J : Subgroup (EscapingQuotient z)) :
        Set (EscapingQuotient z)) := by
    have htN' : c * c' ∈ Subgroup.normalizer
        ((escapingSylowImage S z ⊓ J : Subgroup (EscapingQuotient z)) : Set (EscapingQuotient z)) :=
      Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer htS, htN⟩
    have hc'N : c'⁻¹ ∈ Subgroup.normalizer
        ((escapingSylowImage S z ⊓ J : Subgroup (EscapingQuotient z)) :
        Set (EscapingQuotient z)) := by
      apply Subgroup.centralizer_le_normalizer
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact (Subgroup.mem_centralizer_iff.mp
        (Subgroup.inv_mem _ (h.swap_le_centralizer hs hc'J')) g hg.2)
    have := Subgroup.mul_mem _ htN' hc'N
    rwa [mul_inv_cancel_right] at this
  have hcS := h.mem_sylowImage_of_mem_normalizer hcJ hc2 hcN
  refine ⟨c, hcS, hcJ, c', ?_, hc'J', rfl⟩
  have := (escapingSylowImage S z).mul_mem ((escapingSylowImage S z).inv_mem hcS) htS
  rwa [inv_mul_cancel_left] at this

include hsS in
theorem exists_sq_eq_bar_swap (hs2 : s * s ∈ J ⊔ swapComponent J s) :
    ∃ y ∈ escapingSylowImage S z, y ∉ Subgroup.normalizer (J : Set (EscapingQuotient z)) ∧
      y ^ 2 = escapingBar z := by
  set N := Subgroup.normalizer (J : Set (EscapingQuotient z)) with hN
  have hsN2 : s * s ∈ N := by
    have := h.inv_mul_mem_normalizer_swap hs (u := s⁻¹) (v := s)
      (fun h1 => hs (by simpa using N.inv_mem h1)) hs
    rwa [inv_inv] at this
  obtain ⟨c, hcS, hcJ, c', -, hc'J', hcc'⟩ := h.exists_mul_eq_of_mem_normalizer_sup hs
    ((escapingSylowImage S z).mul_mem hsS hsS) hsN2 hs2
  have hcN : c ∈ N := Subgroup.le_normalizer hcJ
  have hyS : s * c⁻¹ ∈ escapingSylowImage S z :=
    (escapingSylowImage S z).mul_mem hsS ((escapingSylowImage S z).inv_mem hcS)
  have hyN : s * c⁻¹ ∉ N := fun h1 => hs (by
    have := N.mul_mem h1 hcN
    rwa [inv_mul_cancel_right] at this)
  have hA : s * c * s⁻¹ ∈ swapComponent J s := ⟨c, hcJ, rfl⟩
  have hB : s * c' * s⁻¹ ∈ J := by
    obtain ⟨j, hj, rfl⟩ := hc'J'
    have := (Subgroup.mem_normalizer_iff.mp hsN2 j).mp hj
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show s * (s * j * s⁻¹) * s⁻¹ = s * s * j * (s * s)⁻¹ by group]
    exact this
  have hcomm : ∀ a ∈ swapComponent J s, ∀ b ∈ J, a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.mp (h.swap_le_centralizer hs ha) b hb).symm
  have hy2 : (s * c⁻¹) ^ 2 = (s * c * s⁻¹)⁻¹ * c' := by
    have hc'c : c' * c⁻¹ = c⁻¹ * c' := hcomm c' hc'J' c⁻¹ (J.inv_mem hcJ)
    calc (s * c⁻¹) ^ 2 = (s * c * s⁻¹)⁻¹ * (s * s) * c⁻¹ := by rw [pow_two]; group
      _ = (s * c * s⁻¹)⁻¹ * (c * c') * c⁻¹ := by rw [hcc']
      _ = (s * c * s⁻¹)⁻¹ * (c * (c' * c⁻¹)) := by group
      _ = (s * c * s⁻¹)⁻¹ * c' := by rw [hc'c]; group
  have hAB : (s * c * s⁻¹)⁻¹ * c' = c⁻¹ * (s * c' * s⁻¹) := by
    have h1 : (s * c * s⁻¹) * (s * c' * s⁻¹) = c * c' := by
      calc (s * c * s⁻¹) * (s * c' * s⁻¹) = s * (c * c') * s⁻¹ := by group
        _ = s * (s * s) * s⁻¹ := by rw [hcc']
        _ = s * s := by group
        _ = c * c' := hcc'.symm
    rw [eq_inv_mul_of_mul_eq h1]
    have hAc : (s * c * s⁻¹)⁻¹ * c⁻¹ = c⁻¹ * (s * c * s⁻¹)⁻¹ :=
      hcomm _ (Subgroup.inv_mem _ hA) _ (J.inv_mem hcJ)
    calc (s * c * s⁻¹)⁻¹ * c' = ((s * c * s⁻¹)⁻¹ * c⁻¹) * c * c' := by group
      _ = (c⁻¹ * (s * c * s⁻¹)⁻¹) * c * c' := by rw [hAc]
      _ = c⁻¹ * ((s * c * s⁻¹)⁻¹ * (c * c')) := by group
  have hyJ : (s * c⁻¹) ^ 2 ∈ J := by
    rw [hy2, hAB]
    exact J.mul_mem (J.inv_mem hcJ) hB
  have hyJ' : (s * c⁻¹) ^ 2 ∈ swapComponent J s := by
    rw [hy2]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hA) hc'J'
  refine ⟨s * c⁻¹, hyS, hyN, ?_⟩
  rcases h.eq_of_mem_inf_of_ne h.component h.swap_isComponent (swapComponent_ne hs).symm hyJ hyJ'
    with h1 | h1
  · exact absurd (h.mem_normalizer_of_mul_self_eq_one hs hyS (by rw [← pow_two]; exact h1)) hyN
  · exact h1

end RankOneSetting

end CFSG.ProperTwoGeneratedCore.Lemma37
