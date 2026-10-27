module

public import CFSG.LargeExtraspecial.S5Gen2
public import CFSG.LargeExtraspecial.S5Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S5

open Subgroup Module CFSG.LargeExtraspecial.S4

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

theorem card_LmodN_le_four_of_tau_not_mem (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (h4 : finrank (ZMod 2) (Vt S g t) = 4)
    (hτ : spTransvection _ (beta_isAlt H C ht ht1 hVQ) (aV ht) ∉ LmodN S g t) :
    Nat.card (LmodN S g t) ≤ 4 := by
  have : Finite (Vt S g t ≃ₗ[ZMod 2] Vt S g t) := finite_linearEquiv_of_finite
  have hle := LmodN_le_spPointRadical H C ht ht1 hVQ
  have hlt : LmodN S g t < spPointRadical (beta H C ht ht1 hVQ) (aV ht) :=
    lt_of_le_of_ne hle fun h => hτ (h ▸ spTransvection_mem_U _ _)
  have h8 : Nat.card (spPointRadical (beta H C ht ht1 hVQ) (aV ht)) = 8 := by
    rw [card_spPointRadical (beta_isAlt H C ht ht1 hVQ) (beta_nondegenerate H C ht ht1 hVQ)
      (aV_ne_zero H ht), h4]
    norm_num
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hle
  have h2 := Subgroup.card_lt_of_lt hlt
  have hpos : 0 < Nat.card (LmodN S g t) := Nat.card_pos
  rw [h8] at hk h2
  rcases k with _ | _ | k
  · omega
  · omega
  · nlinarith

theorem eq_of_isSubnormal_of_isSimpleGroup {X : Type*} [Group X] {K B : Subgroup X}
    (hK : CFSG.Open.IsSubnormal K B) (hq : CFSG.Open.IsQuasisimple K) (hB : IsSimpleGroup B) :
    K = B :=
  (eq_bot_or_eq_of_isSubnormal_of_isSimpleGroup hK hB).resolve_left (ne_bot_of_isQuasisimple hq)

theorem false_of_isQuasisimple_of_le_solvable {X : Type*} [Group X] {K B : Subgroup X}
    (hKB : K ≤ B) (hq : CFSG.Open.IsQuasisimple K) (hB : Group.IsSolvable B) : False :=
  not_isSolvable_of_isQuasisimple hq
    (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hKB))

theorem quasisimple_of_eq_top {t : S.O} (ht : t ∈ S.Lbar g)
    {K : Subgroup (Vt S g t ≃ₗ[ZMod 2] Vt S g t)} (hKR : K = RmodN S g t) :
    (∀ x ∈ RmodN S g t, ∃ k ∈ K, ∃ e ∈ LmodN S g t, x = k * e) ∧
      (LmodN S g t ⊓ K).relIndex (LmodN S g t) ≤ 2 := by
  refine ⟨fun x hx => ⟨x, hKR ▸ hx, 1, one_mem _, (mul_one x).symm⟩, ?_⟩
  rw [hKR, inf_eq_left.mpr (LmodN_le_RmodN ht), relIndex_self]
  norm_num

theorem quasisimple_of_index_le_two {t : S.O} (ht : t ∈ S.Lbar g)
    {K : Subgroup (Vt S g t ≃ₗ[ZMod 2] Vt S g t)}
    (hgen : RmodN S g t ≤ closure {u | ∃ x ∈ RmodN S g t, ∃ e ∈ LmodN S g t, u = x * e * x⁻¹})
    (hKn : (K.subgroupOf (RmodN S g t)).Normal) (hidx : K.relIndex (RmodN S g t) ≤ 2) :
    (∀ x ∈ RmodN S g t, ∃ k ∈ K, ∃ e ∈ LmodN S g t, x = k * e) ∧
      (LmodN S g t ⊓ K).relIndex (LmodN S g t) ≤ 2 := by
  have : Finite (Vt S g t ≃ₗ[ZMod 2] Vt S g t) := finite_linearEquiv_of_finite
  exact ⟨exists_mul_of_relIndex_le_two (LmodN_le_RmodN ht) hgen hKn hidx,
    relIndex_inf_le_two (LmodN_le_RmodN ht) hidx⟩

theorem Hyp45Q.quasisimple {H : Hyp4 S g} {C : Cons311 S g} (Q : Hyp45Q H C) (hNo : NoA2 S g)
    {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hR : Rbar S g t ≠ S.Lbar g)
    {K : Subgroup (Vt S g t ≃ₗ[ZMod 2] Vt S g t)}
    (hK : CFSG.Open.IsSubnormal K (RmodN S g t)) (hq : CFSG.Open.IsQuasisimple K) :
    ((∀ x ∈ RmodN S g t, ∃ k ∈ K, ∃ e ∈ LmodN S g t, x = k * e) ∧
      (LmodN S g t ⊓ K).relIndex (LmodN S g t) ≤ 2) ∧
    (V S g t ≤ S.Qa g → K = RmodN S g t ∧ 3 ≤ finrank (ZMod 2) (Vt S g t)) ∧
    ((∃ P : Subgroup (Vt S g t ≃ₗ[ZMod 2] Vt S g t), P ≤ K ∧ IsPGroup 2 P ∧
        ¬ 2 ∣ P.relIndex K ∧ ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) →
      ¬ V S g t ≤ S.Qa g ∧ Nat.card (LmodN S g t) ≤ 4) := by
  have : Finite (Vt S g t ≃ₗ[ZMod 2] Vt S g t) := finite_linearEquiv_of_finite
  have hKR := CFSG.ClassicalInvolution.isSubnormal_le hK
  have hsimple : IsSimpleGroup (RmodN S g t) → NonabelianSylowTwo (RmodN S g t) →
      ((∀ x ∈ RmodN S g t, ∃ k ∈ K, ∃ e ∈ LmodN S g t, x = k * e) ∧
        (LmodN S g t ⊓ K).relIndex (LmodN S g t) ≤ 2) ∧ K = RmodN S g t ∧
      ((∃ P : Subgroup (Vt S g t ≃ₗ[ZMod 2] Vt S g t), P ≤ K ∧ IsPGroup 2 P ∧
          ¬ 2 ∣ P.relIndex K ∧ ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) → False) := by
    intro hs hn
    have hKe := eq_of_isSubnormal_of_isSimpleGroup hK hq hs
    refine ⟨quasisimple_of_eq_top ht hKe, hKe, ?_⟩
    rintro ⟨P, hPK, hP2, hPi, hPc⟩
    obtain ⟨x, hx, y, hy, hxy⟩ := hn P (hKe ▸ hPK) hP2 (hKe ▸ hPi)
    exact hxy (hPc x hx y hy)
  rcases timmesfeld_4_5 H hNo C ht ht1 with hR' | hL | ⟨hVQ, hSp | hA | hΩ | hP⟩
  · exact absurd hR' hR
  ·
    have h2 := hL.two_le_finrank
    rcases (show finrank (ZMod 2) (Vt S g t) = 2 ∨ 3 ≤ finrank (ZMod 2) (Vt S g t) by omega)
      with h2' | h3
    · exact (false_of_isQuasisimple_of_le_solvable hKR hq (Q.lin_two ht hL h2')).elim
    · obtain ⟨hs, hn⟩ := Q.lin ht hL h3
      obtain ⟨h1, hKe, h4⟩ := hsimple hs hn
      exact ⟨h1, fun _ => ⟨hKe, h3⟩, fun hP => (h4 hP).elim⟩
  ·
    have h4 := four_le_finrank_Vt H C ht ht1 hVQ hNo
    obtain ⟨k, hk⟩ := even_finrank_Vt H C ht ht1 hVQ
    rcases (show finrank (ZMod 2) (Vt S g t) = 4 ∨ 6 ≤ finrank (ZMod 2) (Vt S g t) by omega)
      with h4' | h6
    · obtain ⟨M₀, hM₀, hMn, hMs, hMi, hMn2⟩ := Q.sp_four ht ht1 hVQ hSp h4'
      have hKe := eq_of_isSubnormal_of_isQuasisimple hK hq hM₀ hMs hMi.le
      subst hKe
      refine ⟨quasisimple_of_index_le_two ht
        (RmodN_le_closure_conj_of_transitive H ht hSp.transitive) hMn hMi.le,
        fun h => absurd h hVQ, ?_⟩
      rintro ⟨P, hPK, hP2, hPi, hPc⟩
      obtain ⟨x, hx, y, hy, hxy⟩ := hMn2 P hPK hP2 hPi
      exact (hxy (hPc x hx y hy)).elim
    · obtain ⟨hs, hn⟩ := Q.sp ht ht1 hVQ hSp h6
      obtain ⟨h1, -, h4⟩ := hsimple hs hn
      exact ⟨h1, fun h => absurd h hVQ, fun hP => (h4 hP).elim⟩
  ·
    have hKe := eq_of_isSubnormal_of_isSimpleGroup hK hq (Q.a6 ht ht1 hVQ hA)
    exact ⟨quasisimple_of_eq_top ht hKe, fun h => absurd h hVQ, fun _ => ⟨hVQ,
      card_LmodN_le_four_of_tau_not_mem H C ht ht1 hVQ hA.finrank_eq hA.tau_not_mem⟩⟩
  ·
    have h4 := four_le_finrank_Vt H C ht ht1 hVQ hNo
    obtain ⟨k, hk⟩ := even_finrank_Vt H C ht ht1 hVQ
    rcases (show finrank (ZMod 2) (Vt S g t) = 4 ∨ 6 ≤ finrank (ZMod 2) (Vt S g t) by omega)
      with h4' | h6
    · rcases Q.omega_four ht ht1 hVQ hΩ h4' with hs | hsol
      · have hKe := eq_of_isSubnormal_of_isSimpleGroup hK hq hs
        refine ⟨quasisimple_of_eq_top ht hKe, fun h => absurd h hVQ, fun _ => ⟨hVQ, ?_⟩⟩
        obtain ⟨Qf, hQ, -, -, hE, hsing⟩ := hΩ.exists_form
        have hQa : Qf (aV ht) = 0 := (hsing _ (aV_ne_zero H ht)).mpr ⟨1, one_mem _, rfl⟩
        rw [hE, card_pointRadical hQ (aV_ne_zero H ht) hQa, h4']
        norm_num
      · exact (false_of_isQuasisimple_of_le_solvable hKR hq hsol).elim
    · obtain ⟨hs, hn⟩ := Q.omega ht ht1 hVQ hΩ h6
      obtain ⟨h1, -, h4⟩ := hsimple hs hn
      exact ⟨h1, fun h => absurd h hVQ, fun hP => (h4 hP).elim⟩
  ·
    obtain ⟨M₀, hM₀, hMn, hMs, hMi⟩ := Q.pgl25 ht ht1 hVQ hP
    have hKe := eq_of_isSubnormal_of_isQuasisimple hK hq hM₀ hMs hMi
    subst hKe
    exact ⟨quasisimple_of_index_le_two ht hP.le_closure hMn hMi, fun h => absurd h hVQ,
      fun _ => ⟨hVQ,
        card_LmodN_le_four_of_tau_not_mem H C ht ht1 hVQ hP.finrank_eq hP.tau_not_mem⟩⟩

theorem Hyp45Q.unique {H : Hyp4 S g} {C : Cons311 S g} (Q : Hyp45Q H C) (hNo : NoA2 S g)
    {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hR : Rbar S g t ≠ S.Lbar g)
    {K₁ K₂ : Subgroup (Vt S g t ≃ₗ[ZMod 2] Vt S g t)}
    (hK₁ : CFSG.Open.IsSubnormal K₁ (RmodN S g t)) (hq₁ : CFSG.Open.IsQuasisimple K₁)
    (hK₂ : CFSG.Open.IsSubnormal K₂ (RmodN S g t)) (hq₂ : CFSG.Open.IsQuasisimple K₂) :
    K₁ = K₂ := by
  have : Finite (Vt S g t ≃ₗ[ZMod 2] Vt S g t) := finite_linearEquiv_of_finite
  have hKR := CFSG.ClassicalInvolution.isSubnormal_le hK₁
  have hsimple : IsSimpleGroup (RmodN S g t) → K₁ = K₂ := fun hs =>
    (eq_of_isSubnormal_of_isSimpleGroup hK₁ hq₁ hs).trans
      (eq_of_isSubnormal_of_isSimpleGroup hK₂ hq₂ hs).symm
  have hindex : (∃ M₀ ≤ RmodN S g t, IsSimpleGroup M₀ ∧ M₀.relIndex (RmodN S g t) ≤ 2) →
      K₁ = K₂ := by
    rintro ⟨M₀, hM₀, hMs, hMi⟩
    exact (eq_of_isSubnormal_of_isQuasisimple hK₁ hq₁ hM₀ hMs hMi).trans
      (eq_of_isSubnormal_of_isQuasisimple hK₂ hq₂ hM₀ hMs hMi).symm
  rcases timmesfeld_4_5 H hNo C ht ht1 with hR' | hL | ⟨hVQ, hSp | hA | hΩ | hP⟩
  · exact absurd hR' hR
  · have h2 := hL.two_le_finrank
    rcases (show finrank (ZMod 2) (Vt S g t) = 2 ∨ 3 ≤ finrank (ZMod 2) (Vt S g t) by omega)
      with h2' | h3
    · exact (false_of_isQuasisimple_of_le_solvable hKR hq₁ (Q.lin_two ht hL h2')).elim
    · exact hsimple (Q.lin ht hL h3).1
  · have h4 := four_le_finrank_Vt H C ht ht1 hVQ hNo
    obtain ⟨k, hk⟩ := even_finrank_Vt H C ht ht1 hVQ
    rcases (show finrank (ZMod 2) (Vt S g t) = 4 ∨ 6 ≤ finrank (ZMod 2) (Vt S g t) by omega)
      with h4' | h6
    · obtain ⟨M₀, hM₀, -, hMs, hMi, -⟩ := Q.sp_four ht ht1 hVQ hSp h4'
      exact hindex ⟨M₀, hM₀, hMs, hMi.le⟩
    · exact hsimple (Q.sp ht ht1 hVQ hSp h6).1
  · exact hsimple (Q.a6 ht ht1 hVQ hA)
  · have h4 := four_le_finrank_Vt H C ht ht1 hVQ hNo
    obtain ⟨k, hk⟩ := even_finrank_Vt H C ht ht1 hVQ
    rcases (show finrank (ZMod 2) (Vt S g t) = 4 ∨ 6 ≤ finrank (ZMod 2) (Vt S g t) by omega)
      with h4' | h6
    · rcases Q.omega_four ht ht1 hVQ hΩ h4' with hs | hsol
      · exact hsimple hs
      · exact (false_of_isQuasisimple_of_le_solvable hKR hq₁ hsol).elim
    · exact hsimple (Q.omega ht ht1 hVQ hΩ h6).1
  · obtain ⟨M₀, hM₀, -, hMs, hMi⟩ := Q.pgl25 ht ht1 hVQ hP
    exact hindex ⟨M₀, hM₀, hMs, hMi⟩

end CFSG.LargeExtraspecial.S5
