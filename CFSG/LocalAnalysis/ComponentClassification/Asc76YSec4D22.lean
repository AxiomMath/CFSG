module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4D21
public import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4D13

public section

namespace CFSG.ComponentClassification.Asc76.Sec4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.AschbacherTheorem3

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem dAdj_or_isZInv (H : Sec4Hyp Ω) {J T₀ V₀ : Subgroup G} (hJ : J ∈ Ω)
    (hT₀ : IsSylowOf 2 T₀ J) (hV₀ : IsDihedralRot V₀ T₀) {t : G} (htV : t ∈ V₀) (ht1 : t ≠ 1)
    (htt : t * t = 1) (r : G) (hc : t * (r⁻¹ * t * r) = (r⁻¹ * t * r) * t) :
    DAdj Ω J (AschbacherTightEmbedding.rightConjugate J r) ∨ IsZInv Ω (t * (r⁻¹ * t * r)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΩ := H.hΩ
  by_contra hcon
  push Not at hcon
  obtain ⟨hadj, hz⟩ := hcon
  set t' := r⁻¹ * t * r with ht'def
  set L := AschbacherTightEmbedding.rightConjugate J r with hLdef
  have htJ : t ∈ J := hT₀.le (hV₀.le htV)
  have hL : L ∈ Ω := hΩ.conj_mem J hJ r
  have ht'L : t' ∈ L := conj_mem_rightConjugate htJ r
  have ht'1 : t' ≠ 1 := by
    intro h
    apply ht1
    calc t = r * t' * r⁻¹ := by rw [ht'def]; group
      _ = 1 := by rw [h]; group
  have ht't' : t' * t' = 1 := by
    calc t' * t' = r⁻¹ * (t * t) * r := by rw [ht'def]; group
      _ = 1 := by rw [htt]; group
  have ht'Z : IsZInv Ω t' := IsZInv.conj hΩ ⟨J, hJ, T₀, V₀, hT₀, hV₀, htV, ht1, htt⟩ r
  have ht'C : t' ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.mpr hc.symm
  have ht'N : t' ∈ normalizer (J : Set G) :=
    Sec4.centralizer_le_normalizer (Assumption41.tightlyEmbedded hΩ hJ) htJ ht1 htt ht'C
  have hJL : J ≠ L := by
    intro h
    apply hadj
    rw [← h]
    exact ⟨hJ, hJ, le_normalizer, le_normalizer⟩
  have ht'P : IsPGroup 2 (zpowers t') :=
    isPGroup_zpowers_of_pow_eq_one (n := 1) (by rw [pow_one, pow_two]; exact ht't')
  obtain ⟨V₁, hV₁, ht'V₁⟩ := exists_isSylowOf_le ht'P
    ((zpowers_le).mpr (mem_inf.mpr ⟨ht'L, ht'N⟩) : zpowers t' ≤ L ⊓ normalizer (J : Set G))
  have hV₁1 : V₁ ≠ ⊥ := by
    intro h
    rw [h] at ht'V₁
    exact ht'1 (mem_bot.mp (ht'V₁ (mem_zpowers t')))
  obtain ⟨R₁, hR₁, hV₁R₁⟩ := exists_isSylowOf_normalized hV₁.isPGroup (hV₁.le.trans inf_le_right)
  obtain ⟨U₁, hU₁⟩ := Assumption41.exists_rot hΩ hJ hR₁
  obtain ⟨z₁, hz₁U, hz₁1, hz₁z₁, -, -⟩ := hU₁.exists_involution
  have hkey : IsZInv Ω (t' * z₁) ∧ t' * z₁ = z₁ * t' := by
    rcases lemma415 H.h22 hΩ hJ hL hR₁ hU₁ hV₁ hV₁1 hV₁R₁ with ⟨-, h1, h2⟩ | ⟨⟨e⟩, hcomm, -, -⟩ |
      ⟨hV2, -, hinv⟩
    · exact absurd ⟨hJ, hL, h1, h2⟩ hadj
    ·
      have hcardV : Nat.card V₁ = Nat.card U₁ := Nat.card_congr e.toEquiv
      have hVc : IsCyclic V₁ := by
        have := hU₁.isCyclic
        exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
      obtain ⟨T, hT, hVT⟩ := exists_isDihedralRot_of_isCyclic hΩ hL hJ hR₁ hU₁
        (hV₁.le.trans inf_le_left) hV₁.isPGroup hVc hcardV
      have hP : IsPGroup 2 (V₁ ⊔ R₁ : Subgroup G) :=
        IsPGroup.to_sup_of_normal_right' hV₁.isPGroup hR₁.isPGroup hV₁R₁
      obtain ⟨S', hS', hPS'⟩ := exists_isSylowOf_le hP (le_top : V₁ ⊔ R₁ ≤ ⊤)
      have hR₁W : R₁ ≤ normalizer (sec4W Ω S' : Set G) :=
        (le_sup_right.trans hPS').trans (le_normalizer_sec4W hΩ.conj_mem S')
      have hVW : V₁ ≤ sec4W Ω S' := le_sec4W (le_sup_left.trans hPS') (isRot_of hL hT hVT)
      obtain ⟨T₁, hT₁, hVT₁, hT₁W⟩ := exists_isSylowOf_le_normalizer_of_isRot hΩ hS' hL hT hVT hVW
      have hnot : ¬ T₁ ≤ normalizer (J : Set G) := by
        intro h
        obtain ⟨h1, h2⟩ := le_normalizer_of_sylow H.h22 hΩ hJ hL hJL hT₁ h
        exact hadj ⟨hJ, hL, h1, h2⟩
      obtain ⟨x, hxR, hxU⟩ := hU₁.exists_not_mem
      have ht'V : t' ∈ V₁ := ht'V₁ (mem_zpowers t')
      have h1 := conj_z_of_not_sylow H hS' hJ hL hJL hR₁ hT₁ hR₁W hT₁W hU₁ hnot
        ⟨U₁, hU₁, hz₁U, hz₁1, hz₁z₁⟩ ⟨V₁, hVT₁, ht'V, ht'1, ht't'⟩ hxR hxU
      refine ⟨h1 ▸ ht'Z.conj hΩ x, ?_⟩
      have := (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm) ht'V
      exact ((mem_centralizer_iff.mp this) z₁ hz₁U).symm
    ·
      have hinv' := hinv t' (ht'V₁ (mem_zpowers t')) ht'1
      obtain ⟨w, hwU, hwz⟩ := hU₁.exists_sq_of_mul_self hz₁U hz₁z₁
      have hz₁inv : z₁⁻¹ = z₁ := inv_eq_of_mul_eq_one_right hz₁z₁
      have ht'z : t' * z₁ = z₁ * t' := by
        calc t' * z₁ = (t' * z₁ * t'⁻¹) * t' := by group
          _ = z₁ * t' := by rw [hinv' z₁ hz₁U, hz₁inv]
      refine ⟨?_, ht'z⟩
      have e : w⁻¹ * t' * w = t' * z₁ := by
        rw [ht'z]
        calc w⁻¹ * t' * w = w⁻¹ * (t' * w * t'⁻¹) * t' := by group
          _ = (w * w)⁻¹ * t' := by rw [hinv' w hwU]; group
          _ = z₁ * t' := by rw [← hwz, hz₁inv]
      rw [← e]
      exact ht'Z.conj hΩ w
  obtain ⟨hZ, ht'z⟩ := hkey
  obtain ⟨o, ho, hz₁eq⟩ := exists_oddCoreIn_conj_eq_of_isDihedralRot hR₁ hU₁ hT₀ hV₀
    (H.hnil J hJ T₀ hT₀) hz₁U hz₁1 hz₁z₁ htV ht1 htt
  set c := o * t' * o⁻¹ * t'⁻¹ with hcdef
  have hcO : c ∈ oddCoreIn J := by
    have h1 : t' * o⁻¹ * t'⁻¹ ∈ oddCoreIn J :=
      (mem_normalizer_iff.mp (normalizer_le_normalizer_oddCoreIn J ht'N) _).mp (inv_mem ho)
    have e : c = o * (t' * o⁻¹ * t'⁻¹) := by rw [hcdef]; group
    rw [e]
    exact mul_mem ho h1
  have hcodd : Odd (orderOf c) :=
    (odd_card_oddCoreIn J).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hcO)
  set y := t' * t with hydef
  have hyy : y * y = 1 := by
    calc y * y = t' * (t * t') * t := by rw [hydef]; group
      _ = t' * (t' * t) * t := by rw [hc]
      _ = 1 := by rw [← mul_assoc, ht't', one_mul, htt]
  have hcy : c * y = o * (t' * z₁) * o⁻¹ := by
    rw [hcdef, hydef, hz₁eq]
    group
  have hcycy : c * y * (c * y) = 1 := by
    rw [hcy]
    calc o * (t' * z₁) * o⁻¹ * (o * (t' * z₁) * o⁻¹) = o * (t' * (z₁ * t') * z₁) * o⁻¹ := by
          group
      _ = o * (t' * (t' * z₁) * z₁) * o⁻¹ := by rw [ht'z]
      _ = o * ((t' * t') * (z₁ * z₁)) * o⁻¹ := by group
      _ = 1 := by rw [ht't', hz₁z₁]; group
  obtain ⟨d, hd⟩ := exists_conj_eq_mul_of_odd hyy hcodd hcycy
  apply hz
  have e : t * t' = (o⁻¹ * d)⁻¹ * (t' * z₁) * (o⁻¹ * d) := by
    have h1 : y = d⁻¹ * (c * y) * d := by rw [← hd]; group
    calc t * t' = y := by rw [hydef, hc]
      _ = d⁻¹ * (o * (t' * z₁) * o⁻¹) * d := by rw [← hcy]; exact h1
      _ = (o⁻¹ * d)⁻¹ * (t' * z₁) * (o⁻¹ * d) := by group
  rw [e]
  exact hZ.conj hΩ _

theorem MinCounter.rightConjugate_eq_of_mem_omegaD_of_not_mem (h22 : Asc76Lemma22)
    {S : Subgroup G} (hM : MinCounter Ω S) {J T₀ V₀ : Subgroup G} (hJ : J ∈ Ω)
    (hT₀ : IsSylowOf 2 T₀ J) (hV₀ : IsDihedralRot V₀ T₀) {t : G} (htV : t ∈ V₀) (ht1 : t ≠ 1)
    (htt : t * t = 1) (htW : t ∈ normalizer (sec4W Ω S : Set G)) (htW' : t ∉ sec4W Ω S)
    {K : Subgroup G} (hK : K ∈ omegaD Ω (sec4W Ω S)) :
    AschbacherTightEmbedding.rightConjugate K t = K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΩ := hM.assumption
  have hS := hM.sylow
  have H : Sec4Hyp Ω := ⟨h22, hΩ, hM.twoNil⟩
  set W := sec4W Ω S with hWdef
  by_contra hKt
  obtain ⟨hKΩ, R, hR, hRW⟩ := hK
  have hRt := (hM.rightConjugate_eq_or_le_normalizer_of_not_mem h22 hJ hT₀ hV₀ htV ht1 htt htW
    htW' hKΩ hR hRW).resolve_left hKt
  set K' := AschbacherTightEmbedding.rightConjugate K t with hK'def
  have hK' : K' ∈ Ω := hΩ.conj_mem K hKΩ t
  have hKK' : K ≠ K' := fun h => hKt h.symm
  obtain ⟨-, h2⟩ :=
    le_normalizer_of_sylow h22 hΩ hKΩ hK' hKK' (isSylowOf_rightConjugate hR t) hRt
  obtain ⟨R₁, hR₁, hR₁W, hc⟩ :=
    exists_isSylowOf_commute_rightConjugate hΩ hKΩ hR hRW htt htW hKt h2
  obtain ⟨U₁, hU₁⟩ := Assumption41.exists_rot hΩ hKΩ hR₁
  have hR₁' : IsSylowOf 2 (AschbacherTightEmbedding.rightConjugate R₁ t) K' :=
    isSylowOf_rightConjugate hR₁ t
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hR₁J : R₁ ≤ setStab (dComp Ω J) := by
    refine hU₁.le_of_forall_not_mem fun r hrR hrU => ?_
    apply mem_setStab_dComp hΩ
    have hrr : r * r = 1 := hU₁.mul_self r hrR hrU
    have hrinv : r⁻¹ = r := inv_eq_of_mul_eq_one_right hrr
    set r' := t⁻¹ * r * t with hr'def
    have hr'R : r' ∈ AschbacherTightEmbedding.rightConjugate R₁ t :=
      conj_mem_rightConjugate hrR t
    have hr'1 : r' ≠ 1 := by
      intro h
      have hr1 : r ≠ 1 := fun h' => hrU (h' ▸ U₁.one_mem)
      apply hr1
      calc r = t * r' * t⁻¹ := by rw [hr'def]; group
        _ = 1 := by rw [h]; group
    have hrr' := hc r hrR r' hr'R
    have e : t * (r⁻¹ * t * r) = r' * r := by
      rw [hrinv, hr'def, htinv]
      group
    have e' : (r⁻¹ * t * r) * t = r * r' := by
      rw [hrinv, hr'def, htinv]
      group
    have hcomm : t * (r⁻¹ * t * r) = (r⁻¹ * t * r) * t := by
      rw [e, e', hrr']
    have hnz := not_isZInv_mul_of_commute h22 hΩ hKΩ hK' hKK' hR₁ hU₁ hR₁' hc hrR hrU hr'R hr'1
    rcases dAdj_or_isZInv H hJ hT₀ hV₀ htV ht1 htt r hcomm with h | h
    · exact Relation.ReflTransGen.single h
    · rw [e] at h
      exact absurd h hnz
  set X := sSup (dComp Ω J) with hXdef
  have hX : X ≠ ⊤ := hM.sSup_dComp_ne_top hJ
  have hR₁X : R₁ ≤ normalizer (X : Set G) := hR₁J.trans (setStab_le_normalizer_sSup _)
  obtain ⟨P, hP, hR₁P⟩ := exists_isSylowOf_normalized hR₁.isPGroup hR₁X
  have hP2 : IsPGroup 2 (R₁ ⊔ P : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' hR₁.isPGroup hP.isPGroup hR₁P
  obtain ⟨S', hS', hPS'⟩ := exists_isSylowOf_le hP2 (le_top : R₁ ⊔ P ≤ ⊤)
  have hJX : J ≤ X := le_sSup (show J ∈ dComp Ω J from Relation.ReflTransGen.refl)
  obtain ⟨-, TJ, hTJ, hTJW⟩ := hM.mem_omegaD_of_le_of_isSylowOf hX (sSup_members_dComp hJ) hP hS'
    (le_sup_right.trans hPS') hJ hJX
  obtain ⟨VJ, hVJ⟩ := Assumption41.exists_rot hΩ hJ hTJ
  have hVJW : VJ ≤ sec4W Ω S' := rot_le_sec4W hΩ hS' hJ hTJ hVJ hTJW
  have hU₁W' : U₁ ≤ sec4W Ω S' := rot_le_sec4W hΩ hS' hKΩ hR₁ hU₁
    ((le_sup_left.trans hPS').trans (le_normalizer_sec4W hΩ.conj_mem S'))
  obtain ⟨z, hzU, hz1, hzz, -, -⟩ := hU₁.exists_involution
  obtain ⟨zJ, hzJV, hzJ1, hzJzJ, -, -⟩ := hVJ.exists_involution
  have hzzJ : z * zJ = zJ * z := sec4W_mul_comm hΩ hS' (hU₁W' hzU) (hVJW hzJV)
  obtain ⟨o, ho, hteq⟩ := exists_oddCoreIn_conj_eq_of_isDihedralRot hT₀ hV₀ hTJ hVJ
    (hM.twoNil J hJ TJ hTJ) htV ht1 htt hzJV hzJ1 hzJzJ
  have hzJJ : zJ ∈ J := hTJ.le (hVJ.le hzJV)
  have hzN : z ∈ normalizer (J : Set G) :=
    Sec4.centralizer_le_normalizer (Assumption41.tightlyEmbedded hΩ hJ) hzJJ hzJ1 hzJzJ
      (mem_centralizer_singleton_iff.mpr hzzJ)
  set c := z * o * z⁻¹ with hcdef
  have hcO : c ∈ oddCoreIn J :=
    (mem_normalizer_iff.mp (normalizer_le_normalizer_oddCoreIn J hzN) o).mp ho
  have hcomO : z * t * z⁻¹ * t⁻¹ ∈ oddCoreIn J := by
    have e1 : z * zJ * z⁻¹ = zJ := by rw [hzzJ]; group
    have e : z * t * z⁻¹ * t⁻¹ = c⁻¹ * (zJ * (c * o⁻¹) * zJ⁻¹) * o := by
      calc z * t * z⁻¹ * t⁻¹ = z * (o⁻¹ * zJ * o) * z⁻¹ * (o⁻¹ * zJ * o)⁻¹ := by rw [hteq]
        _ = c⁻¹ * (z * zJ * z⁻¹) * c * (o⁻¹ * zJ * o)⁻¹ := by rw [hcdef]; group
        _ = c⁻¹ * zJ * c * (o⁻¹ * zJ * o)⁻¹ := by rw [e1]
        _ = c⁻¹ * (zJ * (c * o⁻¹) * zJ⁻¹) * o := by group
    rw [e]
    refine mul_mem (mul_mem (inv_mem hcO) ?_) ho
    exact (mem_normalizer_iff.mp (le_normalizer_oddCoreIn J hzJJ) _).mp
      (mul_mem hcO (inv_mem ho))
  have hU₁W : U₁ ≤ W := rot_le_sec4W hΩ hS hKΩ hR₁ hU₁ hR₁W
  have hcomW : z * t * z⁻¹ * t⁻¹ ∈ W := by
    have h1 : t * z⁻¹ * t⁻¹ ∈ W := (mem_normalizer_iff.mp htW _).mp (inv_mem (hU₁W hzU))
    have e : z * t * z⁻¹ * t⁻¹ = z * (t * z⁻¹ * t⁻¹) := by group
    rw [e]
    exact mul_mem (hU₁W hzU) h1
  have hbot : oddCoreIn J ⊓ W = ⊥ :=
    eq_bot_of_isPGroup_of_odd ((sec4W_isPGroup hS).to_le inf_le_right)
      ((odd_card_oddCoreIn J).of_dvd_nat (card_dvd_of_le inf_le_left))
  have h1 := mem_inf.mpr ⟨hcomO, hcomW⟩
  rw [hbot, mem_bot] at h1
  apply hKt
  apply (rightConjugate_eq_self_iff K t).mpr
  apply Sec4.centralizer_le_normalizer (Assumption41.tightlyEmbedded hΩ hKΩ)
    (hR₁.le (hU₁.le hzU)) hz1 hzz
  rw [mem_centralizer_singleton_iff]
  calc t * z = (z * t * z⁻¹ * t⁻¹)⁻¹ * (z * t) := by group
    _ = z * t := by rw [h1, inv_one, one_mul]

end CFSG.ComponentClassification.Asc76.Sec4
