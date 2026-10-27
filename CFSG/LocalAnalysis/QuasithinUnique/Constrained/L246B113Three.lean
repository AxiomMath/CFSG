module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.B1MoreElevenB
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreTwelveA
public import CFSG.Quasithin.Background.B1MoreTwelveC
public import CFSG.Quasithin.Background.B6Offenders

public section

namespace CFSG.Quasithin

open CFSG.Open
open CFSG.Quasithin.EmptyFaithfulMultiple
open scoped commutatorElement

namespace B1Red

section ThreeOffender

variable {V : Type} [CommGroup V] [Finite V]

theorem ffJ_le_normalizer_of_card_three (hV : ∀ v : V, v ^ 2 = 1) {T K A : Subgroup (MulAut V)}
    (hT : IsPGroup 2 T) (hK3 : Nat.card ↥K = 3) (hsub : IsSubnormal K (T ⊔ K))
    (hA : IsFFStarOffender T A) (hAK : ⁅K, A⁆ = K) :
    ffJ T ≤ Subgroup.normalizer (K : Set (MulAut V)) := by
  classical
  set H : Subgroup (MulAut V) := T ⊔ K with hH
  set U : Subgroup V := fixV (pCoreOf 2 H) with hU
  have hst : H ≤ stabSub U := le_stabSub_fixV_pCoreOf H
  have hKH : K ≤ H := le_sup_right
  have hTH : T ≤ H := le_sup_left
  have hK0 : K ≤ conjClosure K T := le_conjClosure K T
  have hker : H ⊓ centSub U = pCoreOf 2 H :=
    kernel_eq_pCoreOf hV (fun _ hx ho => odd_mem_conjClosure hT hx ho)
      (commute_conjClosure_pCoreOf hK3 hsub)
  have hinj : ∀ x ∈ conjClosure K T, x ∈ centSub U → x = 1 := by
    intro x hx hc
    have hxQ : x ∈ pCoreOf 2 H := by
      rw [← hker]
      exact ⟨conjClosure_le_sup hx, hc⟩
    have hbot := conjClosure_inf_pCoreOf hK3 hsub
    have hmem : x ∈ conjClosure K T ⊓ pCoreOf 2 H := ⟨hx, hxQ⟩
    rwa [hbot, Subgroup.mem_bot] at hmem
  have hsolv : Group.IsSolvable ↥(autSub H U) := by
    have hS : Group.IsSolvable ↥H := isSolvable_sup hT hK3 hsub
    rw [autSub_eq_range hst]
    exact Group.isSolvable_of_surjective
      (((resHom U).comp (Subgroup.inclusion hst)).rangeRestrict_surjective)
  have hO2 : ∀ Q : Subgroup (MulAut ↥U), Q ≤ autSub H U →
      (Q.subgroupOf (autSub H U)).Normal → IsPGroup 2 Q → Q = ⊥ :=
    normal_two_subgroups_trivial_of_pCoreOf_eq_bot (pCoreOf_autSub_eq_bot hker)
  obtain ⟨𝓗, hb, hoff⟩ := exists_blocks (B1.sq_eq_one_sub hV U) hsolv hO2
  have hAH : A ≤ H := hA.1.trans hTH
  have hAn : ∀ a ∈ A, ∀ k ∈ K, a * k * a⁻¹ ∈ K := fun a ha k hk =>
    conj_mem_of_commutator_eq hAK ha hk
  have hAU : ∀ b ∈ A, ∀ w ∈ U, b w ∈ U := fun b hb w hw =>
    (mem_stabSub.1 (hst (hAH hb)) w).2 hw
  have hKU : K ≤ stabSub U := hKH.trans hst
  obtain ⟨a₀, ha₀, k₀, hk₀, hak⟩ : ∃ a ∈ A, ∃ k ∈ K, a * k ≠ k * a := by
    by_contra hcon
    push Not at hcon
    have hle : A ≤ Subgroup.centralizer (K : Set (MulAut V)) := fun a ha =>
      Subgroup.mem_centralizer_iff.2 fun k hk => (hcon a ha k hk).symm
    have hbot : ⁅K, A⁆ = ⊥ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 hle
    rw [hAK] at hbot
    rw [hbot, Subgroup.card_bot] at hK3
    omega
  have hnt : ¬ A ≤ centSub U := by
    intro hle
    have hAQ : a₀ ∈ pCoreOf 2 H := by
      rw [← hker]
      exact ⟨hAH ha₀, hle ha₀⟩
    exact hak (commute_conjClosure_pCoreOf hK3 hsub k₀ (hK0 hk₀) a₀ hAQ).symm
  have hAoff : IsFFStarOffender (autSub H U) (autSub A U) :=
    isFFStarOffender_autSub ⟨hAH, hA.2.1, hA.2.2.1, hA.2.2.2⟩ hAU hnt
  obtain ⟨af, haf, -, hAeq⟩ := hoff _ hAoff
  have hex : ∃ G ∈ 𝓗, ∃ s ∈ af G, ∃ k' ∈ autSub K U, s * k' ≠ k' * s := by
    by_contra hcon
    push Not at hcon
    have hle : autSub A U ≤ Subgroup.centralizer (autSub K U : Set (MulAut ↥U)) := by
      rw [hAeq]
      refine iSup₂_le fun G hG s hs => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro k' hk'
      exact (hcon G hG s hs k' hk').symm
    have has : a₀ ∈ stabSub U := hst (hAH ha₀)
    have hks : k₀ ∈ stabSub U := hKU hk₀
    have haA' : resHom U ⟨a₀, has⟩ ∈ autSub A U := mem_autSub.2 ⟨⟨a₀, has⟩, ha₀, rfl⟩
    have hkK' : resHom U ⟨k₀, hks⟩ ∈ autSub K U := mem_autSub.2 ⟨⟨k₀, hks⟩, hk₀, rfl⟩
    have hcomm := Subgroup.mem_centralizer_iff.1 (hle haA') _ hkK'
    have hc : ⁅a₀, k₀⁆ ∈ conjClosure K T := by
      have e : ⁅a₀, k₀⁆ = (a₀ * k₀ * a₀⁻¹) * k₀⁻¹ := by simp [commutatorElement_def, mul_assoc]
      rw [e]
      exact (conjClosure K T).mul_mem (hK0 (hAn a₀ ha₀ k₀ hk₀))
        ((conjClosure K T).inv_mem (hK0 hk₀))
    have hcs : ⁅a₀, k₀⁆ ∈ stabSub U :=
      (stabSub U).mul_mem ((stabSub U).mul_mem ((stabSub U).mul_mem has hks)
        ((stabSub U).inv_mem has)) ((stabSub U).inv_mem hks)
    have h1 : resHom U ⟨⁅a₀, k₀⁆, hcs⟩ = 1 := by
      have e : resHom U ⟨⁅a₀, k₀⁆, hcs⟩ = ⁅resHom U ⟨a₀, has⟩, resHom U ⟨k₀, hks⟩⁆ := by
        rw [← map_commutatorElement]
        rfl
      rw [e, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm.symm
    have h2 : ⁅a₀, k₀⁆ ∈ centSub U := by
      have : (⟨⁅a₀, k₀⁆, hcs⟩ : stabSub U) ∈ (resHom U).ker := h1
      rw [ker_resHom, Subgroup.mem_subgroupOf] at this
      exact this
    exact hak (commutatorElement_eq_one_iff_mul_comm.1 (hinj _ hc h2))
  obtain ⟨G₀, hG₀, s, hsa, k', hk', hsk'⟩ := hex
  have hsG₀ : s ∈ G₀ := by
    rcases haf G₀ hG₀ with h0 | hsyl
    · rw [h0, Subgroup.mem_bot] at hsa
      subst hsa
      exact absurd (by simp) hsk'
    · exact hsyl.1 hsa
  have hsA : s ∈ autSub A U := by
    rw [hAeq]
    exact Subgroup.mem_iSup_of_mem G₀ (Subgroup.mem_iSup_of_mem hG₀ hsa)
  have hnorm : ∀ x ∈ autSub K U, s * x * s⁻¹ ∈ autSub K U := fun x hx =>
    autSub_conj_mem (X := A) (Y := K) hAn hsA hx
  have hKU0 : K ⊓ centSub U = ⊥ :=
    (Subgroup.eq_bot_iff_forall _).2 fun x hx => hinj x (hK0 hx.1) hx.2
  have hcardK : Nat.card ↥(autSub K U) = 3 := by
    have h1 := card_autSub_mul (U := U) hKU
    rw [hKU0, Subgroup.card_bot, mul_one] at h1
    rw [h1, hK3]
  have hKJ : autSub K U ≤ ffJ (autSub H U) := by
    have hcomm : ⁅autSub K U, autSub A U⁆ = autSub K U :=
      commutator_autSub_eq hKU (hAH.trans hst) hAK
    calc autSub K U = ⁅autSub K U, autSub A U⁆ := hcomm.symm
      _ ≤ ffJ (autSub H U) := by
        rw [Subgroup.commutator_le]
        intro a ha j hj
        have haX : a ∈ autSub H U := autSub_mono hKH U ha
        have hjJ : j ∈ ffJ (autSub H U) := B6.le_ffJ hAoff hj
        have h1 : a * j * a⁻¹ ∈ ffJ (autSub H U) :=
          (Subgroup.mem_normalizer_iff.mp (B6.le_normalizer_ffJ _ haX) j).mp hjJ
        exact (ffJ _).mul_mem h1 ((ffJ _).inv_mem hjJ)
  have hKeq : autSub K U = oddCoreOfSub G₀ :=
    hb.eq_oddCoreOfSub_of_inverted hG₀ hcardK hKJ hsG₀ hnorm ⟨k', hk', hsk'⟩
  have hJn : ffJ (autSub H U) ≤ Subgroup.normalizer (oddCoreOfSub G₀ : Set (MulAut ↥U)) := by
    rw [← hb.iSup_eq]
    refine iSup₂_le fun H' hH' => le_normalizer_of_conj fun j hj y hy => ?_
    by_cases hHG : H' = G₀
    · subst hHG
      obtain ⟨hyG, hy3⟩ := (hb.mem_oddCoreOfSub_iff_of_mem hH').1 hy
      refine (hb.mem_oddCoreOfSub_iff_of_mem hH').2
        ⟨H'.mul_mem (H'.mul_mem hj hyG) (H'.inv_mem hj), ?_⟩
      rw [conj_pow, hy3]
      group
    · have hyG : y ∈ G₀ := oddCoreOfSub_le G₀ hy
      have hc := hb.comm H' hH' G₀ hG₀ hHG j hj y hyG
      rw [hc]
      simpa using hy
  refine iSup₂_le fun B hB => ?_
  have hBT : B ≤ T := hB.1
  have hBH : B ≤ H := hBT.trans hTH
  by_cases hBU : B ≤ centSub U
  · intro b hb
    have hbQ : b ∈ pCoreOf 2 H := by
      rw [← hker]
      exact ⟨hBH hb, hBU hb⟩
    refine Subgroup.centralizer_le_normalizer (K : Set (MulAut V))
      (Subgroup.mem_centralizer_iff.2 fun k hk => ?_)
    exact commute_conjClosure_pCoreOf hK3 hsub k (hK0 hk) b hbQ
  · have hBU' : ∀ b ∈ B, ∀ w ∈ U, b w ∈ U := fun b hb w hw =>
      (mem_stabSub.1 (hst (hBH hb)) w).2 hw
    have hBoff : IsFFStarOffender (autSub H U) (autSub B U) :=
      isFFStarOffender_autSub ⟨hBH, hB.2.1, hB.2.2.1, hB.2.2.2⟩ hBU' hBU
    have hBJ : autSub B U ≤ ffJ (autSub H U) := B6.le_ffJ hBoff
    refine le_normalizer_of_conj fun b hb k hk => ?_
    have hbT : b ∈ T := hBT hb
    have hbs : b ∈ stabSub U := hst (hBH hb)
    have hks : k ∈ stabSub U := hKU hk
    have hbk : b * k * b⁻¹ ∈ conjClosure K T := mem_conjClosure hbT hk
    have hbks : b * k * b⁻¹ ∈ stabSub U :=
      (stabSub U).mul_mem ((stabSub U).mul_mem hbs hks) ((stabSub U).inv_mem hbs)
    have hres : resHom U ⟨b * k * b⁻¹, hbks⟩ ∈ autSub K U := by
      rw [hKeq]
      have h1 : resHom U ⟨b, hbs⟩ ∈ ffJ (autSub H U) :=
        hBJ (mem_autSub.2 ⟨⟨b, hbs⟩, hb, rfl⟩)
      have h2 : resHom U ⟨k, hks⟩ ∈ oddCoreOfSub G₀ := by
        rw [← hKeq]
        exact mem_autSub.2 ⟨⟨k, hks⟩, hk, rfl⟩
      have e : (⟨b * k * b⁻¹, hbks⟩ : stabSub U) = ⟨b, hbs⟩ * ⟨k, hks⟩ * ⟨b, hbs⟩⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.1 (hJn h1) _).1 h2
    obtain ⟨g, hgK, hg⟩ := mem_autSub.1 hres
    have hgx : (g : MulAut V)⁻¹ * (b * k * b⁻¹) ∈ centSub U := by
      have h0 : resHom U (g⁻¹ * ⟨b * k * b⁻¹, hbks⟩) = 1 := by
        rw [map_mul, map_inv, hg, inv_mul_cancel]
      have h1 : (g⁻¹ * ⟨b * k * b⁻¹, hbks⟩ : stabSub U) ∈ (resHom U).ker := h0
      rw [ker_resHom, Subgroup.mem_subgroupOf] at h1
      exact h1
    have hmem : (g : MulAut V)⁻¹ * (b * k * b⁻¹) ∈ conjClosure K T :=
      (conjClosure K T).mul_mem ((conjClosure K T).inv_mem (hK0 hgK)) hbk
    have h1 := hinj _ hmem hgx
    have hbkg : b * k * b⁻¹ = g := by
      calc b * k * b⁻¹ = (g : MulAut V) * ((g : MulAut V)⁻¹ * (b * k * b⁻¹)) := by group
        _ = g := by rw [h1, mul_one]
    rw [hbkg]
    exact hgK

end ThreeOffender

end B1Red

end CFSG.Quasithin
