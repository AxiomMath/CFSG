module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Lemma313
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherGoldschmidtFour

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

namespace Sec3

variable {L T : Subgroup G}

theorem facts_of_psl2
    (h : Sec3 G L T) (hF : Foundation) {f : ℕ} (hf : 3 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) : Facts L T (2 ^ f) := by
  have hZ := odd_card_center_of_psl2 h.hyp.standard.1.1 hf e
  have hT₁el := isElemAbelian_of_psl2 hZ (by omega) e h.isSylowOf_T₁
  have : Finite PSL(2, GaloisField 2 f) := Finite.of_surjective e e.surjective
  have hB : fusionBenderBorel (rankTwoQuot L) (2 ^ f) 1 :=
    (bender_psl2_borel_full f (by omega)).map_mulEquiv e.symm
  have hq : 8 ≤ 2 ^ f := (show 8 = 2 ^ 3 by norm_num) ▸ Nat.pow_le_pow_right (by norm_num) hf
  have hAT₁ : gmsA L T = T ⊓ L :=
    inf_eq_left.mpr (le_centralizer_iff_isMulCommutative.mpr hT₁el.1)
  refine ⟨by omega, hZ, ⟨1, hB⟩, fun x hx => ?_, fun z hz => ?_⟩
  · rw [hT₁el.2 x hx]
    exact one_mem _
  · have hVW : gmsV L T = gmsW L T := by
      show gmsA L T ⊔ _ = _
      rw [hAT₁]
    rw [hVW]
    exact h.eq_of_psl2 hF hf e hz (isElemAbelian_map _ (h.isElemAbelian_sup_of_psl2 hF hf e))
      (rightConjugate_card _ _).ge

theorem not_deltaPair_of_psl2
    (h : Sec3 G L T) (hF : Foundation) {f : ℕ} (hf : 3 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) : ¬ DeltaPair L T := by
  rintro ⟨⟨x₀, hx₀⟩, hpair⟩
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX := h.facts_of_psl2 hF hf e
  set K := centralizer (L : Set G) with hKdef
  set T₀ := T ⊓ K with hT₀def
  set T₁ := T ⊓ L with hT₁def
  have hZ := hX.oddCenter
  have hT₁el := isElemAbelian_of_psl2 hZ (by omega) e h.isSylowOf_T₁
  have hAT₁ : gmsA L T = T₁ :=
    inf_eq_left.mpr (le_centralizer_iff_isMulCommutative.mpr hT₁el.1)
  have hVW : gmsV L T = gmsW L T := by
    show gmsA L T ⊔ _ = _
    rw [hAT₁]
  set V := gmsW L T with hVdef
  have hVel : IsElemAbelian 2 V := h.isElemAbelian_sup_of_psl2 hF hf e
  have hVT : V ≤ T := sup_le inf_le_left inf_le_left
  have hinf : T₁ ⊓ T₀ = ⊥ := h.inf_eq_bot_of_odd hZ
  have hNT₀ : normalizer (T₀ : Set G) ≤ normalizer (L : Set G) := by
    have h1 := AS76b.Lemma36.normalizer_le h.hyp.hyp31 h.isSylowOf_T₀ 1
    rwa [rightConjugate_one, rightConjugate_one] at h1
  obtain ⟨hVc, -, -, -, -⟩ := hX.vFacts h hF
  have hA₁c := (hX.sylow h).1
  rw [hVW] at hVc
  rw [hAT₁] at hA₁c
  have hVcard : Nat.card V = Nat.card T₁ * Nat.card T₀ := by rw [hVc, hA₁c]
  have h8 : 8 ≤ Nat.card T₁ := h.eight_le_card_T₁
  have hTV : T ≤ normalizer (V : Set G) := fun t ht => mem_normalizer_sup (h.mem_normalizer_T₁ ht)
    (le_normalizer_of_conj_mem (fun t ht p hp => h.conj_mem_T₀ ht hp) ht)
  obtain ⟨S₂, hTS₂, y, hyS₂, hyN, hyM, hy2⟩ :=
    h.exists_mem_normalizer_sq_mem (hX.not_isSylowOf_top h hF)
  have hyV : y ∈ normalizer (V : Set G) := h.normalizer_le hF hyN
  have hT₀y : rightConjugate T₀ y = T₁ := by
    have hle : rightConjugate T₀ y ≤ gmsV L T := by
      rw [hVW]
      calc rightConjugate T₀ y ≤ rightConjugate V y := map_mono le_sup_right
        _ = V := (rightConjugate_eq_self_iff _ _).mpr hyV
    rcases hpair y hle with h4 | h4
    · exact (hyM (hNT₀ ((rightConjugate_eq_self_iff _ y).mp h4))).elim
    · rw [h4, hAT₁]
  have hconj : ∀ t ∈ T, y⁻¹ * t * y ∈ T := fun t ht => by
    simpa using (mem_normalizer_iff.mp (inv_mem hyN) t).mp ht
  have hTy : ∀ b, y⁻¹ * b ∈ T → rightConjugate T₀ b = T₁ := by
    intro b hb
    have hb' : b = y * (y⁻¹ * b) := by group
    rw [hb', ← rightConjugate_mul, hT₀y]
    exact (rightConjugate_eq_self_iff _ _).mpr (h.mem_normalizer_T₁ hb)
  have hCb : ∀ b, rightConjugate T₀ b = T₁ →
      Nat.card (V ⊓ centralizer ({b} : Set G) : Subgroup G) ≤ Nat.card T₀ := by
    intro b hb
    have hbot : (V ⊓ centralizer ({b} : Set G)) ⊓ T₁ = ⊥ := by
      rw [eq_bot_iff]
      intro a ha
      obtain ⟨hab, haT₁⟩ := mem_inf.mp ha
      have h1 : b * a * b⁻¹ ∈ T₀ := (mem_rightConjugate_iff T₀ b a).mp (hb ▸ haT₁)
      have hab' : b * a = a * b := (mem_centralizer_singleton_iff.mp (mem_inf.mp hab).2).symm
      rw [hab', mul_inv_cancel_right] at h1
      have h2 : a ∈ T₁ ⊓ T₀ := mem_inf.mpr ⟨haT₁, h1⟩
      rwa [hinf] at h2
    have h1 := card_mul_card_le (inf_le_left : V ⊓ centralizer ({b} : Set G) ≤ V)
      (le_sup_left : T₁ ≤ V)
    rw [hbot, card_bot, mul_one, hVcard, mul_comm (Nat.card T₁)] at h1
    exact Nat.le_of_mul_le_mul_right h1 Nat.card_pos
  set S₁ := T ⊔ zpowers y with hS₁def
  have hy2' : y ^ (2 : ℤ) ∈ T := by
    rw [zpow_two, ← sq]
    exact hy2
  have hS₁mem : ∀ b ∈ S₁, b ∈ T ∨ y⁻¹ * b ∈ T := by
    intro b hb
    rw [hS₁def, sup_comm] at hb
    obtain ⟨u, hu, t, ht, rfl⟩ :=
      CFSG.Goldschmidt.G37.mem_sup_of_le_normalizer (zpowers_le.mpr hyN) hb
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hu
    rcases Int.even_or_odd' n with ⟨m, rfl | rfl⟩
    · left
      rw [zpow_mul]
      exact mul_mem (zpow_mem hy2' m) ht
    · right
      rw [add_comm, zpow_one_add, mul_assoc, inv_mul_cancel_left, zpow_mul]
      exact mul_mem (zpow_mem hy2' m) ht
  have hS₁T : T ≤ S₁ := le_sup_left
  have hyS₁ : y ∈ S₁ := mem_sup_right (mem_zpowers y)
  have hS₁S₂ : S₁ ≤ S₂ := sup_le hTS₂ (zpowers_le.mpr hyS₂)
  have hS₁2 : IsPGroup 2 S₁ := S₂.isPGroup'.to_le hS₁S₂
  have hS₁V : S₁ ≤ normalizer (V : Set G) := sup_le hTV (zpowers_le.mpr hyV)
  have hS₁out : ∀ b ∈ S₁, b ∉ T → rightConjugate T₀ b = T₁ := fun b hb hbT =>
    hTy b ((hS₁mem b hb).resolve_left hbT)
  have hpair2 : ∀ E : Subgroup G, E ≤ S₁ → Nat.card E ≤ 2 * Nat.card (E ⊓ T : Subgroup G) := by
    intro E hE
    apply card_le_two_mul_of_mul_mem
    intro x₁ hx₁ x₂ hx₂ hx₁E hx₂E
    have hx₁T : x₁ ∉ T := fun hT => hx₁E (mem_inf.mpr ⟨hx₁, hT⟩)
    have hx₂T : x₂ ∉ T := fun hT => hx₂E (mem_inf.mpr ⟨hx₂, hT⟩)
    refine mem_inf.mpr ⟨mul_mem hx₁ hx₂, ?_⟩
    have h1 := (hS₁mem x₁ (hE hx₁)).resolve_left hx₁T
    have h2 := (hS₁mem x₂ (hE hx₂)).resolve_left hx₂T
    rw [show x₁ * x₂ = y ^ 2 * (y⁻¹ * (y⁻¹ * x₁) * y) * (y⁻¹ * x₂) by group]
    exact mul_mem (mul_mem hy2 (hconj _ h1)) h2
  have hB := (rankTwoBenderType_iff.mp h.hyp.bender).fusionIsBenderGroup
  have hquad : ∀ E : Subgroup G, E ≤ S₁ → IsElemAbelian 2 E →
      Nat.card E ≤ 4 * Nat.card (E ⊓ V : Subgroup G) := by
    intro E hE hEel
    have h1 := hpair2 E hE
    have h2 := card_le_two_mul_inf h.hyp.standard.1.1 hB (inf_le_right.trans h.sylow.le)
      (isElemAbelian_of_le hEel (inf_le_left : E ⊓ T ≤ E))
    rw [h.inf_sup_eq_of_le inf_le_right] at h2
    have h3 : Nat.card ((E ⊓ T) ⊓ ((T ⊓ L) ⊔ (T ⊓ centralizer (L : Set G))) : Subgroup G) ≤
        Nat.card (E ⊓ V : Subgroup G) :=
      card_le_of_le (inf_le_inf_right V inf_le_left)
    omega
  have hwc : ∀ g : G, rightConjugate V g ≤ S₁ → rightConjugate V g = V := by
    intro g hg
    by_cases hgT : rightConjugate V g ≤ T
    · exact h.eq_of_psl2 hF hf e hgT (isElemAbelian_map _ hVel) (rightConjugate_card V g).ge
    · exfalso
      obtain ⟨b, hbV, hbT⟩ := IsConcreteLE.not_le_iff_exists.mp hgT
      have hVgel : IsElemAbelian 2 (rightConjugate V g) := isElemAbelian_map _ hVel
      have h1 := hquad _ hg hVgel
      have hEV : rightConjugate V g ⊓ V ≤ V ⊓ centralizer ({b} : Set G) := fun x hx =>
        mem_inf.mpr ⟨(mem_inf.mp hx).2, mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
          (hVgel.1.is_comm.comm ⟨x, (mem_inf.mp hx).1⟩ ⟨b, hbV⟩))⟩
      have h2 := (card_le_of_le hEV).trans (hCb b (hS₁out b (hg hbV) hbT))
      rw [rightConjugate_card, hVcard] at h1
      have h3 : Nat.card T₁ * Nat.card T₀ ≤ 4 * Nat.card T₀ := h1.trans (by omega)
      have := Nat.le_of_mul_le_mul_right h3 Nat.card_pos
      omega
  have hS₁syl : IsSylowOf 2 S₁ ⊤ := by
    by_contra hns
    obtain ⟨S₃, hS₁S₃, z, hzS₃, hzN, hzS₁⟩ := exists_mem_normalizer_of_not_isSylowOf hS₁2 hns
    have hzV : z ∈ normalizer (V : Set G) := by
      have h1 : rightConjugate V z ≤ S₁ := by
        calc rightConjugate V z ≤ rightConjugate S₁ z := map_mono (hVT.trans hS₁T)
          _ = S₁ := (rightConjugate_eq_self_iff _ _).mpr hzN
      exact (rightConjugate_eq_self_iff _ _).mp (hwc z h1)
    have key : ∀ z' ∈ (S₃ : Subgroup G), rightConjugate T₀ z' = T₀ → z' ∈ S₁ := fun z' hz' h' =>
      hS₁T (h.mem_of_mem_normalizer S₃.isPGroup' (hS₁T.trans hS₁S₃) hz'
        (hNT₀ ((rightConjugate_eq_self_iff _ _).mp h')))
    have hT₀z : rightConjugate T₀ z ≤ gmsV L T := by
      rw [hVW]
      calc rightConjugate T₀ z ≤ rightConjugate V z := map_mono le_sup_right
        _ = V := (rightConjugate_eq_self_iff _ _).mpr hzV
    rcases hpair z hT₀z with h4 | h4
    · exact hzS₁ (key z hzS₃ h4)
    · rw [hAT₁] at h4
      apply hzS₁
      have hz' : rightConjugate T₀ (z * y⁻¹) = T₀ := by
        rw [← rightConjugate_mul, h4, ← hT₀y, rightConjugate_mul, mul_inv_cancel,
          rightConjugate_one]
      have h5 := key (z * y⁻¹) (mul_mem hzS₃ (inv_mem (hS₁S₃ hyS₁))) hz'
      rw [show z = z * y⁻¹ * y by group]
      exact mul_mem h5 hyS₁
  obtain ⟨-, hS₁p, hS₁idx⟩ := isSylowOf_iff.mp hS₁syl
  rw [relIndex_top_right] at hS₁idx
  let S : Sylow 2 G := hS₁p.toSylow hS₁idx
  have hSc : (S : Subgroup G) = S₁ := IsPGroup.toSylow_coe hS₁p hS₁idx
  have hVS : V ≤ S := hSc ▸ (hVT.trans hS₁T)
  have hV1 : V ≠ ⊥ := fun hb => h.T₀_ne_bot (le_bot_iff.mp (hb ▸ le_sup_right))
  by_cases hsc : ∃ v ∈ V, ∃ g : G, g⁻¹ * v * g ∈ (S : Subgroup G) ∧ g⁻¹ * v * g ∉ V
  · obtain ⟨U, hUV, g, hUg, hUgV, hbound⟩ := GoldschmidtFour.goldschmidt_theorem_four_holds G S V
      hVS hVel (fun g hg => hwc g (hSc ▸ hg)) hsc
    set U' := rightConjugate U g with hU'def
    have hU'el : IsElemAbelian 2 U' := isElemAbelian_map _ (isElemAbelian_of_le hVel hUV)
    have hU'S₁ : U' ≤ S₁ := hSc ▸ hUg
    have hidx := relIndex_mul_card V U'
    rw [inf_comm] at hidx
    have hpos : 0 < Nat.card (U' ⊓ V : Subgroup G) := Nat.card_pos
    by_cases hU'T : U' ≤ T
    ·
      have h2 := card_le_two_mul_inf h.hyp.standard.1.1 hB (hU'T.trans h.sylow.le) hU'el
      rw [h.inf_sup_eq_of_le hU'T] at h2
      obtain ⟨w, hwU, hwV⟩ := IsConcreteLE.not_le_iff_exists.mp hUgV
      have hww : w * w = 1 := by rw [← sq]; exact hU'el.2 w hwU
      have hb := hbound w hwU
      have hidx2 : V.relIndex U' ≤ 2 := by nlinarith
      have hT₁ab : IsMulCommutative (T ⊓ L : Subgroup G) := hT₁el.1
      have hc := card_le_card_inf_centralizer_mul hT₁ab (h.mem_normalizer_T₁ (hU'T hwU))
      have hcm : Nat.card (⁅T ⊓ L, zpowers w⁆ : Subgroup G) ≤
          Nat.card (⁅V, zpowers w⁆ : Subgroup G) :=
        card_le_of_le (commutator_mono le_sup_left le_rfl)
      have hlt := h.two_mul_card_lt_of_psl2 hf e (hU'T hwU) hww hwV
      have hc2 : Nat.card (T ⊓ L : Subgroup G) ≤
          Nat.card (T ⊓ L ⊓ centralizer ({w} : Set G) : Subgroup G) * 2 :=
        hc.trans (Nat.mul_le_mul_left _ (hcm.trans (hb.trans hidx2)))
      omega
    ·
      obtain ⟨w, hwU, hwT⟩ := IsConcreteLE.not_le_iff_exists.mp hU'T
      have hb := hbound w hwU
      have h4 := hquad U' hU'S₁ hU'el
      have hidx4 : V.relIndex U' ≤ 4 := by nlinarith
      have hc := card_le_card_inf_centralizer_mul hVel.1 (hS₁V (hU'S₁ hwU))
      have hC := hCb w (hS₁out w (hU'S₁ hwU) hwT)
      have h1 : Nat.card V ≤ Nat.card T₀ * 4 := hc.trans (Nat.mul_le_mul hC (hb.trans hidx4))
      rw [hVcard, mul_comm (Nat.card T₀)] at h1
      have := Nat.le_of_mul_le_mul_right h1 Nat.card_pos
      omega
  · push Not at hsc
    exact h.hyp.lemma34 S hVS hVel.1 hV1 hsc

theorem lemma313_of_psl2
    (h : Sec3 G L T) (hF : Foundation) {f : ℕ} (hf : 3 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) : Lemma313 L T (2 ^ f) :=
  (h.facts_of_psl2 hF hf e).lemma313_of_not_pair h hF (h.not_deltaPair_of_psl2 hF hf e)

end Sec3

end CFSG.ComponentClassification.GMS78
