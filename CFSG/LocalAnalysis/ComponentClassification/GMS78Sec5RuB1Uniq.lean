module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuB1Aut
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step17L2
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Lemma315SzR
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5Setup

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

variable {G : Type} [Group G] [Finite G] {L T : Subgroup G}

namespace SzMinCounter

omit [Finite G] in
theorem eq_one_of_mem_of_mem_centralizer (hZ : Odd (Nat.card (center L))) {a : G} (haL : a ∈ L)
    (haK : a ∈ centralizer (L : Set G)) (ha2 : a * a = 1) : a = 1 := by
  have hz : (⟨a, haL⟩ : L) ∈ center L := mem_center_iff.mpr fun l =>
    Subtype.ext (mem_centralizer_iff.mp haK l l.2)
  have hx2 : (⟨a, haL⟩ : L) ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using ha2)
  have hodd : Odd (orderOf (⟨a, haL⟩ : L)) := hZ.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hz)
  have h1 : orderOf (⟨a, haL⟩ : L) ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
  have h2 : orderOf (⟨a, haL⟩ : L) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  exact congrArg Subtype.val (orderOf_eq_one_iff.mp h2)

theorem le_oddCoreIn_of_le_normalizer_gmsV
    (hM : SzMinCounter G L 1) (h3 : Sec3 G L T) (hF : Foundation)
    (hZ : Odd (Nat.card (center L)))
    (h4 : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4) {Y : Subgroup G}
    (hY : Odd (Nat.card Y)) (hVY : gmsV L T ≤ normalizer (Y : Set G)) :
    Y ≤ AS76b.oddCoreIn (centralizer (L : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := centralizer (L : Set G) with hKdef
  set T₀ := T ⊓ K with hT₀def
  have hstd := hM.hyp.standard
  have hLp : commutator L = ⊤ := hstd.1.1
  have hKt := AS76b.tightlyEmbedded_centralizer hstd
  have hNK : normalizer (K : Set G) = normalizer (L : Set G) :=
    AS76b.normalizer_centralizer_eq hstd
  obtain ⟨eS⟩ := hM.nonempty_mulEquiv_sz
  have hX := h3.facts_of_sz hF hZ hM.one_le eS
  obtain ⟨hA8, -, -⟩ := hX.sylow h3
  obtain ⟨-, hVel, -, -, -⟩ := hX.vFacts h3 hF
  have hT₀el : IsElemAbelian 2 T₀ := h3.isElemAbelian_T₀ hF
  have hT₀V : T₀ ≤ gmsV L T := le_sup_right
  have hAV : gmsA L T ≤ gmsV L T := le_sup_left
  have hAL : gmsA L T ≤ L := inf_le_left.trans inf_le_right
  have hpY : ¬ 2 ∣ Nat.card Y := fun h2 =>
    (Nat.not_even_iff_odd.mpr hY) (even_iff_two_dvd.mpr h2)
  have hKn : ¬ K.Normal := by
    intro hn
    apply hM.hyp.not_normal
    rw [← normalizer_eq_top_iff, ← hNK]
    exact normalizer_eq_top_iff.mpr hn
  have hYN : Y ≤ normalizer (L : Set G) := by
    refine AS81.le_of_forall_inf_centralizer_le
      (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.isElementaryAbelian_of_sq_eq_one
        hT₀el.2) (by rw [h4]; norm_num) hpY (hT₀V.trans hVY) ?_
    intro t ht ht1 y hy
    have hyt := (mem_inf.mp hy).2
    rw [← hNK]
    have hzK : zpowers t ≤ K := zpowers_le.mpr (mem_inf.mp ht).2
    have hev : Even (Nat.card (zpowers t)) := by
      rw [Nat.card_zpowers, orderOf_eq_prime (hT₀el.2 t ht) ht1]
      exact even_two
    refine AS76b.Lemma37.normalizer_le_of_le_of_even hKt hzK hev ?_
    have hc : Commute y t := mem_centralizer_singleton_iff.mp hyt
    refine mem_normalizer_of_conj_mem_of_finite fun z hz => ?_
    obtain ⟨k, rfl⟩ := hz
    refine ⟨k, ?_⟩
    simp only
    rw [(hc.zpow_right k).eq, mul_inv_cancel_right]
  have hYK : Y ≤ K := by
    have hVnt : Nontrivial (gmsV L T) := by
      have h1 : gmsA L T ≤ gmsV L T := hAV
      have h8 : 1 < Nat.card (gmsV L T) := by
        have := Subgroup.card_le_of_le h1
        rw [hA8] at this
        omega
      exact Finite.one_lt_card_iff_nontrivial.mp h8
    refine AS81.le_of_forall_inf_centralizer_hyperplane_le
      (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.isElementaryAbelian_of_sq_eq_one
        hVel.2) hVnt hpY hVY ?_
    intro B hBV hB2 y hy
    obtain ⟨hyY, hyB⟩ := mem_inf.mp hy
    refine mem_centralizer_of_odd_of_fix_four hLp eS hZ (B := B ⊓ gmsA L T)
      (inf_le_right.trans hAL) ?_ ?_ (hYN hyY) ?_ ?_
    · intro b hb
      have := hVel.2 b (hAV (mem_inf.mp hb).2)
      rwa [pow_two] at this
    · have h1 := Subgroup.relIndex_mul_card B (gmsA L T)
      have h2 : B.relIndex (gmsA L T) ≤ 2 :=
        hB2 ▸ Subgroup.relIndex_le_of_le_right hAV (by rw [hB2]; norm_num)
      rw [hA8] at h1
      rw [inf_comm] at h1 ⊢
      interval_cases h : B.relIndex (gmsA L T) <;> omega
    · exact hY.of_dvd_nat (Subgroup.orderOf_dvd_natCard Y hyY)
    · intro b hb
      have hc := mem_centralizer_iff.mp hyB b (mem_inf.mp hb).1
      calc y * b * y⁻¹ = b * y * y⁻¹ := by rw [hc]
        _ = b := by group
  exact AS81.le_oddCoreIn_of_le_normalizer hF.asc75Theorem4 hKt h3.isSylowOf_T₀ hT₀el
    (by rw [h4]; norm_num) (AS76b.asc08Lemma34 G L hM.hyp.hyp31).2 hKn hYK (hT₀V.trans hVY) hY

theorem normalizer_gmsV_le
    (hM : SzMinCounter G L 1) (h3 : Sec3 G L T) (hF : Foundation)
    (hZ : Odd (Nat.card (center L)))
    (h4 : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4) :
    normalizer (gmsV L T : Set G) ≤
      normalizer (AS76b.oddCoreIn (centralizer (L : Set G)) : Set G) := by
  intro g hg
  set W := AS76b.oddCoreIn (centralizer (L : Set G)) with hWdef
  have hstd := hM.hyp.standard
  have hNK : normalizer (centralizer (L : Set G) : Set G) = normalizer (L : Set G) :=
    AS76b.normalizer_centralizer_eq hstd
  have hVT : gmsV L T ≤ T :=
    sup_le (inf_le_left.trans inf_le_left) inf_le_left
  have hVW : gmsV L T ≤ normalizer (W : Set G) :=
    (hVT.trans h3.sylow.le).trans
      (hNK ▸ AS76b.normalizer_le_normalizer_oddCoreIn (centralizer (L : Set G)))
  have hVg : rightConjugate (gmsV L T) g = gmsV L T := (rightConjugate_eq_self_iff _ g).mpr hg
  have hVW' : gmsV L T ≤ normalizer (rightConjugate W g : Set G) := by
    intro v hv
    have hv' : g * v * g⁻¹ ∈ gmsV L T := by
      rw [← mem_rightConjugate_iff, hVg]
      exact hv
    have h1 := hVW hv'
    rw [mem_normalizer_iff] at h1 ⊢
    intro w
    rw [mem_rightConjugate_iff, mem_rightConjugate_iff]
    have e : g * (v * w * v⁻¹) * g⁻¹ =
        (g * v * g⁻¹) * (g * w * g⁻¹) * (g * v * g⁻¹)⁻¹ := by group
    rw [e]
    exact h1 _
  have hodd : Odd (Nat.card (rightConjugate W g)) := by
    rw [rightConjugate_card]
    exact AS76b.odd_card_oddCoreIn _
  have hle := hM.le_oddCoreIn_of_le_normalizer_gmsV h3 hF hZ h4 hodd hVW'
  have heq : rightConjugate W g = W := eq_of_le_of_card_ge hle (by rw [rightConjugate_card])
  exact (rightConjugate_eq_self_iff _ g).mp heq

theorem exists_mem_normalizer_gmsV_not_mem
    (hM : SzMinCounter G L 1) (h3 : Sec3 G L T) (hF : Foundation)
    (hZ : Odd (Nat.card (center L))) :
    ∃ g ∈ normalizer (gmsV L T : Set G), g ∉ normalizer (L : Set G) := by
  classical
  set K := centralizer (L : Set G) with hKdef
  set T₀ := T ⊓ K with hT₀def
  have hstd := hM.hyp.standard
  have hNK : normalizer (K : Set G) = normalizer (L : Set G) :=
    AS76b.normalizer_centralizer_eq hstd
  obtain ⟨eS⟩ := hM.nonempty_mulEquiv_sz
  have hX := h3.facts_of_sz hF hZ hM.one_le eS
  have h313 := h3.lemma313_of_sz_of_odd hF hZ hM.one_le eS
  obtain ⟨-, hVel, -, -, -⟩ := hX.vFacts h3 hF
  have hAL : gmsA L T ≤ L := inf_le_left.trans inf_le_right
  have hKV : ∀ v ∈ gmsV L T, v ∈ K → v ∈ T₀ := by
    intro v hv hvK
    have hAT : gmsA L T ≤ normalizer (T₀ : Set G) := fun a ha =>
      centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun t ht =>
        (mem_centralizer_iff.mp (mem_inf.mp ht).2 a (hAL ha)).symm)
    obtain ⟨a, ha, t, ht, rfl⟩ := CFSG.Goldschmidt.G37.mem_sup_of_le_normalizer hAT hv
    have haK : a ∈ K := by
      have := K.mul_mem hvK (K.inv_mem (mem_inf.mp ht).2)
      rwa [mul_inv_cancel_right] at this
    have ha2 : a * a = 1 := by
      have := hVel.2 a ((le_sup_left : gmsA L T ≤ gmsV L T) ha)
      rwa [pow_two] at this
    rw [eq_one_of_mem_of_mem_centralizer hZ (hAL ha) haK ha2, one_mul]
    exact ht
  have hT₀Δ : T₀ ∈ gmsDelta L T := ⟨⟨1, rightConjugate_one _⟩, le_sup_right⟩
  obtain ⟨Q, hQΔ, hQne⟩ : ∃ Q ∈ gmsDelta L T, Q ≠ T₀ := by
    by_contra hcon
    push Not at hcon
    have hsub : gmsDelta L T ⊆ {T₀} := fun Q hQ => hcon Q hQ
    have h1 : Nat.card (gmsDelta L T) ≤ 1 := by
      rw [Nat.card_coe_set_eq]
      exact (Set.ncard_le_ncard hsub (Set.finite_singleton T₀)).trans (Set.ncard_singleton _).le
    rw [h313.card_eq] at h1
    norm_num at h1
  obtain ⟨⟨x, rfl⟩, hQV⟩ := hQΔ
  obtain ⟨z, hzV, hz⟩ := hX.exists_mem_normalizer h3 hF hQV
  refine ⟨z, hzV, fun hzN => hQne ?_⟩
  have hzK : z ∈ normalizer (K : Set G) := hNK ▸ hzN
  have hle : rightConjugate T₀ x ≤ T₀ := by
    intro q hq
    refine hKV q (hQV hq) ?_
    have h1 : z⁻¹ * q * z ∈ rightConjugate (rightConjugate T₀ x) z := by
      rw [mem_rightConjugate_iff]
      group
      exact hq
    rw [hz] at h1
    have h2 := (mem_normalizer_iff.mp hzK (z⁻¹ * q * z)).mp (mem_inf.mp h1).2
    rwa [show z * (z⁻¹ * q * z) * z⁻¹ = q by group] at h2
  exact eq_of_le_of_card_ge hle (by rw [rightConjugate_card])

theorem not_normal_normalizer_oddCoreIn
    (hM : SzMinCounter G L 1) (h3 : Sec3 G L T) (hF : Foundation)
    (hZ : Odd (Nat.card (center L)))
    (h4 : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4) :
    ¬ (L.subgroupOf (normalizer (AS76b.oddCoreIn (centralizer (L : Set G)) : Set G))).Normal := by
  intro hn
  obtain ⟨g, hgV, hgL⟩ := hM.exists_mem_normalizer_gmsV_not_mem h3 hF hZ
  have hgW := hM.normalizer_gmsV_le h3 hF hZ h4 hgV
  have hLN : L ≤ normalizer (AS76b.oddCoreIn (centralizer (L : Set G)) : Set G) := fun l hl =>
    centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun w hw =>
      (mem_centralizer_iff.mp (AS76b.oddCoreIn_le _ hw) l hl).symm)
  exact hgL ((normal_subgroupOf_iff_le_normalizer hLN).mp hn hgW)

end SzMinCounter

end CFSG.ComponentClassification.GMS78
