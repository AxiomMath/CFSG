module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Step35
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Step36

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open scoped Pointwise

namespace Sec3

theorem quaternion_facts :
    (∀ g : QuaternionGroup 2, g ^ 4 = 1) ∧ (∀ g h : QuaternionGroup 2, g ^ 2 * h = h * g ^ 2) ∧
    (∀ g h : QuaternionGroup 2, g * g = 1 → h * h = 1 → g = 1 ∨ h = 1 ∨ g = h) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

variable {G : Type} [Group G] [Finite G]

theorem le_centralizer_of_quaternion {Q₀ T : Subgroup G} {x : G}
    (hQ : Nonempty (↥Q₀ ≃* QuaternionGroup 2)) (hx3 : x ^ 3 = 1)
    (hxQ : x ∈ normalizer (Q₀ : Set G)) (hxQ' : x ∉ centralizer (Q₀ : Set G))
    (hT2 : IsPGroup 2 T) (hTQ : T ≤ normalizer (Q₀ : Set G))
    (hTx : T ≤ centralizer ({x} : Set G)) : T ≤ centralizer (Q₀ : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := hQ
  obtain ⟨h4, -, hinv⟩ := quaternion_facts
  have hQ8 : Nat.card Q₀ = 8 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hQ4 : ∀ q ∈ Q₀, q ^ 4 = 1 := fun q hq => by
    have h := congrArg Subtype.val (e.injective (show e (⟨q, hq⟩ ^ 4) = e 1 by
      rw [map_pow, h4, map_one]))
    simpa using h
  have hQinv : ∀ a ∈ Q₀, ∀ b ∈ Q₀, a * a = 1 → b * b = 1 → a = 1 ∨ b = 1 ∨ a = b := by
    intro a ha b hb haa hbb
    have h1 := hinv (e ⟨a, ha⟩) (e ⟨b, hb⟩)
      (by rw [← map_mul, show (⟨a, ha⟩ : ↥Q₀) * ⟨a, ha⟩ = 1 from Subtype.ext haa, map_one])
      (by rw [← map_mul, show (⟨b, hb⟩ : ↥Q₀) * ⟨b, hb⟩ = 1 from Subtype.ext hbb, map_one])
    rcases h1 with h | h | h
    · left
      have := congrArg Subtype.val (e.injective (h.trans (map_one e).symm))
      simpa using this
    · right; left
      have := congrArg Subtype.val (e.injective (h.trans (map_one e).symm))
      simpa using this
    · right; right
      exact congrArg Subtype.val (e.injective h)
  have hxconj : ∀ q ∈ Q₀, x * q * x⁻¹ ∈ Q₀ := fun q hq => (mem_normalizer_iff.mp hxQ q).mp hq
  have hxfix : ∀ q ∈ Q₀, q * q = 1 → x * q * x⁻¹ = q := by
    intro q hq hqq
    by_cases hq1 : q = 1
    · rw [hq1, mul_one, mul_inv_cancel]
    have hq' : (x * q * x⁻¹) * (x * q * x⁻¹) = 1 := by
      rw [show (x * q * x⁻¹) * (x * q * x⁻¹) = x * (q * q) * x⁻¹ by group, hqq, mul_one,
        mul_inv_cancel]
    rcases hQinv _ (hxconj q hq) q hq hq' hqq with h | h | h
    · exfalso
      apply hq1
      rw [show q = x⁻¹ * (x * q * x⁻¹) * x by group, h, mul_one, inv_mul_cancel]
    · exact absurd h hq1
    · exact h
  obtain ⟨q, hqC, hqx⟩ : ∃ q ∈ Q₀ ⊓ centralizer (T : Set G), x * q * x⁻¹ ≠ q := by
    by_contra hcon
    apply hxQ'
    have hc : zpowers x ≤ centralizer ((Q₀ ⊓ centralizer (T : Set G) : Subgroup G) : Set G) := by
      rw [zpowers_le, mem_centralizer_iff]
      intro q hq
      by_contra hne
      apply hcon
      refine ⟨q, hq, fun h => hne ?_⟩
      calc q * x = (x * q * x⁻¹) * x := by rw [h]
        _ = x * q := by group
    have hcop : (Nat.card Q₀).Coprime (Nat.card (zpowers x)) := by
      rw [hQ8, Nat.card_zpowers]
      have h3 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
      exact Nat.Coprime.coprime_dvd_right h3 (by norm_num)
    have hQ2 : IsPGroup 2 Q₀ := IsPGroup.of_card (n := 3) (by rw [hQ8]; norm_num)
    have h := CFSG.RankThreeCoreUniqueness.Helpers.ambient_subgroup_axb_centralizer_le 2
      Nat.prime_two T (zpowers x) Q₀ hT2 hQ2 hcop hTQ (zpowers_le.mpr hxQ)
      (zpowers_le.mpr (mem_centralizer_iff.mpr fun t ht =>
        mem_centralizer_singleton_iff.mp (hTx ht))) hc
    exact h (mem_zpowers x)
  obtain ⟨hqQ, hqT⟩ := mem_inf.mp hqC
  have hqq : q * q ≠ 1 := fun h => hqx (hxfix q hqQ h)
  have h4q := hQ4 q hqQ
  have hord : orderOf q = 4 := by
    have h1 : orderOf q ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one (by simpa using h4q)
    have h2 : ¬ orderOf q ∣ 2 := fun h =>
      hqq (by rw [← pow_two]; exact orderOf_dvd_iff_pow_eq_one.mp h)
    obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    interval_cases i
    · exact absurd (by rw [hi']; norm_num) h2
    · exact absurd (by rw [hi']; norm_num) h2
    · rw [hi']; norm_num
  have hq'Q : x * q * x⁻¹ ∈ Q₀ := hxconj q hqQ
  have hq'T : x * q * x⁻¹ ∈ centralizer (T : Set G) := by
    rw [mem_centralizer_iff]
    intro t ht
    have htx : t * x = x * t := mem_centralizer_singleton_iff.mp (hTx ht)
    have htx' : t * x⁻¹ = x⁻¹ * t := by
      rw [mul_inv_eq_iff_eq_mul, mul_assoc, htx, inv_mul_cancel_left]
    have htq : t * q = q * t := mem_centralizer_iff.mp hqT t ht
    calc t * (x * q * x⁻¹) = (t * x) * q * x⁻¹ := by group
      _ = x * (t * q) * x⁻¹ := by rw [htx]; group
      _ = x * q * (t * x⁻¹) := by rw [htq]; group
      _ = x * q * x⁻¹ * t := by rw [htx']; group
  have hq'z : x * q * x⁻¹ ∉ zpowers q := by
    intro h
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h
    have hk' : q ^ (k % 4) = x * q * x⁻¹ := by
      have h1 := zpow_mod_orderOf q k
      rw [hord, Nat.cast_ofNat] at h1
      rw [h1, hk]
    have hcases : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
    rcases hcases with h0 | h0 | h0 | h0 <;> rw [h0] at hk'
    ·
      apply hqq
      have h1 : x * q * x⁻¹ = 1 := by rw [← hk', zpow_zero]
      rw [show q = x⁻¹ * (x * q * x⁻¹) * x by group, h1, mul_one, inv_mul_cancel, one_mul]
    · exact hqx (by rw [← hk', zpow_one])
    ·
      apply hqq
      have h1 : (x * q * x⁻¹) * (x * q * x⁻¹) = 1 := by
        rw [← hk', ← zpow_add, show (2 : ℤ) + 2 = ((4 : ℕ) : ℤ) by norm_num, zpow_natCast, h4q]
      rw [show (x * q * x⁻¹) * (x * q * x⁻¹) = x * (q * q) * x⁻¹ by group] at h1
      rw [show q * q = x⁻¹ * (x * (q * q) * x⁻¹) * x by group, h1, mul_one, inv_mul_cancel]
    ·
      apply hqq
      have h1 : x * q * x⁻¹ = q⁻¹ := by
        rw [← hk', eq_inv_iff_mul_eq_one, ← zpow_add_one,
          show (3 : ℤ) + 1 = ((4 : ℕ) : ℤ) by norm_num, zpow_natCast, h4q]
      have h2 : x * (x * (x * q * x⁻¹) * x⁻¹) * x⁻¹ = q⁻¹ := by
        calc x * (x * (x * q * x⁻¹) * x⁻¹) * x⁻¹ = x * (x * q⁻¹ * x⁻¹) * x⁻¹ := by rw [h1]
          _ = x * (x * q * x⁻¹)⁻¹ * x⁻¹ := by group
          _ = q⁻¹ := by rw [h1, inv_inv, h1]
      have hx3' : x * (x * x) = 1 := by rw [← pow_three]; exact hx3
      rw [show x * (x * (x * q * x⁻¹) * x⁻¹) * x⁻¹ = (x * (x * x)) * q * (x * (x * x))⁻¹ by
        group, hx3', one_mul, inv_one, mul_one] at h2
      calc q * q = q * q⁻¹ := by rw [← h2]
        _ = 1 := mul_inv_cancel q
  have hlt : zpowers q < Q₀ ⊓ centralizer (T : Set G) :=
    lt_of_le_of_ne (zpowers_le.mpr hqC) (fun h => hq'z (h ▸ mem_inf.mpr ⟨hq'Q, hq'T⟩))
  have hcard := Subgroup.card_lt_of_lt hlt
  rw [Nat.card_zpowers, hord] at hcard
  have hdvd : Nat.card ↥(Q₀ ⊓ centralizer (T : Set G)) ∣ 8 :=
    hQ8 ▸ Subgroup.card_dvd_of_le inf_le_left
  have h8 : Nat.card ↥(Q₀ ⊓ centralizer (T : Set G)) = 8 := by
    have hmem : Nat.card ↥(Q₀ ⊓ centralizer (T : Set G)) ∈ Nat.divisors 8 :=
      Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    have hdiv : Nat.divisors 8 = {1, 2, 4, 8} := by decide
    rw [hdiv] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    omega
  have hQC : Q₀ ⊓ centralizer (T : Set G) = Q₀ :=
    eq_of_le_of_card_ge inf_le_left (by rw [h8, hQ8])
  rw [le_centralizer_iff, ← hQC]
  exact inf_le_right

theorem isExtraspecialPGroup_sup {Q₀ Q : Subgroup G} (hQ₀ : Nonempty (↥Q₀ ≃* QuaternionGroup 2))
    (hQ : CFSG.IsExtraspecialPGroup 2 Q) (hQc : Q ≤ centralizer (Q₀ : Set G))
    (hZ : centerIn Q₀ = centerIn Q) :
    CFSG.IsExtraspecialPGroup 2 ↥(Q₀ ⊔ Q) ∧ Nat.card ↥(Q₀ ⊔ Q) = 4 * Nat.card Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := hQ₀
  obtain ⟨-, hsqc, -⟩ := quaternion_facts
  have hQ₀8 : Nat.card Q₀ = 8 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hQ₀2 : IsPGroup 2 Q₀ := IsPGroup.of_card (n := 3) (by rw [hQ₀8]; norm_num)
  have hQ2 : IsPGroup 2 Q := hQ.1
  have hZc2 : Nat.card (centerIn Q) = 2 := by rw [card_centerIn]; exact hQ.2.2.2
  have hZcQ : centerIn Q ≤ Q := inf_le_left
  have hZcQ₀ : centerIn Q ≤ Q₀ := by
    rw [← hZ]
    exact inf_le_left
  have hcomm : ∀ a ∈ Q₀, ∀ b ∈ Q, a * b = b * a := fun a ha b hb =>
    mem_centralizer_iff.mp (hQc hb) a ha
  have hsq₀ : ∀ q ∈ Q₀, q ^ 2 ∈ centerIn Q := by
    intro q hq
    rw [← hZ]
    refine mem_inf.mpr ⟨pow_mem hq 2, mem_centralizer_iff.mpr fun w hw => ?_⟩
    have h := hsqc (e ⟨q, hq⟩) (e ⟨w, hw⟩)
    rw [← map_pow, ← map_mul, ← map_mul] at h
    have h' := congrArg Subtype.val (e.injective h)
    simpa using h'.symm
  have hsq : ∀ q ∈ Q, q ^ 2 ∈ centerIn Q := by
    intro q hq
    have : Fact (IsPGroup 2 ↥Q) := ⟨hQ2⟩
    have h1 : (⟨q, hq⟩ : ↥Q) ^ 2 ∈ frattini ↥Q := by
      rw [CFSG.frattini_eq_closure_commutator_union_powers (p := 2)]
      exact subset_closure (Or.inr ⟨_, rfl⟩)
    rw [hQ.2.2.1] at h1
    rw [← map_center_eq_centerIn]
    exact ⟨_, h1, by simp⟩
  have hQN : Q ≤ normalizer (Q₀ : Set G) := hQc.trans (centralizer_le_normalizer _)
  have hH2 : IsPGroup 2 ↥(Q₀ ⊔ Q) := hQ₀2.to_sup_of_normal_left' hQ2 hQN
  have hmulH : ∀ h ∈ Q₀ ⊔ Q, ∃ a ∈ Q₀, ∃ b ∈ Q, h = a * b := by
    intro h hh
    have hh' : h ∈ (Q₀ : Set G) * (Q : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left Q₀ Q hQN]
      exact hh
    obtain ⟨a, ha, b, hb, hab⟩ := hh'
    exact ⟨a, ha, b, hb, hab.symm⟩
  have hsqH : ∀ h ∈ Q₀ ⊔ Q, h ^ 2 ∈ centerIn Q := by
    intro h hh
    obtain ⟨a, ha, b, hb, rfl⟩ := hmulH h hh
    rw [(Commute.mul_pow (hcomm a ha b hb) 2)]
    exact mul_mem (hsq₀ a ha) (hsq b hb)
  have hcommH : ⁅Q₀ ⊔ Q, Q₀ ⊔ Q⁆ = centerIn Q := by
    refine le_antisymm ?_ ?_
    · rw [commutator_le]
      intro a ha b hb
      rw [commutatorElement_def]
      have h1 : a * b * a⁻¹ * b⁻¹ = a ^ 2 * (a⁻¹ * b) ^ 2 * (b⁻¹) ^ 2 := by
        rw [pow_two, pow_two, pow_two]
        group
      rw [h1]
      exact mul_mem (mul_mem (hsqH a ha) (hsqH _ (mul_mem (inv_mem ha) hb))) (hsqH _ (inv_mem hb))
    · have h1 : ⁅Q, Q⁆ = centerIn Q := by
        rw [← map_center_eq_centerIn, ← hQ.2.1, _root_.commutator_def, map_commutator,
          ← MonoidHom.range_eq_map, range_subtype]
      rw [← h1]
      exact commutator_mono le_sup_right le_sup_right
  have hcenH : centerIn (Q₀ ⊔ Q) = centerIn Q := by
    refine le_antisymm (fun h hh => ?_) (fun w hw => ?_)
    · obtain ⟨hhH, hhc⟩ := mem_inf.mp hh
      obtain ⟨a, ha, b, hb, rfl⟩ := hmulH _ hhH
      have haZ : a ∈ centerIn Q₀ := by
        refine mem_inf.mpr ⟨ha, mem_centralizer_iff.mpr fun c hc => ?_⟩
        have h1 := mem_centralizer_iff.mp hhc c (mem_sup_left hc)
        have hbc : c * b = b * c := hcomm c hc b hb
        calc c * a = c * (a * b) * b⁻¹ := by group
          _ = a * b * c * b⁻¹ := by rw [h1]
          _ = a * (b * c) * b⁻¹ := by group
          _ = a * (c * b) * b⁻¹ := by rw [hbc]
          _ = a * c := by group
      have hbZ : b ∈ centerIn Q := by
        refine mem_inf.mpr ⟨hb, mem_centralizer_iff.mpr fun c hc => ?_⟩
        have h1 := mem_centralizer_iff.mp hhc c (mem_sup_right hc)
        have hac : a * c = c * a := hcomm a ha c hc
        calc c * b = a⁻¹ * ((a * c) * b) := by group
          _ = a⁻¹ * ((c * a) * b) := by rw [hac]
          _ = a⁻¹ * (c * (a * b)) := by group
          _ = a⁻¹ * (a * b * c) := by rw [h1]
          _ = b * c := by group
      rw [hZ] at haZ
      exact mul_mem haZ hbZ
    · refine mem_inf.mpr ⟨mem_sup_right (hZcQ hw), mem_centralizer_iff.mpr fun h hh => ?_⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := hmulH h hh
      have hw₀ : w ∈ centerIn Q₀ := by rw [hZ]; exact hw
      have hwa : a * w = w * a := mem_centralizer_iff.mp (mem_inf.mp hw₀).2 a ha
      have hwb : b * w = w * b := mem_centralizer_iff.mp (mem_inf.mp hw).2 b hb
      calc a * b * w = a * (b * w) := by group
        _ = a * (w * b) := by rw [hwb]
        _ = (a * w) * b := by group
        _ = (w * a) * b := by rw [hwa]
        _ = w * (a * b) := by group
  have hinj := (Q₀ ⊔ Q).subtype_injective
  have hcommMap : (commutator ↥(Q₀ ⊔ Q)).map (Q₀ ⊔ Q).subtype = centerIn Q := by
    rw [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype, hcommH]
  have hcenMap : (center ↥(Q₀ ⊔ Q)).map (Q₀ ⊔ Q).subtype = centerIn Q := by
    rw [map_center_eq_centerIn, hcenH]
  have : Fact (IsPGroup 2 ↥(Q₀ ⊔ Q)) := ⟨hH2⟩
  have hfratMap : (frattini ↥(Q₀ ⊔ Q)).map (Q₀ ⊔ Q).subtype = centerIn Q := by
    refine le_antisymm ?_ ?_
    · rw [map_le_iff_le_comap, CFSG.frattini_eq_closure_commutator_union_powers (p := 2),
        closure_le]
      rintro w (hw | ⟨v, rfl⟩)
      · have hw' : (Q₀ ⊔ Q).subtype w ∈ (commutator ↥(Q₀ ⊔ Q)).map (Q₀ ⊔ Q).subtype :=
          mem_map_of_mem _ hw
        rw [hcommMap] at hw'
        exact hw'
      · show (Q₀ ⊔ Q).subtype (v ^ 2) ∈ centerIn Q
        rw [map_pow]
        exact hsqH v v.2
    · rw [← hcommMap]
      refine map_mono ?_
      rw [CFSG.frattini_eq_closure_commutator_union_powers (p := 2)]
      exact fun w hw => subset_closure (Or.inl hw)
  refine ⟨⟨hH2, map_injective hinj (hcommMap.trans hcenMap.symm),
    map_injective hinj (hfratMap.trans hcenMap.symm), ?_⟩, ?_⟩
  · rw [← card_map_of_injective hinj, hcenMap, hZc2]
  ·
    have hinf : Q₀ ⊓ Q = centerIn Q := by
      refine le_antisymm (fun w hw => ?_) (le_inf hZcQ₀ hZcQ)
      obtain ⟨hw₀, hwQ⟩ := mem_inf.mp hw
      rw [← hZ]
      exact mem_inf.mpr ⟨hw₀, mem_centralizer_iff.mpr fun c hc => hcomm c hc w hwQ⟩
    have h := card_sup_mul_card_inf hQN
    rw [hinf, hQ₀8, hZc2] at h
    omega

end Sec3

section Step37

variable {G : Type} [Group G] [Finite G] {A A₁ R : Subgroup G} {g : G} {E F : Subgroup G} {x : G}
  {Zs P T Q B₀ : Subgroup G} {z y : G} {D J U V₀ V Q₀ : Subgroup G}

omit [Finite G] in
theorem mem_normalizer_centralizer {X : Subgroup G} {n : G} (hn : n ∈ normalizer (X : Set G)) :
    n ∈ normalizer ((centralizer (X : Set G) : Subgroup G) : Set G) :=
  G2.mem_normalizer_of_conj (fun c hc => conj_mem_centralizer_of_mem hn hc)
    (fun c hc => by simpa using conj_mem_centralizer_of_mem (inv_mem hn) hc)

theorem sec3Q0_facts
    (hQ : Sec3Q0 G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀) :
    (V₀ : Set G) = {d | d ∈ D ∧ ∀ w ∈ P ⊔ F, d * w * d⁻¹ * w⁻¹ ∈ E ⊓ A} ∧
      x ∉ centralizer (Q₀ : Set G) := by
  have hD := hQ.dData
  have hSz := hD.suz
  have hS := hSz.setting
  have hFr := hS.frame
  obtain ⟨K, _, _, _, hK, f, hM, l, t₀, h₀, hl0, ht₀1, ht₀, hfh₀, hDf, hQm⟩ :=
    exists_sec3Q0_model hD
  have hfinj := hM.inj
  have hD₀C : g2ShortParabolicRadical K ≤ adjointGroup .G2 K :=
    G2.g2ShortParabolicRadical_le_adjointGroup
  have hV0C : G2.g2V0 K ≤ adjointGroup .G2 K := G2.g2V0_le_g2ShortParabolicRadical.trans hD₀C
  have hVC : G2.g2V K ≤ adjointGroup .G2 K := G2.g2V_le_g2V0.trans hV0C
  have hLPC : G2.g2LongPos K ≤ adjointGroup .G2 K :=
    G2.g2LongPos_le_g2LongA2.trans g2LongA2_le_adjointGroup
  have hACC : G2.g2ACGroup K ≤ adjointGroup .G2 K := G2.g2ACGroup_le_g2LongPos.trans hLPC
  have hV₀ : V₀ = ((G2.g2V0 K).subgroupOf (adjointGroup .G2 K)).map f :=
    SetLike.coe_injective (hQ.V₀_eq.trans hQm.V₀_eq.symm)
  have hV : V = ((G2.g2V K).subgroupOf (adjointGroup .G2 K)).map f := by
    rw [hQ.V_eq, hQm.V_eq, hV₀]
  have hQ₀ : Q₀ = ((G2.g2Q0 K l).subgroupOf (adjointGroup .G2 K)).map f :=
    (hQ.unique _ (hV ▸ hQm.Q₀_le) hQm.x_Q₀ hQm.Q₀_iso hQm.center_Q₀).symm
  have hPc := P_le_centralizer_D hD
  have hRA : R ≤ centralizer (A : Set G) := hS.sylowR.le
  have hFAR : F ≤ A ⊔ R := hFr.F_le.trans (sup_le_sup_right hS.le _)
  have hFP : F ≤ normalizer (P : Set G) := hSz.F_le.trans hSz.T_P
  obtain ⟨hEA₁, hFA₁, -⟩ := Sec3.frame_inf_A₁ hS
  have hDA : D ≤ A := by
    rw [hD.D_eq]
    exact (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_left
  refine ⟨?_, ?_⟩
  · rw [hV₀]
    ext d
    simp only [SetLike.mem_coe, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨hDf ▸ Sec3.tr_mono G2.g2V0_le_g2ShortParabolicRadical ⟨a, ha, rfl⟩,
        fun w hw => ?_⟩
      have hdD : f a ∈ D := hDf ▸ Sec3.tr_mono G2.g2V0_le_g2ShortParabolicRadical ⟨a, ha, rfl⟩
      have hw' : w ∈ (P : Set G) * (F : Set G) := by
        rw [← coe_mul_of_right_le_normalizer_left P F hFP]
        exact hw
      obtain ⟨p, hp, f', hf', hpf⟩ := hw'
      have hpf' : w = p * f' := hpf.symm
      subst hpf'
      obtain ⟨a', ha', r, hr, rfl⟩ := exists_eq_mul_of_le_sup hRA hFr.R_le_F hFAR hf'
      have hdp : f a * p * (f a)⁻¹ * p⁻¹ = 1 := by
        rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
        exact mem_centralizer_iff.mp (hPc hp) _ hdD
      have hdr : f a * r * (f a)⁻¹ * r⁻¹ = 1 := by
        rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
        exact mem_centralizer_iff.mp (hRA hr) _ (hDA hdD)
      have e : f a * (p * (a' * r)) * (f a)⁻¹ * (p * (a' * r))⁻¹ =
          (f a * p * (f a)⁻¹ * p⁻¹) * (p * ((f a * a' * (f a)⁻¹ * a'⁻¹) *
            (a' * (f a * r * (f a)⁻¹ * r⁻¹) * a'⁻¹)) * p⁻¹) := by group
      rw [e, hdp, hdr, one_mul, mul_one, mul_inv_cancel, mul_one]
      have ha'₁ : a' ∈ F ⊓ A₁ := hFA₁ ▸ ha'
      rw [← hM.F_eq] at ha'₁
      obtain ⟨b, hb, rfl⟩ := ha'₁
      have hc : f a * f b * (f a)⁻¹ * (f b)⁻¹ ∈ E ⊓ A := by
        rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← hM.E_eq]
        exact ⟨_, mem_subgroupOf.mpr (G2.commutator_mem_g2BCGroup_of_mem_g2V0
          (mem_subgroupOf.mp ha) (G2.g2ACGroup_le_g2LongPos (mem_subgroupOf.mp hb))), rfl⟩
      have h1 := mem_centralizer_iff.mp (hSz.P_cent hp) _ (hEA₁ ▸ hc)
      rw [← h1, mul_inv_cancel_right]
      exact hc
    · rintro ⟨hdD, hd⟩
      rw [hDf] at hdD
      obtain ⟨a, ha, rfl⟩ := hdD
      have hXa1 : g2N 0 1 0 0 0 0 ∈ adjointGroup .G2 K := hACC ⟨1, 0, rfl⟩
      have hfa : f ⟨_, hXa1⟩ ∈ F ⊓ A₁ := by
        rw [← hM.F_eq]
        exact ⟨⟨_, hXa1⟩, mem_subgroupOf.mpr ⟨1, 0, rfl⟩, rfl⟩
      have h1 := hd _ (mem_sup_right (mem_inf.mp hfa).1)
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← hM.E_eq,
        mem_map_iff_mem hfinj, mem_subgroupOf] at h1
      have hbZ : g2N 0 1 0 0 0 0 ∉ g2BCGroup K := by
        rintro ⟨E', F', h⟩
        obtain ⟨-, h2, -⟩ := g2N_injective h
        exact one_ne_zero h2
      exact ⟨a, mem_subgroupOf.mpr (G2.mem_g2V0_of_commutator_mem (mem_subgroupOf.mp ha)
        (G2.g2ACGroup_le_g2LongPos ⟨1, 0, rfl⟩) hbZ h1), rfl⟩
  ·
    intro hxc
    obtain ⟨ω, hω0, hω1⟩ := G2.exists_ne_zero_ne_one hK
    obtain ⟨r, hr⟩ := G2.exists_root_g2Q0 (l := l) hK (G2.sq_add_self_add_one_of_ne hK hω0 hω1) 1
    have hw : g2N 0 0 1 (l * 1 ^ 2) 0 r ∈ G2.g2Q0 K l :=
      ⟨1, r, by norm_num, by linear_combination (norm := char2_ring) hr, rfl⟩
    have hwC : g2N 0 0 1 (l * 1 ^ 2) 0 r ∈ adjointGroup .G2 K :=
      ((G2.g2Q0_le_g2V l).trans hVC) hw
    have hfw : f ⟨_, hwC⟩ ∈ Q₀ := by
      rw [hQ₀]
      exact ⟨⟨_, hwC⟩, mem_subgroupOf.mpr hw, rfl⟩
    have h1 := mem_centralizer_iff.mp hxc _ hfw
    rw [← hfh₀, ← map_mul, ← map_mul] at h1
    have h2 := congrArg Subtype.val (hfinj h1)
    simp only [Subgroup.coe_mul] at h2
    rw [← ht₀] at h2
    have h3 : torusElt .G2 K g2ir t₀ * g2N 0 0 1 (l * 1 ^ 2) 0 r *
        (torusElt .G2 K g2ir t₀)⁻¹ = g2N 0 0 1 (l * 1 ^ 2) 0 r := by
      rw [← h2, mul_inv_cancel_right]
    rw [G2.torus_r_conj_g2N_uv' hK] at h3
    obtain ⟨-, -, h4, -⟩ := g2N_injective h3
    have ht2 : t₀ ^ 2 = 1 := Units.ext (by
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      linear_combination h4)
    have ht3 : t₀ ^ 3 = 1 := G2.pow_three_eq_one_of_card hK t₀
    apply ht₀1
    have h5 := pow_gcd_eq_one.mpr ⟨ht2, ht3⟩
    rwa [show Nat.gcd 2 3 = 1 by norm_num, pow_one] at h5

theorem T_le_normalizer_V₀
    (hQ : Sec3Q0 G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀) :
    T ≤ normalizer (V₀ : Set G) := by
  have hD := hQ.dData
  have hSz := hD.suz
  have hV₀ := (sec3Q0_facts hQ).1
  have hDeq := (step35_of G A A₁ R g E F x Zs P T Q B₀ z y D J U hD).1
  have hTD : T ≤ normalizer (D : Set G) := fun n hn => by
    rw [hDeq]
    exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _
      (mem_normalizer_centralizer (hSz.T_P hn))
  have hTZ : T ≤ normalizer ((E ⊓ A : Subgroup G) : Set G) := fun n hn => by
    rw [hD.center_D]
    exact mem_normalizer_inf (hTD hn) (mem_normalizer_centralizer (hTD hn))
  have key : ∀ n ∈ T, ∀ v ∈ V₀, n * v * n⁻¹ ∈ V₀ := by
    intro n hn v hv
    rw [← SetLike.mem_coe, hV₀] at hv ⊢
    obtain ⟨hvD, hvc⟩ := hv
    refine ⟨(mem_normalizer_iff.mp (hTD hn) v).mp hvD, fun w hw => ?_⟩
    have hw' : n⁻¹ * w * n ∈ P ⊔ F := by
      have h := (mem_normalizer_iff.mp (inv_mem (hSz.T_PF hn)) w).mp hw
      simpa using h
    have h1 := (mem_normalizer_iff.mp (hTZ hn) _).mp (hvc _ hw')
    convert h1 using 1
    group
  exact fun n hn =>
    G2.mem_normalizer_of_conj (key n hn) (fun v hv => by simpa using key n⁻¹ (inv_mem hn) v hv)

theorem T_le_normalizer_V
    (hQ : Sec3Q0 G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀) :
    T ≤ normalizer (V : Set G) := by
  have hSz := hQ.dData.suz
  have hTx : T ≤ centralizer ({x} : Set G) :=
    hSz.T_le.trans (map_subtype_le _ : sec3B A₁ x ≤ centralizer ({x} : Set G))
  intro n hn
  have hnx : n ∈ normalizer ((zpowers x : Subgroup G) : Set G) := centralizer_le_normalizer _
    (by rw [Sec3.centralizer_zpowers]; exact hTx hn)
  rw [mem_normalizer_iff_map_conj_eq] at hnx ⊢
  rw [hQ.V_eq, map_commutator, mem_normalizer_iff_map_conj_eq.mp (T_le_normalizer_V₀ hQ hn), hnx]

theorem T_le_normalizer_Q₀
    (hQ : Sec3Q0 G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀) :
    T ≤ normalizer (Q₀ : Set G) := by
  have hSz := hQ.dData.suz
  have hTx : T ≤ centralizer ({x} : Set G) :=
    hSz.T_le.trans (map_subtype_le _ : sec3B A₁ x ≤ centralizer ({x} : Set G))
  intro n hn
  rw [mem_normalizer_iff_map_conj_eq]
  have hφinj : Function.Injective ((MulAut.conj n : MulAut G) : G →* G) :=
    (MulAut.conj n).injective
  have hnx : n * x = x * n := mem_centralizer_singleton_iff.mp (hTx hn)
  obtain ⟨e⟩ := hQ.Q₀_iso
  refine hQ.unique _ ?_ ?_ ⟨(Q₀.equivMapOfInjective _ hφinj).symm.trans e⟩ ?_
  · have h := map_mono (f := ((MulAut.conj n : MulAut G) : G →* G)) hQ.Q₀_le
    rwa [mem_normalizer_iff_map_conj_eq.mp (T_le_normalizer_V hQ hn)] at h
  · have hconj : ∀ q : G, n * (x * q * x⁻¹) * n⁻¹ = x * (n * q * n⁻¹) * x⁻¹ := fun q => by
      calc n * (x * q * x⁻¹) * n⁻¹ = (n * x) * q * (n * x)⁻¹ := by group
        _ = (x * n) * q * (x * n)⁻¹ := by rw [hnx]
        _ = x * (n * q * n⁻¹) * x⁻¹ := by group
    refine G2.mem_normalizer_of_conj ?_ ?_
    · rintro _ ⟨q, hq, rfl⟩
      refine ⟨x * q * x⁻¹, (mem_normalizer_iff.mp hQ.x_Q₀ q).mp hq, ?_⟩
      exact hconj q
    · rintro _ ⟨q, hq, rfl⟩
      refine ⟨x⁻¹ * q * x, by simpa using (mem_normalizer_iff.mp (inv_mem hQ.x_Q₀) q).mp hq, ?_⟩
      have h := hconj (x⁻¹ * q * x)
      show n * (x⁻¹ * q * x) * n⁻¹ = x⁻¹ * (n * q * n⁻¹) * x
      calc n * (x⁻¹ * q * x) * n⁻¹ = x⁻¹ * (x * (n * (x⁻¹ * q * x) * n⁻¹) * x⁻¹) * x := by group
        _ = x⁻¹ * (n * (x * (x⁻¹ * q * x) * x⁻¹) * n⁻¹) * x := by rw [← h]
        _ = x⁻¹ * (n * q * n⁻¹) * x := by group
  · rw [Sec3.centerIn_map_of_injective _ hφinj, hQ.center_Q₀,
      ← Sec3.centerIn_map_of_injective _ hφinj, mem_normalizer_iff_map_conj_eq.mp (hSz.T_Q hn)]

theorem step37_i
    (hQ : Sec3Q0 G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀) :
    T ≤ centralizer (Q₀ : Set G) := by
  have hSz := hQ.dData.suz
  have hx3 : x ^ 3 = 1 := by
    rw [← hSz.setting.order_x]
    exact pow_orderOf_eq_one x
  exact Sec3.le_centralizer_of_quaternion hQ.Q₀_iso hx3 hQ.x_Q₀ (sec3Q0_facts hQ).2 hSz.T_two
    (T_le_normalizer_Q₀ hQ)
    (hSz.T_le.trans (map_subtype_le _ : sec3B A₁ x ≤ centralizer ({x} : Set G)))

theorem step37_ii
    (hQ : Sec3Q0 G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀) :
    CFSG.IsExtraspecialPGroup 2 ↥(Q₀ ⊔ Q) ∧ Nat.card ↥(Q₀ ⊔ Q) = 2 ^ 9 := by
  have hSz := hQ.dData.suz
  obtain ⟨h1, h2⟩ := Sec3.isExtraspecialPGroup_sup hQ.Q₀_iso hSz.q8.1
    (hSz.Q_le.trans (step37_i hQ)) hQ.center_Q₀
  exact ⟨h1, by rw [h2, hSz.q8.2.1]; norm_num⟩

end Step37

end CFSG.ComponentClassification.AS81
