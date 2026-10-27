module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76YLemma43

public section

namespace CFSG.ComponentClassification.Asc76.Sec4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

omit [Finite G] in
theorem IsDihedralRot.conj_eq_of_gen {U R : Subgroup G} (h : IsDihedralRot U R) {ρ s v r : G}
    (hρ : zpowers ρ = U) (hsR : s ∈ R) (hsU : s ∉ U) (h1 : v * ρ * v⁻¹ = r * ρ * r⁻¹)
    (h2 : v * s * v⁻¹ = r * s * r⁻¹) : ∀ x ∈ R, v * x * v⁻¹ = r * x * r⁻¹ := by
  have hU : ∀ u ∈ U, v * u * v⁻¹ = r * u * r⁻¹ := by
    intro u hu
    rw [← hρ] at hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    rw [← conj_zpow, h1, conj_zpow]
  intro x hx
  by_cases hxU : x ∈ U
  · exact hU x hxU
  have hsx : s⁻¹ * x ∈ U := h.mul_mem_of_not_mem (inv_mem hsR) hx
    (fun h' => hsU (by simpa using inv_mem h')) hxU
  calc v * x * v⁻¹ = (v * s * v⁻¹) * (v * (s⁻¹ * x) * v⁻¹) := by group
    _ = (r * s * r⁻¹) * (r * (s⁻¹ * x) * r⁻¹) := by rw [h2, hU _ hsx]
    _ = r * x * r⁻¹ := by group

omit [Finite G] in
theorem eq_or_eq_inv_of_orderOf_four {ρ y : G} (hρo : orderOf ρ = 4) (hy : y ∈ zpowers ρ)
    (hyy : y * y ≠ 1) : y = ρ ∨ y = ρ⁻¹ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [← zpow_mod_orderOf, hρo] at hyy ⊢
  have h4 : ρ ^ (4 : ℤ) = 1 := by
    rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) by norm_num, zpow_natCast, ← hρo, pow_orderOf_eq_one]
  have hk4 : k % ((4 : ℕ) : ℤ) < 4 := Int.emod_lt_of_pos k (by norm_num)
  have hk0 : 0 ≤ k % ((4 : ℕ) : ℤ) := Int.emod_nonneg k (by norm_num)
  interval_cases h : k % ((4 : ℕ) : ℤ)
  · exact absurd (by simp) hyy
  · left; simp
  · exfalso; apply hyy
    rw [← zpow_add]; norm_num [h4]
  · right
    rw [show (3 : ℤ) = 4 + (-1) by norm_num, zpow_add, h4, one_mul, zpow_neg, zpow_one]

theorem IsDihedralRot.exists_inner {U R Q : Subgroup G} (h : IsDihedralRot U R)
    (hU4 : Nat.card U = 4) (hQR : Q ≤ R) (hQU : ¬ Q ≤ U) (hQ2 : ∀ q ∈ Q, q * q = 1) {v : G}
    (hvR : v ∈ normalizer (R : Set G)) (hvQ : v ∈ normalizer (Q : Set G)) :
    ∃ r ∈ R, ∀ x ∈ R, v * x * v⁻¹ = r * x * r⁻¹ := by
  obtain ⟨ρ, hρ, hρo⟩ := h.exists_gen
  rw [hU4] at hρo
  have hρU : ρ ∈ U := hρ ▸ mem_zpowers ρ
  have hρR : ρ ∈ R := h.le hρU
  obtain ⟨z, hzU, hz1, hzz, hzuniq, hzc⟩ := h.exists_involution
  have hvU : v ∈ normalizer (U : Set G) := h.normalizer_le hvR
  have hρρ : ρ * ρ = z := by
    have h4 : ρ ^ 4 = 1 := by rw [← hρo]; exact pow_orderOf_eq_one ρ
    have h1 : ρ * ρ * (ρ * ρ) = 1 := by
      calc ρ * ρ * (ρ * ρ) = ρ ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        _ = 1 := h4
    have h2 : ρ * ρ ≠ 1 := fun h' => by
      have := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h' : ρ ^ 2 = 1)
      rw [hρo] at this
      exact absurd this (by norm_num)
    exact (hzuniq _ (mul_mem hρU hρU) h1).resolve_left h2
  have hvρ : v * ρ * v⁻¹ = ρ ∨ v * ρ * v⁻¹ = ρ⁻¹ := by
    apply eq_or_eq_inv_of_orderOf_four hρo
    · rw [hρ]; exact (mem_normalizer_iff.mp hvU ρ).mp hρU
    · intro h'
      apply h.gen_mul_self_ne_one (hρo.trans hU4.symm)
      calc ρ * ρ = v⁻¹ * (v * ρ * v⁻¹ * (v * ρ * v⁻¹)) * v := by group
        _ = 1 := by rw [h']; group
  obtain ⟨s, hsQ, hsU⟩ := Set.not_subset.mp hQU
  have hsR : s ∈ R := hQR hsQ
  have hss : s * s = 1 := hQ2 s hsQ
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have hs'Q : v * s * v⁻¹ ∈ Q := (mem_normalizer_iff.mp hvQ s).mp hsQ
  have hs'U : v * s * v⁻¹ ∉ U := fun h' => hsU (by
    have := (mem_normalizer_iff.mp (inv_mem hvU) _).mp h'
    simpa [mul_assoc] using this)
  have hvs : v * s * v⁻¹ = s ∨ v * s * v⁻¹ = s * z := by
    have h1 : s⁻¹ * (v * s * v⁻¹) ∈ U :=
      h.mul_mem_of_not_mem (inv_mem hsR) (hQR hs'Q) (fun h' => hsU (by simpa using inv_mem h'))
        hs'U
    have h2 : s⁻¹ * (v * s * v⁻¹) * (s⁻¹ * (v * s * v⁻¹)) = 1 :=
      hQ2 _ (mul_mem (inv_mem hsQ) hs'Q)
    rcases hzuniq _ h1 h2 with h3 | h3
    · left
      calc v * s * v⁻¹ = s * (s⁻¹ * (v * s * v⁻¹)) := by group
        _ = s := by rw [h3, mul_one]
    · right
      calc v * s * v⁻¹ = s * (s⁻¹ * (v * s * v⁻¹)) := by group
        _ = s * z := by rw [h3]
  have hρs : ρ * s * ρ⁻¹ = s * z := by
    have h1 := h.conj_eq s hsR hsU ρ hρU
    calc ρ * s * ρ⁻¹ = s * (s⁻¹ * ρ * s) * ρ⁻¹ := by group
      _ = s * (s * ρ * s⁻¹) * ρ⁻¹ := by rw [hsinv]
      _ = s * z⁻¹ := by rw [h1, ← hρρ]; group
      _ = s * z := by rw [inv_eq_of_mul_eq_one_right hzz]
  have hsρ : s * ρ * s⁻¹ = ρ⁻¹ := h.conj_eq s hsR hsU ρ hρU
  have hzs : z * s = s * z := (hzc s hsR).symm
  rcases hvρ with h1 | h1 <;> rcases hvs with h2 | h2
  · exact ⟨1, one_mem _, h.conj_eq_of_gen hρ hsR hsU (by rw [h1]; group) (by rw [h2]; group)⟩
  · exact ⟨ρ, hρR, h.conj_eq_of_gen hρ hsR hsU (by rw [h1]; group) (by rw [h2, hρs])⟩
  · exact ⟨s, hsR, h.conj_eq_of_gen hρ hsR hsU (by rw [h1, hsρ]) (by rw [h2]; group)⟩
  · refine ⟨s * ρ, mul_mem hsR hρR, h.conj_eq_of_gen hρ hsR hsU ?_ ?_⟩
    · rw [h1]
      calc ρ⁻¹ = s * ρ * s⁻¹ := hsρ.symm
        _ = s * ρ * ρ * (s * ρ)⁻¹ := by group
    · rw [h2]
      calc s * z = z * s := hzs.symm
        _ = (s * s) * z * s⁻¹ := by rw [hss, hsinv, one_mul]
        _ = s * (s * z) * s⁻¹ := by group
        _ = s * (ρ * s * ρ⁻¹) * s⁻¹ := by rw [hρs]
        _ = s * ρ * s * (s * ρ)⁻¹ := by group

theorem IsDihedralRot.sq_centralizes {U R : Subgroup G} (h : IsDihedralRot U R)
    (hU4 : Nat.card U = 4) {v r : G} (hrR : r ∈ R) (hv : ∀ x ∈ R, v * x * v⁻¹ = r * x * r⁻¹)
    (hvU : ∀ u ∈ U, v * u * v⁻¹ = u) : ∀ x ∈ R, (v * v) * x * (v * v)⁻¹ = x := by
  obtain ⟨z, hzU, hz1, hzz, hzuniq, hzc⟩ := h.exists_involution
  have hrU : r ∈ U := h.mem_of_commute hrR fun u hu => by
    have h1 := hvU u hu
    rw [hv u (h.le hu)] at h1
    calc r * u = r * u * r⁻¹ * r := by group
      _ = u * r := by rw [h1]
  have hr2 : r * r = 1 ∨ r * r = z := by
    have h4 : (r * r) * (r * r) = 1 := by
      have := pow_card_eq_one' (x := (⟨r, hrU⟩ : U))
      rw [hU4] at this
      have h5 := congrArg Subtype.val this
      simp only [coe_pow, OneMemClass.coe_one] at h5
      calc (r * r) * (r * r) = r ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        _ = 1 := h5
    exact hzuniq _ (mul_mem hrU hrU) h4
  intro x hx
  have hrx : r * x * r⁻¹ ∈ R := mul_mem (mul_mem hrR hx) (inv_mem hrR)
  calc (v * v) * x * (v * v)⁻¹ = v * (v * x * v⁻¹) * v⁻¹ := by group
    _ = (r * r) * x * (r * r)⁻¹ := by rw [hv x hx, hv _ hrx]; group
    _ = x := by
      rcases hr2 with h1 | h1
      · rw [h1]; group
      · rw [h1, ← hzc x hx]
        group

omit [Finite G] in
theorem mem_normalizer_zpowers {v x : G} (h : x * v = v * x) :
    x ∈ normalizer (zpowers v : Set G) :=
  mem_normalizer_of_commute' fun u hu => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    exact ((Commute.zpow_left (Commute.symm h) k)).eq

theorem ne_bot_of_even {V M : Subgroup G} (hV : IsSylowOf 2 V M) (heven : Even (Nat.card M)) :
    V ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hbot
  have h1 := hV.card_eq
  rw [hbot, card_bot] at h1
  have h2 : 0 < (Nat.card M).factorization 2 :=
    Nat.prime_two.factorization_pos_of_dvd Nat.card_pos.ne' (even_iff_two_dvd.mp heven)
  have h3 : 2 ≤ 2 ^ (Nat.card M).factorization 2 :=
    le_trans (le_of_eq (pow_one 2).symm) (Nat.pow_le_pow_right (by norm_num) h2)
  omega

theorem sylowNormalizes_of_not_twoNil (h22 : Asc76Lemma22) (hΩ : Assumption41 Ω)
    {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hlayer : twoPrimeLayerIn K = oddCoreIn K)
    (hnil : ∀ R, IsSylowOf 2 R K → ¬ IsTwoNil K R)
    (heven : Even (Nat.card (J ⊓ normalizer (K : Set G) : Subgroup G))) :
    SylowNormalizes J K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hKJ : K = J
  · subst hKJ
    obtain ⟨R, hR⟩ := exists_isSylowOf 2 K
    exact ⟨R, hR, hR.le.trans le_normalizer⟩
  obtain ⟨V, hV⟩ := exists_isSylowOf 2 (J ⊓ normalizer (K : Set G))
  have hV1 : V ≠ ⊥ := ne_bot_of_even hV heven
  have hVK : V ≤ normalizer (K : Set G) := hV.le.trans inf_le_right
  have hVJ0 : V ≤ J := hV.le.trans inf_le_left
  obtain ⟨R, hR, hVR⟩ := exists_isSylowOf_normalized hV.isPGroup hVK
  obtain ⟨U, hU⟩ := Assumption41.exists_rot hΩ hK hR
  obtain ⟨hU4, Q, hQR, hQU, hQ2, hQN⟩ := (lemma43 hlayer hR hU).resolve_left (hnil R hR)
  have hVQ : V ≤ normalizer (Q : Set G) := fun v hv => hQN (mem_inf.mpr ⟨hVK hv, hVR hv⟩)
  rcases lemma415 h22 hΩ hK hJ hR hU hV hV1 hVR with
    ⟨hVJ, -, -⟩ | ⟨⟨e⟩, hVU, -, -⟩ | ⟨hV2, -, hinv⟩
  · exact ⟨V, hVJ, hVK⟩
  · exfalso
    have : IsCyclic U := hU.isCyclic
    have hVc : IsCyclic V := isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
    obtain ⟨v, hv⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top V).mp hVc
    have hvV : v ∈ V := hv ▸ mem_zpowers v
    have hVcard : Nat.card V = 4 := (Nat.card_congr e.toEquiv).trans hU4
    have hvo : orderOf v = 4 := by rw [← hVcard, ← hv, Nat.card_zpowers]
    have hvv1 : v * v ≠ 1 := fun h' => by
      have := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h' : v ^ 2 = 1)
      rw [hvo] at this
      exact absurd this (by norm_num)
    have hvv2 : (v * v) * (v * v) = 1 := by
      calc (v * v) * (v * v) = v ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        _ = 1 := by rw [← hvo]; exact pow_orderOf_eq_one v
    obtain ⟨r, hrR, hr⟩ := hU.exists_inner hU4 hQR hQU hQ2 (hVR hvV) (hVQ hvV)
    have hvU : ∀ u ∈ U, v * u * v⁻¹ = u := by
      intro u hu
      rw [commutator_eq_bot_iff_le_centralizer] at hVU
      have h1 := (mem_centralizer_iff.mp (hVU hvV)) u hu
      calc v * u * v⁻¹ = u * v * v⁻¹ := by rw [h1]
        _ = u := by group
    have hsq := hU.sq_centralizes hU4 hrR hr hvU
    have hRC : R ≤ centralizer ({v * v} : Set G) := fun x hx => by
      rw [mem_centralizer_singleton_iff]
      calc x * (v * v) = (v * v) * x * (v * v)⁻¹ * (v * v) := by rw [hsq x hx]
        _ = (v * v) * x := by group
    have hRJ : R ≤ normalizer (J : Set G) := hRC.trans (centralizer_le_normalizer
      (Assumption41.tightlyEmbedded hΩ hJ) (mul_mem (hVJ0 hvV) (hVJ0 hvV)) hvv1 hvv2)
    obtain ⟨-, hJK⟩ := le_normalizer_of_sylow h22 hΩ hJ hK (Ne.symm hKJ) hR hRJ
    have hVJ : IsSylowOf 2 V J := by
      have h1 := hV
      rwa [inf_eq_left.mpr hJK] at h1
    have h2 := Assumption41.card_sylow_eq hΩ hJ hK hVJ hR
    rw [hU.card_eq, hU4, hVcard] at h2
    omega
  · exfalso
    obtain ⟨v, hvV, hv1⟩ : ∃ v ∈ V, v ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hV1 (eq_bot_iff.mpr fun x hx => (mem_bot).mpr (hcon x hx))
    have hvv : v * v = 1 := by
      have := pow_card_eq_one' (x := (⟨v, hvV⟩ : V))
      rw [hV2, pow_two] at this
      exact congrArg Subtype.val this
    have hvo : orderOf v = 2 := orderOf_eq_prime (by rw [pow_two]; exact hvv) hv1
    have hzpow : zpowers v = V := eq_of_le_of_card_ge ((zpowers_le).mpr hvV)
      (by rw [Nat.card_zpowers, hvo, hV2])
    obtain ⟨r, hrR, hr⟩ := hU.exists_inner hU4 hQR hQU hQ2 (hVR hvV) (hVQ hvV)
    obtain ⟨ρ, hρ, hρo⟩ := hU.exists_gen
    have hρU : ρ ∈ U := hρ ▸ mem_zpowers ρ
    have hrU : r ∉ U := by
      intro hrU
      have h1 := hinv v hvV hv1 ρ hρU
      rw [hr ρ (hU.le hρU), hU.commute_of_mem hrU hρU, mul_assoc, mul_inv_cancel, mul_one] at h1
      apply hU.gen_mul_self_ne_one hρo
      calc ρ * ρ = ρ⁻¹ * ρ := by rw [← h1]
        _ = 1 := inv_mul_cancel ρ
    have hrr : r * r = 1 := hU.mul_self r hrR hrU
    obtain ⟨z, hzU, hz1, hzz, -, hzc⟩ := hU.exists_involution
    have hrv : r * v = v * r := by
      have h2 : v * r * v⁻¹ = r := by rw [hr r hrR]; group
      calc r * v = (v * r * v⁻¹) * v := by rw [h2]
        _ = v * r := by group
    have hzv : z * v = v * z := by
      have h2 : v * z * v⁻¹ = z := by
        rw [hr z (hU.le hzU), show r * z = z * r from hzc r hrR]; group
      calc z * v = (v * z * v⁻¹) * v := by rw [h2]
        _ = v * z := by group
    have hs : Setting22 Ω K J V R := ⟨hK, hJ, hKJ, hV, hV1, hR, hVR⟩
    have hA2 : Nat.card (R ⊓ normalizer (V : Set G) : Subgroup G) = 2 :=
      (hs.card_inf_normalizer h22 hΩ).trans hV2
    have hrN : r ∈ R ⊓ normalizer (V : Set G) := mem_inf.mpr ⟨hrR, hzpow ▸
      mem_normalizer_zpowers hrv⟩
    have hzN : z ∈ R ⊓ normalizer (V : Set G) := mem_inf.mpr ⟨hU.le hzU, hzpow ▸
      mem_normalizer_zpowers hzv⟩
    have hr1 : r ≠ 1 := fun h' => hrU (h' ▸ U.one_mem)
    have hrz : r ≠ z := fun h' => hrU (h' ▸ hzU)
    have h4 := card_fourGroup hrr hzz (hzc r hrR) hr1 hz1 hrz
    have hle : fourGroup r z hrr hzz (hzc r hrR) ≤ R ⊓ normalizer (V : Set G) := by
      intro y hy
      rcases mem_fourGroup.mp hy with rfl | rfl | rfl | rfl
      · exact one_mem _
      · exact hrN
      · exact hzN
      · exact mul_mem hrN hzN
    have := card_le_of_le hle
    omega

end CFSG.ComponentClassification.Asc76.Sec4
