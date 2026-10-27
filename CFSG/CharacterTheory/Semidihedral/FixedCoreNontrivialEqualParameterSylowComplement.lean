module

public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialEqualParameterLocal
public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialEqualParameterSylowBasic

public section

namespace CFSG.Semidihedral.FixedCoreNontrivial

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.ABGLocalTools (IsSylowOf)

namespace EqualParameterData

variable {G : Type} [Group G] [Finite G] {t s₀ d d₁ : G} {J : Subgroup G} {p f : ℕ}
  {F : Type} [Field F] [Finite F] {κ : C t →* Equiv.Perm (Omega F)}
  {F' : Type} [Field F'] [Finite F']
  {φ : torusH G t s₀ ⧸ CFSG.pPrimeCore 2 (torusH G t s₀) ≃* CFSG.GorensteinWalter.PGL2 F'}

theorem card_C_eq_of_mod_four_eq_three (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ)
    (he : p ^ f % 4 = 3) :
    Nat.card (C t) = p ^ f * (2 ^ 4 *
      (Nat.card (torusW G t s₀) * Nat.card ((N t).map (C t).subtype) ^ 2)) := by
  obtain ⟨h1, h2⟩ := h.card_W_B.2.1 he
  rw [h.card_C]
  generalize Nat.card (torusW G t s₀) = w at h1 h2 ⊢
  generalize Nat.card ((N t).map (C t).subtype) = b at h1 h2 ⊢
  generalize p ^ f = q at h1 h2 he ⊢
  obtain rfl : q = 2 * w + 1 := by omega
  have hb : w + 1 = 2 * b := by omega
  have e1 : (2 * w + 1) ^ 2 - 1 = 4 * w * (w + 1) :=
    Nat.sub_eq_of_eq_add (by ring)
  rw [e1, hb]
  ring

theorem exists_complement (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ) {R : Subgroup G}
    (hR : Odd (Nat.card R)) (hWR : torusW G t s₀ ≤ R) (hBR : (N t).map (C t).subtype ≤ R)
    (hRH : R ⊓ torusH G t s₀ = torusW G t s₀ ⊔ (N t).map (C t).subtype) :
    ∃ U : Subgroup G, U ≤ R ∧ R ≤ Subgroup.normalizer (U : Set G) ∧
      Disjoint U (torusW G t s₀ ⊔ (N t).map (C t).subtype) ∧
      U.relIndex R = Nat.card (torusW G t s₀) * Nat.card ((N t).map (C t).subtype) ∧
      Nat.Coprime (Nat.card U) (Nat.card (torusW G t s₀)) := by
  have hWB := h.card_W_sup_B
  have hHall : Nat.Coprime (Nat.card (torusW G t s₀))
      ((torusW G t s₀).relIndex (R ⊓ torusH G t s₀)) := by
    rw [hRH]
    have h1 := Subgroup.relIndex_mul_card (torusW G t s₀)
      (torusW G t s₀ ⊔ (N t).map (C t).subtype)
    rw [inf_eq_left.mpr le_sup_left, hWB] at h1
    have h2 : (torusW G t s₀).relIndex (torusW G t s₀ ⊔ (N t).map (C t).subtype) =
        Nat.card ((N t).map (C t).subtype) := by
      apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := torusW G t s₀))
      rw [h1, mul_comm]
    rw [h2]
    exact h.card_W_B_arith.2.2
  obtain ⟨-, U, hUR, hRU, hdisj, -, hcard, hcop⟩ :=
    h.exists_normal_complement_torus_core R hR hWR hBR hHall
  refine ⟨U, hUR, hRU, hdisj, ?_, hcop⟩
  have h1 := Subgroup.relIndex_mul_card U R
  rw [inf_eq_left.mpr hUR, ← hcard, hWB] at h1
  apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := U))
  rw [h1, mul_comm]

theorem coprime_card_U_B (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ)
    {Q₁ : Subgroup G} (hQ₁ : IsSylowOf p Q₁ (C t))
    (hsW : Subgroup.zpowers s₀ ⊔ torusW G t s₀ ≤ Subgroup.normalizer (Q₁ : Set G))
    (hCN : C t ⊓ Subgroup.normalizer (Q₁ : Set G) =
      Q₁ ⊔ torusW G t s₀ ⊔ (N t).map (C t).subtype ⊔
        (Subgroup.zpowers t ⊔ Subgroup.zpowers s₀))
    {R U : Subgroup G} (hBR : (N t).map (C t).subtype ≤ R)
    (hRN : R ≤ Subgroup.normalizer (Q₁ : Set G)) (hUR : U ≤ R)
    (hRU : R ≤ Subgroup.normalizer (U : Set G))
    (hdisj : Disjoint U (torusW G t s₀ ⊔ (N t).map (C t).subtype)) :
    Nat.Coprime (Nat.card U) (Nat.card ((N t).map (C t).subtype)) := by
  classical
  have : Fact p.Prime := ⟨h.prime⟩
  have hL := h.localData
  obtain ⟨hcard, -, -, -, -⟩ := h.sylow_C_facts hQ₁
  obtain ⟨-, hpB, hWB⟩ := h.card_W_B_arith
  have hQC : Q₁ ≤ C t := hQ₁.le
  have hWV : torusW G t s₀ ≤ Subgroup.centralizer
      ((Subgroup.zpowers t ⊔ Subgroup.zpowers s₀ : Subgroup G) : Set G) := by
    rw [torusW]
    exact Subgroup.map_subtype_le _
  have hWC : torusW G t s₀ ≤ C t := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr (h.mem_centralizer_V_iff.mp (hWV hw)).1.symm
  have hDt : Q₁ ⊔ torusW G t s₀ ⊔ (N t).map (C t).subtype ≤ C t :=
    sup_le (sup_le hQC hWC) hL.B_le
  have htD : t ∈ Subgroup.normalizer
      ((Q₁ ⊔ torusW G t s₀ ⊔ (N t).map (C t).subtype : Subgroup G) : Set G) :=
    mem_normalizer_of_conj_mem fun x hx => by
      rw [← Subgroup.mem_centralizer_singleton_iff.mp (hDt hx), mul_inv_cancel_right]
      exact hx
  have hsC : s₀ ∈ C t := Subgroup.mem_centralizer_singleton_iff.mpr hL.ts.symm
  have hsD : s₀ ∈ Subgroup.normalizer
      ((Q₁ ⊔ torusW G t s₀ ⊔ (N t).map (C t).subtype : Subgroup G) : Set G) := by
    refine sup_mem_normalizer (sup_mem_normalizer
      (hsW (Subgroup.mem_sup_left (Subgroup.mem_zpowers s₀))) ?_) ?_
    · exact mem_normalizer_of_conj_mem fun w hw => by
        rw [(h.mem_centralizer_V_iff.mp (hWV hw)).2, mul_inv_cancel_right]
        exact hw
    · exact mem_normalizer_of_conj_mem fun b hb => hL.B_conj s₀ hsC b hb
  have hVD : Subgroup.zpowers t ⊔ Subgroup.zpowers s₀ ≤ Subgroup.normalizer
      ((Q₁ ⊔ torusW G t s₀ ⊔ (N t).map (C t).subtype : Subgroup G) : Set G) := by
    rw [sup_le_iff, Subgroup.zpowers_le, Subgroup.zpowers_le]
    exact ⟨htD, hsD⟩
  have hV2 : IsPGroup 2 (Subgroup.zpowers t ⊔ Subgroup.zpowers s₀ : Subgroup G) := by
    have := h.isKleinFour_V
    exact IsPGroup.of_card (n := 2) (by rw [IsKleinFour.card_four]; norm_num)
  have hDcard : Nat.card (Q₁ ⊔ torusW G t s₀ ⊔ (N t).map (C t).subtype : Subgroup G) ∣
      Nat.card (torusW G t s₀) * p ^ f * Nat.card ((N t).map (C t).subtype) := by
    have hBn : Q₁ ⊔ torusW G t s₀ ≤
        Subgroup.normalizer (((N t).map (C t).subtype : Subgroup G) : Set G) := fun x hx =>
      mem_normalizer_of_conj_mem fun y hy => hL.B_conj x (sup_le hQC hWC hx) y hy
    have h1 := card_sup_dvd_mul_of_le_normalizer hBn
    have h2 := card_sup_dvd_mul_of_le_normalizer
      (le_sup_right.trans hsW : torusW G t s₀ ≤ Subgroup.normalizer (Q₁ : Set G))
    rw [sup_comm] at h2
    rw [← hcard]
    exact h1.trans (Nat.mul_dvd_mul_right h2 _)
  apply Nat.coprime_of_dvd
  intro r hr hrU hrB
  have : Fact r.Prime := ⟨hr⟩
  have hB0 : Nat.card ((N t).map (C t).subtype) ≠ 0 := Nat.card_pos.ne'
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr h.odd_card_B) (even_iff_two_dvd.mpr hrB)
  have hrodd : Odd r := hr.odd_of_ne_two hr2
  obtain ⟨P⟩ : Nonempty (Sylow r ((N t).map (C t).subtype)) := inferInstance
  have hP'R : (P : Subgroup ((N t).map (C t).subtype)).map ((N t).map (C t).subtype).subtype ≤
      R := (Subgroup.map_subtype_le _).trans hBR
  have hP'r : IsPGroup r (((P : Subgroup ((N t).map (C t).subtype)).map
      ((N t).map (C t).subtype).subtype).subgroupOf R) :=
    (P.isPGroup'.map _).comap_subtype
  obtain ⟨Y₀, hY₀⟩ := hP'r.exists_le_sylow
  have hY : IsSylowOf r ((Y₀ : Subgroup R).map R.subtype) R := ⟨Y₀, rfl⟩
  have hPY : (P : Subgroup ((N t).map (C t).subtype)).map ((N t).map (C t).subtype).subtype ≤
      (Y₀ : Subgroup R).map R.subtype := fun x hx =>
    ⟨⟨x, hP'R hx⟩, hY₀ (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  obtain ⟨hYC, -⟩ := h.le_C_of_isPGroup hr hrB P hY.isPGroup hPY
  have hYD : (Y₀ : Subgroup R).map R.subtype ≤ Q₁ ⊔ torusW G t s₀ ⊔ (N t).map (C t).subtype := by
    intro y hy
    have hyCN : y ∈ C t ⊓ Subgroup.normalizer (Q₁ : Set G) := ⟨hYC hy, hRN (hY.le hy)⟩
    rw [hCN] at hyCN
    apply mem_of_odd_of_mem_sup hVD hV2 hyCN
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hY.isPGroup) ⟨y, hy⟩
    rw [Subgroup.orderOf_mk] at hk
    rw [hk]
    exact hrodd.pow
  obtain ⟨a, ha⟩ := hY.isPGroup.exists_card_eq
  have hYdvd : r ^ a ∣ Nat.card (torusW G t s₀) * p ^ f * Nat.card ((N t).map (C t).subtype) := by
    rw [← ha]
    exact (Subgroup.card_dvd_of_le hYD).trans hDcard
  have hrW : ¬ r ∣ Nat.card (torusW G t s₀) * p ^ f := by
    intro hd
    rcases (Nat.Prime.dvd_mul hr).mp hd with hd | hd
    · exact hr.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hd hWB) hrB)
    · have hrp : r = p := (Nat.prime_dvd_prime_iff_eq hr h.prime).mp (hr.dvd_of_dvd_pow hd)
      exact hpB (hrp ▸ hrB)
  have hYB : r ^ a ∣ Nat.card ((N t).map (C t).subtype) :=
    (Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hr).mpr hrW)).dvd_of_dvd_mul_left
      hYdvd
  have hle : Nat.card ((Y₀ : Subgroup R).map R.subtype) ≤ Nat.card
      ((P : Subgroup ((N t).map (C t).subtype)).map ((N t).map (C t).subtype).subtype) := by
    rw [ha, Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
      Sylow.card_eq_multiplicity]
    exact Nat.pow_le_pow_right hr.pos ((hr.pow_dvd_iff_le_factorization hB0).mp hYB)
  have hYeq := Subgroup.eq_of_le_of_card_ge hPY hle
  have hYB' : (Y₀ : Subgroup R).map R.subtype ≤ (N t).map (C t).subtype :=
    hYeq ▸ Subgroup.map_subtype_le _
  have hYU := hY.inf_of_le_normalizer hUR hRU
  have hbot : (Y₀ : Subgroup R).map R.subtype ⊓ U = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxY, hxU⟩
    have : x ∈ U ⊓ (torusW G t s₀ ⊔ (N t).map (C t).subtype) :=
      ⟨hxU, Subgroup.mem_sup_right (hYB' hxY)⟩
    rwa [disjoint_iff.mp hdisj] at this
  have h1 := hYU.card_eq
  rw [hbot, Subgroup.card_bot] at h1
  have h2 := hr.factorization_pos_of_dvd Nat.card_pos.ne' hrU
  have h3 : 1 < r ^ (Nat.card U).factorization r := Nat.one_lt_pow h2.ne' hr.one_lt
  omega

theorem complement_facts (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ)
    (he : p ^ f % 4 = 3) {Q₁ : Subgroup G} (hQ₁ : IsSylowOf p Q₁ (C t)) {R U : Subgroup G}
    (hR : Odd (Nat.card R)) (hUR : U ≤ R) (hRU : R ≤ Subgroup.normalizer (U : Set G))
    (hrel : U.relIndex R = Nat.card (torusW G t s₀) * Nat.card ((N t).map (C t).subtype))
    (hcopW : Nat.Coprime (Nat.card U) (Nat.card (torusW G t s₀)))
    (hcopB : Nat.Coprime (Nat.card U) (Nat.card ((N t).map (C t).subtype)))
    (hVR : Subgroup.zpowers t ⊔ Subgroup.zpowers s₀ ≤ Subgroup.normalizer (R : Set G))
    (hQR : Q₁ ≤ R) :
    Odd (Nat.card U) ∧
      Subgroup.zpowers t ⊔ Subgroup.zpowers s₀ ≤ Subgroup.normalizer (U : Set G) ∧ Q₁ ≤ U ∧
      (∀ x ∈ R, x ^ p ^ (f + 1) = 1 → x ∈ U) ∧
      (∀ x : G, orderOf x = 2 →
        Nat.card (U ⊓ Subgroup.centralizer {x} : Subgroup G) ∣ p ^ f) ∧
      Nat.card (U ⊓ Subgroup.centralizer
        ((Subgroup.zpowers t ⊔ Subgroup.zpowers s₀ : Subgroup G) : Set G) : Subgroup G) = 1 := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hpW, hpB, -⟩ := h.card_W_B_arith
  obtain ⟨hcard, -⟩ := h.sylow_C_facts hQ₁
  have hUodd : Odd (Nat.card U) := Odd.of_dvd_nat hR (Subgroup.card_dvd_of_le hUR)
  have hpWB : Nat.Coprime p (Nat.card (torusW G t s₀) * Nat.card ((N t).map (C t).subtype)) :=
    (Nat.Prime.coprime_iff_not_dvd hp).mpr fun hd => (hp.dvd_mul.mp hd).elim hpW hpB
  have hUrel : Nat.Coprime (Nat.card U) (U.relIndex R) := by
    rw [hrel]
    exact Nat.Coprime.mul_right hcopW hcopB
  have hVU : Subgroup.zpowers t ⊔ Subgroup.zpowers s₀ ≤ Subgroup.normalizer (U : Set G) := by
    intro v hv
    exact mem_normalizer_of_conj_mem (conj_mem_of_coprime_relIndex hUR hRU hUrel (hVR hv))
  refine ⟨hUodd, hVU, ?_, ?_, ?_, ?_⟩
  · apply le_of_coprime_relIndex hUR hRU hQR
    rw [hcard, hrel]
    exact Nat.Coprime.pow_left f hpWB
  · intro x hxR hx
    have hord : orderOf x ∣ p ^ (f + 1) := orderOf_dvd_of_pow_eq_one hx
    have hle := le_of_coprime_relIndex hUR hRU (Subgroup.zpowers_le.mpr hxR) (by
      rw [Nat.card_zpowers, hrel]
      exact Nat.Coprime.coprime_dvd_left hord (Nat.Coprime.pow_left _ hpWB))
    exact hle (Subgroup.mem_zpowers x)
  · intro x hx
    obtain ⟨c, hc⟩ := isConj_iff.mp (h.conj_t x hx)
    have hCx : Nat.card (Subgroup.centralizer {x}) = Nat.card (C t) := by
      rw [← hc]
      exact (card_centralizer_conj c x).symm
    have hUX : Nat.Coprime (Nat.card U) (2 ^ 4 *
        (Nat.card (torusW G t s₀) * Nat.card ((N t).map (C t).subtype) ^ 2)) :=
      Nat.Coprime.mul_right (Nat.Coprime.pow_right 4 hUodd.coprime_two_right)
        (Nat.Coprime.mul_right hcopW (Nat.Coprime.pow_right 2 hcopB))
    have hcop := Nat.Coprime.coprime_dvd_left
      (Subgroup.card_dvd_of_le (inf_le_left : U ⊓ Subgroup.centralizer {x} ≤ U)) hUX
    apply hcop.dvd_of_dvd_mul_right
    rw [← h.card_C_eq_of_mod_four_eq_three he, ← hCx]
    exact Subgroup.card_dvd_of_le inf_le_right
  · have hU4 : Nat.Coprime (Nat.card U) (4 * Nat.card (torusW G t s₀)) :=
      Nat.Coprime.mul_right (by simpa using Nat.Coprime.pow_right 2 hUodd.coprime_two_right)
        hcopW
    have hcop := Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le (inf_le_left :
      U ⊓ Subgroup.centralizer ((Subgroup.zpowers t ⊔ Subgroup.zpowers s₀ : Subgroup G) :
        Set G) ≤ U)) hU4
    apply Nat.Coprime.eq_one_of_dvd hcop
    rw [← h.eq_bot_of_le_centralizer_kleinFour.1]
    exact Subgroup.card_dvd_of_le inf_le_right

end EqualParameterData

end CFSG.Semidihedral.FixedCoreNontrivial
