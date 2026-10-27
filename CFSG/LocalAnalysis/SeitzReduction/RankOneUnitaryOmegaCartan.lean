module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryOmegaBasic

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.GH74.Uniqueness.Bender

theorem unitary_e_of_even {n : ℕ} (hn : Even n) :
    (2 ^ n + 1) / Nat.gcd 3 (2 ^ n + 1) = 2 ^ n + 1 := by
  obtain ⟨k, rfl⟩ := hn
  have h4 : 2 ^ (k + k) = 4 ^ k := by rw [← two_mul, pow_mul]; norm_num
  have hmod : (4 ^ k + 1) % 3 = 2 := by
    rw [Nat.add_mod, Nat.pow_mod]
    norm_num
  have hg : Nat.gcd 3 (4 ^ k + 1) = 1 := by
    rw [Nat.gcd_rec, hmod]
    norm_num
  rw [h4, hg, Nat.div_one]

theorem BenderType.exists_cartan_conj_quot_of_even {K : Type*} [Group K] [Finite K] {n e : ℕ}
    (hB : BenderType K n 3 e) (hn : Even n) (Q : Sylow 2 K) {t₀ : K}
    (hc : BenderCore (2 ^ n) 3 e (Q : Subgroup K) t₀) {x x' : K}
    (hx : x ∈ (Q : Subgroup K)) (hxZ : x ∉ rootCenter (Q : Subgroup K))
    (hx' : x' ∈ (Q : Subgroup K)) (hx'Z : x' ∉ rootCenter (Q : Subgroup K)) :
    ∃ d ∈ cartan (Q : Subgroup K) t₀, (d * x * d⁻¹)⁻¹ * x' ∈ rootCenter (Q : Subgroup K) := by
  classical
  set P : Subgroup K := (Q : Subgroup K) with hP
  set Z : Subgroup K := rootCenter P with hZ
  have hZP : Z ≤ P := inf_le_left
  have he : e = 2 ^ n + 1 := by
    rcases hB.cases' with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, he, -⟩
    · omega
    · omega
    · rw [he, unitary_e_of_even hn]
  have hdP : ∀ d ∈ cartan P t₀, d ∈ normalizer (P : Set K) := fun d hd => cartan_le_borel _ _ hd
  have hconjP : ∀ d ∈ cartan P t₀, ∀ y ∈ P, d * y * d⁻¹ ∈ P := fun d hd y hy =>
    (mem_normalizer_iff.mp (hdP d hd) y).mp hy
  have hconjZ : ∀ d ∈ normalizer (P : Set K), ∀ z ∈ Z, d * z * d⁻¹ ∈ Z := fun d hd z hz =>
    conj_mem_inf_centralizer_of_mem_normalizer hd hz
  have hZinv : ∀ d ∈ normalizer (P : Set K), ∀ y : K, d * y * d⁻¹ ∈ Z → y ∈ Z := by
    intro d hd y hy
    have := hconjZ _ (inv_mem hd) _ hy
    rwa [show d⁻¹ * (d * y * d⁻¹) * d⁻¹⁻¹ = y by group] at this
  let φ : Option (cartan P t₀) → P ⧸ Z.subgroupOf P := fun o =>
    o.elim (QuotientGroup.mk 1) fun d => QuotientGroup.mk ⟨(d : K) * x * (d : K)⁻¹,
      hconjP d d.2 x hx⟩
  have hinj : Function.Injective φ := by
    rintro (_ | d) (_ | d') hdd
    · rfl
    · exfalso
      have h1 := QuotientGroup.eq.mp hdd
      rw [mem_subgroupOf] at h1
      simp only [inv_one, one_mul] at h1
      exact hxZ (hZinv d' (hdP d' d'.2) x h1)
    · exfalso
      have h1 := QuotientGroup.eq.mp hdd
      rw [mem_subgroupOf] at h1
      simp only [mul_one] at h1
      exact hxZ (hZinv d (hdP d d.2) x (by simpa using inv_mem h1))
    · have h1 := QuotientGroup.eq.mp hdd
      rw [mem_subgroupOf] at h1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
      set g := (d : K)⁻¹ * d' with hg
      have hgD : g ∈ cartan P t₀ := mul_mem (inv_mem d.2) d'.2
      have h2 : x⁻¹ * (g * x * g⁻¹) ∈ Z := by
        have := hconjZ _ (inv_mem (hdP d d.2)) _ h1
        rw [hg]
        convert this using 1
        group
      have h3 : g * x * g⁻¹ * x⁻¹ ∈ Z := by
        have := hconjZ x (le_normalizer hx) _ h2
        convert this using 1
        group
      by_cases hg1 : g = 1
      · congr 1
        apply Subtype.ext
        have : (d' : K) = d := by
          have := congrArg ((d : K) * ·) hg1
          simp only [hg, mul_inv_cancel_left, mul_one] at this
          exact this
        exact this.symm
      · exact absurd (hB.fixedPointFree_unitary Q hc.sq_eq_one hc.not_mem hgD hg1 hx h3) hxZ
  have hcardQ : Nat.card (P ⧸ Z.subgroupOf P) = (2 ^ n) ^ 2 := by
    have h1 := (Z.subgroupOf P).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hZP).toEquiv, hc.card_center, hc.card_eq] at h1
    have h2 : 2 ^ n * (Z.subgroupOf P).index = 2 ^ n * (2 ^ n) ^ 2 := by rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h2
  have hcardO : Nat.card (Option (cartan P t₀)) = (2 ^ n) ^ 2 := by
    rw [Finite.card_option, hc.card_cartan, he]
    obtain ⟨m, hm⟩ : ∃ m, 2 ^ n = m + 1 :=
      ⟨2 ^ n - 1, by have := Nat.one_le_two_pow (n := n); omega⟩
    rw [hm, Nat.add_sub_cancel]
    ring
  have hbij := hinj.bijective_of_nat_card_le (by rw [hcardQ, hcardO])
  obtain ⟨o, ho⟩ := hbij.2 (QuotientGroup.mk ⟨x', hx'⟩)
  rcases o with _ | d
  · exfalso
    have h1 := QuotientGroup.eq.mp ho
    rw [mem_subgroupOf] at h1
    simp only [inv_one, one_mul] at h1
    exact hx'Z h1
  · refine ⟨d, d.2, ?_⟩
    have h1 := QuotientGroup.eq.mp ho
    rw [mem_subgroupOf] at h1
    simpa using h1

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem exists_cartan_conj_szT₁_of_card_sylow
    (h : U3Start G L f t T) (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (heven : Even f) {w w' : G} (hw : w ∈ szT₁ L T) (hwA : w ∉ szA₁ (szT₁ L T))
    (hw' : w' ∈ szT₁ L T) (hw'A : w' ∉ szA₁ (szT₁ L T)) :
    ∃ d ∈ L, d * t = t * d ∧ d ∈ normalizer (szT₁ L T : Set G) ∧
      d ∈ normalizer (szA L T t : Set G) ∧ (d * w * d⁻¹)⁻¹ * w' ∈ szA₁ (szT₁ L T) := by
  obtain ⟨e, Q, hB, hmemQ, hmemZ⟩ := h.exists_bender_of_card_sylow hS2
  obtain ⟨t₀, hc⟩ := hB.exists_benderCore Q
  have hwL : w ∈ L := szT₁_le_right L T hw
  have hwL' : w' ∈ L := szT₁_le_right L T hw'
  obtain ⟨d, hd, hdd⟩ := BenderType.exists_cartan_conj_quot_of_even hB heven Q hc
    ((hmemQ ⟨w, hwL⟩).mpr hw) (fun h1 => hwA ((hmemZ _).mp h1))
    ((hmemQ ⟨w', hwL'⟩).mpr hw') (fun h1 => hw'A ((hmemZ _).mp h1))
  have hdT : (d : G) ∈ normalizer (szT₁ L T : Set G) :=
    (mem_borel_iff_mem_normalizer hmemQ (szT₁_le_right L T) d).mp (cartan_le_borel _ _ hd)
  refine ⟨d, d.2, mem_centralizer_iff.mp h.mem d d.2, hdT,
    h.inf_normalizer_le_normalizer_szA ⟨d.2, hdT⟩, ?_⟩
  have := (hmemZ _).mp hdd
  simpa using this

section Certificates


theorem ncard_u3Omega_of_even_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (heven : Even f)
    (hmove : ∃ y ∈ normalizer ((szT₁ L T ⊔ R₂ ⊔ zpowers t : Subgroup G) : Set G),
      y * t * y⁻¹ ∉ R₂ ⊔ zpowers t) : (u3Omega L T R₂ t).ncard = (2 ^ f) ^ 2 := by
  obtain ⟨-, -, -, hNR₁⟩ := h.char_of_card_sylow hS2 hR
  obtain ⟨-, -, -, hNAR₁, -, -⟩ := h.u3R2_canonical_of_card_sylow hS2 hR
  have hsub : Set.range (u3OmegaPoint L T R₂ t hR.le h.mem_centralizer_szT₁) ⊆
      u3Omega L T R₂ t := by
    rintro _ ⟨c, rfl⟩
    induction c using QuotientGroup.induction_on with | H w => ?_
    rw [u3OmegaPoint_mk]
    have hwt : (w : G) * t = t * w := hR.t_comm _ w.2
    by_cases hwA : (w : G) ∈ szA₁ (szT₁ L T)
    · rw [hwt, sup_zpowers_mul_eq (hR.le hwA)]
      exact sup_zpowers_mem_u3Omega L T R₂ t
    · obtain ⟨y, hy, hyt⟩ := hmove
      obtain ⟨w₀, hw₀, r₀, hr₀, hyw⟩ := h.exists_mul_of_mem_normalizer_szR_of_card_sylow hS2 hR hy
      have hw₀A : w₀ ∉ szA₁ (szT₁ L T) := fun h1 => hyt (by
        rw [hyw]
        exact mul_mem (mem_sup_left (mul_mem (hR.le h1) hr₀)) (mem_sup_right (mem_zpowers t)))
      obtain ⟨d, -, hdt, -, hdA, hdw⟩ :=
        h.exists_cartan_conj_szT₁_of_card_sylow hS2 heven hw₀ hw₀A w.2 hwA
      have hdY := hNAR₁ hdA
      have hdyY := mul_mem hdY hy
      refine ⟨d * y, hdyY, ?_⟩
      rw [map_conj_sup_zpowers (mem_inf.mp (hNR₁ hdyY)).2]
      have hdr : t⁻¹ * (d * r₀ * d⁻¹) * t ∈ R₂ := by
        have h1 : d * r₀ * d⁻¹ ∈ R₂ := (mem_normalizer_iff.mp (mem_inf.mp (hNR₁ hdY)).2 r₀).mp hr₀
        have := hR.tN _ h1
        rw [hR.t_inv] at this ⊢
        exact this
      have hdt' : d * t * d⁻¹ = t := by rw [hdt, mul_inv_cancel_right]
      have e1 : d * y * t * (d * y)⁻¹ = (d * w₀ * d⁻¹) * t * (t⁻¹ * (d * r₀ * d⁻¹) * t) := by
        calc d * y * t * (d * y)⁻¹ = d * (y * t * y⁻¹) * d⁻¹ := by group
          _ = d * (w₀ * r₀ * t) * d⁻¹ := by rw [hyw]
          _ = (d * w₀ * d⁻¹) * (d * r₀ * d⁻¹) * (d * t * d⁻¹) := by group
          _ = (d * w₀ * d⁻¹) * t * (t⁻¹ * (d * r₀ * d⁻¹) * t) := by rw [hdt']; group
      rw [e1, sup_zpowers_mul_eq hdr]
      set a := (d * w₀ * d⁻¹)⁻¹ * (w : G) with ha
      have hat : a * t = t * a := hR.szA₁_comm_t hdw
      have e2 : (w : G) * t = (d * w₀ * d⁻¹) * t * a := by
        rw [mul_assoc (d * w₀ * d⁻¹) t a, ← hat, ha]
        group
      rw [e2, sup_zpowers_mul_eq (hR.le hdw)]
  have hfin : (u3Omega L T R₂ t).Finite :=
    (Set.finite_range (u3OmegaPoint L T R₂ t hR.le h.mem_centralizer_szT₁)).subset
      (h.u3Omega_subset_range_of_card_sylow hS2 hR)
  refine le_antisymm (h.ncard_u3Omega_le_of_card_sylow hS2 hR) ?_
  calc (2 ^ f) ^ 2 = (Set.range (u3OmegaPoint L T R₂ t hR.le h.mem_centralizer_szT₁)).ncard := by
        rw [Set.ncard_range_of_injective (h.u3OmegaPoint_injective_of_card_sylow hS2 hR),
          h.card_quotient_szA₁_of_card_sylow hS2]
    _ ≤ (u3Omega L T R₂ t).ncard := Set.ncard_le_ncard hsub hfin

end Certificates

end U3Start

end CFSG.SeitzReduction.RankOne
