module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddLocal

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup

variable {G : Type} [Group G] [Finite G] {A V K : Subgroup G} {t y : G}

omit [Finite G] in
private theorem mul_comm_of_mem_V_of_l34SuzOdd (hD : L34SuzOddData A V K y) {a b : G}
    (ha : a ∈ V) (hb : b ∈ V) : a * b = b * a := by
  have ha2 : a * a = 1 := hD.mul_self a ha
  have hb2 : b * b = 1 := hD.mul_self b hb
  have hab2 : (a * b) * (a * b) = 1 := hD.mul_self (a * b) (V.mul_mem ha hb)
  have h1 : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right hab2
  have h2 : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have h3 : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  calc a * b = (a * b)⁻¹ := h1.symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [h2, h3]

private theorem eq_one_of_mem_oddIn_of_involution {H : Subgroup G} {e : G}
    (he : e ∈ oddIn H) (he2 : e * e = 1) : e = 1 := by
  have hodd : Odd (Nat.card (oddIn H)) := by
    rw [oddIn]
    exact CFSG.ComponentClassification.HarrisLit.odd_card_map_pPrimeCore H.subtype
  have hpow : e ^ 2 = 1 := by rwa [pow_two]
  have hdvd : orderOf e ∣ 2 := orderOf_dvd_of_pow_eq_one hpow
  have hdvd' : orderOf e ∣ Nat.card (oddIn H) := (oddIn H).orderOf_dvd_natCard he
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hodd.coprime_two_left hdvd hdvd')

private theorem eq_t_of_involution_mem_centralizer_inf
    (hS : L34SuzOddSetting A t) {a : G}
    (haH : a ∈ centralizer ({t} : Set G)) (haA : a ∈ centralizer (A : Set G))
    (ha2 : a * a = 1) (ha1 : a ≠ 1) : a = t := by
  have ht2 : t * t = 1 := by rw [← pow_two, ← hS.orderOf_t, pow_orderOf_eq_one]
  have ha_sup : a ∈ oddIn (centralizer ({t} : Set G)) ⊔ zpowers t := by
    have h : a ∈ centralizer ({t} : Set G) ⊓ centralizer (A : Set G) :=
      Subgroup.mem_inf.mpr ⟨haH, haA⟩
    rwa [centralizer_inf_centralizer_eq_of_l34SuzOdd hS] at h
  have hc : ∀ e ∈ oddIn (centralizer ({t} : Set G)), e * t = t * e := fun e he =>
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.map_subtype_le _ he)
  rcases CFSG.ComponentClassification.GrSLit.GrS4.mem_or_mul_of_mem_sup_zpowers ht2 hc ha_sup
    with hin | ⟨e, he, rfl⟩
  · exact absurd (eq_one_of_mem_oddIn_of_involution hin ha2) ha1
  · have he2 : e * e = 1 := by
      have h1 : (e * t) * (e * t) = e * e * (t * t) := by
        rw [show (e * t) * (e * t) = e * (t * e) * t by group, ← hc e he]
        group
      rw [h1, ht2, mul_one] at ha2
      exact ha2
    have he1 : e = 1 := eq_one_of_mem_oddIn_of_involution he he2
    rw [he1, one_mul]

private theorem not_mem_centralizer_of_l34SuzOdd (hS : L34SuzOddSetting A t)
    (hD : L34SuzOddData A V K y) {u : G} (hu : u ∈ V) (hu1 : u ≠ 1) :
    u ∉ centralizer (A : Set G) := by
  intro huC
  have huA : u ∈ A := hD.le_A hu
  have hcen : (⟨u, huA⟩ : ↥A) ∈ center ↥A := by
    rw [Subgroup.mem_center_iff]
    intro a
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp huC (a : G) a.2
  have hu2 : (⟨u, huA⟩ : ↥A) * ⟨u, huA⟩ = 1 := by
    apply Subtype.ext
    show u * u = 1
    exact hD.mul_self u hu
  have hpow : (⟨u, huA⟩ : ↥A) ^ 2 = 1 := by rwa [pow_two]
  have h1 : (⟨u, huA⟩ : ↥A) = 1 :=
    CFSG.Walter.eq_one_of_mem_center_of_pow hS.odd_card_center hcen (m := 1) (by simpa using hpow)
  exact hu1 (congrArg Subtype.val h1)

private theorem eq_of_involutions_mul_mem_center_of_l34SuzOdd (hS : L34SuzOddSetting A t)
    {a b : ↥A} (ha : a * a = 1) (hb : b * b = 1) (hz : a * b ∈ center ↥A) : a = b := by
  have hba : b * a = a * b := by
    have h1 := Subgroup.mem_center_iff.mp hz b
    calc b * a = b * a * (b * b) := by rw [hb, mul_one]
      _ = (b * (a * b)) * b := by group
      _ = ((a * b) * b) * b := by rw [h1]
      _ = a * (b * b) * b := by group
      _ = a * b := by rw [hb]; group
  have hab2 : (a * b) * (a * b) = 1 := by
    calc (a * b) * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hba]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha, hb, one_mul]
  have hz1 : a * b = 1 := by
    have hpow : (a * b) ^ 2 = 1 := by rwa [pow_two]
    exact CFSG.Walter.eq_one_of_mem_center_of_pow hS.odd_card_center hz (m := 1)
      (by simpa using hpow)
  calc a = a * 1 := (mul_one a).symm
    _ = a * (b * b) := by rw [hb]
    _ = (a * b) * b := by group
    _ = b := by rw [hz1, one_mul]

private theorem exists_fused_conj_of_l34SuzOdd
    (hS : L34SuzOddSetting A t)
    (hD : L34SuzOddData A V K y) {u : G} (hu : u ∈ V) (hu1 : u ≠ 1) :
    ∃ (g₀ r₀ : G), r₀ = g₀ * t * g₀⁻¹ ∧ r₀ ≠ t ∧ r₀ * t = t * r₀ ∧
      r₀ ∈ centralizer ({t} : Set G) ∧ r₀ * r₀ = 1 ∧ r₀ ≠ 1 ∧
      r₀ ∉ centralizer (A : Set G) := by
  have ht2 : t * t = 1 := by rw [← pow_two, ← hS.orderOf_t, pow_orderOf_eq_one]
  have ht1 : t ≠ 1 := by
    intro h
    have h2 : orderOf t = 1 := by rw [h, orderOf_one]
    rw [hS.orderOf_t] at h2
    exact absurd h2 (by decide)
  have huCA : u ∉ centralizer (A : Set G) := not_mem_centralizer_of_l34SuzOdd hS hD hu hu1
  have : IsSimpleGroup G := hS.base.1
  obtain ⟨g₀, hne₀, hcomm₀⟩ :=
    CFSG.EvenSporadicStandard.exists_fused_commuting_involution hS.base.2.1 hS.orderOf_t
  let r₀ : G := g₀ * t * g₀⁻¹
  have hr₀H : r₀ ∈ centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcomm₀
  have hr₀1 : r₀ ≠ 1 := by
    intro h
    have h1 : t = 1 := by
      have h2 := congrArg (fun z => g₀⁻¹ * z * g₀) h
      have h3 : g₀⁻¹ * (g₀ * t * g₀⁻¹) * g₀ = t := by group
      rw [h3] at h2
      simpa [r₀] using h2
    exact ht1 h1
  have hr₀2 : r₀ * r₀ = 1 := by
    have h1 : r₀ * r₀ = g₀ * (t * t) * g₀⁻¹ := by simp only [r₀]; group
    rw [h1, ht2]; group
  have hr₀CA : r₀ ∉ centralizer (A : Set G) := fun h =>
    hne₀ (eq_t_of_involution_mem_centralizer_inf hS hr₀H h hr₀2 hr₀1)
  exact ⟨g₀, r₀, rfl, hne₀, hcomm₀, hr₀H, hr₀2, hr₀1, hr₀CA⟩

private theorem exists_fixed_coset_of_umoves
    (hS : L34SuzOddSetting A t) (hD : L34SuzOddData A V K y)
    {u : G} (hu : u ∈ V) (hu1 : u ≠ 1) {r₀ : G}
    (hHnorm : centralizer ({t} : Set G) ≤ normalizer (A : Set G))
    (hr₀H : r₀ ∈ centralizer ({t} : Set G)) (hr₀2 : r₀ * r₀ = 1) :
    ∃ hA : ↥A,
      let w : ↥A := hA * ⟨u, hD.le_A hu⟩ * hA⁻¹
      w * w = 1 ∧
        (QuotientGroup.mk' (center ↥A))
            (normalizerConjAutOfMem A (centralizer ({t} : Set G)) hHnorm ⟨r₀, hr₀H⟩ w) =
          (QuotientGroup.mk' (center ↥A)) w := by
  have huCA : u ∉ centralizer (A : Set G) := not_mem_centralizer_of_l34SuzOdd hS hD hu hu1
  let B : Subgroup G := centralizer ({t} : Set G)
  let r₀B : ↥B := ⟨r₀, hr₀H⟩
  let α : MulAut (↥A ⧸ center ↥A) := normalizerToCenterQuotientAut A B hHnorm r₀B
  have hαα : α * α = 1 := by
    have hsq : r₀B * r₀B = 1 := Subtype.ext hr₀2
    calc α * α = normalizerToCenterQuotientAut A B hHnorm (r₀B * r₀B) :=
          (map_mul (normalizerToCenterQuotientAut A B hHnorm) r₀B r₀B).symm
      _ = 1 := by rw [hsq, map_one]
  let uA : ↥A := ⟨u, hD.le_A hu⟩
  let q : ↥A →* (↥A ⧸ center ↥A) := QuotientGroup.mk' (center ↥A)
  have huA2 : uA * uA = 1 := Subtype.ext (hD.mul_self u hu)
  have hq2 : q uA * q uA = 1 := by rw [← map_mul, huA2, map_one]
  have hqne : q uA ≠ 1 := by
    intro h
    apply huCA
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hmem : uA ∈ center ↥A := (QuotientGroup.eq_one_iff uA).mp h
    have h1 := Subgroup.mem_center_iff.mp hmem (⟨a, ha⟩ : ↥A)
    simpa using congrArg Subtype.val h1
  have hqu2 : orderOf (q uA) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hq2) hqne
  have hU : CFSG.EvenSporadicStandard.Solomon78.UMovesCond (↥A ⧸ center ↥A) :=
    CFSG.EvenSporadicStandard.Solomon78.suz_umovesCond_of_isSporadic hS.suz
  obtain ⟨hbar, hfix⟩ := hU (q uA) hqu2 α hαα
  obtain ⟨hA, rfl⟩ := QuotientGroup.mk'_surjective (center ↥A) hbar
  let w : ↥A := hA * uA * hA⁻¹
  refine ⟨hA, ?_, ?_⟩
  · have h1 : w * w = hA * (uA * uA) * hA⁻¹ := by simp only [w]; group
    rw [h1, huA2]; group
  · have hqw : q w = q hA * q uA * (q hA)⁻¹ := by
      simp only [w, map_mul, map_inv]
    rw [hqw]
    exact hfix

private theorem exists_lift_fixed_of_umoves
    (hS : L34SuzOddSetting A t) (hD : L34SuzOddData A V K y)
    {u : G} (hu : u ∈ V) (hu1 : u ≠ 1) {r₀ : G}
    (hHnorm : centralizer ({t} : Set G) ≤ normalizer (A : Set G))
    (hr₀H : r₀ ∈ centralizer ({t} : Set G)) (hr₀2 : r₀ * r₀ = 1) :
    ∃ hA : ↥A, r₀ * (hA * ⟨u, hD.le_A hu⟩ * hA⁻¹ : ↥A) * r₀⁻¹ =
      (hA * ⟨u, hD.le_A hu⟩ * hA⁻¹ : ↥A) := by
  obtain ⟨hA, hw2, hqeq⟩ :=
    exists_fixed_coset_of_umoves hS hD hu hu1 hHnorm hr₀H hr₀2
  let uA : ↥A := ⟨u, hD.le_A hu⟩
  let w : ↥A := hA * uA * hA⁻¹
  have hw2' : w * w = 1 := by simpa [w, uA] using hw2
  let w' : ↥A := normalizerConjAutOfMem A (centralizer ({t} : Set G)) hHnorm ⟨r₀, hr₀H⟩ w
  have hcoe : (w' : G) = r₀ * (w : G) * r₀⁻¹ := by
    change ((Subgroup.normalizerMonoidHom (H := A))
      (Subgroup.inclusion hHnorm ⟨r₀, hr₀H⟩) w : G) = _
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_inclusion]
  have hw'2 : w' * w' = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_one, hcoe]
    have hwval : (w : G) * (w : G) = 1 := by
      have h2 : ((w * w : ↥A) : G) = (w : G) * (w : G) := Subgroup.coe_mul A w w
      rw [← h2, hw2', Subgroup.coe_one]
    calc r₀ * (w : G) * r₀⁻¹ * (r₀ * (w : G) * r₀⁻¹)
        = r₀ * ((w : G) * (w : G)) * r₀⁻¹ := by group
      _ = 1 := by rw [hwval]; group
  have hqww2 : (QuotientGroup.mk' (center ↥A)) w *
      (QuotientGroup.mk' (center ↥A)) w = 1 := by
    rw [← map_mul, hw2', map_one]
  have hqmem : (QuotientGroup.mk' (center ↥A)) (w' * w) = 1 := by
    rw [map_mul, hqeq, hqww2]
  have hmem : w' * w ∈ center ↥A := (QuotientGroup.eq_one_iff (w' * w)).mp hqmem
  have hw'eq : w' = w := eq_of_involutions_mul_mem_center_of_l34SuzOdd hS hw'2 hw2' hmem
  have hconj : r₀ * (w : G) * r₀⁻¹ = (w : G) := by rw [← hcoe, hw'eq]
  exact ⟨hA, by simpa [w, uA] using hconj⟩

private theorem exists_conj_commute_of_fixed_lift (hS : L34SuzOddSetting A t)
    (hD : L34SuzOddData A V K y) {u : G} (hu : u ∈ V) {g₀ r₀ : G}
    (hr₀def : r₀ = g₀ * t * g₀⁻¹) (hne₀ : r₀ ≠ t) (hcomm₀ : r₀ * t = t * r₀)
    {hA : ↥A}
    (hfix : r₀ * (hA * ⟨u, hD.le_A hu⟩ * hA⁻¹ : ↥A) * r₀⁻¹ =
      (hA * ⟨u, hD.le_A hu⟩ * hA⁻¹ : ↥A)) :
    ∃ g : G, g * t * g⁻¹ ≠ t ∧
      (g * t * g⁻¹) * t = t * (g * t * g⁻¹) ∧
      (g * t * g⁻¹) * u = u * (g * t * g⁻¹) := by
  have ht2 : t * t = 1 := by rw [← pow_two, ← hS.orderOf_t, pow_orderOf_eq_one]
  let hg : G := (hA : G)
  let w : ↥A := hA * ⟨u, hD.le_A hu⟩ * hA⁻¹
  have hwG : (w : G) = hg * u * hg⁻¹ := by
    simp only [w, hg, Subgroup.coe_mul, Subgroup.coe_inv]
  have hcomm_r₀w : r₀ * (w : G) = (w : G) * r₀ := by
    have h1 : r₀ * (w : G) * r₀⁻¹ = (w : G) := by simpa [w] using hfix
    calc r₀ * (w : G) = (r₀ * (w : G) * r₀⁻¹) * r₀ := by group
      _ = (w : G) * r₀ := by rw [h1]
  have hgt_comm : hg * t = t * hg :=
    Subgroup.mem_centralizer_iff.mp hS.t_mem (hA : G) hA.2
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  let r : G := hg⁻¹ * r₀ * hg
  have hr_ne : r ≠ t := by
    intro h
    apply hne₀
    calc r₀ = hg * r * hg⁻¹ := by simp only [r]; group
      _ = hg * t * hg⁻¹ := by rw [h]
      _ = t := by rw [hgt_comm]; group
  have hr_t : r * t = t * r := by
    have hgtC : Commute hg t := hgt_comm
    have h1 : Commute hg⁻¹ t := hgtC.inv_left
    have h2 : Commute r₀ t := hcomm₀
    have h3 : Commute (hg⁻¹ * r₀ * hg) t := (h1.mul_left h2).mul_left hgtC
    exact h3.eq
  have hr_u : r * u = u * r := by
    calc r * u = hg⁻¹ * r₀ * hg * u := by simp only [r]
      _ = hg⁻¹ * r₀ * (hg * u * hg⁻¹) * hg := by group
      _ = hg⁻¹ * r₀ * (w : G) * hg := by rw [← hwG]
      _ = hg⁻¹ * (r₀ * (w : G)) * hg := by group
      _ = hg⁻¹ * ((w : G) * r₀) * hg := by rw [hcomm_r₀w]
      _ = hg⁻¹ * (hg * u * hg⁻¹) * r₀ * hg := by rw [hwG]; group
      _ = u * (hg⁻¹ * r₀ * hg) := by group
      _ = u * r := by simp only [r]
  refine ⟨hg⁻¹ * g₀, ?_, ?_, ?_⟩
  · have h1 : (hg⁻¹ * g₀) * t * (hg⁻¹ * g₀)⁻¹ = r := by
      simp only [r]
      rw [hr₀def]
      group
    rw [h1]
    exact hr_ne
  · have h1 : (hg⁻¹ * g₀) * t * (hg⁻¹ * g₀)⁻¹ = r := by
      simp only [r]
      rw [hr₀def]
      group
    rw [h1]
    exact hr_t
  · have h1 : (hg⁻¹ * g₀) * t * (hg⁻¹ * g₀)⁻¹ = r := by
      simp only [r]
      rw [hr₀def]
      group
    rw [h1]
    exact hr_u

private theorem exists_conj_commute_of_l34SuzOdd
    (hS : L34SuzOddSetting A t) (hD : L34SuzOddData A V K y)
    {u : G} (hu : u ∈ V) (hu1 : u ≠ 1) :
    ∃ g : G, g * t * g⁻¹ ≠ t ∧
      (g * t * g⁻¹) * t = t * (g * t * g⁻¹) ∧
      (g * t * g⁻¹) * u = u * (g * t * g⁻¹) := by
  obtain ⟨g₀, r₀, hr₀def, hne₀, hcomm₀, hr₀H, hr₀2, hr₀1, _⟩ :=
    exists_fused_conj_of_l34SuzOdd hS hD hu hu1
  have hHnorm : centralizer ({t} : Set G) ≤ normalizer (A : Set G) := by
    intro x hx
    exact CFSG.Open.standardComponentIsStandard.mem_normalizer_of_commute
      hS.standard.standardComponentIsStandard hS.t_mem hS.orderOf_t
      (Subgroup.mem_centralizer_singleton_iff.mp hx)
  obtain ⟨hA, hfix⟩ :=
    exists_lift_fixed_of_umoves hS hD hu hu1 hHnorm hr₀H hr₀2
  exact exists_conj_commute_of_fixed_lift hS hD hu hr₀def hne₀ hcomm₀ hfix

omit [Finite G] in
private theorem mem_oddIn_iff_mem_pPrimeCore {Q : Subgroup G} (q : ↥Q) :
    q ∈ pPrimeCore 2 ↥Q ↔ (q : G) ∈ oddIn Q := by
  rw [oddIn, Subgroup.mem_map]
  constructor
  · exact fun hq => ⟨q, hq, rfl⟩
  · rintro ⟨y, hy, hyq⟩
    rwa [show y = q from Subtype.ext hyq] at hy

private theorem oddIn_le_oddIn_of_le_of_normalizer {Q J : Subgroup G} (hQJ : Q ≤ J)
    (hnorm : J ≤ normalizer (oddIn Q : Set G)) : oddIn Q ≤ oddIn J := by
  have h1 : oddIn Q ≤ Q := by
    simpa [oddIn] using Subgroup.map_subtype_le (pPrimeCore 2 ↥Q)
  have hOQleJ : oddIn Q ≤ J := h1.trans hQJ
  have hodd : Odd (Nat.card (oddIn Q)) := by
    rw [oddIn]
    exact CFSG.ComponentClassification.HarrisLit.odd_card_map_pPrimeCore Q.subtype
  have hnorm' : (oddIn Q).subgroupOf J ≤ pPrimeCore 2 ↥J := by
    refine le_sSup ⟨?_, ?_⟩
    · exact (Subgroup.normal_subgroupOf_iff_le_normalizer hOQleJ).mpr hnorm
    · have hcard : Nat.card ↥((oddIn Q).subgroupOf J) = Nat.card ↥(oddIn Q) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOQleJ).toEquiv
      rw [hcard]
      exact hodd.coprime_two_left
  have hmap := Subgroup.map_mono (f := J.subtype) hnorm'
  rw [Subgroup.map_subgroupOf_eq_of_le hOQleJ] at hmap
  simpa [oddIn] using hmap

private theorem card_le_two_of_isPGroup_le_centralizer_conj (hS : L34SuzOddSetting A t) (g : G)
    {B : Subgroup G} (hmemB : ∀ a ∈ A, g⁻¹ * a * g ∈ B) {P : Subgroup G}
    (hPB : P ≤ centralizer (B : Set G)) (hP : IsPGroup 2 P) : Nat.card P ≤ 2 := by
  have hmap_le : P.map (MulAut.conj g).toMonoidHom ≤ centralizer (A : Set G) := by
    rintro _ ⟨p, hpP, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hcomm := Subgroup.mem_centralizer_iff.mp (hPB hpP) (g⁻¹ * a * g) (hmemB a ha)
    calc a * (g * p * g⁻¹) = g * ((g⁻¹ * a * g) * p) * g⁻¹ := by group
      _ = g * (p * (g⁻¹ * a * g)) * g⁻¹ := by rw [← hcomm]
      _ = (g * p * g⁻¹) * a := by group
  have hP'p : IsPGroup 2 (P.map (MulAut.conj g).toMonoidHom) := hP.map _
  have hP'sub : IsPGroup 2
      ((P.map (MulAut.conj g).toMonoidHom).subgroupOf (centralizer (A : Set G))) :=
    hP'p.of_equiv (Subgroup.subgroupOfEquivOfLe hmap_le).symm
  obtain ⟨SA, hSA⟩ := hP'sub.exists_le_sylow
  have hcardSA : Nat.card SA = 2 := hS.card_sylow SA
  have hcardSub : Nat.card ↥((P.map (MulAut.conj g).toMonoidHom).subgroupOf
      (centralizer (A : Set G))) = Nat.card ↥(P.map (MulAut.conj g).toMonoidHom) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hmap_le).toEquiv
  have hcardP' : Nat.card ↥(P.map (MulAut.conj g).toMonoidHom) = Nat.card P :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hdvd : Nat.card P ∣ Nat.card SA := by
    rw [← hcardP', ← hcardSub]
    exact Subgroup.card_dvd_of_le hSA
  rw [hcardSA] at hdvd
  exact Nat.le_of_dvd (by norm_num) hdvd

private theorem index_pPrimeCore_eq_two_of_card_le_two {Q : Subgroup G} {s : G} (hsQ : s ∈ Q)
    (hs2 : s * s = 1) (hs1 : s ≠ 1)
    (hQ2 : ∀ P : Subgroup G, P ≤ Q → IsPGroup 2 P → Nat.card P ≤ 2) :
    (pPrimeCore 2 ↥Q).index = 2 := by
  have h2dvdQ : 2 ∣ Nat.card ↥Q := by
    have hsQord : orderOf (⟨s, hsQ⟩ : ↥Q) = 2 := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime (by rw [pow_two]; exact hs2) hs1
    rw [← hsQord]
    exact orderOf_dvd_natCard _
  obtain ⟨S⟩ := Sylow.nonempty (p := 2) (G := ↥Q)
  have hSle2 : Nat.card ↥S ≤ 2 := by
    have hmap := (S.isPGroup').map Q.subtype
    have h := hQ2 ((S : Subgroup ↥Q).map Q.subtype) (Subgroup.map_subtype_le _) hmap
    rwa [Subgroup.card_map_of_injective Q.subtype_injective] at h
  have hSdvd : 2 ∣ Nat.card ↥S := S.dvd_card_of_dvd_card h2dvdQ
  have hcardS : Nat.card ↥S = 2 := by
    obtain ⟨k, hk⟩ := hSdvd
    have hpos := Nat.card_pos (α := ↥S)
    omega
  have hScyc : IsCyclic ↥S := isCyclic_of_prime_card (p := 2) hcardS
  obtain ⟨-, -, -, ⟨-, -, hOindex, -⟩, -⟩ := cyclic_sylow_normal_odd_complement S hScyc
  exact hOindex.trans hcardS

omit [Finite G] in
private theorem conj_coset_eq_of_index_two {Q J : Subgroup G}
    (hOindex : (pPrimeCore 2 ↥Q).index = 2)
    (hnorm : J ≤ normalizer (oddIn Q : Set G)) (hJNQ : J ≤ normalizer (Q : Set G))
    {s x : G} (hsQ : s ∈ Q) (hxJ : x ∈ J) (hs2 : s * s = 1) :
    (QuotientGroup.mk' (pPrimeCore 2 ↥Q))
        ⟨x * s * x⁻¹, (Subgroup.mem_normalizer_iff.mp (hJNQ hxJ) s).mp hsQ⟩ =
      (QuotientGroup.mk' (pPrimeCore 2 ↥Q)) ⟨s, hsQ⟩ := by
  have hcardQuot : Nat.card (↥Q ⧸ pPrimeCore 2 ↥Q) = 2 := by
    rw [← Subgroup.index_eq_card]
    exact hOindex
  let sQ : ↥Q := ⟨s, hsQ⟩
  let s'Q : ↥Q :=
    ⟨x * s * x⁻¹, (Subgroup.mem_normalizer_iff.mp (hJNQ hxJ) s).mp hsQ⟩
  have hs'Q2 : s'Q * s'Q = 1 := by
    apply Subtype.ext
    show (x * s * x⁻¹) * (x * s * x⁻¹) = 1
    calc (x * s * x⁻¹) * (x * s * x⁻¹) = x * (s * s) * x⁻¹ := by group
      _ = 1 := by rw [hs2]; group
  have hxNoO : x ∈ normalizer (oddIn Q : Set G) := hnorm hxJ
  have hmem_s'O : s'Q ∈ pPrimeCore 2 ↥Q ↔ sQ ∈ pPrimeCore 2 ↥Q := by
    rw [mem_oddIn_iff_mem_pPrimeCore s'Q, mem_oddIn_iff_mem_pPrimeCore sQ]
    constructor
    · intro h
      have hxinv : x⁻¹ ∈ normalizer (oddIn Q : Set G) :=
        (Subgroup.normalizer (oddIn Q : Set G)).inv_mem hxNoO
      have h1 : x⁻¹ * (s'Q : G) * (x⁻¹)⁻¹ ∈ oddIn Q :=
        (Subgroup.mem_normalizer_iff.mp hxinv (s'Q : G)).mp h
      have h2 : x⁻¹ * (s'Q : G) * (x⁻¹)⁻¹ = s := by
        simp only [s'Q]; group
      rwa [h2] at h1
    · intro h
      have h1 : x * (sQ : G) * x⁻¹ ∈ oddIn Q :=
        (Subgroup.mem_normalizer_iff.mp hxNoO (sQ : G)).mp h
      have h2 : x * (sQ : G) * x⁻¹ = (s'Q : G) := by
        simp only [sQ, s'Q]
      rwa [h2] at h1
  by_cases hsO : sQ ∈ pPrimeCore 2 ↥Q
  · have hs'O : s'Q ∈ pPrimeCore 2 ↥Q := hmem_s'O.mpr hsO
    change (↑s'Q : ↥Q ⧸ pPrimeCore 2 ↥Q) = ↑sQ
    rw [(QuotientGroup.eq_one_iff s'Q).mpr hs'O, (QuotientGroup.eq_one_iff sQ).mpr hsO]
  · have hs'O : s'Q ∉ pPrimeCore 2 ↥Q := fun h => hsO (hmem_s'O.mp h)
    obtain ⟨y, -, huniq⟩ :=
      (Nat.card_eq_two_iff' (1 : ↥Q ⧸ pPrimeCore 2 ↥Q)).mp hcardQuot
    have h1 : (QuotientGroup.mk' (pPrimeCore 2 ↥Q)) s'Q = y :=
      huniq _ (by intro h; exact hs'O ((QuotientGroup.eq_one_iff s'Q).mp h))
    have h2 : (QuotientGroup.mk' (pPrimeCore 2 ↥Q)) sQ = y :=
      huniq _ (by intro h; exact hsO ((QuotientGroup.eq_one_iff sQ).mp h))
    rw [h1, h2]

private theorem conj_commutator_mem_oddIn_of_index_two {Q J : Subgroup G} (hQJ : Q ≤ J)
    (hJNQ : J ≤ normalizer (Q : Set G))
    (hOindex : (pPrimeCore 2 ↥Q).index = 2)
    (hnorm : J ≤ normalizer (oddIn Q : Set G))
    {s : G} (hsQ : s ∈ Q) (hs2 : s * s = 1) :
    ∀ x ∈ J, s * x * s⁻¹ * x⁻¹ ∈ oddIn J := by
  intro x hxJ
  have hs'Q : x * s * x⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hJNQ hxJ) s).mp hsQ
  let sQ : ↥Q := ⟨s, hsQ⟩
  let s'Q : ↥Q := ⟨x * s * x⁻¹, hs'Q⟩
  have hcoset := conj_coset_eq_of_index_two hOindex hnorm hJNQ hsQ hxJ hs2
  change (QuotientGroup.mk' (pPrimeCore 2 ↥Q)) s'Q =
    (QuotientGroup.mk' (pPrimeCore 2 ↥Q)) sQ at hcoset
  have hsQ2 : sQ * sQ = 1 := Subtype.ext hs2
  have hs'Q2 : s'Q * s'Q = 1 := by
    apply Subtype.ext
    show (x * s * x⁻¹) * (x * s * x⁻¹) = 1
    calc (x * s * x⁻¹) * (x * s * x⁻¹) = x * (s * s) * x⁻¹ := by group
      _ = 1 := by rw [hs2]; group
  have hmemQuot : s'Q⁻¹ * sQ ∈ pPrimeCore 2 ↥Q := QuotientGroup.eq.mp hcoset
  have hs's : sQ * s'Q ∈ pPrimeCore 2 ↥Q := by
    have hinv : (s'Q⁻¹ * sQ)⁻¹ ∈ pPrimeCore 2 ↥Q :=
      (pPrimeCore 2 ↥Q).inv_mem hmemQuot
    have h1 : sQ⁻¹ = sQ := inv_eq_of_mul_eq_one_right hsQ2
    have h2 : s'Q⁻¹ = s'Q := inv_eq_of_mul_eq_one_right hs'Q2
    simpa [mul_inv_rev, h1, h2] using hinv
  have htarget : s * x * s⁻¹ * x⁻¹ ∈ oddIn Q := by
    have h := (mem_oddIn_iff_mem_pPrimeCore (sQ * s'Q)).mp hs's
    have hcoe : ((sQ * s'Q : ↥Q) : G) = s * x * s⁻¹ * x⁻¹ := by
      simp only [sQ, s'Q, Subgroup.coe_mul]
      rw [inv_eq_of_mul_eq_one_right hs2]
      group
    rwa [hcoe] at h
  exact oddIn_le_oddIn_of_le_of_normalizer hQJ hnorm htarget

private theorem commute_conj_data_of_l34SuzOdd (hS : L34SuzOddSetting A t) {w : G}
    (hw2 : w * w = 1) (hwt : t * w = w * t) (g b s : G)
    (hb : b = g⁻¹ * w * g) (hs : s = g⁻¹ * t * g)
    (hct : (g * t * g⁻¹) * t = t * (g * t * g⁻¹))
    (hcw : (g * t * g⁻¹) * w = w * (g * t * g⁻¹)) :
    b * b = 1 ∧ s * s = 1 ∧ b * t = t * b ∧ s * t = t * s ∧ s * b = b * s ∧
      s ≠ 1 := by
  have ht2 : t * t = 1 := by rw [← pow_two, ← hS.orderOf_t, pow_orderOf_eq_one]
  have ht1 : t ≠ 1 := by
    intro h
    have h2 : orderOf t = 1 := by rw [h, orderOf_one]
    rw [hS.orderOf_t] at h2
    exact absurd h2 (by decide)
  have hb2 : b * b = 1 := by
    have h1 : b * b = g⁻¹ * (w * w) * g := by simp only [hb]; group
    rw [h1, hw2]; group
  have hs2 : s * s = 1 := by
    have h1 : s * s = g⁻¹ * (t * t) * g := by simp only [hs]; group
    rw [h1, ht2]; group
  have hbt : b * t = t * b := by
    rw [hb]
    calc g⁻¹ * w * g * t = g⁻¹ * w * (g * t * g⁻¹) * g := by group
      _ = g⁻¹ * (w * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * w) * g := by rw [hcw]
      _ = t * (g⁻¹ * w * g) := by group
  have hst : s * t = t * s := by
    rw [hs]
    calc g⁻¹ * t * g * t = g⁻¹ * (t * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * t) * g := by rw [← hct]
      _ = t * (g⁻¹ * t * g) := by group
  have hsb : s * b = b * s := by
    rw [hs, hb]
    calc g⁻¹ * t * g * (g⁻¹ * w * g) = g⁻¹ * (t * w) * g := by group
      _ = g⁻¹ * (w * t) * g := by rw [hwt]
      _ = g⁻¹ * w * g * (g⁻¹ * t * g) := by group
  have hs1 : s ≠ 1 := by
    intro h
    have h2 : g * s * g⁻¹ = t := by simp only [hs]; group
    rw [h] at h2
    exact ht1 (by simpa using h2.symm)
  exact ⟨hb2, hs2, hbt, hst, hsb, hs1⟩

omit [Finite G] in
private theorem centralizer_le_normalizer_conj_of_l34SuzOdd {u : G}
    (hN : centralizer ({u} : Set G) ≤ normalizer (A : Set G)) (g b : G)
    (hb : b = g⁻¹ * u * g) :
    centralizer ({b} : Set G) ≤ normalizer (conjugate A g : Set G) := by
  have hforward : ∀ z ∈ centralizer ({b} : Set G),
      ∀ w ∈ conjugate A g, z * w * z⁻¹ ∈ conjugate A g := by
    intro z hz w hw
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hw
    have hz' : g * z * g⁻¹ ∈ centralizer ({u} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hzb : z * b = b * z := Subgroup.mem_centralizer_singleton_iff.mp hz
      calc g * z * g⁻¹ * u = g * (z * b) * g⁻¹ := by rw [hb]; group
        _ = g * (b * z) * g⁻¹ := by rw [hzb]
        _ = u * (g * z * g⁻¹) := by rw [hb]; group
    have hNA : g * z * g⁻¹ ∈ normalizer (A : Set G) := hN hz'
    have hmem : (g * z * g⁻¹) * a * (g * z * g⁻¹)⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.mp hNA a).mp ha
    rw [show conjugate A g = A.map (MulAut.conj g⁻¹).toMonoidHom from rfl,
      Subgroup.mem_map]
    refine ⟨_, hmem, ?_⟩
    change (MulAut.conj g⁻¹) ((g * z * g⁻¹) * a * (g * z * g⁻¹)⁻¹) =
      z * (MulAut.conj g⁻¹) a * z⁻¹
    rw [MulAut.conj_apply, MulAut.conj_apply]
    group
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact hforward x hx y
  · intro hy
    have hxinv : x⁻¹ ∈ centralizer ({b} : Set G) :=
      (centralizer ({b} : Set G)).inv_mem hx
    have h := hforward x⁻¹ hxinv (x * y * x⁻¹) hy
    have h2 : x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y := by group
    rwa [h2] at h

private theorem s_mem_inf_centralizer_of_l34SuzOdd (hS : L34SuzOddSetting A t)
    (g b s : G) (hs : s = g⁻¹ * t * g)
    (hst : s * t = t * s) (hsb : s * b = b * s) :
    s ∈ (centralizer ({t} : Set G) ⊓ centralizer ({b} : Set G)) ⊓
      centralizer (conjugate A g : Set G) := by
  refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
  · exact Subgroup.mem_centralizer_singleton_iff.mpr hst
  · exact Subgroup.mem_centralizer_singleton_iff.mpr hsb
  · rw [Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hw
    change (MulAut.conj g⁻¹) a * s = s * (MulAut.conj g⁻¹) a
    rw [MulAut.conj_apply, inv_inv, hs]
    have hta : a * t = t * a := Subgroup.mem_centralizer_iff.mp hS.t_mem a ha
    calc (g⁻¹ * a * g) * (g⁻¹ * t * g) = g⁻¹ * (a * t) * g := by group
      _ = g⁻¹ * (t * a) * g := by rw [hta]
      _ = (g⁻¹ * t * g) * (g⁻¹ * a * g) := by group

private theorem commutator_mem_oddIn_of_l34SuzOdd (hS : L34SuzOddSetting A t)
    {w : G} (hw2 : w * w = 1) (hwt : t * w = w * t)
    (hN : centralizer ({w} : Set G) ≤ normalizer (A : Set G))
    (g b s : G) (hb : b = g⁻¹ * w * g) (hs : s = g⁻¹ * t * g)
    (hct : (g * t * g⁻¹) * t = t * (g * t * g⁻¹))
    (hcw : (g * t * g⁻¹) * w = w * (g * t * g⁻¹)) :
    ∀ x ∈ centralizer ({t} : Set G) ⊓ centralizer ({b} : Set G),
      s * x * s⁻¹ * x⁻¹ ∈
        oddIn (centralizer ({t} : Set G) ⊓ centralizer ({b} : Set G)) := by
  obtain ⟨hb2, hs2, hbt, hst, hsb, hs1⟩ :=
    commute_conj_data_of_l34SuzOdd hS hw2 hwt g b s hb hs hct hcw
  let B : Subgroup G := conjugate A g
  let J : Subgroup G := centralizer ({t} : Set G) ⊓ centralizer ({b} : Set G)
  let Q : Subgroup G := J ⊓ centralizer (B : Set G)
  have hmemB : ∀ a ∈ A, g⁻¹ * a * g ∈ B := fun a ha => by
    rw [show B = A.map (MulAut.conj g⁻¹).toMonoidHom from rfl]
    exact ⟨a, ha, by simp⟩
  have hNb : centralizer ({b} : Set G) ≤ normalizer (B : Set G) :=
    centralizer_le_normalizer_conj_of_l34SuzOdd hN g b hb
  have hJNQ : J ≤ normalizer (Q : Set G) := by
    have h1 : J ≤ normalizer (J : Set G) := Subgroup.le_normalizer
    have h2 : J ≤ normalizer (centralizer (B : Set G) : Set G) :=
      ((inf_le_right : J ≤ centralizer ({b} : Set G)).trans
        (hNb.trans (CFSG.Walter.Huppert.normalizer_le_normalizer_centralizer B)))
    exact (le_inf h1 h2).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hsQ : s ∈ Q := by
    simpa [Q, J, B] using s_mem_inf_centralizer_of_l34SuzOdd hS g b s hs hst hsb
  have hQ2 : ∀ P : Subgroup G, P ≤ Q → IsPGroup 2 P → Nat.card P ≤ 2 :=
    fun P hPQ hP =>
      card_le_two_of_isPGroup_le_centralizer_conj hS g hmemB
        (fun p hp => (Subgroup.mem_inf.mp (hPQ hp)).2) hP
  have hOindex : (pPrimeCore 2 ↥Q).index = 2 :=
    index_pPrimeCore_eq_two_of_card_le_two hsQ hs2 hs1 hQ2
  have hnorm : J ≤ normalizer (oddIn Q : Set G) :=
    hJNQ.trans (CFSG.Walter.normalizer_le_normalizer_map_of_characteristic
      (A := Q) (D := pPrimeCore 2 ↥Q))
  exact conj_commutator_mem_oddIn_of_index_two (by simp [Q])
    (by simpa [Q] using hJNQ) hOindex hnorm hsQ hs2
private theorem not_mem_centralizer_of_conj_involution
    (hS : L34SuzOddSetting A t)
    (hD : L34SuzOddData A V K y) {u : G} (hu : u ∈ V) (hu1 : u ≠ 1) (g b : G)
    (hb : b = g⁻¹ * u * g) (hb2 : b * b = 1) (hb1 : b ≠ 1)
    (hbt : b * t = t * b) : b ∉ centralizer (A : Set G) := by
  intro hbC
  have hbH : b ∈ centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hbt
  have hbeq : b = t := eq_t_of_involution_mem_centralizer_inf hS hbH hbC hb2 hb1
  exact conj_ne_of_l34SuzOdd hS hD hu hu1 g (by
    calc g * t * g⁻¹ = g * b * g⁻¹ := by rw [← hbeq]
      _ = u := by simp only [hb]; group)

private theorem eq_t_mul_u_of_conj_commute_of_l34SuzOdd
    (hS : L34SuzOddSetting A t)
    (hD : L34SuzOddData A V K y)
    {u : G} (hu : u ∈ V) (hu1 : u ≠ 1)
    (hN : centralizer ({u} : Set G) ≤ normalizer (A : Set G))
    (g : G)
    (hne : g * t * g⁻¹ ≠ t)
    (hct : (g * t * g⁻¹) * t = t * (g * t * g⁻¹))
    (hcu : (g * t * g⁻¹) * u = u * (g * t * g⁻¹)) :
    g * t * g⁻¹ = t * u := by
  have ht2 : t * t = 1 := by rw [← pow_two, ← hS.orderOf_t, pow_orderOf_eq_one]
  have ht1 : t ≠ 1 := by
    intro h
    have h2 : orderOf t = 1 := by rw [h, orderOf_one]
    rw [hS.orderOf_t] at h2
    exact absurd h2 (by decide)
  have hu2 : u * u = 1 := hD.mul_self u hu
  have htu : t * u = u * t :=
    (Subgroup.mem_centralizer_iff.mp hS.t_mem u (hD.le_A hu)).symm
  have huCA : u ∉ centralizer (A : Set G) := not_mem_centralizer_of_l34SuzOdd hS hD hu hu1
  let b : G := g⁻¹ * u * g
  let s : G := g⁻¹ * t * g
  obtain ⟨hb2, hs2, hbt, hst, hsb, hs1⟩ :=
    commute_conj_data_of_l34SuzOdd hS hu2 htu g b s rfl rfl hct hcu
  have hb1 : b ≠ 1 := by
    intro h
    have h2 : g * b * g⁻¹ = u := by simp only [b]; group
    rw [h] at h2
    exact hu1 (by simpa using h2.symm)
  have hbord : orderOf b = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hb2) hb1
  have hsord : orderOf s = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hs2) hs1
  have hbA : b ∉ centralizer (A : Set G) :=
    not_mem_centralizer_of_conj_involution hS hD hu hu1 g b rfl hb2 hb1 hbt
  have hsJ : ∀ x ∈ centralizer ({t} : Set G) ⊓ centralizer ({b} : Set G),
      s * x * s⁻¹ * x⁻¹ ∈
        oddIn (centralizer ({t} : Set G) ⊓ centralizer ({b} : Set G)) :=
    commutator_mem_oddIn_of_l34SuzOdd hS hu2 htu hN g b s rfl rfl hct hcu
  rcases eq_of_commutator_mem_oddIn_of_l34SuzOdd hS hbord hbt hbA hsord hst hsb hsJ
    with hst' | hsb' | hstb
  · exact absurd (by
      calc g * t * g⁻¹ = g * s * g⁻¹ := by rw [← hst']
        _ = t := by simp only [s]; group) hne
  · have htu' : t = u := by
      calc t = g * s * g⁻¹ := by simp only [s]; group
        _ = g * b * g⁻¹ := by rw [hsb']
        _ = u := by simp only [b]; group
    exact absurd (by rw [← htu']; exact hS.t_mem) huCA
  · have h1 : t = (g * t * g⁻¹) * u := by
      calc t = g * s * g⁻¹ := by simp only [s]; group
        _ = g * (t * b) * g⁻¹ := by rw [hstb]
        _ = (g * t * g⁻¹) * u := by simp only [b]; group
    calc g * t * g⁻¹ = g * t * g⁻¹ * (u * u) := by rw [hu2, mul_one]
      _ = g * t * g⁻¹ * u * u := by group
      _ = t * u := by rw [← h1]

private theorem exists_conj_commute_of_moved_of_l34SuzOdd (hS : L34SuzOddSetting A t)
    (hD : L34SuzOddData A V K y) {u : G} (hu : u ∈ V) (hu1 : u ≠ 1) {g : G}
    (hr : g * t * g⁻¹ = t * u) :
    ∃ g' : G, g' * t * g'⁻¹ ≠ t ∧
      (g' * t * g'⁻¹) * t = t * (g' * t * g'⁻¹) ∧
      (g' * t * g'⁻¹) * u = u * (g' * t * g'⁻¹) ∧
      g' * t * g'⁻¹ = t * (y * u * y⁻¹) ∧ y * u * y⁻¹ ≠ u := by
  have ht2 : t * t = 1 := by rw [← pow_two, ← hS.orderOf_t, pow_orderOf_eq_one]
  have hu2 : u * u = 1 := hD.mul_self u hu
  let u₂ : G := y * u * y⁻¹
  have hu₂V : u₂ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp hD.y_normalizes u).mp hu
  have hu₂A : u₂ ∈ A := hD.le_A hu₂V
  have hu₂1 : u₂ ≠ 1 := by
    intro h
    apply hu1
    have h2 : y⁻¹ * u₂ * y = u := by simp only [u₂]; group
    rw [h] at h2
    simpa using h2.symm
  have hu₂u : u₂ ≠ u := hD.y_moves u hu hu1
  have hyt : y * t * y⁻¹ = t := by
    have h1 : y * t = t * y := Subgroup.mem_centralizer_iff.mp hS.t_mem y hD.y_mem
    rw [h1]; group
  let g' : G := y * g
  have hr' : g' * t * g'⁻¹ = t * u₂ := by
    simp only [g', u₂]
    calc y * g * t * (y * g)⁻¹ = y * (g * t * g⁻¹) * y⁻¹ := by group
      _ = y * (t * u) * y⁻¹ := by rw [hr]
      _ = (y * t * y⁻¹) * (y * u * y⁻¹) := by group
      _ = t * (y * u * y⁻¹) := by rw [hyt]
  have hne' : g' * t * g'⁻¹ ≠ t := by
    intro h
    apply hu₂1
    have h2 : t * u₂ = t := by rw [← hr']; exact h
    have h3 : t * u₂ = t * 1 := by rwa [mul_one]
    exact mul_left_cancel h3
  have hu₂t : u₂ * t = t * u₂ :=
    Subgroup.mem_centralizer_iff.mp hS.t_mem u₂ hu₂A
  have hct' : (g' * t * g'⁻¹) * t = t * (g' * t * g'⁻¹) := by
    rw [hr']
    calc (t * u₂) * t = t * (u₂ * t) := by group
      _ = t * (t * u₂) := by rw [hu₂t]
  have htu : t * u = u * t :=
    (Subgroup.mem_centralizer_iff.mp hS.t_mem u (hD.le_A hu)).symm
  have hu₂u' : u₂ * u = u * u₂ := mul_comm_of_mem_V_of_l34SuzOdd hD hu₂V hu
  have hcu' : (g' * t * g'⁻¹) * u = u * (g' * t * g'⁻¹) := by
    rw [hr']
    calc (t * u₂) * u = t * (u₂ * u) := by group
      _ = t * (u * u₂) := by rw [hu₂u']
      _ = (t * u) * u₂ := by group
      _ = (u * t) * u₂ := by rw [htu]
      _ = u * (t * u₂) := by group
  exact ⟨g', hne', hct', hcu', hr', hu₂u⟩

theorem not_centralizer_le_normalizer_of_l34SuzOdd
    (hS : L34SuzOddSetting A t) (hD : L34SuzOddData A V K y) {u : G} (hu : u ∈ V)
    (hu1 : u ≠ 1) :
    ¬ centralizer ({u} : Set G) ≤ normalizer (A : Set G) := by
  intro hN
  obtain ⟨g, hne, hct, hcu⟩ := exists_conj_commute_of_l34SuzOdd hS hD hu hu1
  have hr : g * t * g⁻¹ = t * u :=
    eq_t_mul_u_of_conj_commute_of_l34SuzOdd hS hD hu hu1 hN g hne hct hcu
  obtain ⟨g', hne', hct', hcu', hr', hneq⟩ :=
    exists_conj_commute_of_moved_of_l34SuzOdd hS hD hu hu1 hr
  have hr2 : g' * t * g'⁻¹ = t * u :=
    eq_t_mul_u_of_conj_commute_of_l34SuzOdd hS hD hu hu1 hN g' hne' hct' hcu'
  have heq : t * (y * u * y⁻¹) = t * u := by rw [← hr', hr2]
  exact hneq (mul_left_cancel heq)

theorem not_centralizer_mul_le_normalizer_of_l34SuzOdd
    (hS : L34SuzOddSetting A t) (hD : L34SuzOddData A V K y) {u : G} (hu : u ∈ V)
    (hu1 : u ≠ 1) (hconj : ∀ g : G, g * t * g⁻¹ ≠ t * u) :
    ¬ centralizer ({t * u} : Set G) ≤ normalizer (A : Set G) := by
  intro hN
  have ht2 : t * t = 1 := by rw [← pow_two, ← hS.orderOf_t, pow_orderOf_eq_one]
  have hu2 : u * u = 1 := hD.mul_self u hu
  have htu : t * u = u * t :=
    (Subgroup.mem_centralizer_iff.mp hS.t_mem u (hD.le_A hu)).symm
  obtain ⟨g, hne, hct, hcu⟩ := exists_conj_commute_of_l34SuzOdd hS hD hu hu1
  have hcw : (g * t * g⁻¹) * (t * u) = (t * u) * (g * t * g⁻¹) := by
    calc (g * t * g⁻¹) * (t * u) = ((g * t * g⁻¹) * t) * u := by group
      _ = (t * (g * t * g⁻¹)) * u := by rw [hct]
      _ = t * ((g * t * g⁻¹) * u) := by group
      _ = t * (u * (g * t * g⁻¹)) := by rw [hcu]
      _ = (t * u) * (g * t * g⁻¹) := by group
  let w : G := t * u
  have hw2 : w * w = 1 := by
    simp only [w]
    calc (t * u) * (t * u) = t * (u * t) * u := by group
      _ = t * (t * u) * u := by rw [htu]
      _ = (t * t) * (u * u) := by group
      _ = 1 := by rw [ht2, hu2, one_mul]
  have hwt : t * w = w * t := by
    have h1 : t * w = u := by simp only [w]; rw [← mul_assoc, ht2, one_mul]
    have h2 : w * t = u := by
      simp only [w]
      rw [mul_assoc, ← htu, ← mul_assoc, ht2, one_mul]
    rw [h1, h2]
  have hcw' : (g * t * g⁻¹) * w = w * (g * t * g⁻¹) := hcw
  have hw1 : w ≠ 1 := by
    intro h
    have hueq : u = t := by
      have h1 : t * u = 1 := h
      calc u = 1 * u := (one_mul u).symm
        _ = (t * t) * u := by rw [ht2]
        _ = t * (t * u) := by group
        _ = t * 1 := by rw [h1]
        _ = t := mul_one t
    exact not_mem_centralizer_of_l34SuzOdd hS hD hu hu1 (by rw [hueq]; exact hS.t_mem)
  let b : G := g⁻¹ * w * g
  let s : G := g⁻¹ * t * g
  obtain ⟨hb2, hs2, hbt, hst, hsb, hs1⟩ :=
    commute_conj_data_of_l34SuzOdd hS hw2 hwt g b s rfl rfl hct hcw'
  have hb1 : b ≠ 1 := by
    intro h
    apply hw1
    have h1 : g * b * g⁻¹ = w := by simp only [b]; group
    rw [h] at h1
    simpa using h1.symm
  have hbA : b ∉ centralizer (A : Set G) := by
    intro hbC
    have hbH : b ∈ centralizer ({t} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hbt
    have hbeq : b = t := eq_t_of_involution_mem_centralizer_inf hS hbH hbC hb2 hb1
    have h1 : g * t * g⁻¹ = w := by
      calc g * t * g⁻¹ = g * b * g⁻¹ := by rw [hbeq]
        _ = w := by simp only [b]; group
    exact hconj g (by simpa only [w] using h1)
  have hbord : orderOf b = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hb2) hb1
  have hsord : orderOf s = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hs2) hs1
  have hsJ : ∀ x ∈ centralizer ({t} : Set G) ⊓ centralizer ({b} : Set G),
      s * x * s⁻¹ * x⁻¹ ∈
        oddIn (centralizer ({t} : Set G) ⊓ centralizer ({b} : Set G)) :=
    commutator_mem_oddIn_of_l34SuzOdd hS hw2 hwt hN g b s rfl rfl hct hcw'
  rcases eq_of_commutator_mem_oddIn_of_l34SuzOdd hS hbord hbt hbA hsord hst hsb hsJ
    with hst' | hsb' | hstb
  · exact hne (by
      calc g * t * g⁻¹ = g * s * g⁻¹ := by rw [← hst']
        _ = t := by simp only [s]; group)
  · have htu1 : u = 1 := by
      have h1 : t * u = t * 1 := by
        rw [mul_one]
        calc t * u = w := rfl
          _ = g * b * g⁻¹ := by simp only [b]; group
          _ = g * s * g⁻¹ := by rw [hsb']
          _ = t := by simp only [s]; group
      exact mul_left_cancel h1
    exact hu1 htu1
  · have hr_u : g * t * g⁻¹ = u := by
      have h1 : t = (g * t * g⁻¹) * w := by
        calc t = g * s * g⁻¹ := by simp only [s]; group
          _ = g * (t * b) * g⁻¹ := by rw [hstb]
          _ = (g * t * g⁻¹) * w := by simp only [b]; group
      calc g * t * g⁻¹ = (g * t * g⁻¹) * (w * w) := by rw [hw2, mul_one]
        _ = ((g * t * g⁻¹) * w) * w := by group
        _ = t * w := by rw [← h1]
        _ = t * (t * u) := rfl
        _ = (t * t) * u := by group
        _ = u := by rw [ht2, one_mul]
    exact conj_ne_of_l34SuzOdd hS hD hu hu1 g hr_u

end CFSG.ComponentClassification.GrSLit.L34Sec5S
