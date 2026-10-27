module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L12EA
public import CFSG.ClassicalInvolution.Balance.Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}

theorem sec12E_R_odd {r : G} (hr : r ∈ secR t) : Odd (orderOf r) :=
  Odd.of_dvd_nat
    (CFSG.ClassicalInvolution.Balance.odd_card_oddCoreIn (centralizer ({t} : Set G)))
    (Subgroup.orderOf_dvd_natCard (secR t) hr)

theorem sec12E_C_le_Ct (F : Sec12Frame t L S) :
    centralizer (secA t S L : Set G) ≤ centralizer ({t} : Set G) := by
  refine Subgroup.centralizer_le ?_
  rw [Set.singleton_subset_iff]
  show t ∈ secB S L ⊔ zpowers t
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)

theorem sec12E_odd_C (F : Sec12Frame t L S) {c : G} (hc : c ∈ centralizer (secA t S L : Set G))
    (hodd : Odd (orderOf c)) : c ∈ centralizer (L : Set G) := by
  have hct : c ∈ centralizer ({t} : Set G) := sec12E_C_le_Ct F hc
  have hcN : c ∈ normalizer (L : Set G) := F.hCt hct
  have hcommB : ∀ b ∈ secB S L, c * b = b * c := by
    intro b hb
    exact (Subgroup.mem_centralizer_iff.mp hc b (Subgroup.mem_sup_left hb)).symm
  have hcSup : c ∈ secB S L ⊔ centralizer (L : Set G) := F.centB c hcN hcommB
  have hcomm' : ∀ x ∈ secB S L, ∀ y ∈ centralizer (L : Set G), x * y = y * x := by
    intro x hx y hy
    exact Subgroup.mem_centralizer_iff.mp hy x (F.bdata.1 hx)
  obtain ⟨b, hb, c', hc', hxc⟩ := exists_mul_of_mem_sup_of_commute hcomm' hcSup
  have hbc : Commute b c' := (commute_iff_eq b c').mpr (hcomm' b hb c' hc')
  have hpair : b ^ orderOf c * c' ^ orderOf c = 1 := by
    rw [← hbc.mul_pow (orderOf c), ← hxc, pow_orderOf_eq_one]
  have hbn1 : b ^ orderOf c = 1 := by
    have hbcL : b ^ orderOf c ∈ centralizer (L : Set G) := by
      have hinv : b ^ orderOf c = (c' ^ orderOf c)⁻¹ :=
        eq_inv_of_mul_eq_one_left hpair
      rw [hinv]
      exact (centralizer (L : Set G)).inv_mem
        ((centralizer (L : Set G)).pow_mem hc' (orderOf c))
    have hbL : b ^ orderOf c ∈ L := F.bdata.1 ((secB S L).pow_mem hb (orderOf c))
    have hbot : b ^ orderOf c ∈ (⊥ : Subgroup G) := by
      have hmem : b ^ orderOf c ∈ L ⊓ centralizer (L : Set G) := ⟨hbL, hbcL⟩
      rwa [F.hLC] at hmem
    simpa using hbot
  have hb1 : b = 1 := by
    obtain ⟨k, hk⟩ := hodd
    have hpow : b ^ orderOf c = b := by
      rw [hk, pow_succ', pow_mul, pow_two, sec12E_B_sq F hb, one_pow, mul_one]
    rw [← hpow, hbn1]
  have hceq : c = c' := by rw [hxc, hb1, one_mul]
  rw [hceq]
  exact hc'

theorem sec12E_R_le_C (F : Sec12Frame t L S) : secR t ≤ centralizer (secA t S L : Set G) := by
  intro r hr
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have hrt : r ∈ centralizer ({t} : Set G) :=
    CFSG.ClassicalInvolution.Balance.oddCoreIn_le _ hr
  have hrL : r ∈ centralizer (L : Set G) := F.rcent hr
  rcases (sec12E_mem_A F).mp ha with hb | ⟨b, hb, rfl⟩
  · exact Subgroup.mem_centralizer_iff.mp hrL a (F.bdata.1 hb)
  · have hbr : b * r = r * b := Subgroup.mem_centralizer_iff.mp hrL b (F.bdata.1 hb)
    have htr : t * r = r * t :=
      Subgroup.mem_centralizer_iff.mp hrt t (Set.mem_singleton t)
    calc (t * b) * r = t * (b * r) := by rw [mul_assoc]
      _ = t * (r * b) := by rw [hbr]
      _ = (t * r) * b := by rw [mul_assoc]
      _ = (r * t) * b := by rw [htr]
      _ = r * (t * b) := by rw [mul_assoc]

theorem sec12E_C_decomp (F : Sec12Frame t L S) {c : G}
    (hc : c ∈ centralizer (secA t S L : Set G)) :
    ∃ a ∈ secA t S L, ∃ r ∈ secR t, c = a * r := by
  have hct : c ∈ centralizer ({t} : Set G) := sec12E_C_le_Ct F hc
  have hcN : c ∈ normalizer (L : Set G) := F.hCt hct
  have hcommB : ∀ b ∈ secB S L, c * b = b * c := by
    intro b hb
    exact (Subgroup.mem_centralizer_iff.mp hc b (Subgroup.mem_sup_left hb)).symm
  have hcSup : c ∈ secB S L ⊔ centralizer (L : Set G) := F.centB c hcN hcommB
  have hcomm' : ∀ x ∈ secB S L, ∀ y ∈ centralizer (L : Set G), x * y = y * x := by
    intro x hx y hy
    exact Subgroup.mem_centralizer_iff.mp hy x (F.bdata.1 hx)
  obtain ⟨b, hb, c', hc', hxc⟩ := exists_mul_of_mem_sup_of_commute hcomm' hcSup
  have hbL : b ∈ L := F.bdata.1 hb
  have hb_t : b * t = t * b := Subgroup.mem_centralizer_iff.mp F.htC b hbL
  have hbct : b ∈ centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hb_t
  have hc'_eq : c' = b⁻¹ * c := by
    rw [hxc]
    group
  have hc'ct : c' ∈ centralizer ({t} : Set G) := by
    rw [hc'_eq]
    exact (centralizer ({t} : Set G)).mul_mem
      ((centralizer ({t} : Set G)).inv_mem hbct) hct
  obtain ⟨e, m, hm, hm0⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos c').ne'
  have hcop : Nat.Coprime m (2 ^ e) := (hm.coprime_two_right).pow_right e
  obtain ⟨x, y, hxy⟩ := hcop.isCoprime
  let u : G := c' ^ (x * (m : ℤ))
  let v : G := c' ^ (y * ((2 ^ e : ℕ) : ℤ))
  have huL : u ∈ centralizer (L : Set G) := (centralizer (L : Set G)).zpow_mem hc' _
  have hut : u ∈ centralizer ({t} : Set G) := (centralizer ({t} : Set G)).zpow_mem hc'ct _
  have hvL : v ∈ centralizer (L : Set G) := (centralizer (L : Set G)).zpow_mem hc' _
  have hvt : v ∈ centralizer ({t} : Set G) := (centralizer ({t} : Set G)).zpow_mem hc'ct _
  have hu2 : u ^ (2 ^ e) = 1 := by
    rw [← zpow_natCast]
    change (c' ^ (x * (m : ℤ))) ^ ((2 ^ e : ℕ) : ℤ) = 1
    rw [← zpow_mul]
    have hE : (x * (m : ℤ)) * ((2 ^ e : ℕ) : ℤ) = x * (orderOf c' : ℤ) := by
      rw [hm0, Nat.cast_mul]
      ring
    rw [hE, zpow_mul', zpow_natCast, pow_orderOf_eq_one, one_zpow]
  have hv : v ^ m = 1 := by
    rw [← zpow_natCast]
    change (c' ^ (y * ((2 ^ e : ℕ) : ℤ))) ^ ((m : ℕ) : ℤ) = 1
    rw [← zpow_mul]
    have hE : (y * ((2 ^ e : ℕ) : ℤ)) * (m : ℤ) = y * (orderOf c' : ℤ) := by
      rw [hm0, Nat.cast_mul]
      ring
    rw [hE, zpow_mul', zpow_natCast, pow_orderOf_eq_one, one_zpow]
  have huv : u * v = c' := by
    change c' ^ (x * (m : ℤ)) * c' ^ (y * ((2 ^ e : ℕ) : ℤ)) = c'
    rw [← zpow_add, hxy, zpow_one]
  have huA : u ∈ secA t S L := Subgroup.mem_sup_right (F.two u huL hut ⟨e, hu2⟩)
  have hoddv : Odd (orderOf v) := Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one hv)
  have hrv : v ∈ secR t := F.rmem v hvL hvt hoddv
  refine ⟨b * u, ?_, v, hrv, ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hb) huA
  · rw [hxc, ← huv]
    group

theorem sec12E_two_C (F : Sec12Frame t L S) {c : G} (hc : c ∈ centralizer (secA t S L : Set G))
    (h2 : ∃ k : ℕ, c ^ (2 ^ k) = 1) : c ∈ secA t S L := by
  obtain ⟨a, ha, r, hr, hceq⟩ := sec12E_C_decomp F hc
  have hra : a * r = r * a :=
    Subgroup.mem_centralizer_iff.mp (sec12E_R_le_C F hr) a ha
  have harc : Commute a r := (commute_iff_eq a r).mpr hra
  obtain ⟨k, hk⟩ := h2
  rcases k with _ | j
  · rw [pow_zero, pow_one] at hk
    rw [hk]
    exact (secA t S L).one_mem
  · have ha2 : a * a = 1 := sec12E_A_sq F ha
    have han : a ^ (2 ^ (j + 1)) = 1 := by
      rw [show (2 : ℕ) ^ (j + 1) = 2 * 2 ^ j by rw [pow_succ']]
      rw [pow_mul, pow_two, ha2, one_pow]
    have hcr : c ^ (2 ^ (j + 1)) = a ^ (2 ^ (j + 1)) * r ^ (2 ^ (j + 1)) := by
      rw [hceq]
      exact harc.mul_pow _
    have hrn : r ^ (2 ^ (j + 1)) = 1 := by
      have h := hk
      rw [hcr, han, one_mul] at h
      exact h
    have hdvd : orderOf r ∣ 2 ^ (j + 1) := orderOf_dvd_of_pow_eq_one hrn
    have hcop : Nat.Coprime (orderOf r) (2 ^ (j + 1)) :=
      (sec12E_R_odd hr).coprime_two_right.pow_right (j + 1)
    have hone : orderOf r = 1 := Nat.eq_one_of_dvd_coprimes hcop dvd_rfl hdvd
    have hr1 : r = 1 := orderOf_eq_one_iff.mp hone
    rw [hceq, hr1, mul_one]
    exact ha

theorem sec12E_R_normal (F : Sec12Frame t L S) {m r : G} (hm : m ∈ secM t S L)
    (hr : r ∈ secR t) : m * r * m⁻¹ ∈ secR t := by
  have hrC : r ∈ centralizer (secA t S L : Set G) := sec12E_R_le_C F hr
  have hconjC : m * r * m⁻¹ ∈ centralizer (secA t S L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have ha' : m⁻¹ * a * m ∈ secA t S L :=
      (Subgroup.mem_set_normalizer_iff''.mp hm a).mp ha
    have hcomm : (m⁻¹ * a * m) * r = r * (m⁻¹ * a * m) :=
      Subgroup.mem_centralizer_iff.mp hrC (m⁻¹ * a * m) ha'
    calc a * (m * r * m⁻¹) = m * ((m⁻¹ * a * m) * r) * m⁻¹ := by group
      _ = m * (r * (m⁻¹ * a * m)) * m⁻¹ := by rw [hcomm]
      _ = (m * r * m⁻¹) * a := by group
  have hord : orderOf (m * r * m⁻¹) = orderOf r := by
    have h := (MulAut.conj m).orderOf_eq r
    rwa [MulAut.conj_apply] at h
  have hodd : Odd (orderOf (m * r * m⁻¹)) := by
    rw [hord]
    exact sec12E_R_odd hr
  exact F.rmem (m * r * m⁻¹) (sec12E_odd_C F hconjC hodd) (sec12E_C_le_Ct F hconjC) hodd

theorem sec12E_pow_four (F : Sec12Frame t L S) {p : G} (hp : p ∈ secCMB t S L) :
    p ^ 4 ∈ secR t := by
  have hpp : p * p ∈ secCMB t S L := (secCMB t S L).mul_mem hp hp
  have hf : sec12f t (p * p) = 1 := by
    rw [sec12E_f_mul F hp hp]
    exact sec12E_B_sq F (sec12E_f_mem F hp)
  have hppC : p * p ∈ centralizer (secA t S L : Set G) := (sec12E_f_eq_one F hpp).mp hf
  obtain ⟨a, ha, r, hr, har⟩ := sec12E_C_decomp F hppC
  have hra : a * r = r * a :=
    Subgroup.mem_centralizer_iff.mp (sec12E_R_le_C F hr) a ha
  have haa : a * a = 1 := sec12E_A_sq F ha
  have hmul : (a * r) * (a * r) = a * a * (r * r) := by
    have hcomm : Commute a r := (commute_iff_eq a r).mpr hra
    have h := hcomm.mul_pow 2
    simpa [pow_two] using h
  have hp4 : p ^ 4 = r * r := by
    calc p ^ 4 = (p * p) * (p * p) := by
          rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
          simp only [pow_two]
      _ = (a * r) * (a * r) := by rw [har]
      _ = a * a * (r * r) := hmul
      _ = r * r := by rw [haa, one_mul]
  rw [hp4]
  exact (secR t).mul_mem hr hr

end CFSG.OddStandard.SmallF3.Omega
