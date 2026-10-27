module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4LayerB
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4Sec8

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup

namespace SecInner

theorem ordL2_sq_eq {q k : ℕ} (hk : q = 2 * k + 1) :
    Cat8.ordL2 (q ^ 2) = q ^ 2 * (4 * k * (k + 1) * (2 * k ^ 2 + 2 * k + 1)) := by
  have h1 : (q ^ 2) ^ 2 = 8 * k * (k + 1) * (2 * k ^ 2 + 2 * k + 1) + 1 := by
    rw [hk]
    ring
  show q ^ 2 * ((q ^ 2) ^ 2 - 1) / 2 = _
  rw [h1, Nat.add_sub_cancel]
  rw [show q ^ 2 * (8 * k * (k + 1) * (2 * k ^ 2 + 2 * k + 1)) =
    2 * (q ^ 2 * (4 * k * (k + 1) * (2 * k ^ 2 + 2 * k + 1))) by ring]
  exact Nat.mul_div_cancel_left _ two_pos

theorem sq_dvd_ordL2_sq {q : ℕ} (hq : Odd q) : q ^ 2 ∣ Cat8.ordL2 (q ^ 2) := by
  obtain ⟨k, hk⟩ := hq
  rw [ordL2_sq_eq hk]
  exact dvd_mul_right _ _

theorem not_ordL2_sq_dvd {q : ℕ} (hq : Odd q) (hq3 : 3 ≤ q) :
    ¬ Cat8.ordL2 (q ^ 2) ∣ (q * (q ^ 2 - 1)) ^ 2 := by
  obtain ⟨k, hk⟩ := hq
  have hk1 : 1 ≤ k := by omega
  have hsub : q ^ 2 - 1 = 4 * k * (k + 1) := by
    have : q ^ 2 = 4 * k * (k + 1) + 1 := by rw [hk]; ring
    omega
  rw [ordL2_sq_eq hk, hsub]
  intro h
  set s := 2 * k ^ 2 + 2 * k + 1 with hs
  have hq0 : 0 < q ^ 2 * (4 * k * (k + 1)) := by positivity
  have h1 : q ^ 2 * (4 * k * (k + 1)) * s ∣ q ^ 2 * (4 * k * (k + 1)) * (4 * k * (k + 1)) := by
    have e1 : q ^ 2 * (4 * k * (k + 1) * s) = q ^ 2 * (4 * k * (k + 1)) * s := by ring
    have e2 : (q * (4 * k * (k + 1))) ^ 2 =
        q ^ 2 * (4 * k * (k + 1)) * (4 * k * (k + 1)) := by ring
    rw [← e1, ← e2]
    exact h
  have h2 : s ∣ 4 * k * (k + 1) := Nat.dvd_of_mul_dvd_mul_left hq0 h1
  have h3 : 2 * s = 4 * k * (k + 1) + 2 := by rw [hs]; ring
  have h4 : s ∣ 2 := by
    have h5 : s ∣ 2 * s - 4 * k * (k + 1) := Nat.dvd_sub (dvd_mul_left s 2) h2
    rwa [h3, Nat.add_sub_cancel_left] at h5
  have h6 : s ≤ 2 := Nat.le_of_dvd two_pos h4
  have h7 : 5 ≤ s := by
    rw [hs]
    nlinarith
  omega

open CatFactsSp4 Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag

variable {K : Type} [Field K]

theorem card_range_dvd {G G' : Type*} [Group G] [Group G'] [Finite G] (φ : G →* G') :
    Nat.card φ.range ∣ Nat.card G := by
  rw [MonoidHom.range_eq_map]
  exact (Subgroup.card_map_dvd ⊤ φ).trans (by rw [Subgroup.card_top])

theorem card_centralizer_T1_dvd [Finite K] (h2 : (2 : K) ≠ 0) :
    Nat.card (centralizer {T1 K}) ∣ Nat.card (SpecialLinearGroup (Fin 2) K) ^ 2 := by
  have h : centralizer {T1 K} = (blkSL K).range := by
    ext x
    exact mem_centralizer_T1_iff h2
  rw [h, sq, ← Nat.card_prod]
  exact card_range_dvd _

theorem card_centralizer_T2_dvd [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (h2 : (2 : K) ≠ 0) : ∃ m, ¬ p ∣ m ∧
      Nat.card (centralizer {T2 K}) ∣ Nat.card (SpecialLinearGroup (Fin 2) K) * m := by
  set φ := (detE (K := K)).toHomUnits with hφ
  have hker : φ.ker = (diagSL K).range.subgroupOf (centralizer {T2 K}) := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    constructor
    · intro h
      exact mem_range_diagSL_of_detE h2 x (congrArg Units.val h)
    · rintro ⟨k, hk⟩
      apply Units.ext
      change detE x = 1
      have : x = ⟨diagSL K k, diagSL_mem_centralizer k⟩ := Subtype.ext hk.symm
      rw [this, detE_diagSL]
  have hle : (diagSL K).range ≤ centralizer {T2 K} := by
    rintro _ ⟨k, rfl⟩
    exact diagSL_mem_centralizer k
  refine ⟨Nat.card φ.range, ?_, ?_⟩
  · intro hpd
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := φ.range) p hpd
    have hu1 : (u : (Gauss K)ˣ) ^ p = 1 := by
      rw [← Subgroup.coe_pow, ← hu, pow_orderOf_eq_one, Subgroup.coe_one]
    have h1 : (-1 : K) ≠ 0 := neg_ne_zero.mpr one_ne_zero
    have := eq_one_of_pow_char_qAlg h2 h1 hu1
    have hu' : u = 1 := Subtype.ext this
    rw [hu', orderOf_one] at hu
    exact (Fact.out : p.Prime).one_lt.ne hu
  · rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, mul_comm]
    refine Nat.mul_dvd_mul_right ?_ _
    rw [hker, Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv]
    exact card_range_dvd _

theorem card_centralizer_proj_dvd [Finite K] (h2 : (2 : K) ≠ 0) (T : StatedSp 2 K) :
    Nat.card (centralizer {proj 2 K T}) ∣ Nat.card (centralizer {T}) := by
  have hθα : ∀ g, MulAut.conj (proj 2 K T) (proj 2 K g) = proj 2 K (MulAut.conj T g) :=
    fun g => by simp only [MulAut.conj_apply, map_mul, map_inv]
  have h := card_fixOf_dvd h2 (MulAut.conj T) hθα
  rwa [fixOf_conj, fixOf_conj] at h

theorem card_centralizer_conj {G : Type*} [Group G] (u g : G) :
    Nat.card (centralizer {g⁻¹ * u * g}) = Nat.card (centralizer {u}) := by
  have h := map_centralizer_singleton (MulAut.conj g⁻¹) u
  rw [MulAut.conj_apply, inv_inv] at h
  rw [← h, card_map_of_injective (MulAut.conj g⁻¹).injective]

theorem not_dvd_card_centralizer_P [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) {u : StatedProj (StatedSp 2 K)} (hu : orderOf u = 2) :
    ¬ Cat8.ordL2 ((p ^ f) ^ 2) ∣ Nat.card (centralizer {u}) := by
  have : Fact p.Prime := ⟨hp⟩
  have hodd : Odd (Nat.card K) := odd_card_of_card_eq hp hp2 hK
  have hqodd : Odd (p ^ f) := hK ▸ hodd
  have h2 := two_ne_zero_of_odd_card hodd
  have : CharP K p := finite_field_prime_power_characteristic hp hf hK
  have hq3 : 3 ≤ p ^ f := by
    have h3 : 3 ≤ p := by have := hp.two_le; omega
    exact h3.trans (Nat.le_self_pow (by omega) p)
  have hSL : Nat.card (SpecialLinearGroup (Fin 2) K) = p ^ f * ((p ^ f) ^ 2 - 1) := by
    rw [card_SL2, hK]
  obtain ⟨g, hg⟩ := exists_conj_of_orderOf_eq_two hodd hu
  rw [← card_centralizer_conj u g]
  intro hdvd
  rcases hg with hg | hg <;> rw [hg] at hdvd
  ·
    have h1 := (card_centralizer_proj_dvd h2 (T1 K)).trans (card_centralizer_T1_dvd h2)
    rw [hSL] at h1
    exact not_ordL2_sq_dvd hqodd hq3 (hdvd.trans h1)
  ·
    obtain ⟨m, hm, hdm⟩ := card_centralizer_T2_dvd (p := p) h2
    have h1 := (card_centralizer_proj_dvd h2 (T2 K)).trans hdm
    rw [hSL] at h1
    exact not_sq_dvd_typeI hp hf rfl hm (((sq_dvd_ordL2_sq hqodd).trans hdvd).trans h1)

theorem not_five_dvd_card_centralizer_perm {σ : Equiv.Perm (Fin 8)} (hσ : orderOf σ = 2)
    (hsign : Equiv.Perm.sign σ = 1) :
    ¬ 5 ∣ Nat.card (centralizer ({σ} : Set (Equiv.Perm (Fin 8)))) := by
  have hp : (orderOf σ).Prime := by rw [hσ]; exact Nat.prime_two
  obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order hp
  rw [hσ] at hn
  have hsum : 2 * (n + 1) ≤ 8 := by
    have h := Equiv.Perm.sum_cycleType_le σ
    rw [hn, Multiset.sum_replicate, smul_eq_mul, Fintype.card_fin] at h
    omega
  have heven : Even (n + 1) := by
    rcases Nat.even_or_odd (n + 1) with h | h
    · exact h
    · exfalso
      have hsg := Equiv.Perm.sign_of_cycleType σ
      rw [hsign, hn, Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul] at hsg
      have hodd : Odd ((n + 1) * 2 + (n + 1)) :=
        (Nat.even_mul.mpr (Or.inr even_two)).add_odd h
      rw [hodd.neg_one_pow] at hsg
      exact absurd hsg (by decide)
  have hn' : n = 1 ∨ n = 3 := by
    obtain ⟨k, hk⟩ := heven
    omega
  rw [Equiv.Perm.nat_card_centralizer, hn, Fintype.card_fin]
  rcases hn' with rfl | rfl <;> decide

end SecInner

open SecInner in
theorem cfSec8InnerCentralizer : CFSec8InnerCentralizer := by
  intro K₀ _ _ Y _ _ p f hp hp2 hf hK hY t ht
  rw [CatFactsSp4.cfSec8JOrder Y p f hp hp2 hf hY]
  rcases hK with hK | ⟨rfl, rfl, ⟨e⟩⟩
  · obtain ⟨-, -, F, _, _, hF, ⟨e⟩⟩ := CFSG.GH74.Generic.lieModel_psp_data hK
    have hc := CatFactsSp4.map_centralizer_singleton e t
    have hcard : Nat.card (centralizer ({t} : Set K₀)) =
        Nat.card (centralizer ({e t} : Set _)) := by
      rw [← hc, card_map_of_injective e.injective]
    rw [hcard]
    exact not_dvd_card_centralizer_P hp hp2 hf hF (by rw [MulEquiv.orderOf_eq, ht])
  ·
    intro hdvd
    have h5 : 5 ∣ Nat.card (centralizer ({t} : Set K₀)) :=
      (show 5 ∣ Cat8.ordL2 ((3 ^ 1) ^ 2) by decide).trans hdvd
    have hc := CatFactsSp4.map_centralizer_singleton e t
    have hcard : Nat.card (centralizer ({e t} : Set (alternatingGroup (Fin 8)))) =
        Nat.card (centralizer ({t} : Set K₀)) := by
      rw [← hc, card_map_of_injective e.injective]
    rw [← hcard] at h5
    set σ : Equiv.Perm (Fin 8) := (e t : Equiv.Perm (Fin 8)) with hσ
    have hσo : orderOf σ = 2 := by
      rw [hσ, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ht]
    have hsign : Equiv.Perm.sign σ = 1 := (e t).2
    apply not_five_dvd_card_centralizer_perm hσo hsign
    refine h5.trans ?_
    have hle : (centralizer ({e t} : Set (alternatingGroup (Fin 8)))).map
        (alternatingGroup (Fin 8)).subtype ≤ centralizer ({σ} : Set (Equiv.Perm (Fin 8))) := by
      rintro _ ⟨x, hx, rfl⟩
      have hx' : x * e t = e t * x := mem_centralizer_singleton_iff.mp hx
      rw [mem_centralizer_singleton_iff]
      exact congrArg Subtype.val hx'
    rw [← card_map_of_injective (alternatingGroup (Fin 8)).subtype_injective]
    exact Subgroup.card_dvd_of_le hle

end CFSG.ComponentClassification.GSThmB
