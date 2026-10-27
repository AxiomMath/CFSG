module

public import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5ECom
public import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5Tr
public import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5Pair
public import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5Typ
public import CFSG.RankThree.Chevalley.SteinbergCFOddCommutingSL2
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Mult
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LieType.Steinberg.CentralExt.G2ThreeMultiplier

public section

namespace CFSG.OddStandard.GH71.S55

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 C5

theorem prime_dvd_ordG2_cases {p q : ℕ} (hp : p.Prime) (hq : 1 ≤ q) (hpq : ¬ p ∣ q)
    (h : p ∣ CFSG.Open.ordG2 q) : p ∣ q ^ 2 - 1 ∨ p ∣ q ^ 2 + q + 1 ∨ p ∣ q ^ 2 - q + 1 := by
  have h6 : q ^ 6 - 1 = (q ^ 2 - 1) * (q ^ 2 + q + 1) * (q ^ 2 - q + 1) := by
    have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
    have h2 : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
    have h3 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ hq
    zify [h1, h2, h3]
    ring
  rw [CFSG.Open.ordG2, h6] at h
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact absurd (hp.dvd_of_dvd_pow h) hpq
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  · exact Or.inl h

theorem not_dvd_g2_index {p q k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : ¬ p ∣ q)
    (h1 : p ∣ q ^ 2 - 1) (hq : 1 ≤ q) (hk1 : 1 ≤ k) (hk2 : k ≤ 2) :
    ¬ p ∣ q ^ 4 * (q ^ 4 + q ^ 2 + 1) * k := by
  intro h
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact hpq (hp.dvd_of_dvd_pow h)
    · have he : q ^ 4 + q ^ 2 + 1 = (q ^ 2 - 1) * (q ^ 2 + 2) + 3 := by
        have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
        zify [this]
        ring
      rw [he] at h
      have h3 : p ∣ 3 := (Nat.dvd_add_right (dvd_mul_of_dvd_left h1 _)).1 h
      have := Nat.le_of_dvd (by norm_num) h3
      omega
  · have := Nat.le_of_dvd (by omega) h
    omega


variable {r : ℕ} {Y : Type} [Group Y]

theorem g2_model {f : ℕ} (hm : LieModel Y .G2 0 r f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = r ^ f ∧
      Nonempty (Y ≃* adjointGroup .G2 K) := by
  rcases hm with ⟨ht, -⟩ | ⟨-, -, -, hU⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hU
    refine ⟨K, inferInstance, inferInstance, hK, ⟨e.trans ?_⟩⟩
    exact (QuotientGroup.quotientMulEquivOfEq
      (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot)).trans QuotientGroup.quotientBot
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

theorem noR_two_of_FG2d (hr : r.Prime) (hr2 : r ≠ 2) (h : FG2d r Y) : NoR 2 Y := by
  obtain ⟨f, hf, hm⟩ := h
  intro J _ _ hJ ⟨e⟩
  have hmJ : LieModel (J ⧸ center J) .G2 0 r f :=
    CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm hm
  by_cases h5 : 5 ≤ r ^ f
  · rw [g2_center_eq_bot hJ hmJ h5, Subgroup.card_bot]
    norm_num
  · have h3 : r ^ f = 3 := by
      have hodd : Odd (r ^ f) := (hr.odd_of_ne_two hr2).pow
      have := three_le_pow hr hr2 hf
      obtain ⟨m, hm⟩ := hodd
      omega
    obtain ⟨K, _, _, hK, ⟨e₁⟩⟩ := g2_model hmJ
    have : Group.IsPerfect J := hJ.1
    set π : J →* adjointGroup .G2 K := e₁.toMonoidHom.comp (QuotientGroup.mk' (center J))
    have hπ : Function.Surjective π := e₁.surjective.comp (QuotientGroup.mk'_surjective _)
    have hker : π.ker = center J := by
      ext x
      rw [MonoidHom.mem_ker]
      change e₁ (QuotientGroup.mk' (center J) x) = 1 ↔ _
      rw [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    obtain ⟨c, hc3, hcle⟩ := CFSG.LieType.Steinberg.CentralExt.FieldThree.g2_three_ker_le_zpowers
      (hK.trans h3) hπ hker.le
    rw [hker] at hcle
    have h1 : Nat.card (center J) ∣ 3 :=
      (card_dvd_of_le hcle).trans (by rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hc3)
    intro h2
    have h0 := (Nat.dvd_prime Nat.prime_three).1 (h2.trans h1)
    omega

variable {K : Type} [Field K] [Finite K]

theorem g2_no_two_p (hK : Odd (Nat.card K)) {ε : ℤ} (hε : ε = -1 ∨ ε = 1) {d : ℕ}
    (hd : (d : ℤ) = (Nat.card K : ℤ) ^ 2 + ε * Nat.card K + 1) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpd : p ∣ d) (w : adjointGroup .G2 K) : orderOf w ≠ 2 * p := by
  obtain ⟨T, -, -, -, -, hx⟩ :=
    CFSG.RankThree.Chevalley.odd_G2_cyclotomic_three_six_tori_and_prime_centralizers K hK ε hε d
      hd hp hp3 hpd
  refine no_two_p_of_odd_centralizer hp (fun x hxp => ?_) w
  obtain ⟨-, -, -, hcard, hodd⟩ := hx x hxp
  rw [hcard]
  exact hodd

theorem g2_comp5_block {p f : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hrp : r ≠ p) (hf : 1 ≤ f) (hK : Nat.card K = r ^ f) (h1 : p ∣ (r ^ f) ^ 2 - 1)
    {y : adjointGroup .G2 K} (hy : orderOf y = p) (hyr : RFree r y) : Comp5Concl r y := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact r.Prime := ⟨hr⟩
  have hK3 : Nat.card K = r ^ f := hK
  have : CharP K r := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hr
    (by omega) hK3
  have hch : ringChar K ≠ 2 := by rw [ringChar.eq K r]; exact hr2
  have hpq : ¬ p ∣ r ^ f := fun h => hrp ((Nat.prime_dvd_prime_iff_eq hp hr).1
    (hp.dvd_of_dvd_pow h)).symm
  have hq3 : r ^ f ≠ 3 := by
    intro h3
    rw [h3] at h1
    have h8 : p ∣ 2 ^ 3 := by norm_num at h1 ⊢; exact h1
    have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h8)
    omega
  obtain ⟨ι₁, ι₂, hι₁, hι₂, hc⟩ :=
    CFSG.RankThree.Chevalley.G2_two_commuting_faithful_SL2 K hch
  obtain ⟨k, hk1, hk2, hidx⟩ := index_mul_of_commute ι₁ ι₂ hι₁ hι₂ hc
  have hk2' : k ≤ 2 := hk2.trans card_center_SL2_le
  set q := r ^ f with hqdef
  have hq1 : 1 ≤ q := Nat.one_le_pow _ _ hr.pos
  have hq2 : 2 ≤ q := by have := three_le_pow hr hr2 hf; omega
  rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hK,
    CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hK] at hidx
  have hind : (ι₁.range ⊔ ι₂.range).index = q ^ 4 * (q ^ 4 + q ^ 2 + 1) * k := by
    have hpos : 0 < q * (q ^ 2 - 1) * (q * (q ^ 2 - 1)) := by
      have : 0 < q ^ 2 - 1 := by have : 1 < q ^ 2 := by nlinarith
                                 omega
      exact Nat.mul_pos (Nat.mul_pos (by omega) this) (Nat.mul_pos (by omega) this)
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [hidx, CFSG.Open.ordG2]
    have h1' : 1 ≤ q ^ 2 := by nlinarith
    have h6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ hq1
    zify [h1', h6]
    ring
  have hM : ¬ p ∣ (ι₁.range ⊔ ι₂.range).index := by
    rw [hind]
    exact not_dvd_g2_index hp hp5 hpq h1 hq1 hk1 hk2'
  obtain ⟨hQ, hC, hrL⟩ := typ_sl hr hr2 hf (Or.inl rfl) hK (Or.inr hq3)
    (MonoidHom.ofInjective hι₁)
  refine comp5Concl_of_block hM (le_normalizer_of_commute ι₁ ι₂ hc) ?_ hQ hC hrL hy hyr
  intro htop
  have h1M : (ι₁.range ⊔ ι₂.range).index = 1 := by
    rw [htop, top_sup_eq, index_top]
  rw [hind] at h1M
  have h4 : q ^ 4 ∣ 1 := Dvd.intro _ (by rw [← mul_assoc]; exact h1M)
  have h5 : 1 < q ^ 4 := Nat.one_lt_pow (by norm_num) (by omega)
  have := Nat.le_of_dvd one_pos h4
  omega

theorem g2_comp5 {p f : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hrp : r ≠ p) (hf : 1 ≤ f) (hK : Nat.card K = r ^ f) (hR : NoR 2 (adjointGroup .G2 K))
    {y : adjointGroup .G2 K} (g : adjointGroup .G2 K) (hy : orderOf y = p) (hyr : RFree r y)
    (hJ : PairSL2 p y g) : Comp5Concl r y := by
  have hpq : ¬ p ∣ r ^ f := fun h => hrp ((Nat.prime_dvd_prime_iff_eq hp hr).1
    (hp.dvd_of_dvd_pow h)).symm
  have hpΓ : p ∣ Nat.card (adjointGroup .G2 K) := hy ▸ orderOf_dvd_natCard y
  rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hK] at hpΓ
  have hodd : Odd (Nat.card K) := hK ▸ (hr.odd_of_ne_two hr2).pow
  have hq1 : 1 ≤ r ^ f := Nat.one_le_pow _ _ hr.pos
  rcases prime_dvd_ordG2_cases hp hq1 hpq hpΓ with h1 | h2 | h3
  · exact g2_comp5_block hr hr2 hp hp5 hrp hf hK h1 hy hyr
  · refine absurd hJ (not_pairSL2_of_no_two_p hp (by omega)
      (g2_no_two_p hodd (Or.inr rfl) (d := (r ^ f) ^ 2 + r ^ f + 1) ?_ hp (by omega) h2) hR y g)
    rw [hK]
    push_cast
    ring
  · refine absurd hJ (not_pairSL2_of_no_two_p hp (by omega)
      (g2_no_two_p hodd (Or.inl rfl) (d := (r ^ f) ^ 2 - r ^ f + 1) ?_ hp (by omega) h3) hR y g)
    have h2' : r ^ f ≤ (r ^ f) ^ 2 := Nat.le_self_pow (by norm_num) _
    rw [hK]
    push_cast [h2']
    ring

theorem comp5_fg2d : Comp5 FG2d := by
  refine comp5_of fun r p Y _ _ hr hr2 hp hp5 hrp hY y g hy hyr hJ => ?_
  have hR := noR_two_of_FG2d hr hr2 hY
  obtain ⟨f, hf, hm⟩ := hY
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := g2_model hm
  exact comp5Concl_of_mulEquiv e (fun hy' hyr' hJ' =>
    g2_comp5 hr hr2 hp hp5 hrp hf hK ((noR_congr e).1 hR) (e g) hy' hyr' hJ') hy hyr hJ

end CFSG.OddStandard.GH71.S55
