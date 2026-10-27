module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LyCoreThree
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LyCoreFive

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.LyCore

open Subgroup Equiv Equiv.Perm CFSG CFSG.Blueprint CFSG.GH74.GLS.Stage12
  CFSG.Sporadic.Recognition.LyonsSims
open scoped Pointwise

theorem card_centralizer_t {Y : Type} [Group Y] {t : Y}
    {ρ : ↥(centralizer ({t} : Set Y)) →* Perm (Fin 11)} (D : LyData Y t ρ) :
    Nat.card ↥(centralizer ({t} : Set Y)) = 39916800 := by
  have h1 := Subgroup.card_ker_mul_card_range ρ
  rw [D.cover.ker_eq, D.cover.range_eq, Nat.card_zpowers, Subgroup.orderOf_mk, D.order_t,
    CFSG.GH74.GLS.Stage2.Bender.Thm1.LyMult.card_alternatingGroup_eleven] at h1
  omega

@[expose] def LyThreeBOrder : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], NativeSporadic.IsSporadic Y .Ly →
    ∀ (t : Y) (ρ : ↥(centralizer ({t} : Set Y)) →* Perm (Fin 11)), LyData Y t ρ →
      ∀ x₁ x₂ x₃ : ↥(centralizer ({t} : Set Y)), LyStd ρ x₁ x₂ x₃ →
        Nat.card ↥(centralizer ({(x₁ : Y) * (x₂ : Y)} : Set Y)) ≤ 174960

theorem lyThreeBCore_of_order
    (hord : LyThreeBOrder) : LyThreeBCore := by
  intro Y _ _ hLy t ρ D x₁ x₂ x₃ S W hWC hWn hcop
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hC := hord Y hLy t ρ D x₁ x₂ x₃ S
  have hQC : QE (x₁ : Y) (x₂ : Y) ≤ centralizer ({(x₁ : Y) * (x₂ : Y)} : Set Y) := by
    intro g hg
    rw [mem_QE] at hg
    rw [mem_centralizer_singleton_iff]
    calc g * ((x₁ : Y) * (x₂ : Y)) = (g * (x₁ : Y)) * (x₂ : Y) := by group
      _ = ((x₁ : Y) * g) * (x₂ : Y) := by rw [hg.1]
      _ = (x₁ : Y) * (g * (x₂ : Y)) := by group
      _ = (x₁ : Y) * ((x₂ : Y) * g) := by rw [hg.2]
      _ = (x₁ : Y) * (x₂ : Y) * g := by group
  have hQc : Nat.card ↥(QE (x₁ : Y) (x₂ : Y)) = 87480 := D.card_QE S
  have hQidx : ∀ c ∈ centralizer ({(x₁ : Y) * (x₂ : Y)} : Set Y),
      c * c ∈ QE (x₁ : Y) (x₂ : Y) ∧
      ∀ q ∈ QE (x₁ : Y) (x₂ : Y), c * q * c⁻¹ ∈ QE (x₁ : Y) (x₂ : Y) := by
    set C : Subgroup Y := centralizer ({(x₁ : Y) * (x₂ : Y)} : Set Y) with hCdef
    set Q : Subgroup Y := QE (x₁ : Y) (x₂ : Y) with hQdef
    have hdvd : Nat.card Q ∣ Nat.card C := Subgroup.card_dvd_of_le hQC
    obtain ⟨k, hk⟩ := hdvd
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hk
      exact (Nat.card_pos (α := C)).ne' hk
    have hk2 : k ≤ 2 := by
      have h1 : Nat.card C ≤ 174960 := hC
      rw [hk, hQc] at h1
      omega
    have hk12 : k = 1 ∨ k = 2 := by omega
    rcases hk12 with rfl | rfl
    · have hQeq : Q = C := Subgroup.eq_of_le_of_card_ge hQC (by omega)
      intro c hc
      rw [← hQeq] at hc
      exact ⟨Q.mul_mem hc hc, fun q hq => Q.mul_mem (Q.mul_mem hc hq) (Q.inv_mem hc)⟩
    · have hidx : (Q.subgroupOf C).index = 2 := by
        have h1 : Nat.card (Q.subgroupOf C) * (Q.subgroupOf C).index = Nat.card C :=
          Subgroup.card_mul_index _
        have h2 : Nat.card (Q.subgroupOf C) = Nat.card Q :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQC).toEquiv
        rw [h2, hk, hQc] at h1
        omega
      have hnorm : (Q.subgroupOf C).Normal := Subgroup.normal_of_index_eq_two hidx
      intro c hc
      refine ⟨?_, fun q hq => ?_⟩
      · exact Subgroup.mul_self_mem_of_index_two hidx ⟨c, hc⟩
      · have := hnorm.conj_mem ⟨q, hQC hq⟩ (Subgroup.mem_subgroupOf.mpr hq) ⟨c, hc⟩
        simpa [Subgroup.mem_subgroupOf] using this
  obtain ⟨R, hR⟩ := D.exists_threeCoreE S
  have hRQ : R ≤ QE (x₁ : Y) (x₂ : Y) := hR.le
  have hRn : ∀ c ∈ centralizer ({(x₁ : Y) * (x₂ : Y)} : Set Y), ∀ r ∈ R, c * r * c⁻¹ ∈ R := by
    intro c hc r hr
    let J : Subgroup Y := R.map (MulAut.conj c).toMonoidHom
    have hJQ : J ≤ QE (x₁ : Y) (x₂ : Y) := by
      rintro _ ⟨r', hr', rfl⟩
      exact (hQidx c hc).2 r' (hRQ hr')
    have hJn : ∀ q ∈ QE (x₁ : Y) (x₂ : Y), ∀ j ∈ J,
        q * j * q⁻¹ ∈ J := by
      rintro q hq _ ⟨r', hr', rfl⟩
      have hq' : c⁻¹ * q * c ∈ QE (x₁ : Y) (x₂ : Y) := by
        have := (hQidx c⁻¹ (Subgroup.inv_mem _ hc)).2 q hq
        simpa [mul_assoc] using this
      refine ⟨(c⁻¹ * q * c) * r' * (c⁻¹ * q * c)⁻¹, hR.normal _ hq' r' hr', ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have hJp : IsPGroup 3 ↥J := by
      have hcard : Nat.card ↥J = 3 ^ 6 := by
        rw [Subgroup.card_map_of_injective (MulAut.conj c).injective]
        exact hR.card
      exact IsPGroup.of_card hcard
    exact hR.max J hJQ hJn hJp ⟨r, hr, rfl⟩
  have hWR : W ⊓ R = ⊥ := by
    have hp : IsPGroup 3 ↥(W ⊓ R) := hR.isPGroup.to_le inf_le_right
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hp
    have hdvd : Nat.card ↥(W ⊓ R) ∣ Nat.card W := Subgroup.card_dvd_of_le inf_le_left
    have hm0 : m = 0 := by
      by_contra hne
      have h3 : 3 ∣ Nat.card W := (dvd_pow_self 3 hne).trans (hm ▸ hdvd)
      exact absurd (Nat.Coprime.eq_one_of_dvd hcop.symm h3) (by norm_num)
    rw [hm0, pow_zero] at hm
    exact Subgroup.eq_bot_of_card_eq _ hm
  have hcomm : ∀ w ∈ W, ∀ r ∈ R, w * r = r * w := by
    intro w hw r hr
    have hwC := mem_centralizer_singleton_iff.mp (hWC hw)
    have hrC : r ∈ centralizer ({(x₁ : Y) * (x₂ : Y)} : Set Y) := hQC (hRQ hr)
    have h1 : w * r * w⁻¹ * r⁻¹ ∈ R := by
      have := hRn w (hWC hw) r hr
      exact R.mul_mem this (R.inv_mem hr)
    have h2 : w * r * w⁻¹ * r⁻¹ ∈ W := by
      have h3 := hWn r (mem_centralizer_singleton_iff.mp hrC) w⁻¹ (W.inv_mem hw)
      have := W.mul_mem hw h3
      simpa [mul_assoc] using this
    have h4 : w * r * w⁻¹ * r⁻¹ = 1 := by
      have : w * r * w⁻¹ * r⁻¹ ∈ W ⊓ R := Subgroup.mem_inf.mpr ⟨h2, h1⟩
      rw [hWR] at this
      exact Subgroup.mem_bot.mp this
    calc w * r = w * r * w⁻¹ * r⁻¹ * (r * w) := by group
      _ = r * w := by rw [h4, one_mul]
  have hcardt : Nat.card ↥(centralizer ({t} : Set Y)) = 39916800 := card_centralizer_t D
  have hnoinv : ∀ w ∈ W, w * w = 1 → w = 1 := by
    intro w hw hw2
    by_contra hw1
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hord2 : orderOf w = 2 := orderOf_eq_prime (by rw [pow_two]; exact hw2) hw1
    have hconj : IsConj t w := D.one_class t w D.order_t hord2
    have hcw : Nat.card ↥(centralizer ({w} : Set Y)) = 39916800 := by
      rw [← card_centralizer_eq_of_isConj hconj, hcardt]
    have hRw : R ≤ centralizer ({w} : Set Y) := by
      intro r hr
      rw [mem_centralizer_singleton_iff]
      exact (hcomm w hw r hr).symm
    have h1 : Nat.card R ∣ Nat.card ↥(centralizer ({w} : Set Y)) :=
      Subgroup.card_dvd_of_le hRw
    rw [hR.card, hcw] at h1
    norm_num at h1
  have hWodd : Odd (Nat.card W) := by
    by_contra hev
    have h2 : 2 ∣ Nat.card W := by
      rcases Nat.even_or_odd (Nat.card W) with h | h
      · exact even_iff_two_dvd.mp h
      · exact absurd h hev
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := W) 2 h2
    have hw2 : (w : Y) * (w : Y) = 1 := by
      have : w ^ 2 = 1 := by rw [← hw]; exact pow_orderOf_eq_one w
      have := congrArg Subtype.val this
      simpa [pow_two] using this
    have := hnoinv (w : Y) w.2 hw2
    have hw1 : w = 1 := Subtype.ext this
    rw [hw1, orderOf_one] at hw
    exact absurd hw (by norm_num)
  have hWQ : ∀ w ∈ W, w ∈ QE (x₁ : Y) (x₂ : Y) → w = 1 := by
    intro w hwW hwQ
    let W₀ : Subgroup Y := W ⊓ QE (x₁ : Y) (x₂ : Y)
    have hW₀C : W₀ ≤ centralizer ({(x₁ : Y) * (x₂ : Y)} : Set Y) := inf_le_right.trans hQC
    have hW₀norm : W₀ ≤ normalizer (R : Set Y) := by
      intro w' hw'
      rw [Subgroup.mem_normalizer_iff]
      intro r
      refine ⟨fun hr => hRn w' (hW₀C hw') r hr, fun hr => ?_⟩
      have := hRn w'⁻¹ (Subgroup.inv_mem _ (hW₀C hw')) _ hr
      simpa [mul_assoc] using this
    have hNset : ((W₀ ⊔ R : Subgroup Y) : Set Y) = (W₀ : Set Y) * (R : Set Y) :=
      Subgroup.coe_mul_of_left_le_normalizer_right W₀ R hW₀norm
    have hNn : ∀ g ∈ QE (x₁ : Y) (x₂ : Y), ∀ j ∈ W₀ ⊔ R, g * j * g⁻¹ ∈ W₀ ⊔ R := by
      intro g hg j hj
      have hj' : j ∈ (W₀ : Set Y) * (R : Set Y) := by rw [← hNset]; exact hj
      obtain ⟨w', hw', r', hr', rfl⟩ := hj'
      have h1 : g * w' * g⁻¹ ∈ W₀ := by
        refine Subgroup.mem_inf.mpr ⟨hWn g (mem_centralizer_singleton_iff.mp (hQC hg)) w'
          (Subgroup.mem_inf.mp hw').1, (hQidx g (hQC hg)).2 w' (Subgroup.mem_inf.mp hw').2⟩
      have h2 : g * r' * g⁻¹ ∈ R := hR.normal g hg r' hr'
      have : g * (w' * r') * g⁻¹ = (g * w' * g⁻¹) * (g * r' * g⁻¹) := by group
      rw [this]
      exact (W₀ ⊔ R).mul_mem (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right h2)
    let J : Subgroup Y := (W₀ ⊔ R) ⊓ SL5 ρ
    have hJn : ∀ g ∈ SL5 ρ, ∀ j ∈ J, g * j * g⁻¹ ∈ J := by
      intro g hg j hj
      rw [Subgroup.mem_inf] at hj ⊢
      exact ⟨hNn g (D.SL5_le_QE S hg) j hj.1, (SL5 ρ).mul_mem ((SL5 ρ).mul_mem hg hj.2)
        ((SL5 ρ).inv_mem hg)⟩
    have hJodd : Odd (Nat.card J) := by
      by_contra hev
      have h2 : 2 ∣ Nat.card J := by
        rcases Nat.even_or_odd (Nat.card J) with h | h
        · exact even_iff_two_dvd.mp h
        · exact absurd h hev
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨j, hj⟩ := exists_prime_orderOf_dvd_card' (G := J) 2 h2
      have hj2 : (j : Y) * (j : Y) = 1 := by
        have : j ^ 2 = 1 := by rw [← hj]; exact pow_orderOf_eq_one j
        have := congrArg Subtype.val this
        simpa [pow_two] using this
      have hjN : (j : Y) ∈ (W₀ : Set Y) * (R : Set Y) := by
        rw [← hNset]; exact (Subgroup.mem_inf.mp j.2).1
      obtain ⟨w', hw', r', hr', hjr0⟩ := hjN
      have hjr : w' * r' = (j : Y) := hjr0
      have hw'W : w' ∈ W := (Subgroup.mem_inf.mp hw').1
      have h3 : w' * w' * (r' * r') = 1 := by
        have hc := hcomm w' hw'W r' hr'
        have hsq : w' * w' * (r' * r') = (w' * r') * (w' * r') := by
          calc w' * w' * (r' * r') = w' * (w' * r') * r' := by group
            _ = w' * (r' * w') * r' := by rw [hc]
            _ = (w' * r') * (w' * r') := by group
        rw [hsq, hjr]
        exact hj2
      have h4 : w' * w' = 1 := by
        have h5 : w' * w' ∈ W ⊓ R := by
          refine Subgroup.mem_inf.mpr ⟨W.mul_mem hw'W hw'W, ?_⟩
          have : w' * w' = (r' * r')⁻¹ := eq_inv_of_mul_eq_one_left h3
          rw [this]
          exact R.inv_mem (R.mul_mem hr' hr')
        rw [hWR] at h5
        exact Subgroup.mem_bot.mp h5
      have hw'1 : w' = 1 := hnoinv w' hw'W h4
      have hr'2 : r' * r' = 1 := by
        rw [hw'1] at h3; simpa using h3
      have hr'1 : r' = 1 := by
        obtain ⟨k, hk⟩ := hR.isPGroup (⟨r', hr'⟩ : R)
        have hk' : r' ^ (3 ^ k) = 1 := by simpa using congrArg Subtype.val hk
        have hr'2' : r' ^ 2 = 1 := by rw [pow_two]; exact hr'2
        have : r' ^ (Nat.gcd (3 ^ k) 2) = 1 := pow_gcd_eq_one.mpr ⟨hk', hr'2'⟩
        have hg : Nat.gcd (3 ^ k) 2 = 1 := Nat.Coprime.pow_left k (by norm_num)
        rwa [hg, pow_one] at this
      have hj1 : (j : Y) = 1 := by rw [← hjr, hw'1, hr'1, mul_one]
      have hj1' : j = 1 := Subtype.ext hj1
      rw [hj1', orderOf_one] at hj
      exact absurd hj (by norm_num)
    have hJbot : J = ⊥ := D.SL5_eq_bot_of_odd inf_le_right hJn hJodd
    obtain ⟨r, hr, s, hs, hwrs⟩ := D.QE_eq_mul_SL5 S hR w hwQ
    have hsJ : s ∈ J := by
      have hs' : s = r⁻¹ * w := by rw [hwrs]; group
      refine Subgroup.mem_inf.mpr ⟨?_, hs⟩
      rw [hs']
      exact (W₀ ⊔ R).mul_mem (Subgroup.mem_sup_right (R.inv_mem hr))
        (Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨hwW, hwQ⟩))
    rw [hJbot, Subgroup.mem_bot] at hsJ
    have hwr : w = r := by rw [hwrs, hsJ, mul_one]
    have : w ∈ W ⊓ R := Subgroup.mem_inf.mpr ⟨hwW, hwr ▸ hr⟩
    rw [hWR] at this
    exact Subgroup.mem_bot.mp this
  refine (Subgroup.eq_bot_iff_forall W).mpr fun w hw => ?_
  have h1 := (hQidx w (hWC hw)).1
  have h2 : w * w = 1 := hWQ _ (W.mul_mem hw hw) h1
  exact hnoinv w hw h2

theorem lyCoreAt_three_of_order
    (h : LyThreeBOrder) : LyCoreAt 3 :=
  lyCoreAt_three_of_threeB (lyThreeBCore_of_order h)

theorem lyCentralizerCore_of_threeBOrder
    (h : LyThreeBOrder) : LyCentralizerCore :=
  lyCentralizerCore_of_three (lyCoreAt_three_of_order h)

end CFSG.GH74.GLS.Stage2.Bender.Thm1.LyCore
