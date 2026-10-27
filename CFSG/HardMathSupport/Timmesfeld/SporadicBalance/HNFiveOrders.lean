module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.HNFive
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.HNEleven
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.HNNineteen
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.HNThreeB
public import CFSG.RankThree.PartOne.S11c.HNSevenFix

public noncomputable section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open Equiv Subgroup
open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native

section Abstract

variable {G : Type*} [Group G]

theorem card_inf_centralizer_conj_both (c a b : G) :
    Nat.card (centralizer ({c * a * c⁻¹} : Set G) ⊓ centralizer ({c * b * c⁻¹} : Set G) :
      Subgroup G) =
    Nat.card (centralizer ({a} : Set G) ⊓ centralizer ({b} : Set G) : Subgroup G) := by
  have e : (centralizer ({a} : Set G) ⊓ centralizer ({b} : Set G)).map
      (MulAut.conj c).toMonoidHom =
      centralizer ({c * a * c⁻¹} : Set G) ⊓ centralizer ({c * b * c⁻¹} : Set G) := by
    ext d
    simp only [mem_map, mem_inf, mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    constructor
    · rintro ⟨e, ⟨hea, heb⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · calc c * e * c⁻¹ * (c * a * c⁻¹) = c * (e * a) * c⁻¹ := by group
          _ = c * (a * e) * c⁻¹ := by rw [hea]
          _ = c * a * c⁻¹ * (c * e * c⁻¹) := by group
      · calc c * e * c⁻¹ * (c * b * c⁻¹) = c * (e * b) * c⁻¹ := by group
          _ = c * (b * e) * c⁻¹ := by rw [heb]
          _ = c * b * c⁻¹ * (c * e * c⁻¹) := by group
    · rintro ⟨hda, hdb⟩
      refine ⟨c⁻¹ * d * c, ⟨?_, ?_⟩, by group⟩
      · calc c⁻¹ * d * c * a = c⁻¹ * (d * (c * a * c⁻¹)) * c := by group
          _ = c⁻¹ * ((c * a * c⁻¹) * d) * c := by rw [hda]
          _ = a * (c⁻¹ * d * c) := by group
      · calc c⁻¹ * d * c * b = c⁻¹ * (d * (c * b * c⁻¹)) * c := by group
          _ = c⁻¹ * ((c * b * c⁻¹) * d) * c := by rw [hdb]
          _ = b * (c⁻¹ * d * c) := by group
  rw [← e, Subgroup.card_map_of_injective (MulAut.conj c).injective]

theorem exists_three_of_nine_dvd [Finite G] {x : G}
    (h9 : 9 ∣ Nat.card (centralizer ({x} : Set G))) :
    ∃ s : G, orderOf s = 3 ∧ s * x = x * s ∧
      9 ∣ Nat.card (centralizer ({s} : Set G) ⊓ centralizer ({x} : Set G) : Subgroup G) := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨R', hR'⟩ := Sylow.exists_subgroup_card_pow_prime (G := centralizer ({x} : Set G)) 3
    (n := 2) (by norm_num; exact h9)
  set R : Subgroup G := R'.map (centralizer ({x} : Set G)).subtype with hR
  have hRcard : Nat.card R = 3 ^ 2 := by
    rw [hR, Subgroup.card_map_of_injective (centralizer ({x} : Set G)).subtype_injective, hR']
  have hRx : R ≤ centralizer ({x} : Set G) := by
    rintro _ ⟨r, -, rfl⟩
    exact r.2
  obtain ⟨⟨s, hsR⟩, hs⟩ := exists_prime_orderOf_dvd_card' (G := R) 3
    (by rw [hRcard]; norm_num)
  have hs' : orderOf s = 3 := by rw [← Subgroup.orderOf_mk s hsR]; exact hs
  have hcomm : ∀ a b : R, a * b = b * a :=
    (IsPGroup.isMulCommutative_of_card_eq_prime_sq hRcard).is_comm.comm
  have hRs : R ≤ centralizer ({s} : Set G) := by
    intro r hr
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hcomm ⟨r, hr⟩ ⟨s, hsR⟩)
  refine ⟨s, hs', (mem_centralizer_singleton_iff.1 (hRx hsR)), ?_⟩
  have := Subgroup.card_dvd_of_le (le_inf hRs hRx)
  rw [hRcard] at this
  exact this

theorem isConj_pow_of_mem [Finite G] (K : Subgroup G) {p : ℕ} [Fact p.Prime]
    (hK : ¬ p ^ 2 ∣ Nat.card K) {x f : G} (hx : x ∈ K) (hf : f ∈ K) (hxo : orderOf x = p)
    (hfo : orderOf f = p) : ∃ k : ℕ, IsConj x (f ^ k) := by
  have hfo' : orderOf (⟨f, hf⟩ : K) = p := by rw [Subgroup.orderOf_mk]; exact hfo
  have hxo' : orderOf (⟨x, hx⟩ : K) = p := by rw [Subgroup.orderOf_mk]; exact hxo
  obtain ⟨g, k, hgk⟩ := CFSG.RankThree.PartOne.HNRed.exists_conj_pow_of_orderOf_prime hK hfo' hxo'
  have hgk' : (g : G) * x * (g : G)⁻¹ = f ^ k := congrArg Subtype.val hgk
  exact ⟨k, isConj_iff.2 ⟨g, hgk'⟩⟩

theorem isConj_conj_pow (c f : G) (k : ℕ) : IsConj ((c * f * c⁻¹) ^ k) (f ^ k) := by
  refine isConj_iff.2 ⟨c⁻¹, ?_⟩
  rw [conj_pow]
  group

theorem dvd_of_not_dvd {n : ℕ} (hn : n ∣ 2 ^ 14 * 3 ^ 6 * 5 ^ 6 * 7 * 11 * 19) (h7 : ¬ 7 ∣ n)
    (h11 : ¬ 11 ∣ n) (h19 : ¬ 19 ∣ n) (h9 : ¬ 9 ∣ n) : n ∣ 2 ^ 14 * 3 * 5 ^ 6 := by
  have c7 : Nat.Coprime n 7 := (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd
    (by norm_num)).2 h7))
  have c11 : Nat.Coprime n 11 := (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd
    (by norm_num)).2 h11))
  have c19 : Nat.Coprime n 19 := (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd
    (by norm_num)).2 h19))
  have e : 2 ^ 14 * 3 ^ 6 * 5 ^ 6 * 7 * 11 * 19 = 2 ^ 14 * 5 ^ 6 * 3 ^ 6 * (7 * 11 * 19) := by
    norm_num
  rw [e] at hn
  have h1 : n ∣ 2 ^ 14 * 5 ^ 6 * 3 ^ 6 := ((c7.mul_right c11).mul_right c19).dvd_of_dvd_mul_right hn
  have hg : n ∣ 2 ^ 14 * 5 ^ 6 * Nat.gcd (3 ^ 6) n := by
    have := Nat.dvd_gcd h1 (Dvd.intro_left (2 ^ 14 * 5 ^ 6) rfl)
    rwa [Nat.gcd_mul_left] at this
  obtain ⟨j, hj, hjg⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (Nat.gcd_dvd_left (3 ^ 6) n)
  have hj1 : j ≤ 1 := by
    by_contra hj1
    apply h9
    have : 3 ^ 2 ∣ 3 ^ j := Nat.pow_dvd_pow 3 (by omega)
    exact (this.trans (hjg ▸ Nat.gcd_dvd_right (3 ^ 6) n))
  rw [hjg] at hg
  have h3 : 3 ^ j ∣ 3 := by interval_cases j <;> norm_num
  exact hg.trans (Nat.mul_dvd_mul_left _ h3)

theorem exists_commute_of_dvd [Finite G] {q : ℕ} [Fact q.Prime] {x : G}
    (h : q ∣ Nat.card (centralizer ({x} : Set G))) : ∃ w : G, orderOf w = q ∧ x * w = w * x := by
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := centralizer ({x} : Set G)) q h
  exact ⟨w, by rw [Subgroup.orderOf_coe]; exact hw, (mem_centralizer_singleton_iff.1 w.2).symm⟩

end Abstract

@[expose] def sev5 : Perm (Fin 12) := List.formPerm [(5 : Fin 12), 6, 7, 8, 9, 10, 11]

theorem sev5_isCycle : sev5.IsCycle := List.isCycle_formPerm (by decide) (by decide)

theorem sev5_support_card : sev5.support.card = 7 := by
  rw [sev5, List.support_formPerm_of_nodup _ (by decide) (by decide)]
  decide

theorem sev5_mem : sev5 ∈ alternatingGroup (Fin 12) := by
  rw [Equiv.Perm.mem_alternatingGroup, sev5_isCycle.sign, sev5_support_card]
  norm_num

theorem fiveNat_comm_sev5 : fiveNat * sev5 = sev5 * fiveNat := by decide

@[expose] def piC : Perm (Fin 12) := List.formPerm [(0 : Fin 12), 3, 6, 1, 4, 7, 2, 5] * swap 10 11

theorem piC_mem : piC ∈ alternatingGroup (Fin 12) := by
  have h8 : (List.formPerm [(0 : Fin 12), 3, 6, 1, 4, 7, 2, 5]).IsCycle :=
    List.isCycle_formPerm (by decide) (by decide)
  have hs : (List.formPerm [(0 : Fin 12), 3, 6, 1, 4, 7, 2, 5]).support.card = 8 := by
    rw [List.support_formPerm_of_nodup _ (by decide) (by decide)]
    decide
  rw [Equiv.Perm.mem_alternatingGroup, piC, Equiv.Perm.sign_mul, h8.sign, hs,
    Equiv.Perm.sign_swap (by decide)]
  norm_num

theorem piC_conj_comm :
    tri 0 1 2 * (piC * fiveNat * piC⁻¹) = piC * fiveNat * piC⁻¹ * tri 0 1 2 := by
  decide

theorem orderOf_fJ :
    orderOf fJ = 5 :=
  (CFSG.Sporadic.HNOddCore.ctuc_hn_five_centralizer_perfect_factor).2.2.2.1

theorem fiveNat_mem :
    fiveNat ∈ alternatingGroup (Fin 12) := by
  rw [← thetaJ_fJ]
  exact (thetaJ ⟨fJ, fJ_mem⟩).2

theorem fJ_eq_iotaA :
    fJ = iotaA ⟨fiveNat, fiveNat_mem⟩ := by
  have h := iotaA_theta ⟨fJ, fJ_mem⟩
  have e : thetaJ ⟨fJ, fJ_mem⟩ = ⟨fiveNat, fiveNat_mem⟩ := Subtype.ext thetaJ_fJ
  rw [e] at h
  exact h.symm

@[expose] def sevenF :
    JH := iotaA ⟨sev5, sev5_mem⟩

theorem fJ_comm_sevenF :
    fJ * sevenF = sevenF * fJ := by
  have e : (⟨fiveNat, fiveNat_mem⟩ : alternatingGroup (Fin 12)) * ⟨sev5, sev5_mem⟩ =
      ⟨sev5, sev5_mem⟩ * ⟨fiveNat, fiveNat_mem⟩ := Subtype.ext fiveNat_comm_sev5
  have h1 : fJ * sevenF = iotaA (⟨fiveNat, fiveNat_mem⟩ * ⟨sev5, sev5_mem⟩) := by
    rw [map_mul, ← fJ_eq_iotaA]
    rfl
  have h2 : sevenF * fJ = iotaA (⟨sev5, sev5_mem⟩ * ⟨fiveNat, fiveNat_mem⟩) := by
    rw [map_mul, ← fJ_eq_iotaA]
    rfl
  rw [h1, h2, e]

theorem orderOf_sevenF :
    orderOf sevenF = 7 := by
  rw [sevenF, orderOf_injective iotaA iotaA_injective, Subgroup.orderOf_mk,
    sev5_isCycle.orderOf, sev5_support_card]

theorem fJ3_mem :
    iotaA ⟨piC, piC_mem⟩ * fJ * (iotaA ⟨piC, piC_mem⟩)⁻¹ ∈ CJ (sJ 0) := by
  have e : tri012A * ((⟨piC, piC_mem⟩ : alternatingGroup (Fin 12)) * ⟨fiveNat, fiveNat_mem⟩ *
      (⟨piC, piC_mem⟩ : alternatingGroup (Fin 12))⁻¹) = ((⟨piC, piC_mem⟩ :
      alternatingGroup (Fin 12)) * ⟨fiveNat, fiveNat_mem⟩ *
      (⟨piC, piC_mem⟩ : alternatingGroup (Fin 12))⁻¹) * tri012A := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv, tri012A_val]
    exact piC_conj_comm
  rw [mem_CJ, ← iotaA_tri012, fJ_eq_iotaA, ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_mul, e]

theorem isConj_fJ_of_mem_CJ_s1
    {x : JH} (hx : x ∈ CJ (sJ 0)) (hxo : orderOf x = 5) :
    ∃ k : ℕ, IsConj x (fJ ^ k) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨k, hk⟩ := isConj_pow_of_mem (CJ (sJ 0)) (by rw [card_CJ_s1]; norm_num) hx fJ3_mem hxo
    (by rw [orderOf_conj_eq, orderOf_fJ])
  exact ⟨k, hk.trans (isConj_conj_pow _ fJ k)⟩

theorem not_seven_dvd_card_centralizer
    {x : JH}
    (hx : orderOf x = 5) (hnot : ∀ k : ℕ, ¬ IsConj x (fJ ^ k)) :
    ¬ 7 ∣ Nat.card (centralizer ({x} : Set JH)) := by
  intro h7
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨g, a, hga⟩ := CFSG.RankThree.PartOne.HNRed.exists_conj_pow_of_commute_seven_JH orderOf_fJ
    hx ⟨sevenF, orderOf_sevenF, fJ_comm_sevenF⟩ (exists_commute_of_dvd h7)
  exact hnot a (isConj_iff.2 ⟨g⁻¹, by rw [hga]; group⟩)

theorem not_nine_dvd_card_centralizer
    {x : JH}
    (hx : orderOf x = 5) (hnot : ∀ k : ℕ, ¬ IsConj x (fJ ^ k)) :
    ¬ 9 ∣ Nat.card (centralizer ({x} : Set JH)) := by
  intro h9
  obtain ⟨s, hs, hsx, hs9⟩ := exists_three_of_nine_dvd h9
  have hconj : ∀ {t : JH} {c : JH}, c * t * c⁻¹ = s → c⁻¹ * x * c ∈ CJ t := by
    intro t c hc
    rw [mem_CJ]
    have e : t = c⁻¹ * s * c := by rw [← hc]; group
    rw [e]
    calc c⁻¹ * s * c * (c⁻¹ * x * c) = c⁻¹ * (s * x) * c := by group
      _ = c⁻¹ * (x * s) * c := by rw [hsx]
      _ = c⁻¹ * x * c * (c⁻¹ * s * c) := by group
  have hxo : ∀ c : JH, orderOf (c⁻¹ * x * c) = 5 := fun c => by
    rw [show c⁻¹ * x * c = c⁻¹ * x * c⁻¹⁻¹ by group, orderOf_conj_eq, hx]
  rcases (order_three_classes s).1 hs with h | h
  · obtain ⟨c, hc⟩ := isConj_iff.1 h
    obtain ⟨k, hk⟩ := isConj_fJ_of_mem_CJ_s1 (hconj hc) (hxo c)
    exact hnot k ((isConj_iff.2 ⟨c⁻¹, by rw [inv_inv]⟩).trans hk)
  · obtain ⟨c, hc⟩ := isConj_iff.1 h
    apply not_nine_dvd_card_inf_centralizer (hconj hc) (hxo c)
    have e := card_inf_centralizer_conj_both c (sJ 2) (c⁻¹ * x * c)
    rw [hc, show c * (c⁻¹ * x * c) * c⁻¹ = x by group] at e
    rw [← e]
    exact hs9

theorem hnFiveOrders_holds :
    HNFiveOrders := by
  intro x hx hnot
  have hJ : Nat.card (centralizer ({x} : Set JH)) ∣ 2 ^ 14 * 3 ^ 6 * 5 ^ 6 * 7 * 11 * 19 := by
    have := Subgroup.card_subgroup_dvd_card (centralizer ({x} : Set JH))
    rw [card_JH] at this
    norm_num
    exact this
  exact dvd_of_not_dvd hJ (not_seven_dvd_card_centralizer hx hnot)
    (not_eleven_dvd_card_centralizer hx) (not_nineteen_dvd_card_centralizer hx)
    (not_nine_dvd_card_centralizer hx hnot)

theorem sporadicOPrimeHolds_HN_five :
    SporadicOPrimeHolds .HN 5 :=
  sporadicOPrimeHolds_HN_five_of_orders hnFiveOrders_holds

theorem sporadicOnePairHolds_HN_five :
    SporadicOnePairHolds .HN 5 :=
  ⟨sporadicOPrimeHolds_HN_five, sporadicOuterHolds_HN_five⟩

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
