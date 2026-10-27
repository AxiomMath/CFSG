module

public import Certificates.Certificate17335
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.ConstrainedGen
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Fi22
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PrimeCommute
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22

public section

namespace CFSG.HardMathSupport.Dickson.I271

namespace TabFi22Small

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Three
  CFSG.HardMathSupport.Solomon.Coordinator.YS08
open CFSG.Monster.B.Co2 (Rep)
open CFSG.Monster.B.Fischer (fi22P)

section Counting

theorem card_fix_modEq_card_fix_inter {n q : ℕ} [Fact q.Prime] {a b : Equiv.Perm (Fin n)}
    (hab : a * b = b * a) (hb : b ^ q = 1) :
    Nat.card {w : Fin n // a w = w} ≡ Nat.card {w : Fin n // a w = w ∧ b w = w} [MOD q] := by
  classical
  have hinv : ∀ w : Fin n, a (b w) = b w ↔ a w = w := by
    intro w
    have h : a (b w) = b (a w) := congrArg (fun f : Equiv.Perm (Fin n) => f w) hab
    rw [h]
    exact ⟨fun hw => b.injective hw, fun hw => by rw [hw]⟩
  set σ : Equiv.Perm {w : Fin n // a w = w} := b.subtypePerm hinv with hσ
  have hσq : σ ^ q ^ 1 = 1 := by
    rw [pow_one, hσ, Equiv.Perm.subtypePerm_pow]
    refine Equiv.ext fun w => Subtype.ext ?_
    have h1 : (b ^ q) w.1 = w.1 := by rw [hb]; rfl
    simpa using h1
  have h := Equiv.Perm.card_compl_support_modEq hσq
  have h2 : Nat.card {w : Fin n // a w = w ∧ b w = w} = (σ.supportᶜ).card := by
    rw [← Nat.card_eq_finsetCard]
    refine Nat.card_congr
      { toFun := fun w => ⟨⟨w.1, w.2.1⟩, ?_⟩
        invFun := fun x => ⟨x.1.1, x.1.2, ?_⟩
        left_inv := fun x => rfl
        right_inv := fun w => rfl }
    · have : σ ⟨w.1, w.2.1⟩ = ⟨w.1, w.2.1⟩ := Subtype.ext w.2.2
      simpa [Equiv.Perm.mem_support] using this
    · have hx := x.2
      rw [Finset.mem_compl, Equiv.Perm.mem_support, not_not] at hx
      exact congrArg Subtype.val hx
  have h3 : Nat.card {w : Fin n // a w = w} = Fintype.card {w : Fin n // a w = w} :=
    Nat.card_eq_fintype_card
  rw [h2, h3]
  exact h.symm

theorem exists_fix_inter_modEq {n q : ℕ} [Fact q.Prime] {a b : Equiv.Perm (Fin n)}
    (hab : a * b = b * a) (ha : a ^ 3 = 1) (hb : b ^ q = 1) :
    ∃ m : ℕ, m ≤ Nat.card {w : Fin n // b w = w} ∧
      Nat.card {w : Fin n // b w = w} ≡ m [MOD 3] ∧
      Nat.card {w : Fin n // a w = w} ≡ m [MOD q] := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 := card_fix_modEq_card_fix_inter hab hb
  have h2 := card_fix_modEq_card_fix_inter (q := 3) hab.symm ha
  refine ⟨Nat.card {w : Fin n // a w = w ∧ b w = w}, ?_, ?_, h1⟩
  · exact Nat.card_le_card_of_injective (fun w => ⟨w.1, w.2.2⟩)
      (fun x y h => Subtype.ext (congrArg (fun z : {w : Fin n // b w = w} => z.1) h))
  · have e : Nat.card {w : Fin n // b w = w ∧ a w = w} =
        Nat.card {w : Fin n // a w = w ∧ b w = w} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun w => and_comm)
    rw [e] at h2
    exact h2

end Counting

section Generic

variable {G : Type*} [Group G]

theorem not_dvd_card_centralizer_of_pred [Finite G] {q : ℕ} [Fact q.Prime]
    (hq : ¬ q ^ 2 ∣ Nat.card G) {u : G} (hu : orderOf u = q) {x : G} (R : G → Prop)
    (hR : ∀ g y, R y → R (g * y * g⁻¹)) (hx : R x)
    (hno : ∀ y : G, orderOf y = orderOf x → R y → y * u ≠ u * y) :
    ¬ q ∣ Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  intro hdvd
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card'
    (G := Subgroup.centralizer ({x} : Set G)) q hdvd
  have hw' : orderOf (w : G) = q := by rw [Subgroup.orderOf_coe]; exact hw
  obtain ⟨g, k, hgk⟩ := CFSG.RankThree.PartOne.HNRed.exists_conj_pow_of_orderOf_prime hq hu hw'
  have hxw : (w : G) * x = x * w := Subgroup.mem_centralizer_singleton_iff.1 w.2
  have huk : orderOf (u ^ k) = q := by rw [← hgk, orderOf_conj_eq, hw']
  have hc : g * x * g⁻¹ * u ^ k = u ^ k * (g * x * g⁻¹) := by
    rw [← hgk]
    calc g * x * g⁻¹ * (g * w * g⁻¹) = g * (x * w) * g⁻¹ := by group
      _ = g * (w * x) * g⁻¹ := by rw [hxw]
      _ = g * w * g⁻¹ * (g * x * g⁻¹) := by group
  exact hno _ (orderOf_conj_eq g x) (hR g x hx)
    (CFSG.RankThree.PartOne.HNRed.commute_of_commute_pow hu huk hc)

end Generic

section Points

@[expose] noncomputable def fixCard (p : Equiv.Perm (Fin 3510)) : ℕ :=
  Nat.card {w : Fin 3510 // p w = w}

theorem fixCard_conj (c p : Equiv.Perm (Fin 3510)) : fixCard (c * p * c⁻¹) = fixCard p := by
  refine Nat.card_congr
    { toFun := fun w => ⟨(c⁻¹ : Equiv.Perm (Fin 3510)) w.1, ?_⟩
      invFun := fun w => ⟨c w.1, ?_⟩
      left_inv := fun w => Subtype.ext (by simp)
      right_inv := fun w => Subtype.ext (by simp) }
  · have h : c (p (c⁻¹ w.1)) = w.1 := w.2
    have h2 := congrArg (c⁻¹ : Equiv.Perm (Fin 3510)) h
    simpa using h2
  · have h : p w.1 = w.1 := w.2
    show c (p ((c⁻¹ : Equiv.Perm (Fin 3510)) (c w.1))) = c w.1
    simp [h]

theorem fixCount_eq_card {t : Array ℕ} {p : Equiv.Perm (Fin 3510)} (h : Rep 3510 t p) :
    CFSG.HardMathSupport.Solomon.Coordinator.Fi22Pump.fi22FixCount t = fixCard p := by
  unfold CFSG.HardMathSupport.Solomon.Coordinator.Fi22Pump.fi22FixCount fixCard
  rw [Fi22Three.countP_range_eq_card]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun w => ?_)
  rw [beq_iff_eq, h w]
  exact ⟨fun e => Fin.ext e, fun e => congrArg Fin.val e⟩

theorem fixN_eq_card (p : Equiv.Perm (Fin 3510)) : Fi22Copy.fixN p = fixCard p := by
  have h : Rep 3510 (Array.ofFn fun i : Fin 3510 => (p i : ℕ)) p := fun x => by
    rw [CFSG.Monster.B.Co2.getElem!_ofFn_nat _ x.2]
  rw [← Fi22Copy.fixCount_eq h, fixCount_eq_card h]

end Points

section Centralizers

open CFSG.Sporadic.Fi22 (J)


theorem finite_J_tab : Finite J :=
  Nat.finite_of_card_ne_zero (by rw [Fi22Copy.card_J_eq]; norm_num)

theorem exists_iotaJ_eq {Y : Equiv.Perm (Fin 3510)} (hY : Y ∈ fi22P) :
    ∃ t : J, (Fi22Copy.iotaJ t : Equiv.Perm (Fin 3510)) = Y := by
  haveI := finite_J_tab
  have hinj : Function.Injective
      (fun t : J => (⟨Fi22Copy.iotaJ t, Fi22Copy.iotaJ_mem t⟩ : fi22P)) :=
    fun s t h => Fi22Copy.iotaJ_injective (congrArg Subtype.val h)
  obtain ⟨t, ht⟩ := (Finite.injective_iff_surjective_of_equiv
    (CFSG.Sporadic.FischerOddCore.fi22PJ.symm.toEquiv) |>.1 hinj) ⟨Y, hY⟩
  exact ⟨t, congrArg Subtype.val ht⟩

theorem not_dvd_card_centralizer_of_fixCard {q : ℕ} [Fact q.Prime] (hq : ¬ q ^ 2 ∣ Nat.card J)
    {u : J} (hu : orderOf u = q) {x : J} (hx : orderOf x = 3)
    (hnum : ∀ m : ℕ, m ≤ fixCard (Fi22Copy.iotaJ u) → fixCard (Fi22Copy.iotaJ u) ≡ m [MOD 3] →
      ¬ fixCard (Fi22Copy.iotaJ x) ≡ m [MOD q]) :
    ¬ q ∣ Nat.card (Subgroup.centralizer ({x} : Set J)) := by
  haveI := finite_J_tab
  refine not_dvd_card_centralizer_of_pred hq hu
    (fun y => fixCard (Fi22Copy.iotaJ y) = fixCard (Fi22Copy.iotaJ x)) ?_ rfl ?_
  · intro g y hy
    simp only [map_mul, map_inv, fixCard_conj]
    exact hy
  · intro y hyo hyR hyu
    have hyo3 : orderOf y = 3 := hyo.trans hx
    have hy3 : y ^ 3 = 1 := by
      have := pow_orderOf_eq_one y
      rwa [hyo3] at this
    have hu1 : u ^ q = 1 := by
      have := pow_orderOf_eq_one u
      rwa [hu] at this
    obtain ⟨m, hm, h3, hqm⟩ := exists_fix_inter_modEq (q := q)
      (a := (Fi22Copy.iotaJ y : Equiv.Perm (Fin 3510))) (b := Fi22Copy.iotaJ u)
      (by rw [← map_mul, ← map_mul, hyu])
      (by rw [← map_pow, hy3, map_one]) (by rw [← map_pow, hu1, map_one])
    exact hnum m hm h3 (by rw [← hyR]; exact hqm)

theorem exists_element_of_mem {Y : Equiv.Perm (Fin 3510)} {q f : ℕ} (hP : Y ∈ fi22P)
    (hord : orderOf Y = q) (hf : Nat.card {w : Fin 3510 // Y w = w} = f) :
    ∃ u : J, orderOf u = q ∧ fixCard (Fi22Copy.iotaJ u) = f := by
  obtain ⟨u, hu⟩ := exists_iotaJ_eq hP
  refine ⟨u, ?_, ?_⟩
  · rw [← orderOf_injective Fi22Copy.iotaJ Fi22Copy.iotaJ_injective u]
    simpa [hu] using hord
  · rw [hu]
    exact hf

theorem exists_small_prime_elements :
    (∃ u : J, orderOf u = 7 ∧ fixCard (Fi22Copy.iotaJ u) = 3) ∧
      (∃ u : J, orderOf u = 11 ∧ fixCard (Fi22Copy.iotaJ u) = 1) ∧
      (∃ u : J, orderOf u = 13 ∧ fixCard (Fi22Copy.iotaJ u) = 0) := by
  obtain ⟨⟨u7, m7, o7, f7⟩, ⟨u11, m11, o11, f11⟩, ⟨u13, m13, o13, f13⟩⟩ :=
    Certificates.certificate17335
  exact ⟨exists_element_of_mem m7 o7 f7, exists_element_of_mem m11 o11 f11,
    exists_element_of_mem m13 o13 f13⟩

theorem not_dvd_small_primes
    {x : J} (hx : orderOf x = 3)
    (hf : fixCard (Fi22Copy.iotaJ x) = 27 ∨ fixCard (Fi22Copy.iotaJ x) = 36) :
    ¬ 7 ∣ Nat.card (Subgroup.centralizer ({x} : Set J)) ∧
      ¬ 11 ∣ Nat.card (Subgroup.centralizer ({x} : Set J)) ∧
      ¬ 13 ∣ Nat.card (Subgroup.centralizer ({x} : Set J)) := by
  obtain ⟨⟨u7, ho7, hf7⟩, ⟨u11, ho11, hf11⟩, ⟨u13, ho13, hf13⟩⟩ := exists_small_prime_elements
  have hJ : Nat.card J = 64561751654400 := Fi22Copy.card_J_eq
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  refine ⟨?_, ?_, ?_⟩
  · refine not_dvd_card_centralizer_of_fixCard (by rw [hJ]; norm_num) ho7 hx ?_
    intro m hm h3 hmod
    rw [hf7] at hm h3
    unfold Nat.ModEq at h3 hmod
    rcases hf with hf | hf <;> rw [hf] at hmod <;> omega
  · refine not_dvd_card_centralizer_of_fixCard (by rw [hJ]; norm_num) ho11 hx ?_
    intro m hm h3 hmod
    rw [hf11] at hm h3
    unfold Nat.ModEq at h3 hmod
    rcases hf with hf | hf <;> rw [hf] at hmod <;> omega
  · refine not_dvd_card_centralizer_of_fixCard (by rw [hJ]; norm_num) ho13 hx ?_
    intro m hm h3 hmod
    rw [hf13] at hm h3
    unfold Nat.ModEq at h3 hmod
    rcases hf with hf | hf <;> rw [hf] at hmod <;> omega

theorem card_centralizer_xRep_zero_dvd :
    Nat.card (Subgroup.centralizer ({xRep 0} : Set J)) ∣ 3 ^ 8 * 16 := by
  haveI := finite_J_tab
  set C := Subgroup.centralizer ({xRep 0} : Set J)
  have h2187 : 2187 ∣ Nat.card C :=
    three_pow_seven_dvd_card_centralizer_xRep (k := 0) (by norm_num)
  have hCle : Nat.card C ≤ 34992 := card_centralizer_xRep_zero_le
  obtain ⟨t, ht4, htc⟩ := exists_orderOf_four_comm
  have h4 : 4 ∣ Nat.card C := by
    have := Subgroup.orderOf_dvd_natCard C
      ((Subgroup.mem_centralizer_singleton_iff (g := xRep 0)).2 htc)
    rwa [ht4] at this
  have h8748 : 2187 * 4 ∣ Nat.card C := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2187 h4
  obtain ⟨j, hj⟩ := h8748
  have hpos : 0 < Nat.card C := Nat.card_pos
  have hj4 : j ≤ 4 := by omega
  have hj0 : 0 < j := by
    rcases Nat.eq_zero_or_pos j with h | h
    · rw [h, mul_zero] at hj; omega
    · exact h
  rw [hj]
  interval_cases j <;> norm_num

theorem card_centralizer_dvd_of_fixCard
    {x : J} (hx : orderOf x = 3)
    (hf : fixCard (Fi22Copy.iotaJ x) = 27 ∨ fixCard (Fi22Copy.iotaJ x) = 36) :
    Nat.card (Subgroup.centralizer ({x} : Set J)) ∣ 2 ^ 17 * 3 ^ 9 := by
  obtain ⟨h7, h11, h13⟩ := not_dvd_small_primes hx hf
  have h5 : ¬ 5 ∣ Nat.card (Subgroup.centralizer ({x} : Set J)) :=
    Fi22Copy.not_five_dvd_of_fixN hx (by rw [fixN_eq_card]; omega)
  have hdvd : Nat.card (Subgroup.centralizer ({x} : Set J)) ∣ Nat.card J :=
    Subgroup.card_subgroup_dvd_card _
  rw [Fi22Copy.card_J_eq] at hdvd
  have hcop : Nat.Coprime (Nat.card (Subgroup.centralizer ({x} : Set J)))
      (5 ^ 2 * 7 * 11 * 13) := by
    refine Nat.Coprime.mul_right (Nat.Coprime.mul_right (Nat.Coprime.mul_right
      (Nat.Coprime.pow_right 2 ?_) ?_) ?_) ?_
    · exact ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 h5).symm
    · exact ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 h7).symm
    · exact ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 h11).symm
    · exact ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 h13).symm
  exact hcop.dvd_of_dvd_mul_right (by simpa [show (64561751654400 : ℕ) =
    2 ^ 17 * 3 ^ 9 * (5 ^ 2 * 7 * 11 * 13) by norm_num] using hdvd)

end Centralizers

end TabFi22Small

section Main

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Three
  CFSG.HardMathSupport.Solomon.Coordinator.YS08 TabFi22Small


theorem tabFi22_card_centralizer_xRep_dvd {k : ℕ} (hk : k < 3) :
    Nat.card (Subgroup.centralizer ({xRep k} : Set CFSG.Sporadic.Fi22.J)) ∣ 2 ^ 17 * 3 ^ 9 := by
  interval_cases k
  · exact card_centralizer_xRep_zero_dvd.trans (by norm_num)
  · refine card_centralizer_dvd_of_fixCard (orderOf_xRep (by norm_num)) (Or.inl ?_)
    rw [← fixN_eq_card]
    exact Fi22Copy.fixN_xRep.2.1
  · refine card_centralizer_dvd_of_fixCard (orderOf_xRep (by norm_num)) (Or.inr ?_)
    rw [← fixN_eq_card]
    exact Fi22Copy.fixN_xRep.2.2.1

theorem tabFi22_pConstrained_xRep {k : ℕ} (hk : k < 3) :
    PConstrainedShape 3 (Subgroup.centralizer ({xRep k} : Set CFSG.Sporadic.Fi22.J)) := by
  haveI := finite_J_tab
  refine pConstrainedShape_of_solvable Nat.prime_three
    (isSolvable_of_card_dvd_two_three (a := 17) (b := 9) (tabFi22_card_centralizer_xRep_dvd hk)) ?_
  interval_cases k
  · exact gLAPPrimeCoreOf_xRep_zero
  · exact gLAPPrimeCoreOf_xRep_sep (by decide)
  · exact gLAPPrimeCoreOf_xRep_sep (by decide)

end Main

end CFSG.HardMathSupport.Dickson.I271
