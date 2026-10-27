module

public import CFSG.LocalAnalysis.OddStandard.Solomon75AhatDataSylow

public section

namespace CFSG.OddStandard.Solomon75.AhatData

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

theorem exists_commuting_prime_elem {G : Type*} [Group G] [Finite G] {Xb Pb : Subgroup G}
    (hX : IsPGroup 2 Xb) (hnorm : Xb ≤ normalizer (Pb : Set G)) (hPne : Pb ≠ ⊥)
    (hodd : ¬ 2 ∣ Nat.card Pb) :
    ∃ r : ℕ, r.Prime ∧ r ∣ Nat.card Pb ∧ ∃ e : G, e ≠ 1 ∧ e ^ r = 1 ∧
      ∀ x ∈ Xb, (x * e * x⁻¹) * e = e * (x * e * x⁻¹) := by
  have hcard : 1 < Nat.card Pb := by
    rw [Nat.one_lt_iff_ne_zero_and_ne_one]
    exact ⟨Nat.card_pos.ne', fun h => hPne ((Subgroup.eq_bot_iff_card _).2 h)⟩
  obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd (Nat.ne_of_gt hcard)
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨R, hRnorm, hRne⟩ :=
    CFSG.SignalizerFunctor.Helpers.normalized_subgroup_invariant_sylow_nontrivial 2 r
      Nat.prime_two hr Xb Pb hX hnorm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd) hrdvd
  set R' : Subgroup G := (R : Subgroup Pb).map Pb.subtype with hR'
  have hRp : IsPGroup r R' := (R.isPGroup').map Pb.subtype
  have hnt : Nontrivial R' := (Subgroup.nontrivial_iff_ne_bot R').2 hRne
  have hzne : Nontrivial (center R') := hRp.center_nontrivial
  have hAnorm := CFSG.SignalizerFunctor.Helpers.characteristic_subgroup_map_normalized Xb R'
    hRnorm (center R')
  set A : Subgroup G := (center R').map R'.subtype with hA
  have hAp : IsPGroup r A := (hRp.to_subgroup (center R')).map R'.subtype
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hAp
  have hAcard : 1 < Nat.card A := by
    rw [hA, Subgroup.card_map_of_injective R'.subtype_injective]
    exact Finite.one_lt_card_iff_nontrivial.2 hzne
  have hrA : r ∣ Nat.card A := by
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      omega
    rw [hk]
    exact dvd_pow_self r hk0
  obtain ⟨e, he⟩ := exists_prime_orderOf_dvd_card' (G := A) r hrA
  refine ⟨r, hr, hrdvd, (e : G), ?_, ?_, ?_⟩
  · intro h
    have h1 : e = 1 := Subtype.ext h
    rw [h1, orderOf_one] at he
    exact hr.one_lt.ne he
  · have h1 : e ^ r = 1 := by
      rw [← he]
      exact pow_orderOf_eq_one e
    have := congrArg Subtype.val h1
    simpa using this
  · intro x hx
    have hxe : x * (e : G) * x⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 (hAnorm hx) e).1 e.2
    obtain ⟨c, hc, hce⟩ := Subgroup.mem_map.1 hxe
    obtain ⟨d, hd, hde⟩ := Subgroup.mem_map.1 e.2
    have hcd : d * c = c * d := mem_center_iff.1 hc d
    have h2 := congrArg Subtype.val hcd
    simp only [Subgroup.coe_mul] at h2
    rw [← hce, ← hde]
    exact h2.symm

theorem mul_mem_of_index_le_two {G : Type*} [Group G] [Finite G] {Xb Q : Subgroup G}
    (hXQ : Xb ≤ Q) (hcard : Nat.card Q ≤ 2 * Nat.card Xb) {a b : G} (ha : a ∈ Q) (hb : b ∈ Q)
    (ha' : a ∉ Xb) (hb' : b ∉ Xb) : a * b ∈ Xb := by
  set H : Subgroup Q := Xb.subgroupOf Q with hH
  have hHcard : Nat.card H = Nat.card Xb :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXQ).toEquiv
  have h1 := Subgroup.card_mul_index H
  rw [hHcard] at h1
  have hpos : 0 < Nat.card Xb := Nat.card_pos
  have hidx : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hle : H.index ≤ 2 := by
    by_contra hcon
    push Not at hcon
    have : 2 * Nat.card Xb < Nat.card Xb * H.index := by nlinarith
    omega
  have hne1 : H.index ≠ 1 := by
    intro h
    have htop : H = ⊤ := Subgroup.index_eq_one.1 h
    have : (⟨a, ha⟩ : Q) ∈ H := htop ▸ Subgroup.mem_top _
    exact ha' (Subgroup.mem_subgroupOf.1 this)
  have h2 : H.index = 2 := by omega
  have hmul := Subgroup.mul_mem_iff_of_index_two (a := (⟨a, ha⟩ : Q)) (b := (⟨b, hb⟩ : Q)) h2
  have haH : (⟨a, ha⟩ : Q) ∉ H := fun h => ha' (Subgroup.mem_subgroupOf.1 h)
  have hbH : (⟨b, hb⟩ : Q) ∉ H := fun h => hb' (Subgroup.mem_subgroupOf.1 h)
  have : (⟨a, ha⟩ * ⟨b, hb⟩ : Q) ∈ H := hmul.2 ⟨fun h => absurd h haH, fun h => absurd h hbH⟩
  exact Subgroup.mem_subgroupOf.1 this

section Balance

variable {n : ℕ} [NeZero n] {K : Type} [Group K]

theorem no_odd_of_balance [Finite K] (hn : 8 ≤ n) (hn' : n ≤ 11) {rmin : ℕ} (hrmin : 3 ≤ rmin)
    (hP0 : Nat.card (P0 n) = if n ≤ 9 then 64 else 128) (hbal : BalanceGood n rmin (P0 n))
    (hK : IsDoubleCoverOfAlt K n) (X : Subgroup K) (hX : IsPGroup 2 X)
    (hXcard : Nat.card X = 2 ^ (if n ≤ 9 then 6 else 7)) (P : Subgroup K)
    (hPr : ∀ r : ℕ, r.Prime → r ∣ Nat.card P → rmin ≤ r) (hXP : X ≤ normalizer (P : Set K)) :
    P = ⊥ := by
  let C := CoverSetup.ofCover hK
  obtain ⟨S, hXS⟩ := hX.exists_le_sylow
  obtain ⟨g, hg⟩ := exists_conj_comap hn hn' hK C hP0 S
  have hQcard : Nat.card (conjSub g (P0 n)) = if n ≤ 9 then 64 else 128 := by
    rw [conjSub, Subgroup.card_map_of_injective (MulAut.conj g).injective, hP0]
  have hXQ : X.map C.ρ ≤ conjSub g (P0 n) := by
    rw [Subgroup.map_le_iff_le_comap, ← hg]
    exact hXS
  have hcardQ : Nat.card (conjSub g (P0 n)) ≤ 2 * Nat.card (X.map C.ρ) := by
    have h := C.card_le_two_mul_map X
    rw [hXcard] at h
    rw [hQcard]
    split_ifs at h ⊢ <;> norm_num at h ⊢ <;> omega
  by_cases hbot : P.map C.ρ = ⊥
  ·
    have hPle : P ≤ center K := by
      have : P ≤ C.ρ.ker := (Subgroup.map_eq_bot_iff P).1 hbot
      intro x hx
      exact C.ρ_eq_one_iff.1 (MonoidHom.mem_ker.1 (this hx))
    have hdvd : Nat.card P ∣ 2 := C.center_card ▸ Subgroup.card_dvd_of_le hPle
    by_contra hPne
    have h2 : Nat.card P = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
      · exact absurd ((Subgroup.eq_bot_iff_card _).2 h) hPne
      · exact h
    have := hPr 2 Nat.prime_two (by rw [h2])
    omega
  ·
    have hPbarr : ∀ r : ℕ, r.Prime → r ∣ Nat.card (P.map C.ρ) → rmin ≤ r := fun r hr hrd =>
      hPr r hr (hrd.trans (Subgroup.card_map_dvd P C.ρ))
    have hodd : ¬ 2 ∣ Nat.card (P.map C.ρ) := fun h2 => by
      have := hPbarr 2 Nat.prime_two h2
      omega
    have hnorm : X.map C.ρ ≤
        normalizer ((P.map C.ρ : Subgroup (Perm (Fin n))) : Set (Perm (Fin n))) := by
      rintro _ ⟨x, hx, rfl⟩
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · rintro ⟨p, hp, rfl⟩
        refine ⟨x * p * x⁻¹, ?_, by simp⟩
        exact (Subgroup.mem_normalizer_iff.1 (hXP hx) p).1 hp
      · rintro ⟨p, hp, hph⟩
        have hp' : x⁻¹ * p * x ∈ P := by
          have := (Subgroup.mem_normalizer_iff.1 (hXP (X.inv_mem hx)) p).1 hp
          simpa using this
        refine ⟨x⁻¹ * p * x, hp', ?_⟩
        rw [map_mul, map_mul, map_inv, hph]
        group
    obtain ⟨r, hr, hrdvd, e, he1, her, hecomm⟩ :=
      exists_commuting_prime_elem (hX.map C.ρ) hnorm hbot hodd
    obtain ⟨w₁, hw₁, w₂, hw₂, hwit₁, hwit₂, hwit₁₂⟩ :=
      (hbal.conj g) e he1 r hr (hPbarr r hr hrdvd) her
    have hnot : ∀ w ∈ X.map C.ρ, ¬ Wit e w := fun w hw hwit => hwit (hecomm w hw)
    have h12 := mul_mem_of_index_le_two hXQ hcardQ hw₁ hw₂ (fun h => hnot w₁ h hwit₁)
      (fun h => hnot w₂ h hwit₂)
    exact (hnot _ h12 hwit₁₂).elim

end Balance

section OneClass

variable {n : ℕ} {K : Type} [Group K]

theorem exists_central_comm (C : CoverSetup n K) (hn : 8 ≤ n) {w : K}
    (h2 : C.ρ w * C.ρ w = 1) (h1 : C.ρ w ≠ 1) :
    ∃ y : K, ⁅w, y⁆ ∈ center K ∧ ⁅w, y⁆ ≠ 1 := by
  obtain ⟨a₁, b₁, a₂, b₂, h12, h1b1, h1b2, h2b1, h2b2, hbb, e1, e2, e3, e4⟩ :=
    exists_swap_pairs (C.π w).2 h2 h1
  obtain ⟨y, hy⟩ := C.exists_ρ_eq (sign_swap_mul_swap h12 hbb)
  refine ⟨y, ?_, commutator_ne_one_of_doubleCover hn C.hX C.surj C.ker h12 h1b1 h1b2 h2b1 h2b2
    hbb e1 e2 e3 e4 hy⟩
  rw [← C.ρ_eq_one_iff, map_commutatorElement, hy]
  exact commutatorElement_eq_one_iff_mul_comm.2
    (comm_swap_pairs h1b1 h1b2 h2b1 h2b2 (C.ρ w) e1 e2 e3 e4)

theorem center_unique (C : CoverSetup n K) {c₀ c₁ : K} (h₀ : c₀ ∈ center K) (h₁ : c₁ ∈ center K)
    (hne₀ : c₀ ≠ 1) (hne₁ : c₁ ≠ 1) : c₀ = c₁ := by
  obtain ⟨z, -, hz⟩ := (Nat.card_eq_two_iff' (1 : center K)).1 C.center_card
  have e₀ : (⟨c₀, h₀⟩ : center K) = z := hz _ (fun h => hne₀ (congrArg Subtype.val h))
  have e₁ : (⟨c₁, h₁⟩ : center K) = z := hz _ (fun h => hne₁ (congrArg Subtype.val h))
  exact congrArg Subtype.val (e₀.trans e₁.symm)

theorem one_class_of_cover (hn : 8 ≤ n) (hn' : n ≤ 11) (hK : IsDoubleCoverOfAlt K n) {u v : K}
    (hu : orderOf u = 2) (hv : orderOf v = 2) (hunc : u ∉ center K) (hvnc : v ∉ center K) :
    IsConj u v := by
  let C := CoverSetup.ofCover hK
  have hu2 : u * u = 1 := by
    rw [← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.1 (dvd_of_eq hu)
  have hv2 : v * v = 1 := by
    rw [← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.1 (dvd_of_eq hv)
  have hiso : ∀ x : K, x * x = 1 → x ∉ center K → IsoI (C.ρ x) := by
    intro x hx2 hxc
    have h2 : C.ρ x * C.ρ x = 1 := by rw [← map_mul, hx2, map_one]
    have h1 : C.ρ x ≠ 1 := fun h => hxc (C.ρ_eq_one_iff.1 h)
    rcases support_card_of_involution hn' h2 h1 (C.sign_ρ x) with h4 | h8
    · exact absurd hx2 (C.dblI_sq_ne_one hn ⟨h2, h4⟩)
    · exact ⟨h2, h8⟩
  have hiu := hiso u hu2 hunc
  have hiv := hiso v hv2 hvnc
  obtain ⟨g, hg, hgc⟩ :=
    exists_even_conj hiu.1 hiv.1 hiu.ne_one hiv.ne_one (by rw [hiu.2, hiv.2])
  obtain ⟨k, hk⟩ := C.exists_ρ_eq hg
  have hρw : C.ρ (k * u * k⁻¹) = C.ρ v := by rw [map_mul, map_mul, map_inv, hk, hgc]
  have hcenter : (k * u * k⁻¹)⁻¹ * v ∈ center K := by
    rw [← C.ρ_eq_one_iff, map_mul, map_inv, hρw, inv_mul_cancel]
  have huw : IsConj u (k * u * k⁻¹) := isConj_iff.2 ⟨k, rfl⟩
  by_cases hc : (k * u * k⁻¹)⁻¹ * v = 1
  · rw [← inv_mul_eq_one.1 hc]
    exact huw
  · set w := k * u * k⁻¹ with hw
    have hw2 : C.ρ w * C.ρ w = 1 := by rw [hρw, ← map_mul, hv2, map_one]
    have hw1 : C.ρ w ≠ 1 := by
      rw [hρw]
      exact hiv.ne_one
    obtain ⟨y, hyc, hyne⟩ := exists_central_comm C hn hw2 hw1
    have hz2 : ⁅w, y⁆ * ⁅w, y⁆ = 1 := C.sq_of_mem_center hyc
    have hp : y * w * y⁻¹ = w * ⁅w, y⁆ := by
      have e : ⁅w, y⁆⁻¹ = ⁅w, y⁆ := inv_eq_of_mul_eq_one_right hz2
      have h1 : y * w * y⁻¹ = ⁅w, y⁆⁻¹ * w := by
        simp only [commutatorElement_def, mul_inv_rev, inv_inv]
        group
      rw [h1, e]
      exact (mem_center_iff.1 hyc w).symm
    have hcc : w⁻¹ * v = ⁅w, y⁆ := center_unique C hcenter hyc hc hyne
    have hwv : y * w * y⁻¹ = v := by
      rw [hp, ← hcc]
      group
    exact huw.trans (isConj_iff.2 ⟨y, hwv⟩)

end OneClass

section Assembly

variable {n : ℕ} [NeZero n]

theorem three_le_of_odd {m r : ℕ} (hm : Odd m) (hr : r.Prime) (hd : r ∣ m) : 3 ≤ r := by
  have h2 := hr.two_le
  by_contra hcon
  have : r = 2 := by omega
  subst this
  exact (Nat.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 hd)

theorem five_le_of_coprime {m r : ℕ} (hm : Nat.Coprime m 6) (hr : r.Prime) (hd : r ∣ m) :
    5 ≤ r := by
  have h2 := hr.two_le
  by_contra hcon
  have hr6 : ¬ r ∣ 6 := by
    intro h6
    have := Nat.dvd_gcd hd h6
    rw [hm] at this
    exact hr.one_lt.ne' (Nat.dvd_one.1 this)
  interval_cases r
  · exact hr6 (by norm_num)
  · exact hr6 (by norm_num)
  · exact absurd hr (by norm_num)

theorem alternatingBalanceData_of_good (hn : 8 ≤ n) (hn' : n ≤ 11)
    (hP0 : Nat.card (P0 n) = if n ≤ 9 then 64 else 128)
    (hbal : BalanceGood n (if n ≤ 10 then 3 else 5) (P0 n)) :
    CFSG.OddStandard.Solomon75.AlternatingBalanceData n where
  no_odd hn10 K _ _ hK X hX hXcard P hP hXP :=
    no_odd_of_balance hn hn' (rmin := 3) le_rfl hP0 (by simpa [hn10] using hbal) hK X hX hXcard P
      (fun r hr hd => three_le_of_odd hP hr hd) hXP
  no_odd' K _ _ hK X hX hXcard P hP hXP :=
    no_odd_of_balance hn hn' (rmin := 5) (by norm_num) hP0
      (hbal.mono (by split_ifs <;> omega)) hK X hX hXcard P
      (fun r hr hd => five_le_of_coprime hP hr hd) hXP
  one_class K _ _ hK u v hu hv hunc hvnc := one_class_of_cover hn hn' hK hu hv hunc hvnc

end Assembly

end CFSG.OddStandard.Solomon75.AhatData
