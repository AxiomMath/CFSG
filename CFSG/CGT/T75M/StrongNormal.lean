module

public import CFSG.CGT.Timmesfeld75.Core214Proof
public import CFSG.CGT.Timmesfeld75.Lemma27
public import CFSG.StronglyEmbedded.BenderUnitaryBorel
public import CFSG.Walter.PSL2Facts.Even
import CFSG.Models.BenderSuzuki
public import CFSG.Timmesfeld.Bridge.Asc72Bender

public section

namespace CFSG.CGT.T75M

open CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement

theorem card_le_two_of_comm_mem {H : Type*} [Group H] [Finite H] {A : Subgroup H}
    (hA : StrongWC A) {a : H} (ha : a ∈ classD A) (haA : a ∉ A) {N : Subgroup H}
    (hNA : ∀ x ∈ A, x ∈ N → x = 1) (hcomm : ∀ t ∈ A, t ≠ 1 → ⁅a, t⁆ ∈ N) :
    Nat.card A ≤ 2 := by
  have haa : a * a = 1 := classD_mul_self hA ha
  have hmem : ∀ t ∈ A, t ≠ 1 → a * t ∈ N := by
    intro t ht ht1
    have hodd := odd_orderOf_mul_of_not_mem hA ha haA ht ht1
    have htt : t * t = 1 := elemAbelian_mul_self hA.1 ht
    have hsq : (a * t) ^ 2 = ⁅a, t⁆ := by
      rw [commutatorElement_def, elemAbelian_inv hA.1 ht, inv_eq_of_mul_eq_one_right haa, pow_two]
      simp only [mul_assoc]
    obtain ⟨k, hk⟩ := hodd
    have h1 : a * t = ((a * t) ^ 2) ^ (k + 1) := by
      rw [← pow_mul]
      have : (a * t) ^ (2 * (k + 1)) = (a * t) ^ (orderOf (a * t) + 1) := by
        congr 1; omega
      rw [this, pow_succ, pow_orderOf_eq_one, one_mul]
    rw [h1, hsq]
    exact N.pow_mem (hcomm t ht ht1) _
  have hinj : ∀ t ∈ A, t ≠ 1 → ∀ t' ∈ A, t' ≠ 1 → t = t' := by
    intro t ht ht1 t' ht' ht1'
    have h1 : t⁻¹ * t' ∈ N := by
      have e : t⁻¹ * t' = (a * t)⁻¹ * (a * t') := by group
      rw [e]
      exact N.mul_mem (N.inv_mem (hmem t ht ht1)) (hmem t' ht' ht1')
    have h2 : t⁻¹ * t' = 1 := hNA _ (A.mul_mem (A.inv_mem ht) ht') h1
    exact inv_mul_eq_one.1 h2
  classical
  have hf : Function.Injective (fun x : A => decide ((x : H) = 1)) := by
    intro x y hxy
    by_cases hx : (x : H) = 1
    · have : (y : H) = 1 := by simpa [hx] using hxy.symm
      exact Subtype.ext (hx.trans this.symm)
    · have hy : (y : H) ≠ 1 := by
        intro hy
        simp [hx, hy] at hxy
      exact Subtype.ext (hinj x x.2 hx y y.2 hy)
  have := Nat.card_le_card_of_injective _ hf
  simpa using this


section Bender

open CFSG.BenderSuzuki in
theorem sq_card_le_of_bender {B : Type} [Group B] [Finite B]
    (hB : IsBenderGroup B) {X : Type} [Group X] [Finite X] (π : X →* B)
    (hπ : Function.Surjective π) {V : Type} [Group V] [Finite V] (ρ' : X →* MulAut V)
    (hρ' : Function.Injective ρ') {d : ℕ} (hV : Nat.card V = 2 ^ d) {P : Subgroup B}
    (hP : IsPGroup 2 P) : Nat.card P ^ 2 ≤ 2 ^ d := by
  classical
  obtain ⟨Q, hPQ⟩ := hP.exists_le_sylow
  have hPQc : Nat.card P ≤ Nat.card (Q : Subgroup B) := Subgroup.card_le_of_le hPQ
  have hBX : Nat.card B ∣ Nat.card X := Subgroup.card_dvd_of_surjective hπ
  rcases hB with ⟨n, hn, e⟩ | ⟨n, hn, e⟩ | ⟨n, hn, e⟩
  ·
    have hQ := ((CFSG.Open.bender_psl2_borel_full n hn).map_mulEquiv e.symm) Q
    have hQc : Nat.card (Q : Subgroup B) = (2 ^ n) ^ 1 := hQ.2.2.2.2
    have hd : 2 * n ≤ d := by
      by_cases hn3 : n = 3
      · subst hn3
        have := lemma27_psl2_eight (e.toMonoidHom.comp π)
          (e.surjective.comp hπ) ρ' hρ' hV
        omega
      · refine lemma27_psl2 hn hn3 ?_ ρ' hρ' hV
        have hcard : Nat.card B = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
          rw [Nat.card_congr e.toEquiv]
          exact CFSG.Walter.psl2_even_card (by omega)
        exact hcard ▸ hBX
    calc Nat.card P ^ 2 ≤ ((2 ^ n) ^ 1) ^ 2 := by
          rw [hQc] at hPQc; exact Nat.pow_le_pow_left hPQc 2
      _ = 2 ^ (2 * n) := by rw [pow_one, ← pow_mul, mul_comm]
      _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd
  ·
    have hmodel : SzModel n = CFSG.Open.Sz n := CFSG.Models.benderSzModel_eq_sz n
    let e' : B ≃* CFSG.Open.Sz n := e.trans (MulEquiv.subgroupCongr hmodel)
    have : Finite (CFSG.Open.Sz n) := Finite.of_equiv _ e'.toEquiv
    have hQ := ((CFSG.Open.bender_suzuki_borel_full n hn).map_mulEquiv e'.symm) Q
    have hQc : Nat.card (Q : Subgroup B) = (2 ^ (2 * n + 1)) ^ 2 := hQ.2.2.2.2
    have hd : 4 * (2 * n + 1) ≤ d :=
      lemma27_sz hn ((Nat.card_congr e'.toEquiv).symm ▸ hBX) ρ' hρ' hV
    calc Nat.card P ^ 2 ≤ ((2 ^ (2 * n + 1)) ^ 2) ^ 2 := by
          rw [hQc] at hPQc; exact Nat.pow_le_pow_left hPQc 2
      _ = 2 ^ (4 * (2 * n + 1)) := by rw [← pow_mul, ← pow_mul]; congr 1; ring
      _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd
  ·
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hmodel : PSU3Model n = CFSG.Open.PSU3 2 n := CFSG.Models.benderPSU3Model_eq_psu3 n
    let e' : B ≃* CFSG.Open.PSU3 2 n := e.trans (MulEquiv.subgroupCongr hmodel)
    have : Finite (CFSG.Open.PSU3 2 n) := Finite.of_equiv _ e'.toEquiv
    have hQ := ((CFSG.Open.bender_psu3_borel_full n hn).map_mulEquiv e'.symm) Q
    have hQc : Nat.card (Q : Subgroup B) = (2 ^ n) ^ 3 := hQ.2.2.2.2
    have hd : 6 * n ≤ d :=
      lemma27_psu3 hn ((Nat.card_congr e'.toEquiv).symm ▸ hBX) ρ' hρ' hV
    calc Nat.card P ^ 2 ≤ ((2 ^ n) ^ 3) ^ 2 := by
          rw [hQc] at hPQc; exact Nat.pow_le_pow_left hPQc 2
      _ = 2 ^ (6 * n) := by rw [← pow_mul, ← pow_mul]; congr 1; ring
      _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd


open CFSG.BenderSuzuki in
theorem false_of_bender {H : Type} [Group H] [Finite H] {V : Type}
    [Group V] [Finite V] (ρ : H →* MulAut V) {A R : Subgroup H} (hAR : A ≤ R)
    (hA : StrongWC A) (hρab : ¬ ∀ x ∈ R, ∀ y ∈ R, ρ x * ρ y = ρ y * ρ x)
    (hAZ : ∀ a ∈ A, (∀ r ∈ R, r * a = a * r) → a = 1)
    (hB : IsBenderGroup (↥R ⧸ Subgroup.center ↥R)) {d : ℕ} (hV : Nat.card V = 2 ^ d)
    (hlt : Nat.card V < Nat.card A ^ 2) : False := by
  classical
  let ρR : ↥R →* MulAut V := ρ.comp R.subtype
  let Z : Subgroup ↥R := Subgroup.center ↥R
  have hfin : Finite (↥R ⧸ Z) := inferInstance
  have hsimple : IsSimpleGroup (↥R ⧸ Z) :=
    CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.isSimpleGroup hB
  have hKZ : ρR.ker ≤ Z := by
    by_contra hnot
    have hnorm : (ρR.ker.map (QuotientGroup.mk' Z)).Normal :=
      Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective Z)
    have htop : ρR.ker.map (QuotientGroup.mk' Z) = ⊤ := by
      rcases hnorm.eq_bot_or_eq_top with h | h
      · exfalso
        apply hnot
        intro k hk
        have : QuotientGroup.mk' Z k ∈ ρR.ker.map (QuotientGroup.mk' Z) := ⟨k, hk, rfl⟩
        rw [h] at this
        exact (QuotientGroup.eq_one_iff k).1 (by simpa using this)
      · exact h
    have hrep : ∀ r : ↥R, ∃ z ∈ Z, ρR r = ρR z := by
      intro r
      have : QuotientGroup.mk' Z r ∈ ρR.ker.map (QuotientGroup.mk' Z) := by
        rw [htop]; exact Subgroup.mem_top _
      obtain ⟨k, hk, hkr⟩ := this
      refine ⟨k⁻¹ * r, QuotientGroup.eq.1 hkr, ?_⟩
      rw [map_mul, map_inv, MonoidHom.mem_ker.1 hk, inv_one, one_mul]
    apply hρab
    intro x hx y hy
    obtain ⟨z, hz, hxz⟩ := hrep ⟨x, hx⟩
    obtain ⟨z', hz', hyz⟩ := hrep ⟨y, hy⟩
    have e1 : ρ x = ρR z := hxz
    have e2 : ρ y = ρR z' := hyz
    rw [e1, e2, ← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hz' z).symm]
  let X := ↥R ⧸ ρR.ker
  let ρ' : X →* MulAut V := QuotientGroup.kerLift ρR
  have hρ' : Function.Injective ρ' := QuotientGroup.kerLift_injective ρR
  let π : X →* ↥R ⧸ Z := QuotientGroup.map ρR.ker Z (MonoidHom.id ↥R) hKZ
  have hπ : Function.Surjective π := by
    intro b
    obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨QuotientGroup.mk r, rfl⟩
  let φ : ↥A →* ↥R ⧸ Z := (QuotientGroup.mk' Z).comp (Subgroup.inclusion hAR)
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 : (Subgroup.inclusion hAR a : ↥R) ∈ Z := (QuotientGroup.eq_one_iff _).1 ha
    have h2 : (a : H) = 1 := hAZ a a.2 fun r hr => by
      have := Subgroup.mem_center_iff.1 h1 ⟨r, hr⟩
      exact congrArg Subtype.val this
    exact Subtype.ext h2
  have hP2 : IsPGroup 2 φ.range := by
    have hA2 : IsPGroup 2 ↥A := isPGroup_two_of_isElemAbelian hA.1
    exact hA2.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have hcard : Nat.card φ.range = Nat.card A :=
    (Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv).symm
  have hsq := sq_card_le_of_bender hB π hπ ρ' hρ' hV hP2
  rw [hcard, ← hV] at hsq
  omega

end Bender



section Main

variable {H : Type} [Group H] [Finite H]

theorem exists_mem_classD_not_mem {A : Subgroup H} {g : H} (hg : conjSubgroup g A ≠ A) :
    ∃ a ∈ classD A, a ∉ A ∧ a ∈ conjSubgroup g A := by
  by_contra h
  push Not at h
  refine hg (conjSubgroup_eq_of_le fun x hx => ?_)
  by_cases hx1 : x = 1
  · exact hx1 ▸ A.one_mem
  · have hxA : g⁻¹ * x * g ∈ A := mem_conjSubgroup.1 hx
    have hxD : x ∈ classD A :=
      ⟨g⁻¹, g⁻¹ * x * g, hxA, fun h1 => hx1 (by
        have : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
        rw [this, h1]; group), by group⟩
    by_contra hxA
    exact h x hxD hxA hx

theorem normal_of_strongly_closed (hAsc : AschbacherNoPolarInput)
    {V : Type} [Group V] [Finite V] (ρ : H →* MulAut V) {A : Subgroup H} (hA : StrongWC A)
    (h4 : 4 ≤ Nat.card A) (hρ : ∀ a ∈ A, ρ a = 1 → a = 1) {d : ℕ} (hV : Nat.card V = 2 ^ d)
    (hlt : Nat.card V < Nat.card A ^ 2) : ∀ g : H, conjSubgroup g A = A := by
  classical
  by_contra hnot
  push Not at hnot
  obtain ⟨g, hg⟩ := hnot
  obtain ⟨a, haD, haA, haC⟩ := exists_mem_classD_not_mem hg
  set R : Subgroup H := Subgroup.normalClosure (A : Set H) with hR
  have hAR : A ≤ R := Subgroup.le_normalClosure
  have haR : a ∈ R := conjSubgroup_le_normalClosure A g haC
  have haa : a * a = 1 := classD_mul_self hA haD
  by_cases hab : ∀ x ∈ R, ∀ y ∈ R, ρ x * ρ y = ρ y * ρ x
  ·
    have := card_le_two_of_comm_mem hA haD haA (N := ρ.ker)
      (fun x hx hxk => hρ x hx (MonoidHom.mem_ker.1 hxk)) (fun t ht _ => by
        rw [MonoidHom.mem_ker, map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.2 (hab a haR t (hAR ht)))
    omega
  · rcases lemma25 hAsc hA with hZ | hB
    ·
      let O : Subgroup H := (fusionOddCore ↥R).map R.subtype
      have hOodd : Odd (Nat.card O) := by
        rw [Subgroup.card_map_of_injective R.subtype_injective]
        exact odd_card_fusionOddCore ↥R
      have := card_le_two_of_comm_mem hA haD haA (N := O) (fun x hx hxO => by
        by_contra hx1
        have hxx : x * x = 1 := elemAbelian_mul_self hA.1 hx
        have h2 : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact hxx) hx1
        have hdvd : orderOf (⟨x, hxO⟩ : O) ∣ Nat.card O := orderOf_dvd_natCard _
        rw [Subgroup.orderOf_mk, h2] at hdvd
        obtain ⟨m, hm⟩ := hOodd
        omega) (fun t ht ht1 => by
        have hx : (⟨a, haR⟩ : ↥R) ∈ fusionZStar ↥R := by
          have h : fusionZStar ↥R = ⊤ := hZ
          rw [h]; exact Subgroup.mem_top _
        have hmem := mem_fusionZStar_iff.1 hx ⟨t, hAR ht⟩
        refine ⟨_, hmem, ?_⟩
        have htt : t * t = 1 := elemAbelian_mul_self hA.1 ht
        show (t * a)⁻¹ * (a * t) = ⁅a, t⁆
        rw [commutatorElement_def, mul_inv_rev, elemAbelian_inv hA.1 ht,
          inv_eq_of_mul_eq_one_right haa]
        simp only [mul_assoc])
      omega
    ·
      have hAZ : ∀ a₀ ∈ A, (∀ r ∈ R, r * a₀ = a₀ * r) → a₀ = 1 := by
        intro a₀ ha₀ hc
        by_contra ha₀1
        refine hg (conjSubgroup_eq_of_le fun x hx => ?_)
        by_cases hx1 : x = 1
        · exact hx1 ▸ A.one_mem
        · have hxD : x ∈ classD A := by
            have hxA : g⁻¹ * x * g ∈ A := mem_conjSubgroup.1 hx
            refine ⟨g⁻¹, g⁻¹ * x * g, hxA, fun h1 => hx1 (by
              have : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
              rw [this, h1]; group), by group⟩
          exact commute_classD_le hA ha₀ ha₀1 hxD (hc x (conjSubgroup_le_normalClosure A g hx))
      exact false_of_bender ρ hAR hA hab hAZ hB hV hlt

end Main

end CFSG.CGT.T75M
