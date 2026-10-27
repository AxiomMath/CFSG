module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6Four

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54Ns CFSG.HardMathSupport.Dickson.I271
  CFSG.LieType.Seitz CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier CFSG.Blueprint.Multiplier
open scoped commutatorElement


namespace Gen2318Lift

theorem exists_twoElem_lift {K : Type*} [Group K] [Finite K] (Z : Subgroup K) [Z.Normal]
    (s : K ⧸ Z) (hs : ∃ j : ℕ, s ^ (2 ^ j) = 1) :
    ∃ k : K, (k : K ⧸ Z) = s ∧ ∃ j : ℕ, k ^ (2 ^ j) = 1 := by
  obtain ⟨k₀, rfl⟩ := QuotientGroup.mk_surjective s
  obtain ⟨j, hj⟩ := hs
  have hn : 0 < orderOf k₀ := orderOf_pos k₀
  obtain ⟨a, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd hn.ne'
  have hsn : (k₀ : K ⧸ Z) ^ (orderOf k₀) = 1 := by
    rw [← QuotientGroup.mk_pow, pow_orderOf_eq_one, QuotientGroup.mk_one]
  have hsa : (k₀ : K ⧸ Z) ^ (2 ^ a) = 1 := by
    have h1 : orderOf (k₀ : K ⧸ Z) ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hj
    obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
    have h2 : orderOf (k₀ : K ⧸ Z) ∣ 2 ^ a * m := hnm ▸ orderOf_dvd_of_pow_eq_one hsn
    rw [hb] at h2
    have hcop : Nat.Coprime (2 ^ b) m :=
      Nat.Coprime.pow_left b (Nat.coprime_two_left.2 hm)
    have h3 : 2 ^ b ∣ 2 ^ a := hcop.dvd_of_dvd_mul_right h2
    rw [← orderOf_dvd_iff_pow_eq_one, hb]
    exact h3
  have hcop : Nat.Coprime (2 ^ a) m := Nat.Coprime.pow_left a (Nat.coprime_two_left.2 hm)
  obtain ⟨e, he1, he2⟩ := Nat.chineseRemainder hcop 1 0
  obtain ⟨w, hw⟩ : m ∣ e := (Nat.modEq_zero_iff_dvd.1 he2)
  refine ⟨k₀ ^ e, ?_, a, ?_⟩
  · rw [QuotientGroup.mk_pow, pow_eq_pow_mod e hsa, he1, ← pow_eq_pow_mod 1 hsa, pow_one]
  · rw [← pow_mul, hw, show m * w * 2 ^ a = orderOf k₀ * w by rw [hnm]; ring, pow_mul,
      pow_orderOf_eq_one, one_pow]

theorem twoElem_unique {K : Type*} [Group K] [Finite K]
    (hodd : Odd (Nat.card (Subgroup.center K))) {k k' : K} (hk : ∃ j : ℕ, k ^ (2 ^ j) = 1)
    (hk' : ∃ j : ℕ, k' ^ (2 ^ j) = 1) (h : (k : K ⧸ Subgroup.center K) = k') : k = k' := by
  obtain ⟨j, hj⟩ := hk
  obtain ⟨j', hj'⟩ := hk'
  have hz : k⁻¹ * k' ∈ Subgroup.center K := QuotientGroup.eq.1 h
  have hkz : Commute k (k⁻¹ * k') := Subgroup.mem_center_iff.1 hz k
  have hcomm : Commute k⁻¹ k' := by
    have h1 : k' = k * (k⁻¹ * k') := by group
    rw [h1]
    exact (Commute.inv_left (Commute.refl k)).mul_right (Commute.inv_left hkz)
  set M := j + j' with hM
  have hkM : k ^ (2 ^ M) = 1 := by
    have : 2 ^ M = 2 ^ j * 2 ^ j' := by rw [hM, pow_add]
    rw [this, pow_mul, hj, one_pow]
  have hk'M : k' ^ (2 ^ M) = 1 := by
    have : 2 ^ M = 2 ^ j' * 2 ^ j := by rw [hM, pow_add, mul_comm]
    rw [this, pow_mul, hj', one_pow]
  have hzM : (k⁻¹ * k') ^ (2 ^ M) = 1 := by
    rw [hcomm.mul_pow, inv_pow, hkM, hk'M]
    simp
  have hord : orderOf (k⁻¹ * k') = 1 := by
    have h1 : orderOf (k⁻¹ * k') ∣ 2 ^ M := orderOf_dvd_of_pow_eq_one hzM
    have h2 : orderOf (k⁻¹ * k') ∣ Nat.card (Subgroup.center K) := by
      have := orderOf_dvd_natCard (⟨k⁻¹ * k', hz⟩ : Subgroup.center K)
      rwa [Subgroup.orderOf_mk] at this
    have hcop : Nat.Coprime (2 ^ M) (Nat.card (Subgroup.center K)) :=
      Nat.Coprime.pow_left M (Nat.coprime_two_left.2 hodd)
    exact Nat.Coprime.eq_one_of_dvd (hcop.coprime_dvd_left h1) h2
  have h1 : k⁻¹ * k' = 1 := orderOf_eq_one_iff.1 hord
  calc k = k * (k⁻¹ * k') := by rw [h1, mul_one]
    _ = k' := by group

section Closure

variable {X : Type} [Group X] [Finite X]

theorem le_gammaPrime_of_fixed2 {B K : Subgroup X} (hperf : commutator ↥K = ⊤)
    (hodd : Odd (Nat.card (Subgroup.center ↥K)))
    (Fam : Set (Subgroup (MulAut (↥K ⧸ Subgroup.center ↥K))))
    (hFam : ∀ P ∈ Fam, 4 ≤ CFSG.Open.pRank 3 (actPre B K P))
    (hgen : Subgroup.closure {s : ↥K ⧸ Subgroup.center ↥K |
      (∃ P ∈ Fam, ∀ e ∈ P, e s = s) ∧ ∃ j : ℕ, s ^ (2 ^ j) = 1} = ⊤) :
    K ≤ gammaPrimeIn 3 4 B K := by
  set Γ : Subgroup X := gammaPrimeIn 3 4 B K with hΓ
  set Γ₀ : Subgroup ↥K := Γ.subgroupOf K with hΓ₀
  set S : Set (↥K ⧸ Subgroup.center ↥K) :=
    {s | (∃ P ∈ Fam, ∀ e ∈ P, e s = s) ∧ ∃ j : ℕ, s ^ (2 ^ j) = 1} with hS
  have hlift : ∀ s ∈ S, ∃ k ∈ Γ₀, (QuotientGroup.mk k : ↥K ⧸ Subgroup.center ↥K) = s := by
    rintro s ⟨⟨P, hP, hs⟩, hs2⟩
    obtain ⟨k, rfl, j', hk⟩ := exists_twoElem_lift (Subgroup.center ↥K) s hs2
    refine ⟨k, ?_, rfl⟩
    show (k : X) ∈ Γ
    have hcent : (k : X) ∈ Subgroup.centralizer (actPre B K P : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      obtain ⟨hqN, hqB, hqP⟩ := mem_actPre.1 hq
      set k' : ↥K := K.normalizerMonoidHom ⟨q, hqN⟩ k with hk'
      have h1 : (QuotientGroup.mk k' : ↥K ⧸ Subgroup.center ↥K) = QuotientGroup.mk k := by
        have := hs _ hqP
        rwa [actHom_mk] at this
      have h2 : ∃ j : ℕ, k' ^ (2 ^ j) = 1 := ⟨j', by rw [hk', ← map_pow, hk, map_one]⟩
      have h3 : k' = k := twoElem_unique hodd h2 ⟨j', hk⟩ h1
      have h4 : (k' : X) = q * (k : X) * q⁻¹ := coe_normalizerMonoidHom K ⟨q, hqN⟩ k
      have h5 : q * (k : X) * q⁻¹ = (k : X) := by rw [← h4, h3]
      calc q * (k : X) = q * (k : X) * q⁻¹ * q := by group
        _ = (k : X) * q := by rw [h5]
    have hle : K ⊓ Subgroup.centralizer (actPre B K P : Set X) ≤ Γ :=
      le_iSup₂_of_le (f := fun (E : Subgroup X) (_ : E ≤ B ∧ 4 ≤ CFSG.Open.pRank 3 E) =>
        K ⊓ Subgroup.centralizer (E : Set X)) (actPre B K P) ⟨actPre_le_left, hFam P hP⟩ le_rfl
    exact hle ⟨k.2, hcent⟩
  have hle : Subgroup.closure S ≤ Γ₀.map (QuotientGroup.mk' (Subgroup.center ↥K)) := by
    rw [Subgroup.closure_le]
    intro s hs
    obtain ⟨k, hk, rfl⟩ := hlift s hs
    exact ⟨k, hk, rfl⟩
  have hsup : Γ₀ ⊔ Subgroup.center ↥K = ⊤ := by
    rw [eq_top_iff]
    intro g _
    have hg : (QuotientGroup.mk g : ↥K ⧸ Subgroup.center ↥K) ∈ Subgroup.closure S := by
      rw [hgen]; exact Subgroup.mem_top _
    obtain ⟨γ, hγ, hγg⟩ := hle hg
    have hz : γ⁻¹ * g ∈ Subgroup.center ↥K := QuotientGroup.eq.1 hγg
    have : g = γ * (γ⁻¹ * g) := by group
    rw [this]
    exact Subgroup.mul_mem_sup hγ hz
  have htop : Γ₀ = ⊤ := eq_top_of_sup_center_eq_top hperf hsup
  intro x hx
  have : (⟨x, hx⟩ : ↥K) ∈ Γ₀ := by rw [htop]; exact Subgroup.mem_top _
  exact this

end Closure

section Seitz

variable {X : Type} [Group X] [Finite X]

theorem closure_fixed2_eq_top_of_seitz {S : Type} [Group S] {E : Subgroup (MulAut S)}
    (Fam : Set (Subgroup (MulAut S))) (hFam : ∀ F, F ≤ E ∧ F.relIndex E = 3 → F ∈ Fam)
    (h : (⨆ (F : Subgroup (MulAut S)) (_ : F ≤ E ∧ F.relIndex E = 3),
      CFSG.GH74.GLS.oPrimeResidualOf 2 (fixedPoints F)) = ⊤) :
    Subgroup.closure {s : S | (∃ P ∈ Fam, ∀ e ∈ P, e s = s) ∧ ∃ j : ℕ, s ^ (2 ^ j) = 1} = ⊤ := by
  rw [eq_top_iff, ← h]
  refine iSup₂_le fun F hF => ?_
  unfold CFSG.GH74.GLS.oPrimeResidualOf CFSG.GH74.GLS.oPrimeResidual
  rw [MonoidHom.map_closure]
  apply Subgroup.closure_mono
  rintro _ ⟨x, ⟨k, hk⟩, rfl⟩
  refine ⟨⟨F, hFam F hF, fun e he => ?_⟩, k, ?_⟩
  · exact mem_fixedPoints.1 x.2 e he
  · exact congrArg Subtype.val hk

theorem le_gammaPrime_of_seitz (hSeitz : Seitz2313Even) {B K : Subgroup X}
    (hperf : commutator ↥K = ⊤) (hBel : IsElemAbelian 3 B)
    (hodd : Odd (Nat.card (Subgroup.center ↥K))) {d : TauCeti.ValidLieTypeIndex}
    (hs : Seitz2313Cover.EvenScope d.1)
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* (TauCeti.CFSGIndex.lie d).Group)
    {E₀ : Subgroup (MulAut (↥K ⧸ Subgroup.center ↥K))} (hE₀ : E₀ ≤ autImage B K)
    (hEel : IsElemAbelian 3 E₀) {m : ℕ} (hm : Nat.card E₀ = 3 ^ m) (hm1 : 1 ≤ m)
    (hc : 4 ≤ CFSG.Open.pRank 3 (B ⊓ Subgroup.centralizer (K : Set X)) + (m - 1))
    (hU : ∃ U : Subgroup (↥K ⧸ Subgroup.center ↥K), U ≠ ⊥ ∧ IsPGroup 2 ↥U ∧
      ∀ φ ∈ E₀, ∀ u ∈ U, φ u ∈ U) :
    K ≤ gammaPrimeIn 3 4 B K := by
  have hE0 : E₀ ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hm
    have := Nat.one_lt_pow (by omega : m ≠ 0) (by norm_num : 1 < 3)
    omega
  have hgenS := hSeitz 3 Nat.prime_three (by norm_num) _ d ⟨e⟩ hs E₀ hEel hE0 hU
  refine le_gammaPrime_of_fixed2 hperf hodd {F | F ≤ E₀ ∧ F.relIndex E₀ = 3} ?_ ?_
  · rintro F ⟨hFE, hFi⟩
    have h1 := Subgroup.relIndex_mul_card F E₀
    rw [inf_of_le_left hFE, hFi, hm] at h1
    have hFcard : Nat.card F = 3 ^ (m - 1) := by
      have h3 : 3 * Nat.card F = 3 * 3 ^ (m - 1) := by
        rw [h1, ← pow_succ']
        congr 1
        omega
      exact Nat.eq_of_mul_eq_mul_left (by norm_num) h3
    rw [pRank_actPre Nat.prime_three hBel hperf (hFE.trans hE₀) hFcard]
    exact hc
  · exact closure_fixed2_eq_top_of_seitz _ (fun F hF => hF) hgenS

end Seitz

section Center

theorem odd_center_gen2318 (hGA : CFSG.Open.GriessAllModelsStatement) {Y : Type} [Group Y] [Finite Y]
    (hq : CFSG.Open.IsQuasisimple Y) (hQ : IsLieQuot Y Gen2318Index) :
    Odd (Nat.card (Subgroup.center Y)) := by
  obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := hQ
  have hq' := isQuasisimple_of_open_aux hq
  have key : ∀ {t : StatedLieTag} {n f : ℕ},
      CFSG.Models.LieModel (TauCeti.CFSGIndex.lie ⟨d, hv⟩).Group t n 2 f →
      Odd ((genericOrders t n 2 f).1 * (genericOrders t n 2 f).2 *
        ((exceptionalOrders t n 2 f).1 * (exceptionalOrders t n 2 f).2)) →
      Odd (Nat.card (Subgroup.center Y)) := fun hm hodd =>
    Odd.of_dvd_nat hodd (center_dvd_table hGA hq' e hm)
  cases d with
  | A r q =>
    obtain ⟨⟨hq2, hqe⟩, n, hn2, hrn⟩ := hd
    have hm := CFSG.Models.lieModel_A r q hv (MulEquiv.refl (TauCeti.CFSGIndex.lie ⟨.A r q, hv⟩).Group)
    rw [hq2, hqe] at hm
    have h9 : 9 ≤ r + 1 := by
      rw [hrn]
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    refine key hm ?_
    have hex : exceptionalOrders .PSL (r + 1) 2 2 = (1, 1) := by
      unfold exceptionalOrders
      split <;> first | rfl | (exfalso; omega)
    rw [hex]
    have hg1 : (genericOrders .PSL (r + 1) 2 2).1 = Nat.gcd (r + 1) 3 := by simp [genericOrders]
    have hg2 : (genericOrders .PSL (r + 1) 2 2).2 = 1 := by simp [genericOrders]
    rw [hg1, hg2]
    simpa using Odd.of_dvd_nat (by decide : Odd 3) (Nat.gcd_dvd_right (r + 1) 3)
  | twistedA r q =>
    obtain ⟨hq13, n, hn3, hrn⟩ := hd
    have hm := CFSG.Models.lieModel_twistedA r q hv
      (MulEquiv.refl (TauCeti.CFSGIndex.lie ⟨.twistedA r q, hv⟩).Group)
    have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA r q, hv⟩ = q.p := by
      simp [TauCeti.ValidLieTypeIndex.characteristic]
    have hf : TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA r q, hv⟩ = q.exponent := by
      simp [TauCeti.ValidLieTypeIndex.fieldExponent]
    rw [hc, hf] at hm
    have h9 : 9 ≤ r + 1 := by omega
    rcases hq13 with ⟨hq2, hqe⟩ | ⟨hq2, hqe⟩
    · rw [hq2, hqe] at hm
      refine key hm ?_
      have hex : exceptionalOrders .PSU (r + 1) 2 1 = (1, 1) := by
        unfold exceptionalOrders
        split <;> first | rfl | (exfalso; omega)
      rw [hex]
      have hg1 : (genericOrders .PSU (r + 1) 2 1).1 = Nat.gcd (r + 1) 3 := by simp [genericOrders]
      have hg2 : (genericOrders .PSU (r + 1) 2 1).2 = 1 := by simp [genericOrders]
      rw [hg1, hg2]
      simpa using Odd.of_dvd_nat (by decide : Odd 3) (Nat.gcd_dvd_right (r + 1) 3)
    · rw [hq2, hqe] at hm
      refine key hm ?_
      have hex : exceptionalOrders .PSU (r + 1) 2 3 = (1, 1) := by
        unfold exceptionalOrders
        split <;> first | rfl | (exfalso; omega)
      rw [hex]
      have hg1 : (genericOrders .PSU (r + 1) 2 3).1 = Nat.gcd (r + 1) 9 := by simp [genericOrders]
      have hg2 : (genericOrders .PSU (r + 1) 2 3).2 = 1 := by simp [genericOrders]
      rw [hg1, hg2]
      simpa using Odd.of_dvd_nat (by decide : Odd 9) (Nat.gcd_dvd_right (r + 1) 9)
  | F4 q =>
    obtain ⟨hq2, hqe⟩ := hd
    have hm := CFSG.Models.lieModel_of_namesTag (t := .F4) (p := q.p) (f := q.exponent)
      ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.F4 q, hv⟩ ⟨rfl, rfl⟩
      (MulEquiv.refl (TauCeti.CFSGIndex.lie ⟨.F4 q, hv⟩).Group)
    rw [hq2, hqe] at hm
    exact key hm (by decide)
  | E6 q =>
    have hm := CFSG.Models.lieModel_of_namesTag (t := .E6) (p := q.p) (f := q.exponent)
      ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.E6 q, hv⟩ ⟨rfl, rfl⟩
      (MulEquiv.refl (TauCeti.CFSGIndex.lie ⟨.E6 q, hv⟩).Group)
    rcases hd with ⟨hq2, hqe⟩ | ⟨hq2, hqe⟩ | ⟨hq2, hqe⟩ <;> rw [hq2, hqe] at hm <;>
      exact key hm (by decide)
  | E7 q =>
    have hm := CFSG.Models.lieModel_of_namesTag (t := .E7) (p := q.p) (f := q.exponent)
      ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.E7 q, hv⟩ ⟨rfl, rfl⟩
      (MulEquiv.refl (TauCeti.CFSGIndex.lie ⟨.E7 q, hv⟩).Group)
    rcases hd with ⟨hq2, hqe⟩ | ⟨hq2, hqe⟩ <;> rw [hq2, hqe] at hm <;>
      exact key hm (by decide)
  | E8 q =>
    have hm := CFSG.Models.lieModel_of_namesTag (t := .E8) (p := q.p) (f := q.exponent)
      ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.E8 q, hv⟩ ⟨rfl, rfl⟩
      (MulEquiv.refl (TauCeti.CFSGIndex.lie ⟨.E8 q, hv⟩).Group)
    rcases hd with ⟨hq2, hqe⟩ | ⟨hq2, hqe⟩ | ⟨hq2, hqe⟩ <;> rw [hq2, hqe] at hm <;>
      exact key hm (by decide)
  | B r q => exact hd.elim
  | C r q => exact hd.elim
  | D r q => exact hd.elim
  | twistedD r q => exact hd.elim
  | G2 q => exact hd.elim
  | twistedE6 q => exact hd.elim
  | trialityD4 q => exact hd.elim
  | suzuki m => exact hd.elim
  | reeG2 m => exact hd.elim
  | reeF4 m => exact hd.elim
  | tits => exact hd.elim

end Center

end Gen2318Lift

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
