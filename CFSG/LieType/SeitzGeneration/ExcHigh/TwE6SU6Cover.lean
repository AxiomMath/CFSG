module

public import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6SU6Y
public import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6SU6FromM
public import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6SU6Theta
public import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6TwoD4
public import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6SU6Unitary

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHigh

open scoped MatrixGroups

open CFSG.LieType.Chevalley.E6GraphLevi CFSG.Timmesfeld Matrix CFSG.LieType.Chevalley
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Open CFSG.LieType.SeitzGeneration.ExcHigh.TwSU6
  CFSG.LocalAnalysis.ComponentInitial

theorem not_dvd_card_ker_sl2_coprod {G U k : Type} [Field k] [Finite k] [Group G] [Group U]
    [Finite U] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (φ : SL(2, k) →* G)
    (hφ : Function.Injective φ) (Φ : U →* G) (hcomm : ∀ A u, Commute (φ A) (Φ u))
    (hU : ∀ u : U, Φ u = 1 → u ^ p = 1 → u = 1) :
    ¬ p ∣ Nat.card (φ.noncommCoprod Φ hcomm).ker := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  intro hd
  haveI : Finite (φ.noncommCoprod Φ hcomm).ker := inferInstance
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hd
  obtain ⟨⟨a, u⟩, hxk⟩ := x
  have hxk' : φ a * Φ u = 1 := hxk
  have hxp : (a, u) ^ p = 1 := by
    have := pow_orderOf_eq_one (⟨(a, u), hxk⟩ : (φ.noncommCoprod Φ hcomm).ker)
    rw [hx] at this
    exact congrArg Subtype.val this
  have hap : a ^ p = 1 := congrArg Prod.fst hxp
  have hup : u ^ p = 1 := congrArg Prod.snd hxp
  have hacent : a ∈ Subgroup.center SL(2, k) := by
    rw [Subgroup.mem_center_iff]
    intro b
    have h1 : φ a = (Φ u)⁻¹ := eq_inv_of_mul_eq_one_left hxk'
    have h2 : Commute (φ b) (φ a) := by
      rw [h1]
      exact (hcomm b u).inv_right
    apply hφ
    rw [map_mul, map_mul]
    exact h2.eq
  obtain ⟨r, hr, hra⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hacent
  simp only [Fintype.card_fin] at hr
  have ha2 : a * a = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, ← hra, ← map_mul, ← pow_two, hr, map_one,
      Matrix.SpecialLinearGroup.coe_one]
  have ha1 : a = 1 := by
    have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).2 (by omega)
    have hd2 : orderOf a ∣ Nat.gcd 2 p :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one (by rwa [pow_two])) (orderOf_dvd_of_pow_eq_one hap)
    rw [hcop] at hd2
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 hd2)
  have hΦu : Φ u = 1 := by
    rw [ha1, map_one, one_mul] at hxk'
    exact hxk'
  have hu1 : u = 1 := hU u hΦu hup
  have hx1 : (⟨(a, u), hxk⟩ : (φ.noncommCoprod Φ hcomm).ker) = 1 :=
    Subtype.ext (Prod.ext ha1 hu1)
  rw [hx1, orderOf_one] at hx
  exact hp.one_lt.ne hx

section Main


theorem twE6SU6Cover : TwE6SU6Cover := by
  intro K _ _ σ ℓ f hℓ hf hK hσ p hpF hp7 hpq
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hK' : Nat.card K = ℓ ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  have hU : UnitaryFieldData ℓ f K := ⟨hℓ, hf, hK'⟩
  haveI : CharP K ℓ := hU.charP
  set σ' : K →+* K := σ.toRingHom with hσ'def
  have hσ' : ∀ c, σ' c = c ^ (ℓ ^ f) := hσ
  have hσσ : ∀ c, σ' (σ' c) = c := fun c => by
    rw [hσ', hσ']
    exact CFSG.LieType.Simplicity.pow_pow_card_sq hK c
  obtain ⟨c0, hc0⟩ := hU.exists_bar_ne
  have hbar : hU.bar c0 = σ' c0 := by rw [hU.bar_apply, hσ']
  have hε0 : c0 - σ' c0 ≠ 0 := sub_ne_zero.2 (fun h => hc0 (by rw [hbar]; exact h.symm))
  have hε : σ' (c0 - σ' c0) = -(c0 - σ' c0) := by rw [map_sub, hσσ]; ring
  obtain ⟨Ψ, hΨ⟩ := exists_isPsiTw σ' hσσ hε0 hε hℓ (by omega : 1 ≤ 2 * f) hK'
  have hperf : Group.IsPerfect (unitarySL σ') := isPerfect_unitarySL_gen hK hσ'
  have hC0 : (unitarySL σ').map Ψ ≤ graphFixedRootGroup TwistTag.E6 K σ' :=
    map_unitarySL_le_graphFixedRootGroup hΨ σ.surjective hperf
  have hM := orbitRankOneGroup_le_map hΨ hσσ hε0 hε
  let ΨU : unitarySL σ' →* ↥(graphFixedRootGroup TwistTag.E6 K σ') :=
    (Ψ.comp (unitarySL σ').subtype).codRestrict _ fun B => hC0 ⟨B, B.2, rfl⟩
  have hcomm : ∀ (A : SL(2, RingHom.eqLocusField σ' (RingHom.id K))) (B : unitarySL σ'),
      Commute (frameHom σ' 3 A) (ΨU B) := by
    intro A B
    apply Subtype.ext
    exact commute_frameHom_three σ' A (hΨ.range_le ⟨(B : SL(6, K)), rfl⟩)
  have hpq1 : ¬ p ∣ ℓ ^ f := fun hd =>
    hpF.out.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right hd).mp hpq))
  refine ⟨SL(2, RingHom.eqLocusField σ' (RingHom.id K)) × unitarySL σ', inferInstance,
    inferInstance, (frameHom σ' 3).noncommCoprod ΨU hcomm, ?_, ?_, ?_⟩
  ·
    refine not_dvd_card_ker_sl2_coprod hpF.out (by omega) (frameHom σ' 3)
      (frameHom_injective σ' 3) ΨU hcomm ?_
    intro B hB hBp
    have hΨB : Ψ (B : SL(6, K)) = 1 := congrArg Subtype.val hB
    obtain ⟨r, hr6, hrB⟩ := hΨ.scalar_of_eq_one _ hΨB
    have hB1 : (B : SL(6, K)) ^ p = 1 := congrArg Subtype.val hBp
    have h1 : (Matrix.scalar (Fin 6) (r ^ p) : Matrix (Fin 6) (Fin 6) K) = 1 := by
      rw [map_pow, ← hrB, ← Matrix.SpecialLinearGroup.coe_pow, hB1,
        Matrix.SpecialLinearGroup.coe_one]
    have hrp : r ^ p = 1 := by
      have := congrArg (fun M : Matrix (Fin 6) (Fin 6) K => M 0 0) h1
      simpa [Matrix.scalar_apply] using this
    have hr1 : r = 1 := by
      have hcop : Nat.Coprime 6 p := by
        rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hpF.out]
        intro hd
        have := Nat.le_of_dvd (by norm_num) hd
        omega
      have := pow_gcd_eq_one.2 ⟨hr6, hrp⟩
      rwa [hcop, pow_one] at this
    apply Subtype.ext
    apply Subtype.ext
    rw [hrB, hr1]
    simp
  ·
    intro F hF hc
    have hpk : ¬ p ∣ Nat.card (RingHom.eqLocusField σ' (RingHom.id K)) := by
      rw [CFSG.RankThree.Chevalley.card_eqLocusField_of_pow hℓ hf hK hσ']
      exact hpq1
    have hpk0 := natCast_ne_zero_of_not_dvd_card hpF.out hpk
    have hpℓ : p ≠ ℓ := fun h => hpq1 (by rw [h]; exact dvd_pow_self ℓ (by omega))
    refine closure_centralizers_prod_of_plane
      (fun F' hF' => card_le_of_isElemAbelian_specialLinear_two hpk0 hF')
      (fun F' hF' hc' => unitarySL_planeGen hK hf hσ' hpF.out (by omega) hpℓ ?_ F' hF' hc')
      F hF hc
    intro _ h2
    rw [h2] at hpq
    have := Nat.le_of_dvd (by norm_num) hpq
    omega
  ·
    have hYmem : ∀ y : ↥(graphFixedRootGroup TwistTag.E6 K σ'),
        (y : ModGL TwistTag.E6.tag K) ∈ (unitarySL σ').map Ψ →
          y ∈ ((frameHom σ' 3).noncommCoprod ΨU hcomm).range := by
      rintro y ⟨B, hB, hBy⟩
      refine ⟨(1, ⟨B, hB⟩), ?_⟩
      apply Subtype.ext
      rw [MonoidHom.noncommCoprod_apply]
      simp only [map_one, one_mul]
      exact hBy
    have hM0 := hM orb0 (by decide)
    have hM1 := hM orb1 (by decide)
    have hM2 := hM orbLeaf (by decide)
    unfold frameTorusGroup
    refine sup_le (sup_le ?_ ?_) ?_
    · refine iSup_le fun i => ?_
      rintro _ ⟨A, rfl⟩
      by_cases hi : i.val ≤ 2
      · exact hYmem _ (frameHom_mem_of_orbit hM0 hM1 hM2 i hi A)
      · have h3 : i = 3 := Fin.ext (by have h := i.2; have h3 : (3 : Fin 4).val = 3 := rfl; omega)
        subst h3
        exact ⟨(A, 1), by rw [MonoidHom.noncommCoprod_apply]; simp⟩
    · rintro _ ⟨pr, rfl⟩
      exact hYmem _ (by rw [coe_torusG]; exact torusAB_mem_of_orbit hM0 hM1 pr.1.2 pr.2.2)
    · intro y hy
      exact hYmem y ((sup_le (sup_le hM0 hM1) hM2) (Subgroup.mem_subgroupOf.1 hy))

end Main

section Final


theorem seitzExcHighTwE6TwoGeSeven : SeitzExcHighTwE6TwoGeSeven :=
  seitzExcHighTwE6TwoGeSeven_of_su6 twE6SU6Cover

end Final

end CFSG.LieType.SeitzGeneration.ExcHigh
