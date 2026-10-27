module

public import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6SU6Cover

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHigh.TwFive

open scoped MatrixGroups

open CFSG.LieType.Chevalley.E6GraphLevi CFSG.Timmesfeld Matrix CFSG.LieType.Chevalley
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Open CFSG.LieType.SeitzGeneration.ExcHigh.TwSU6
  CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.SeitzGeneration.ExcHigh

section SU6


theorem twE6SU6Cover_five (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (ℓ f : ℕ)
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (p : ℕ) [hpF : Fact p.Prime] (hp5 : 5 ≤ p) (hpq : p ∣ ℓ ^ f + 1) :
    ∃ ψ : SL(2, RingHom.eqLocusField σ.toRingHom (RingHom.id K)) × unitarySL σ.toRingHom →*
        ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      ¬ p ∣ Nat.card ψ.ker ∧
      (∀ F : Subgroup (SL(2, RingHom.eqLocusField σ.toRingHom (RingHom.id K)) ×
          unitarySL σ.toRingHom), IsElemAbelian p F → Nat.card F = p ^ 2 →
        Subgroup.closure {h | ∃ x ∈ F, x ≠ 1 ∧ Commute h x} = ⊤) ∧
      frameTorusGroup σ.toRingHom ⊔ leviRootGroups σ.toRingHom ≤ ψ.range := by
  classical
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
  refine ⟨(frameHom σ' 3).noncommCoprod ΨU hcomm, ?_, ?_, ?_⟩
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
        have h6 := Nat.le_of_dvd (by norm_num) hd
        interval_cases p
        · omega
        · exact absurd hpF.out (by norm_num)
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

end SU6

section D4

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.ModelFacts.OrthAut CFSG.HardMathSupport.Lang.AnisoF4
  CFSG.LieType.SeitzGeneration CFSG.ClassicalInvolution.WeakCT TauCeti CFSG.RankThree.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Classical
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


theorem twE6D4Cover_five (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (ℓ f : ℕ)
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (p : ℕ) [hpF : Fact p.Prime] (hp5 : 5 ≤ p) (hpq : p ∣ ℓ ^ f + 1) :
    PlaneCoverOf p (frameTorusGroup σ.toRingHom ⊔ centerRootGroup σ.toRingHom) := by
  classical
  have hσ' : ∀ c, σ.toRingHom c = c ^ (ℓ ^ f) := hσ
  have hkcard : Nat.card (RingHom.eqLocusField σ.toRingHom (RingHom.id K)) = ℓ ^ f :=
    CFSG.RankThree.Chevalley.card_eqLocusField_of_pow hℓ hf hK hσ'
  obtain ⟨Ψ, hΨker, hΨrange⟩ := exists_psi_d4 hℓ hf σ.toRingHom hkcard
  have hq2 : 2 ≤ ℓ ^ f := Nat.one_lt_pow (by omega) hℓ.one_lt
  have hpk : ¬ p ∣ Nat.card (RingHom.eqLocusField σ.toRingHom (RingHom.id K)) := by
    rw [hkcard]
    intro h
    have h1 : p ∣ ℓ ^ f + 1 - ℓ ^ f := Nat.dvd_sub hpq h
    rw [show ℓ ^ f + 1 - ℓ ^ f = 1 by omega] at h1
    exact hpF.out.one_lt.ne' (Nat.dvd_one.1 h1)
  have hpq1 : ¬ p ∣ Nat.card (RingHom.eqLocusField σ.toRingHom (RingHom.id K)) - 1 := by
    rw [hkcard]
    intro h
    have h1 : p ∣ ℓ ^ f + 1 - (ℓ ^ f - 1) := Nat.dvd_sub hpq h
    rw [show ℓ ^ f + 1 - (ℓ ^ f - 1) = 2 by omega] at h1
    have := Nat.le_of_dvd (by norm_num) h1
    omega
  haveI := finite_spinPlus_four (RingHom.eqLocusField σ.toRingHom (RingHom.id K))
  have hcen := not_dvd_card_center_spinPlus_four hpF.out (by omega) hpq1
  have hcomm : ∀ (t : ↥(normOne σ.toRingHom) × ↥(normOne σ.toRingHom))
      (x : spinGroup (Spin.quadPlus 4 (RingHom.eqLocusField σ.toRingHom (RingHom.id K)))),
      Commute (torusG σ.toRingHom t) (Ψ x) := fun t x => by
    have hmem : Ψ x ∈ d4Group σ.toRingHom := by
      rw [d4Group, ← hΨrange]
      exact ⟨x, rfl⟩
    exact torusG_commute_d4Group σ.toRingHom t (Ψ x) hmem
  let ψ := MonoidHom.noncommCoprod (torusG σ.toRingHom) Ψ hcomm
  have hdr : d4Group σ.toRingHom ≤ ψ.range := by
    rw [d4Group, ← hΨrange]
    rintro _ ⟨x, rfl⟩
    refine ⟨(1, x), ?_⟩
    change torusG σ.toRingHom 1 * Ψ x = Ψ x
    rw [map_one, one_mul]
  have htr : (torusG σ.toRingHom).range ≤ ψ.range := by
    rintro _ ⟨t, rfl⟩
    refine ⟨(t, 1), ?_⟩
    change torusG σ.toRingHom t * Ψ 1 = torusG σ.toRingHom t
    rw [map_one, mul_one]
  refine ⟨_, inferInstance, inferInstance, ψ, ?_, ?_, ?_⟩
  · exact not_dvd_card_ker_noncommCoprod_tw hpF.out _ _ hcomm
      (not_dvd_card_ker_torusG σ.toRingHom hpF.out (by omega)) hΨker hcen
  · intro F hF hc
    exact closure_centralizers_prod_of_abelian_plane (fun F hF hc =>
      closure_centralizers_spinPlus_plane hpF.out (by omega) hpk hpq1 (by norm_num) F hF hc) F hF hc
  · refine sup_le (sup_le (iSup_le fun i => ?_) htr) ?_
    · fin_cases i
      · exact (le_iSup (fun i => (d4Rho σ.toRingHom i).range) 0).trans hdr
      · exact (le_iSup (fun i => (d4Rho σ.toRingHom i).range) 2).trans hdr
      · exact (le_iSup (fun i => (d4Rho σ.toRingHom i).range) 3).trans hdr
      · exact (frameHom_three_le_d4Group σ.toRingHom).trans hdr
    · rintro y hy
      have hy' : (y : ModGL TwistTag.E6.tag K) ∈ orbitRankOneGroup TwistTag.E6 K σ.toRingHom
          ⟨3, by decide⟩ := hy
      obtain ⟨A, hA⟩ := orbitRankOneGroup_le_range_rankOneFix σ.toRingHom orbCenter
        orbCenter_card hy'
      have hyeq : y = centerHom σ.toRingHom A := Subtype.ext hA.symm
      rw [hyeq]
      exact hdr (Subgroup.mem_iSup_of_mem 1 ⟨A, rfl⟩)

end D4

end CFSG.LieType.SeitzGeneration.ExcHigh.TwFive
