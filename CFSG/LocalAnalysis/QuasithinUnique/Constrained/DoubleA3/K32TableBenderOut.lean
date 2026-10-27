module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableBenderSyl
public import CFSG.GH74.Uniqueness.Bender.Out

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.GH74.Uniqueness.Bender

instance k32InnAutNormal (K : Type) [Group K] : (innAut K).Normal := innAut_normal K

variable {K : Type} [Group K] [Finite K]

omit [Finite K] in
theorem k32_benderType (hX : fusionIsBenderGroup K) : ∃ n i e, BenderType K n i e := by
  rcases hX with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
  · exact ⟨f, 1, 1, .linear f hf e⟩
  · have hmodel : CFSG.Theory.Comparator.PSU3Model f = CFSG.Open.PSU3 2 f :=
        CFSG.Models.benderPSU3Model_eq_psu3 f
    exact ⟨f, 3, _, .unitary f hf (e.trans (MulEquiv.subgroupCongr hmodel.symm))⟩
  · have hmodel : CFSG.Theory.Comparator.SzModel a = CFSG.Open.Sz a := CFSG.Models.benderSzModel_eq_sz a
    exact ⟨2 * a + 1, 2, 1, .suzuki a ha (e.trans (MulEquiv.subgroupCongr hmodel.symm))⟩

theorem k32_borel_of_benderType {n i e : ℕ} (hT : BenderType K n i e) :
    fusionBenderBorel K (2 ^ n) i := by
  cases hT with
  | linear n hn e =>
    have : Finite (CFSG.Theory.Comparator.PSL2Model n) := Finite.of_equiv K e.toEquiv
    exact (bender_psl2_borel_full n hn).map_mulEquiv e.symm
  | suzuki a ha e =>
    have hmodel : CFSG.Theory.Comparator.SzModel a = CFSG.Open.Sz a := CFSG.Models.benderSzModel_eq_sz a
    have e' : K ≃* CFSG.Open.Sz a := e.trans (MulEquiv.subgroupCongr hmodel)
    have : Finite (CFSG.Open.Sz a) := Finite.of_equiv K e'.toEquiv
    exact (bender_suzuki_borel_full a ha).map_mulEquiv e'.symm
  | unitary n hn e =>
    have hmodel : CFSG.Theory.Comparator.PSU3Model n = CFSG.Open.PSU3 2 n :=
        CFSG.Models.benderPSU3Model_eq_psu3 n
    have e' : K ≃* CFSG.Open.PSU3 2 n := e.trans (MulEquiv.subgroupCongr hmodel)
    have : Finite (CFSG.Open.PSU3 2 n) := Finite.of_equiv K e'.toEquiv
    exact (bender_psu3_borel_full n hn).map_mulEquiv e'.symm

theorem k32_out_cyclic_sylow {n i e : ℕ} (hT : BenderType K n i e) :
    ∀ S : Sylow 2 (MulAut K ⧸ innAut K), IsCyclic S := fun S => hT.isCyclic_sylow_outer S

omit [Finite K] in
theorem k32_out_linear {n : ℕ} (hT : BenderType K n 1 1) :
    IsCyclic (MulAut K ⧸ innAut K) ∧ Nat.card (MulAut K ⧸ innAut K) = n :=
  hT.outer_linear

theorem k32_card_sylow_inn
    (hX : fusionIsBenderGroup K) {n i e : ℕ} (hT : BenderType K n i e)
    {S : Subgroup (MulAut K)} (hS : IsSylowTwoOf S (innAut K)) :
    Nat.card S = (2 ^ n) ^ i := by
  obtain ⟨Q, hQ⟩ := k32_exists_sylow hX hS
  obtain ⟨-, -, -, hQcard⟩ :=
    CFSG.ComponentClassification.AschbacherToolkit.Bender.benderBorel_sylowCenter
      (k32_borel_of_benderType hT) Q
  rw [← hQ, Subgroup.card_map_of_injective (k32_conj_injective hX)]
  exact hQcard

theorem k32_psl2_abelian
    (hX : fusionIsBenderGroup K) {n : ℕ} (hT : BenderType K n 1 1)
    {S : Subgroup (MulAut K)} (hS : IsSylowTwoOf S (innAut K)) :
    ∀ s ∈ S, ∀ s' ∈ S, s * s' = s' * s := by
  obtain ⟨Q, hQ⟩ := k32_exists_sylow hX hS
  obtain ⟨t, hc⟩ := hT.exists_benderCore Q
  have hZ : rootCenter (Q : Subgroup K) = (Q : Subgroup K) := by
    refine Subgroup.eq_of_le_of_card_ge (rootCenter_le _) ?_
    rw [hc.card_center, hc.card_eq, pow_one]
  intro s hs s' hs'
  rw [← hQ] at hs hs'
  obtain ⟨a, ha, rfl⟩ := hs
  obtain ⟨b, hb, rfl⟩ := hs'
  have h : b * a = a * b := by
    have : a ∈ rootCenter (Q : Subgroup K) := by rw [hZ]; exact ha
    exact (mem_rootCenter_iff.mp this).2 b hb
  show MulAut.conj a * MulAut.conj b = MulAut.conj b * MulAut.conj a
  rw [← map_mul, ← map_mul, h]

theorem k32_psl2_fpf
    (hX : fusionIsBenderGroup K) {n : ℕ} (hT : BenderType K n 1 1)
    {S : Subgroup (MulAut K)} (hS : IsSylowTwoOf S (innAut K)) {c : MulAut K}
    (hcJ : c ∈ innAut K) (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1)
    (hcS : ∀ s ∈ S, c * s * c⁻¹ ∈ S) (hcS' : ∀ s ∈ S, c⁻¹ * s * c ∈ S) :
    S ⊓ Subgroup.centralizer ({c} : Set (MulAut K)) = ⊥ := by
  obtain ⟨Q, hQ⟩ := k32_exists_sylow hX hS
  have hinj := k32_conj_injective hX
  obtain ⟨t, hc⟩ := hT.exists_benderCore Q
  obtain ⟨k₀, rfl⟩ := hcJ
  have hQS : ∀ y : K, y ∈ (Q : Subgroup K) ↔ MulAut.conj y ∈ S := by
    intro y
    rw [← hQ]
    constructor
    · intro hy; exact ⟨y, hy, rfl⟩
    · rintro ⟨u, hu, hu'⟩
      rw [← hinj hu']
      exact hu
  have hk₀ : k₀ ∈ Subgroup.normalizer ((Q : Subgroup K) : Set K) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have e1 : MulAut.conj k₀ * MulAut.conj y * (MulAut.conj k₀)⁻¹ =
        MulAut.conj (k₀ * y * k₀⁻¹) := by
      simp [map_mul, map_inv]
    have e2 : (MulAut.conj k₀)⁻¹ * MulAut.conj (k₀ * y * k₀⁻¹) * MulAut.conj k₀ =
        MulAut.conj y := by
      rw [← map_inv MulAut.conj k₀, ← map_mul, ← map_mul]
      congr 1
      group
    rw [hQS, hQS]
    constructor
    · intro hy
      have := hcS _ hy
      rwa [e1] at this
    · intro hy
      have := hcS' _ hy
      rwa [e2] at this
  have hZ : rootCenter (Q : Subgroup K) = (Q : Subgroup K) := by
    refine Subgroup.eq_of_le_of_card_ge (rootCenter_le _) ?_
    rw [hc.card_center, hc.card_eq, pow_one]
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have hxS := hx.1
  obtain ⟨p, hp, rfl⟩ : ∃ p ∈ (Q : Subgroup K), MulAut.conj p = x := by
    rw [← hQ] at hxS
    obtain ⟨p, hp, hpx⟩ := hxS
    exact ⟨p, hp, hpx⟩
  by_contra hx1
  have hp1 : p ≠ 1 := fun h => hx1 (by rw [h, map_one])
  have hcomm : k₀ * p = p * k₀ := by
    apply hinj
    rw [map_mul, map_mul]
    exact (Subgroup.mem_centralizer_singleton_iff.mp hx.2).symm
  have hpZ : p ∈ rootCenter (Q : Subgroup K) := by rw [hZ]; exact hp
  have hp2 : p * p = 1 := hc.center_sq p hpZ
  have hcent := hc.centralizer_eq_of_e_one hpZ hp1
  have hk₀Q : k₀ ∈ (Q : Subgroup K) := by
    rw [← hcent]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm
  have hk3 : k₀ ^ 3 = 1 := by
    apply hinj
    rw [map_pow, map_one]
    exact hc3
  obtain ⟨m, hm⟩ := Q.isPGroup' ⟨k₀, hk₀Q⟩
  have hkm : k₀ ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have h1 : orderOf k₀ ∣ 3 := orderOf_dvd_of_pow_eq_one hk3
  have h2 : orderOf k₀ ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hkm
  have hcop : Nat.Coprime 3 (2 ^ m) := Nat.Coprime.pow_right _ (by norm_num)
  have : orderOf k₀ = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2
  rw [orderOf_eq_one_iff] at this
  exact hc1 (by rw [this, map_one])

end CFSG.QuasithinUnique.DoubleA3
