module

public import CFSG.ClassicalInvolution.Asc77.AscIH8Red
public import CFSG.ClassicalInvolution.Asc77.ModOApi

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ComponentClassification
open scoped commutatorElement MatrixGroups

section SL2Sub

variable {K : Type} [Group K] {F : Type} [Field F] [Finite F] {R : Subgroup K}

@[expose] noncomputable def sl2Inv (e : R ≃* SL(2, F)) : K := ((e.symm (-1) : R) : K)

omit [Finite F] in
theorem sl2Inv_mem (e : R ≃* SL(2, F)) : sl2Inv e ∈ R := (e.symm (-1)).2

theorem orderOf_sl2Inv (hodd : Odd (Nat.card F)) (e : R ≃* SL(2, F)) :
    orderOf (sl2Inv e) = 2 := by
  have h : orderOf (e.symm (-1)) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact sl2_orderOf_neg_one hodd
  rw [← h]
  exact Subgroup.orderOf_coe (e.symm (-1))

theorem sl2Inv_mul_self (hodd : Odd (Nat.card F)) (e : R ≃* SL(2, F)) :
    sl2Inv e * sl2Inv e = 1 := by
  rw [← pow_two, ← orderOf_sl2Inv hodd e]
  exact pow_orderOf_eq_one _

theorem sl2Inv_ne_one (hodd : Odd (Nat.card F)) (e : R ≃* SL(2, F)) : sl2Inv e ≠ 1 := by
  intro h
  have := orderOf_sl2Inv hodd e
  rw [h, orderOf_one] at this
  omega

theorem eq_sl2Inv_of_orderOf_eq_two (hodd : Odd (Nat.card F)) (e : R ≃* SL(2, F)) {x : K}
    (hx : x ∈ R) (h2 : orderOf x = 2) : x = sl2Inv e := by
  have h : orderOf (⟨x, hx⟩ : R) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact h2
  have := (orderOf_eq_two_iff_of_equiv_sl2 hodd e ⟨x, hx⟩).mp h
  exact congrArg Subtype.val this

omit [Finite F] in
theorem sl2Inv_commute (e : R ≃* SL(2, F)) {y : K} (hy : y ∈ R) :
    sl2Inv e * y = y * sl2Inv e := by
  have h : e.symm (-1) ∈ Subgroup.center R := by
    rw [mem_center_iff_of_equiv_sl2 e, e.apply_symm_apply]
    exact (mem_center_sl2_iff _).mpr (Or.inr rfl)
  have := Subgroup.mem_center_iff.mp h ⟨y, hy⟩
  exact congrArg Subtype.val this.symm

omit [Finite F] in
theorem eq_one_or_eq_sl2Inv_of_central (e : R ≃* SL(2, F)) {x : K} (hx : x ∈ R)
    (hc : ∀ y ∈ R, x * y = y * x) : x = 1 ∨ x = sl2Inv e := by
  have h : (⟨x, hx⟩ : R) ∈ Subgroup.center R := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hc g g.2).symm
  rw [mem_center_iff_of_equiv_sl2 e, mem_center_sl2_iff] at h
  rcases h with h | h
  · left
    have := congrArg e.symm h
    rw [map_one] at this
    simpa using congrArg Subtype.val this
  · right
    have := congrArg e.symm h
    exact congrArg Subtype.val (by simpa using this)

end SL2Sub

section Transfer

variable {K G : Type} [Group K] [Group G] {ψ : K →* G}

theorem ih8_perfect_conjSub {R : Subgroup K} (hR : R ≤ ⁅R, R⁆) (g : K) :
    conjSub g R ≤ ⁅conjSub g R, conjSub g R⁆ := by
  unfold conjSub
  rw [← Subgroup.map_commutator]
  exact Subgroup.map_mono hR

theorem ih8_mem_normalizer_of_conjSub_eq {H : Subgroup K} {g : K} (h : conjSub g H = H) :
    g ∈ Subgroup.normalizer (H : Set K) := by
  have h' : conjSub g⁻¹ H = H := by
    conv_lhs => rw [← h]
    exact conjSub_inv_conjSub g H
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have := conj_mem_conjSub (n := g) hy
    rwa [h] at this
  · intro hy
    have := conj_mem_conjSub (n := g⁻¹) hy
    rw [h'] at this
    simpa [mul_assoc] using this

theorem ih8_mem_normalizer_of_map (hker : ψ.ker ≤ Subgroup.center K) {R : Subgroup K}
    (hR : R ≤ ⁅R, R⁆) {g : K}
    (hg : ψ g ∈ Subgroup.normalizer ((R.map ψ : Subgroup G) : Set G)) :
    g ∈ Subgroup.normalizer (R : Set K) := by
  apply ih8_mem_normalizer_of_conjSub_eq
  apply ih8_eq_of_map_eq ψ hker (ih8_perfect_conjSub hR g) hR
  rw [show Subgroup.map ψ (conjSub g R) = conjSub (ψ g) (R.map ψ) from
    map_conj_eq_conjSub_map ψ g R]
  exact conjSub_eq_of_mem_normalizer hg

theorem ih8_pGroup_lift {S : Subgroup K} {A : Subgroup G} (hA : IsPGroup 2 A)
    (hker : ∀ x ∈ S, x ∈ ψ.ker → x * x = 1) : IsPGroup 2 ↥(S ⊓ A.comap ψ) := by
  intro g
  have hgA : ψ g.1 ∈ A := g.2.2
  obtain ⟨k, hk⟩ := hA ⟨ψ g.1, hgA⟩
  have hk' : (ψ g.1) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  refine ⟨k + 1, ?_⟩
  apply Subtype.ext
  have hmem : g.1 ^ 2 ^ k ∈ S := S.pow_mem g.2.1 _
  have hker' : g.1 ^ 2 ^ k ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_pow]
    exact hk'
  have := hker _ hmem hker'
  show g.1 ^ 2 ^ (k + 1) = 1
  rw [pow_succ, pow_mul, pow_two]
  exact this

theorem ih8_nonabelian_lift {S : Subgroup K} {A : Subgroup G} (hAS : A ≤ S.map ψ)
    (hnc : ∃ x ∈ A, ∃ y ∈ A, x * y ≠ y * x) :
    ∃ x ∈ S ⊓ A.comap ψ, ∃ y ∈ S ⊓ A.comap ψ, x * y ≠ y * x := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hnc
  obtain ⟨x', hx'S, rfl⟩ := hAS hx
  obtain ⟨y', hy'S, rfl⟩ := hAS hy
  refine ⟨x', ⟨hx'S, hx⟩, y', ⟨hy'S, hy⟩, fun h => hxy ?_⟩
  rw [← map_mul, ← map_mul, h]

end Transfer

section Exact

variable {K G : Type} [Group K] [Group G] [Finite G]

theorem ih8_oddCoreOf_map_eq_bot (ψ : K →* G) {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (h4 : 4 ≤ Nat.card F) {R : Subgroup K} (e : R ≃* SL(2, F))
    (hinv : ∃ y ∈ R.map ψ, orderOf y = 2) : oddCoreOf (R.map ψ) = ⊥ := by
  obtain ⟨y, hy, hy2⟩ := hinv
  set K' := R.map ψ with hK'
  let φ : ↥R →* ↥K' := ψ.subgroupMap R
  have hφ : Function.Surjective φ := ψ.subgroupMap_surjective R
  set N := classicalInvolutionOddCore ↥K' with hN
  have hNodd : Odd (Nat.card N) := OddCore.odd_card ↥K'
  have hnorm : (N.comap φ).Normal := inferInstance
  have hback : (N.comap φ).map φ = N := Subgroup.map_comap_eq_self_of_surjective hφ N
  suffices hNbot : N = ⊥ by
    unfold oddCoreOf
    rw [← hN, hNbot, Subgroup.map_bot]
  rcases normal_cases_of_equiv_sl2 h4 e _ hnorm with h | h | h
  · rw [← hback, h, Subgroup.map_bot]
  · have hdvd : Nat.card N ∣ Nat.card (Subgroup.center R) := by
      rw [← hback, h]
      exact Subgroup.card_dvd_of_surjective (f := φ.subgroupMap (Subgroup.center R))
        (φ.subgroupMap_surjective _)
    rw [natCard_center_of_equiv_sl2 hodd e] at hdvd
    have h1 : Nat.card N = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
      · exact h1
      · rw [h1] at hNodd
        exact absurd hNodd (by decide)
    exact Subgroup.card_eq_one.mp h1
  · exfalso
    have hNtop : N = ⊤ := by rw [← hback, h, Subgroup.map_top, MonoidHom.range_eq_top.mpr hφ]
    rw [hNtop, Subgroup.card_top] at hNodd
    have hy' : orderOf (⟨y, hy⟩ : ↥K') = 2 := by
      rw [Subgroup.orderOf_mk]
      exact hy2
    have h2 : 2 ∣ Nat.card ↥K' := hy' ▸ orderOf_dvd_natCard _
    exact (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr h2)

end Exact

section GroupLevel

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem ih8_twin_data {K : Type} [Group K] (hΩ : HypOmegaMod p f Ω) {ψ : K →* G}
    (hker : ψ.ker ≤ Subgroup.center K) {R R' : Subgroup K} (hR : R ≤ ⁅R, R⁆)
    (hK : R.map ψ ∈ Ω) (hL : R'.map ψ ∈ Ω) (hne : R.map ψ ≠ R'.map ψ) {z : G}
    (hzK : IsUniqueInvolution (R.map ψ) z) (hzL : IsUniqueInvolution (R'.map ψ) z)
    (hex : oddCoreOf (R.map ψ) = ⊥) :
    Commutes R R' ∧ ∃ x ∈ R, ∃ x' ∈ R', ψ x = z ∧ ψ x' = z ∧ x' ≠ 1 ∧
      x' * x⁻¹ ∈ Subgroup.center K := by
  have hc := hΩ.comm_le_oddCore_of_twin hK hL hne hzK hzL
  rw [hex, bot_inf_eq, le_bot_iff] at hc
  have hcomm : Commutes (R.map ψ) (R'.map ψ) := by
    intro a ha b hb
    have : ⁅a, b⁆ ∈ ⁅R.map ψ, R'.map ψ⁆ := Subgroup.commutator_mem_commutator ha hb
    rw [hc, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this
  refine ⟨ih8_commutes_of_commutes_map ψ hker hR hcomm, ?_⟩
  obtain ⟨x, hx, hxz⟩ := hzK.mem
  obtain ⟨x', hx', hx'z⟩ := hzL.mem
  refine ⟨x, hx, x', hx', hxz, hx'z, ?_, ?_⟩
  · intro h
    apply hzK.ne_one
    rw [← hx'z, h, map_one]
  · apply hker
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxz, hx'z, mul_inv_cancel]

theorem ih8_nbr_sylow (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω) {K J : Subgroup G}
    (hJ : J ∈ omegaNbr Ω K) :
    ∃ A : Subgroup G, IsPGroup 2 A ∧ A ≤ J ∧ A ≤ Subgroup.normalizer (K : Set G) ∧
      ∃ x ∈ A, ∃ y ∈ A, x * y ≠ y * x := by
  obtain ⟨-, -, A, hA, hAJ, hAN⟩ := hJ
  have hA' := hA
  obtain ⟨M, -, P, rfl⟩ := hA
  exact ⟨_, P.isPGroup'.map _, hAJ, hAN, (hΩ.isQuatSub_of_mem_RSet hp hA').exists_not_commute⟩

end GroupLevel

section NbrModel

variable {K G : Type} [Group K] [Group G]

theorem ih8_nbr_model (ψ : K →* G) (hker : ψ.ker ≤ Subgroup.center K) {F₁ F₂ : Type} [Field F₁]
    [Finite F₁] [Field F₂] [Finite F₂] (hodd₁ : Odd (Nat.card F₁)) (hodd₂ : Odd (Nat.card F₂))
    {R S : Subgroup K} (hR : R ≤ ⁅R, R⁆) (eR : R ≃* SL(2, F₁)) (eS : S ≃* SL(2, F₂))
    {A : Subgroup G} (hA2 : IsPGroup 2 A) (hAS : A ≤ S.map ψ)
    (hnc : ∃ x ∈ A, ∃ y ∈ A, x * y ≠ y * x)
    (hAN : A ≤ Subgroup.normalizer ((R.map ψ : Subgroup G) : Set G)) :
    ∃ T : Subgroup K, T ≤ S ∧ IsPGroup 2 T ∧ (∃ x ∈ T, ∃ y ∈ T, x * y ≠ y * x) ∧
      T ≤ Subgroup.normalizer (R : Set K) ∧ sl2Inv eS ∈ T ∧
      sl2Inv eS * sl2Inv eR = sl2Inv eR * sl2Inv eS := by
  set T := S ⊓ A.comap ψ with hT
  have hTS : T ≤ S := inf_le_left
  have hTn : T ≤ Subgroup.normalizer (R : Set K) := by
    intro g hg
    exact ih8_mem_normalizer_of_map hker hR (hAN hg.2)
  have hker2 : ∀ x ∈ S, x ∈ ψ.ker → x * x = 1 := by
    intro x hxS hxk
    have hc := Subgroup.mem_center_iff.mp (hker hxk)
    rcases eq_one_or_eq_sl2Inv_of_central eS hxS (fun y _ => (hc y).symm) with h | h
    · rw [h, mul_one]
    · rw [h]
      exact sl2Inv_mul_self hodd₂ eS
  have hT2 : IsPGroup 2 ↥T := ih8_pGroup_lift hA2 hker2
  obtain ⟨a, ha, b, hb, hab⟩ := ih8_nonabelian_lift hAS hnc
  have hne : ∃ g ∈ T, g ≠ 1 := by
    by_cases ha1 : a = 1
    · refine ⟨b, hb, fun hb1 => hab ?_⟩
      rw [ha1, hb1]
    · exact ⟨a, ha, ha1⟩
  obtain ⟨g, hgT, hg1⟩ := hne
  have hinv : ∃ w ∈ T, orderOf w = 2 := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hT2) ⟨g, hgT⟩
    have h1 : orderOf g = 2 ^ k := by
      rw [← hk, Subgroup.orderOf_mk]
    have hk1 : 1 ≤ k := by
      by_contra h0
      have hk0 : k = 0 := by omega
      rw [hk0, pow_zero, orderOf_eq_one_iff] at h1
      exact hg1 h1
    refine ⟨g ^ 2 ^ (k - 1), T.pow_mem hgT _, ?_⟩
    have hdvd : 2 ^ (k - 1) ∣ orderOf g := by
      rw [h1]
      exact pow_dvd_pow 2 (Nat.sub_le k 1)
    have h2 := orderOf_pow_of_dvd (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0)) hdvd
    rw [h1, Nat.pow_div (Nat.sub_le k 1) (by norm_num)] at h2
    rw [h2]
    have h3 : k - (k - 1) = 1 := by omega
    rw [h3, pow_one]
  obtain ⟨w, hwT, hw2⟩ := hinv
  have hwz : w = sl2Inv eS := eq_sl2Inv_of_orderOf_eq_two hodd₂ eS (hTS hwT) hw2
  have hzT : sl2Inv eS ∈ T := hwz ▸ hwT
  have hzN : sl2Inv eS ∈ Subgroup.normalizer (R : Set K) := hTn hzT
  have hRz : sl2Inv eR ∈ R := sl2Inv_mem eR
  have hconj : sl2Inv eS * sl2Inv eR * (sl2Inv eS)⁻¹ ∈ R :=
    (Subgroup.mem_normalizer_iff.mp hzN _).mp hRz
  have hord : orderOf (sl2Inv eS * sl2Inv eR * (sl2Inv eS)⁻¹) = 2 := by
    have := MulEquiv.orderOf_eq (MulAut.conj (sl2Inv eS)) (sl2Inv eR)
    rw [MulAut.conj_apply] at this
    rw [this]
    exact orderOf_sl2Inv hodd₁ eR
  have hcomm := eq_sl2Inv_of_orderOf_eq_two hodd₁ eR hconj hord
  refine ⟨T, hTS, hT2, ⟨a, ha, b, hb, hab⟩, hTn, hzT, ?_⟩
  calc sl2Inv eS * sl2Inv eR = (sl2Inv eS * sl2Inv eR * (sl2Inv eS)⁻¹) * sl2Inv eS := by group
    _ = sl2Inv eR * sl2Inv eS := by rw [hcomm]

end NbrModel

end CFSG.ClassicalInvolution.Asc77
