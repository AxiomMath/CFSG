module

public import CFSG.LocalAnalysis.QuasithinUnique.BenderBranchBasic
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.ConfinedInvolution

public section

namespace CFSG.QuasithinUnique.Unc25G2

open CFSG.Open
open scoped commutatorElement

section TwoElements

variable {G : Type*} [Group G]

theorem exists_pow_two_pow_eq_one_of_odd_trivial [Finite G] {y : G}
    (h : ∀ j : ℕ, Odd (orderOf (y ^ j)) → y ^ j = 1) : ∃ k : ℕ, y ^ 2 ^ k = 1 := by
  have hn : orderOf y ≠ 0 := (orderOf_pos y).ne'
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd hn
  refine ⟨k, h _ ?_⟩
  have h1 : orderOf (y ^ 2 ^ k) = orderOf y / Nat.gcd (orderOf y) (2 ^ k) :=
    orderOf_pow' y (pow_ne_zero _ two_ne_zero)
  have h2 : Nat.gcd (orderOf y) (2 ^ k) = 2 ^ k := by
    rw [hkm]
    exact Nat.gcd_eq_right (Dvd.intro _ rfl)
  rw [h1, h2, hkm]
  rw [Nat.mul_div_cancel_left _ (by positivity)]
  exact hm

theorem exists_pow_two_pow_eq_one_mul {a b : G} (hab : a * b = b * a) {i j : ℕ}
    (ha : a ^ 2 ^ i = 1) (hb : b ^ 2 ^ j = 1) : ∃ k : ℕ, (a * b) ^ 2 ^ k = 1 := by
  refine ⟨i + j, ?_⟩
  have hc : Commute a b := hab
  rw [hc.mul_pow]
  have h1 : a ^ 2 ^ (i + j) = 1 := by
    rw [pow_add, pow_mul, ha, one_pow]
  have h2 : b ^ 2 ^ (i + j) = 1 := by
    rw [add_comm, pow_add, pow_mul, hb, one_pow]
  rw [h1, h2, one_mul]

@[expose] def CentreTwo (L : Subgroup G) : Prop :=
  ∀ y ∈ L, (∀ w ∈ L, w * y = y * w) → ∃ k : ℕ, y ^ 2 ^ k = 1

theorem CentreTwo.conjugate {L : Subgroup G} (h : CentreTwo L) (g : G) :
    CentreTwo (CFSG.conjugate L g) := by
  intro y hy hyc
  have hy' : g * y * g⁻¹ ∈ L := BenderBranch.mem_conjugate_iff.mp hy
  have hc : ∀ w ∈ L, w * (g * y * g⁻¹) = (g * y * g⁻¹) * w := by
    intro w hw
    have hw' : g⁻¹ * w * g ∈ CFSG.conjugate L g := by
      rw [BenderBranch.mem_conjugate_iff]
      simpa [mul_assoc] using hw
    have := hyc _ hw'
    calc w * (g * y * g⁻¹) = g * ((g⁻¹ * w * g) * y) * g⁻¹ := by group
      _ = g * (y * (g⁻¹ * w * g)) * g⁻¹ := by rw [this]
      _ = (g * y * g⁻¹) * w := by group
  obtain ⟨k, hk⟩ := h _ hy' hc
  refine ⟨k, ?_⟩
  have : g * y ^ 2 ^ k * g⁻¹ = 1 := by
    rw [← conj_pow]
    exact hk
  calc y ^ 2 ^ k = g⁻¹ * (g * y ^ 2 ^ k * g⁻¹) * g := by group
    _ = 1 := by rw [this]; group

end TwoElements

section Sylow

variable {G : Type*} [Group G] [Finite G]

theorem mem_of_isSylowTwoOf_of_normalizes {P C : Subgroup G} (hP : IsSylowTwoOf P C)
    (hn : C ≤ Subgroup.normalizer (P : Set G)) {w : G} (hwC : w ∈ C)
    (hw : ∃ k : ℕ, w ^ 2 ^ k = 1) : w ∈ P := by
  have h2 : IsPGroup 2 (Subgroup.zpowers w) := by
    obtain ⟨k, hk⟩ := hw
    have hdvd : orderOf w ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    obtain ⟨n, -, hn⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact IsPGroup.of_card (n := n) (by rw [Nat.card_zpowers, hn])
  obtain ⟨Q, hwQ, hQ⟩ := exists_isSylowTwoOf_of_le (Subgroup.zpowers_le.mpr hwC) h2
  obtain ⟨h, hh, hQeq⟩ := hP.exists_conj hQ
  have hPeq : P.map (MulAut.conj h).toMonoidHom = P := by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (hn hh) y).mp hy
    · intro x hx
      refine ⟨h⁻¹ * x * h, ?_, by simp [MulAut.conj_apply]; group⟩
      have := (Subgroup.mem_normalizer_iff.mp (hn (C.inv_mem hh)) x).mp hx
      simpa using this
  rw [hPeq] at hQeq
  have hwQ' : w ∈ Q := hwQ (Subgroup.mem_zpowers w)
  rwa [hQeq] at hwQ'

end Sylow

section Rank

variable {G : Type*} [Group G] [Finite G]

theorem exists_elemAbelian_card_cube_of_commuting {p : ℕ} (hp : p.Prime) {L₁ L₂ L₃ : Subgroup G}
    (h₁₂ : ⁅L₁, L₂⁆ = ⊥) (h₁₃ : ⁅L₁, L₃⁆ = ⊥) (h₂₃ : ⁅L₂, L₃⁆ = ⊥)
    (hZ₁ : ∀ x ∈ L₁, (∀ y ∈ L₁, y * x = x * y) → x ^ p = 1 → x = 1)
    (hZ₂ : ∀ x ∈ L₂, (∀ y ∈ L₂, y * x = x * y) → x ^ p = 1 → x = 1)
    (hd₁ : p ∣ Nat.card L₁) (hd₂ : p ∣ Nat.card L₂) (hd₃ : p ∣ Nat.card L₃) :
    ∃ E : Subgroup G, E ≤ L₁ ⊔ L₂ ⊔ L₃ ∧ CFSG.Assembly.IsElemAbelian p E ∧
      Nat.card E = p ^ 3 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x₁, hx₁⟩ := exists_prime_orderOf_dvd_card' p hd₁
  obtain ⟨x₂, hx₂⟩ := exists_prime_orderOf_dvd_card' p hd₂
  obtain ⟨x₃, hx₃⟩ := exists_prime_orderOf_dvd_card' p hd₃
  set a₁ : G := (x₁ : G) with ha₁
  set a₂ : G := (x₂ : G) with ha₂
  set a₃ : G := (x₃ : G) with ha₃
  have ho₁ : orderOf a₁ = p := (Subgroup.orderOf_coe x₁).trans hx₁
  have ho₂ : orderOf a₂ = p := (Subgroup.orderOf_coe x₂).trans hx₂
  have ho₃ : orderOf a₃ = p := (Subgroup.orderOf_coe x₃).trans hx₃
  have hP₁ : Subgroup.zpowers a₁ ≤ L₁ := Subgroup.zpowers_le.mpr x₁.2
  have hP₂ : Subgroup.zpowers a₂ ≤ L₂ := Subgroup.zpowers_le.mpr x₂.2
  have hP₃ : Subgroup.zpowers a₃ ≤ L₃ := Subgroup.zpowers_le.mpr x₃.2
  have c₁₂ : ∀ x ∈ Subgroup.zpowers a₁, ∀ y ∈ Subgroup.zpowers a₂, x * y = y * x :=
    fun x hx y hy => BenderBranch.commute_of_commutator_eq_bot h₁₂ (hP₁ hx) (hP₂ hy)
  have c₁₃ : ∀ x ∈ Subgroup.zpowers a₁, ∀ y ∈ Subgroup.zpowers a₃, x * y = y * x :=
    fun x hx y hy => BenderBranch.commute_of_commutator_eq_bot h₁₃ (hP₁ hx) (hP₃ hy)
  have c₂₃ : ∀ x ∈ Subgroup.zpowers a₂, ∀ y ∈ Subgroup.zpowers a₃, x * y = y * x :=
    fun x hx y hy => BenderBranch.commute_of_commutator_eq_bot h₂₃ (hP₂ hx) (hP₃ hy)
  let φ₁₂ : Subgroup.zpowers a₁ × Subgroup.zpowers a₂ →* G :=
    (Subgroup.zpowers a₁).subtype.noncommCoprod (Subgroup.zpowers a₂).subtype
      (fun x y => c₁₂ x x.2 y y.2)
  have hφ₁₂ : ∀ q : Subgroup.zpowers a₁ × Subgroup.zpowers a₂, φ₁₂ q = (q.1 : G) * (q.2 : G) :=
    fun q => rfl
  let φ : (Subgroup.zpowers a₁ × Subgroup.zpowers a₂) × Subgroup.zpowers a₃ →* G :=
    φ₁₂.noncommCoprod (Subgroup.zpowers a₃).subtype (fun x z => by
      show φ₁₂ x * (z : G) = (z : G) * φ₁₂ x
      rw [hφ₁₂]
      calc (x.1 : G) * x.2 * z = x.1 * (x.2 * z) := by rw [mul_assoc]
        _ = x.1 * (z * x.2) := by rw [c₂₃ _ x.2.2 _ z.2]
        _ = (x.1 * z) * x.2 := by rw [mul_assoc]
        _ = (z * x.1) * x.2 := by rw [c₁₃ _ x.1.2 _ z.2]
        _ = z * (x.1 * x.2) := by rw [mul_assoc])
  have hφ : ∀ q : (Subgroup.zpowers a₁ × Subgroup.zpowers a₂) × Subgroup.zpowers a₃,
      φ q = (q.1.1 : G) * (q.1.2 : G) * (q.2 : G) := fun q => rfl
  have hc1 : Nat.card (Subgroup.zpowers a₁) = p := by rw [Nat.card_zpowers, ho₁]
  have hc2 : Nat.card (Subgroup.zpowers a₂) = p := by rw [Nat.card_zpowers, ho₂]
  have hc3 : Nat.card (Subgroup.zpowers a₃) = p := by rw [Nat.card_zpowers, ho₃]
  have hpow₁ : ∀ a : Subgroup.zpowers a₁, ((a : G)) ^ p = 1 := by
    intro a
    have := (pow_card_eq_one' : a ^ Nat.card (Subgroup.zpowers a₁) = 1)
    rw [hc1] at this
    exact congrArg Subtype.val this
  have hpow₂ : ∀ a : Subgroup.zpowers a₂, ((a : G)) ^ p = 1 := by
    intro a
    have := (pow_card_eq_one' : a ^ Nat.card (Subgroup.zpowers a₂) = 1)
    rw [hc2] at this
    exact congrArg Subtype.val this
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨⟨a, b⟩, c⟩ hq
    rw [hφ] at hq
    simp only at hq
    have hcb : ∀ y ∈ L₁, y * ((b : G) * c) = ((b : G) * c) * y := by
      intro y hy
      have hb : y * b = b * y := BenderBranch.commute_of_commutator_eq_bot h₁₂ hy (hP₂ b.2)
      have hc : y * c = c * y := BenderBranch.commute_of_commutator_eq_bot h₁₃ hy (hP₃ c.2)
      calc y * (b * c) = (y * b) * c := by rw [mul_assoc]
        _ = (b * y) * c := by rw [hb]
        _ = b * (y * c) := by rw [mul_assoc]
        _ = b * (c * y) := by rw [hc]
        _ = (b * c) * y := by rw [mul_assoc]
    have ha : (a : G) = 1 := by
      apply hZ₁ _ (hP₁ a.2)
      · intro y hy
        have hbc := hcb y hy
        have h1 : (a : G) = ((b : G) * c)⁻¹ := by
          apply eq_inv_of_mul_eq_one_left
          rwa [mul_assoc] at hq
        rw [h1]
        exact ((show Commute y ((b : G) * c) from hbc).inv_right).eq
      · exact hpow₁ a
    have hbc1 : (b : G) * c = 1 := by
      rw [ha, one_mul] at hq
      exact hq
    have hb : (b : G) = 1 := by
      apply hZ₂ _ (hP₂ b.2)
      · intro y hy
        have hc : y * c = c * y := BenderBranch.commute_of_commutator_eq_bot h₂₃ hy (hP₃ c.2)
        have h1 : (b : G) = (c : G)⁻¹ := eq_inv_of_mul_eq_one_left hbc1
        rw [h1]
        exact ((show Commute y (c : G) from hc).inv_right).eq
      · exact hpow₂ b
    have hc1' : (c : G) = 1 := by
      rw [hb, one_mul] at hbc1
      exact hbc1
    exact Prod.ext (Prod.ext (Subtype.ext ha) (Subtype.ext hb)) (Subtype.ext hc1')
  refine ⟨φ.range, ?_, ⟨inferInstance, ?_⟩, ?_⟩
  · rintro _ ⟨q, rfl⟩
    rw [hφ]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.mem_sup_left (Subgroup.mem_sup_left (hP₁ q.1.1.2)))
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right (hP₂ q.1.2.2))))
      (Subgroup.mem_sup_right (hP₃ q.2.2))
  · rintro _ ⟨q, rfl⟩
    rw [← map_pow]
    have : q ^ p = 1 := by
      refine Prod.ext (Prod.ext ?_ ?_) ?_
      · have := (pow_card_eq_one' : q.1.1 ^ Nat.card (Subgroup.zpowers a₁) = 1)
        rwa [hc1] at this
      · have := (pow_card_eq_one' : q.1.2 ^ Nat.card (Subgroup.zpowers a₂) = 1)
        rwa [hc2] at this
      · have := (pow_card_eq_one' : q.2 ^ Nat.card (Subgroup.zpowers a₃) = 1)
        rwa [hc3] at this
    rw [this, map_one]
  · have h1 : Nat.card ((Subgroup.zpowers a₁ × Subgroup.zpowers a₂) × Subgroup.zpowers a₃) =
        Nat.card φ.range := Nat.card_congr (Equiv.ofInjective φ hinj)
    rw [← h1, Nat.card_prod, Nat.card_prod, hc1, hc2, hc3]
    ring

end Rank

theorem false_of_isElemAbelian_card_cube {G : Type} [Group G] [Finite G]
    (he : CFSG.Assembly.evenRank G ≤ 2) {H E : Subgroup G} (hH : pCoreOf 2 H ≠ ⊥) (hEH : E ≤ H)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hE : CFSG.Assembly.IsElemAbelian p E)
    (hcard : Nat.card E = p ^ 3) : False := by
  have hloc : CFSG.Assembly.IsTwoLocal (Subgroup.normalizer (pCoreOf 2 H : Set G)) :=
    ⟨pCoreOf 2 H, hH, CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H, rfl⟩
  have hle : E ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    hEH.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H)
  have hrank : 3 ≤ CFSG.Assembly.pRank p (Subgroup.normalizer (pCoreOf 2 H : Set G)) := by
    unfold CFSG.Assembly.pRank
    apply le_csSup
    · refine ⟨Nat.card G, ?_⟩
      rintro k ⟨E', _, _, hk⟩
      calc k ≤ p ^ k := (Nat.lt_pow_self hp.one_lt).le
        _ = Nat.card E' := hk.symm
        _ ≤ Nat.card G := Subgroup.card_le_card_group E'
    · exact ⟨E, hle, hE, hcard⟩
  have h3 : CFSG.Assembly.pRank p (Subgroup.normalizer (pCoreOf 2 H : Set G)) ≤
      CFSG.Assembly.evenRank G :=
    CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank p hp hp2 _ hloc
  omega

section Components

variable {G : Type*} [Group G]

theorem isComponentIn_conjugate {K H : Subgroup G} (hK : IsComponentIn K H) {g : G} (hg : g ∈ H) :
    IsComponentIn (CFSG.conjugate K g) H := by
  have h := BenderBranch.isComponentIn_map (MulAut.conj g⁻¹) hK
  rw [map_conj_eq_self_of_mem (H.inv_mem hg)] at h
  exact h

theorem isComponentIn_ne_bot {K H : Subgroup G} (hK : IsComponentIn K H) : K ≠ ⊥ := by
  have hq : CFSG.IsQuasisimple K := BenderBranch.isQuasisimple_of_isComponentIn hK
  have : Nontrivial K := CFSG.LocalCores.isQuasisimple_nontrivial hq
  exact (Subgroup.nontrivial_iff_ne_bot K).mp this

theorem mem_oddCoreIn_of_central_odd [Finite G] {K H : Subgroup G} (hK : IsComponentIn K H)
    {y : G} (hyK : y ∈ K) (hyc : ∀ w ∈ K, w * y = y * w) (hodd : Odd (orderOf y)) :
    y ∈ oddCoreIn H := by
  have hyH : y ∈ H := hK.1 hyK
  let π : Set Nat.Primes := {q | q.val ≠ 2}
  have hsub : (K.subgroupOf H).IsSubnormal := hK.2.2
  let y' : K.subgroupOf H := ⟨⟨y, hyH⟩, hyK⟩
  have hy'c : y' ∈ Subgroup.center (K.subgroupOf H) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subtype.ext (hyc _ g.2))
  have hYn : (Subgroup.zpowers y').Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hy'c)
  have hord : orderOf y' = orderOf y := by
    rw [← Subgroup.orderOf_coe y', ← Subgroup.orderOf_coe (y' : H)]
  have hπ : CFSG.IsPiSubgroup π (Subgroup.zpowers y') := by
    intro q hq
    rw [Nat.card_zpowers, hord] at hq
    intro hq2
    exact hodd.not_two_dvd_nat (hq2 ▸ hq)
  have hle : Subgroup.zpowers y' ≤ CFSG.piCore π (K.subgroupOf H) :=
    CFSG.LocalCores.le_piCore_of_normal hYn hπ
  have hmem : (⟨y, hyH⟩ : H) ∈ (K.subgroupOf H) ⊓ CFSG.piCore π H := by
    rw [← CFSG.LocalCores.prime_set_core_subnormal_intersection π hsub]
    exact ⟨y', hle (Subgroup.mem_zpowers y'), rfl⟩
  have hodd' : (⟨y, hyH⟩ : H) ∈ CFSG.oddCore H := by
    rw [CFSG.oddCore_eq_piCore]
    exact hmem.2
  exact (mem_oddCoreIn_iff H ⟨y, hyH⟩).mpr hodd'

theorem commutator_pCoreOf_eq_bot [Finite G] {L H : Subgroup G} (hL : IsComponentIn L H) :
    ⁅L, pCoreOf 2 H⁆ = ⊥ := by
  have hQ2 : IsPGroup 2 ((pCoreOf 2 H).subgroupOf H) :=
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H).of_equiv
      (Subgroup.subgroupOfEquivOfLe
        (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 H)).symm
  have hsolv : Group.IsSolvable ((pCoreOf 2 H).subgroupOf H) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Group.IsNilpotent ((pCoreOf 2 H).subgroupOf H) := hQ2.isNilpotent
    infer_instance
  have hnormal : ((pCoreOf 2 H).subgroupOf H).Normal :=
    CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_normal 2 H
  have h := (CFSG.LocalCores.component_solvable_centralizer hsolv hnormal.isSubnormal).1
    (L.subgroupOf H) hL.2
  have h2 := congrArg (Subgroup.map H.subtype) h
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hL.1,
    Subgroup.map_subgroupOf_eq_of_le (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 H),
    Subgroup.map_bot] at h2
  exact h2

theorem exists_odd_prime_dvd_card [Finite G] {K H : Subgroup G} (hK : IsComponentIn K H) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card K := by
  by_contra hcon
  have hcon' : ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ∣ Nat.card K :=
    fun p hp hp2 hd => hcon ⟨p, hp, hp2, hd⟩
  have hq : CFSG.IsQuasisimple K := BenderBranch.isQuasisimple_of_isComponentIn hK
  have : Nontrivial K := CFSG.LocalCores.isQuasisimple_nontrivial hq
  have : Group.IsPerfect K := hq.1
  have h2 : IsPGroup 2 K := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [IsPGroup.iff_card]
    refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun {d} hd hdK => ?_⟩
    by_contra hd2
    exact hcon' d hd hd2 hdK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent K := h2.isNilpotent
  have hsolv : Group.IsSolvable K := inferInstance
  exact Group.IsPerfect.not_isSolvable K hsolv

end Components

end CFSG.QuasithinUnique.Unc25G2
