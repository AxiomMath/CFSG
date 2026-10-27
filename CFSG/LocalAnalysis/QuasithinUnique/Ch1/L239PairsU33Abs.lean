module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsBlocks

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239

open CFSG.Open CFSG.Quasithin

open scoped commutatorElement

namespace U33

@[expose] def Order23 (Γ : Type*) [Group Γ] : Prop := ∃ a : ℕ, Nat.card Γ = 2 ^ a * 3

section Sylow

variable {Γ : Type*} [Group Γ] [Finite Γ]

omit [Finite Γ] in
theorem card_zpowers_of_orderOf {w : Γ} (hw : orderOf w = 3) : Nat.card (Subgroup.zpowers w) = 3 := by
  rw [Nat.card_zpowers, hw]

theorem exists_conj_mem_zpowers (hΓ : Order23 Γ) {u v : Γ} (hu : orderOf u = 3)
    (hv : orderOf v = 3) : ∃ k : Γ, k * u * k⁻¹ ∈ Subgroup.zpowers v := by
  obtain ⟨a, ha⟩ := hΓ
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP : ∀ w : Γ, orderOf w = 3 → IsPGroup 3 (Subgroup.zpowers w) := fun w hw =>
    IsPGroup.of_card (n := 1) (by rw [card_zpowers_of_orderOf hw]; simp)
  have hidx : ∀ w : Γ, orderOf w = 3 → ¬ 3 ∣ (Subgroup.zpowers w).index := by
    intro w hw h3
    have h := (Subgroup.zpowers w).card_mul_index
    rw [card_zpowers_of_orderOf hw, ha] at h
    have h2 : (Subgroup.zpowers w).index = 2 ^ a := by omega
    rw [h2] at h3
    have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
    omega
  let P : Sylow 3 Γ := (hP u hu).toSylow (hidx u hu)
  let Q : Sylow 3 Γ := (hP v hv).toSylow (hidx v hv)
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq Γ P Q
  refine ⟨k, ?_⟩
  have hmem : k * u * k⁻¹ ∈ ((k • P : Sylow 3 Γ) : Subgroup Γ) := by
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨u, Subgroup.mem_zpowers u, by simp [MulAut.smul_def]⟩
  rw [hk] at hmem
  exact hmem

theorem isPGroup_two_of_normal (hΓ : Order23 Γ) {N : Subgroup Γ} [N.Normal] {g : Γ}
    (hg : orderOf g = 3) (hgN : g ∉ N) : IsPGroup 2 N := by
  obtain ⟨a, ha⟩ := hΓ
  have hdvd : Nat.card N ∣ 2 ^ a * 3 := ha ▸ Subgroup.card_subgroup_dvd_card N
  have h3 : ¬ 3 ∣ Nat.card N := by
    intro h3
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := N) 3 h3
    have hz : orderOf (x : Γ) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
    obtain ⟨k, hk⟩ := exists_conj_mem_zpowers ⟨a, ha⟩ hg hz
    have hkN : k * g * k⁻¹ ∈ N := Subgroup.zpowers_le.2 x.2 hk
    apply hgN
    have := Subgroup.Normal.conj_mem inferInstance _ hkN k⁻¹
    have e : k⁻¹ * (k * g * k⁻¹) * k⁻¹⁻¹ = g := by group
    rwa [e] at this
  have hcop : Nat.Coprime (Nat.card N) 3 := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3 |>.symm
  have h2 : Nat.card N ∣ 2 ^ a := hcop.dvd_of_dvd_mul_right hdvd
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
  exact IsPGroup.of_card hj

omit [Finite Γ] in
theorem order23_of_card_dvd {K : Subgroup Γ} {y : Γ} (hΓ : Order23 Γ) (hy : y ∈ K)
    (hy3 : orderOf y = 3) : Order23 K := by
  obtain ⟨a, ha⟩ := hΓ
  have hd : Nat.card K ∣ 2 ^ a * 3 := ha ▸ Subgroup.card_subgroup_dvd_card K
  have h3 : 3 ∣ Nat.card K := by
    have := orderOf_dvd_natCard (⟨y, hy⟩ : K)
    rwa [Subgroup.orderOf_mk, hy3] at this
  obtain ⟨e, he⟩ := h3
  rw [he] at hd
  have he2 : e ∣ 2 ^ a := by
    have : 3 * e ∣ 3 * 2 ^ a := by rw [mul_comm 3 (2 ^ a)]; exact hd
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 he2
  exact ⟨b, by rw [he, hb, mul_comm]⟩

theorem mem_of_isSubnormal (hΓ : Order23 Γ) {H : Subgroup Γ} (hH : H.IsSubnormal) {y z : Γ}
    (hy : y ∈ H) (hy3 : orderOf y = 3) (hz3 : orderOf z = 3) : z ∈ H := by
  induction hH generalizing y z with
  | top => exact Subgroup.mem_top z
  | step H K hHK hK hN ih =>
    have hzK : z ∈ K := ih (hHK hy) hy3 hz3
    have hK23 : Order23 K := order23_of_card_dvd hΓ (hHK hy) hy3
    have hy' : orderOf (⟨y, hHK hy⟩ : K) = 3 := by rw [Subgroup.orderOf_mk, hy3]
    have hz' : orderOf (⟨z, hzK⟩ : K) = 3 := by rw [Subgroup.orderOf_mk, hz3]
    obtain ⟨k, hk⟩ := exists_conj_mem_zpowers hK23 hz' hy'
    have hkH : k * ⟨z, hzK⟩ * k⁻¹ ∈ H.subgroupOf K :=
      Subgroup.zpowers_le.2 (show (⟨y, hHK hy⟩ : K) ∈ H.subgroupOf K from hy) hk
    have := Subgroup.Normal.conj_mem hN _ hkH k⁻¹
    have e : k⁻¹ * (k * (⟨z, hzK⟩ : K) * k⁻¹) * k⁻¹⁻¹ = ⟨z, hzK⟩ := by group
    rw [e] at this
    exact this

end Sylow

section Witness

variable {G : Type*} [Group G]

structure Witness (K : Subgroup G) : Prop where
  order23 : Order23 ↥K
  exists_witness : ∃ y ∈ K, orderOf y = 3 ∧ ∃ N : Subgroup G, N ≤ K ∧
    (∀ g ∈ K, ∀ x ∈ N, g * x * g⁻¹ ∈ N) ∧ IsPGroup 2 N ∧ ∃ n ∈ N, ⁅⁅n, y⁆, y⁆ ^ 2 ≠ 1

theorem normal_subgroupOf_of_conj {K N : Subgroup G}
    (hN : ∀ g ∈ K, ∀ x ∈ N, g * x * g⁻¹ ∈ N) : (N.subgroupOf K).Normal :=
  ⟨fun x hx g => hN g g.2 x hx⟩

theorem Witness.map {G' : Type*} [Group G'] {K : Subgroup G} (h : Witness K) (f : G →* G')
    (hf : Function.Injective f) : Witness (K.map f) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨a, ha⟩ := h.order23
    exact ⟨a, by rw [← ha]; exact (Nat.card_congr (K.equivMapOfInjective f hf).toEquiv).symm⟩
  · obtain ⟨y, hyK, hy3, N, hNK, hN, hN2, n, hnN, hwit⟩ := h.exists_witness
    refine ⟨f y, Subgroup.mem_map_of_mem f hyK, by rw [orderOf_injective f hf, hy3], N.map f,
      Subgroup.map_mono hNK, ?_, hN2.map f, f n, Subgroup.mem_map_of_mem f hnN, ?_⟩
    · rintro _ ⟨g, hg, rfl⟩ _ ⟨x, hx, rfl⟩
      exact ⟨g * x * g⁻¹, hN g hg x hx, by simp⟩
    · rw [← map_commutatorElement, ← map_commutatorElement, ← map_pow]
      intro h1
      exact hwit (by simpa using hf (h1.trans (map_one f).symm))

theorem Witness.charTwo [Finite G] {K : Subgroup G} (h : Witness K) : CharTwo K := by
  obtain ⟨y, hyK, hy3, N, hNK, hNc, hN2, n, hnN, hwit⟩ := h.exists_witness
  have hNn : (N.subgroupOf K).Normal := normal_subgroupOf_of_conj hNc
  rw [CFSG.QuasithinUnique.charTwo_iff_internal]
  set Q := CFSG.pCore 2 ↥K with hQ
  set Z := Subgroup.centralizer (Q : Set ↥K) with hZ
  have hZn : Z.Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [hZ, Subgroup.mem_centralizer_iff] at hx ⊢
    intro q hq
    have hq' : g⁻¹ * q * g ∈ Q := by
      have := CFSG.pCore_normal.conj_mem q hq g⁻¹
      simpa using this
    have := hx _ hq'
    calc q * (g * x * g⁻¹) = g * ((g⁻¹ * q * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * q * g)) * g⁻¹ := by rw [this]
      _ = g * x * g⁻¹ * q := by group
  have hN2' : IsPGroup 2 (N.subgroupOf K) := hN2.of_equiv (Subgroup.subgroupOfEquivOfLe hNK).symm
  have hNQ : N.subgroupOf K ≤ Q := le_pCore_of_normal hN2'
  have hyZ : (⟨y, hyK⟩ : ↥K) ∉ Z := by
    intro hyZ
    have hn : (⟨n, hNK hnN⟩ : ↥K) ∈ Q := hNQ (show (⟨n, hNK hnN⟩ : ↥K) ∈ N.subgroupOf K from hnN)
    have hc := Subgroup.mem_centralizer_iff.1 hyZ _ hn
    have hc' : n * y = y * n := congrArg Subtype.val hc
    have h1 : ⁅n, y⁆ = 1 := by
      rw [commutatorElement_def, hc']
      group
    apply hwit
    rw [h1, commutatorElement_one_left, one_pow]
  have hZ2 : IsPGroup 2 Z :=
    isPGroup_two_of_normal h.order23 (g := ⟨y, hyK⟩) (by rw [Subgroup.orderOf_mk, hy3]) hyZ
  exact le_pCore_of_normal hZ2

end Witness

section Chi0

variable {G : Type*} [Group G] [Finite G]

theorem Witness.not_hasChi0Block {K : Subgroup G} (h : Witness K) : ¬ HasChi0Block K := by
  obtain ⟨a, ha⟩ := h.order23
  obtain ⟨y, hyK, hy3, N, hNK, hNc, hN2, n, hnN, hwit⟩ := h.exists_witness
  have hNn : (N.subgroupOf K).Normal := normal_subgroupOf_of_conj hNc
  rintro ⟨B, ⟨hshort, hBK, hsub⟩, htype⟩
  obtain ⟨A, _, α, hαs, hαk, hAnt, hAord⟩ := chi0_type_data htype
  have hAdvd : Nat.card A ∣ 2 ^ a * 3 := by
    have h1 : Nat.card A ∣ Nat.card ↥B := Subgroup.card_dvd_of_surjective hαs
    have h2 : Nat.card ↥B ∣ Nat.card ↥K := Subgroup.card_dvd_of_le hBK
    exact ha ▸ h1.trans h2
  have hA3 : Nat.card A = 3 := by
    rcases hAord with h3 | ⟨m, hm, hmeq⟩
    · exact h3
    · exfalso
      have h1 : 4 ^ m - 1 ∣ 2 ^ a * 3 := (Dvd.intro_left _ hmeq.symm).trans hAdvd
      have h4 : 2 ∣ 4 ^ m := dvd_pow (by norm_num : (2 : ℕ) ∣ 4) (by omega)
      have hpos : 1 ≤ 4 ^ m := Nat.one_le_pow _ _ (by norm_num)
      have hcop : Nat.Coprime (4 ^ m - 1) (2 ^ a) :=
        Nat.Coprime.pow_right a (by
          rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
          omega)
      have h3 : 4 ^ m - 1 ∣ 3 := hcop.dvd_of_dvd_mul_left h1
      have h4' : 4 ^ m - 1 ≤ 3 := Nat.le_of_dvd (by norm_num) h3
      have h16 : 4 ^ 2 ≤ 4 ^ m := Nat.pow_le_pow_right (by norm_num) hm
      omega
  have hex : ∃ b : ↥B, α b ≠ 1 := by
    by_contra hne
    push Not at hne
    have : Nat.card A = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      refine ⟨⟨fun x y => ?_⟩, ⟨1⟩⟩
      obtain ⟨bx, rfl⟩ := hαs x
      obtain ⟨by', rfl⟩ := hαs y
      rw [hne bx, hne by']
    omega
  obtain ⟨b, hb⟩ := hex
  have hαb : orderOf (α b) = 3 := by
    have hd : orderOf (α b) ∣ 3 := hA3 ▸ orderOf_dvd_natCard (α b)
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h1 | h3
    · exact absurd (orderOf_eq_one_iff.1 h1) hb
    · exact h3
  have hbord : 3 ∣ orderOf b := hαb ▸ orderOf_map_dvd α b
  have hb0 : orderOf b ≠ 0 := (orderOf_pos b).ne'
  set y' : ↥B := b ^ (orderOf b / 3) with hy'
  have hy'3 : orderOf y' = 3 := orderOf_pow_orderOf_div hb0 hbord
  have hy'G : orderOf (y' : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hy'3
  have hmem : ∀ z : ↥K, orderOf z = 3 → z ∈ B.subgroupOf K := fun z hz =>
    mem_of_isSubnormal h.order23 hsub
      (y := ⟨(y' : G), hBK y'.2⟩) (show (y' : G) ∈ B from y'.2)
      (by rw [Subgroup.orderOf_mk]; exact hy'G) hz
  have hyB : y ∈ B := hmem ⟨y, hyK⟩ (by rw [Subgroup.orderOf_mk, hy3])
  have hnK : n ∈ K := hNK hnN
  have hcB : n * y * n⁻¹ ∈ B := by
    have hord : orderOf (⟨n, hnK⟩ * (⟨y, hyK⟩ : ↥K) * ⟨n, hnK⟩⁻¹) = 3 := by
      have h1 := orderOf_injective (MulAut.conj (⟨n, hnK⟩ : ↥K)).toMonoidHom
        (MulAut.conj (⟨n, hnK⟩ : ↥K)).injective (⟨y, hyK⟩ : ↥K)
      have h2 : (MulAut.conj (⟨n, hnK⟩ : ↥K)).toMonoidHom (⟨y, hyK⟩ : ↥K) =
          ⟨n, hnK⟩ * (⟨y, hyK⟩ : ↥K) * ⟨n, hnK⟩⁻¹ := rfl
      rw [h2] at h1
      rw [h1, Subgroup.orderOf_mk, hy3]
    exact hmem _ hord
  have haB : ⁅n, y⁆ ∈ B := by
    rw [commutatorElement_def]
    exact B.mul_mem hcB (B.inv_mem hyB)
  have hKN : K ≤ Subgroup.normalizer (N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).1 hNn
  have haN : ⁅n, y⁆ ∈ N := by
    have h1 : y * n⁻¹ * y⁻¹ ∈ N := by
      have := (Subgroup.mem_normalizer_iff.1 (hKN hyK) n⁻¹).1 (N.inv_mem hnN)
      simpa using this
    have : n * (y * n⁻¹ * y⁻¹) ∈ N := N.mul_mem hnN h1
    rw [commutatorElement_def]
    simpa [mul_assoc] using this
  have hNB : N ⊓ B ≤ pCoreOf 2 B := by
    refine CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 (N ⊓ B) B inf_le_right
      ((Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).2 fun g hg => ?_)
      (hN2.to_le inf_le_left)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hgN : g ∈ Subgroup.normalizer (N : Set G) := hKN (hBK hg)
    constructor
    · rintro ⟨hxN, hxB⟩
      exact ⟨(Subgroup.mem_normalizer_iff.1 hgN x).1 hxN, B.mul_mem (B.mul_mem hg hxB) (B.inv_mem hg)⟩
    · rintro ⟨hxN, hxB⟩
      refine ⟨(Subgroup.mem_normalizer_iff.1 hgN x).2 hxN, ?_⟩
      have := B.mul_mem (B.mul_mem (B.inv_mem hg) hxB) hg
      simpa [mul_assoc] using this
  have hU : ⁅⁅n, y⁆, y⁆ ∈ blockU B :=
    Subgroup.commutator_mem_commutator (hNB ⟨haN, haB⟩) hyB
  exact hwit (hshort.2.2.1.2 _ hU)

end Chi0

end U33

end CFSG.QuasithinUnique.Vol2Native.L239
