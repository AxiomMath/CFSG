module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporLift
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieBlock

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.Lie

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

section Block

variable {G : Type*} [Group G]

theorem exists_orderOf_three_of_isChi0Block [Finite G] {K B : Subgroup G} (hB : IsChi0Block K B) :
    ∃ b ∈ B, orderOf b = 3 := by
  obtain ⟨A, _, α, hαs, hαk, hnt, hord⟩ := chi0_type_data hB.2
  have h3 : 3 ∣ Nat.card A := by
    rcases hord with h | ⟨n, hn, h⟩
    · rw [h]
    · rw [h]
      have h4 : 4 ^ n % 3 = 1 := by
        rw [Nat.pow_mod]
        norm_num
      have : 3 ∣ 4 ^ n - 1 := by
        have h1 : 1 ≤ 4 ^ n := Nat.one_le_pow _ _ (by norm_num)
        omega
      exact Dvd.dvd.mul_left this _
  have : Finite A := Finite.of_surjective α hαs
  have hdvd := Subgroup.card_dvd_of_surjective hαs
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨b₀, hb₀⟩ := exists_prime_orderOf_dvd_card' 3 (h3.trans hdvd)
  refine ⟨(b₀ : G), b₀.2, ?_⟩
  rw [Subgroup.orderOf_coe, hb₀]

theorem block_commutator_zpowers_centralized [Finite G] {K Q B : Subgroup G} (hQK : Q ≤ K)
    (hKQ : K ≤ Subgroup.normalizer (Q : Set G)) (hQ : IsPGroup 2 Q) (hB : IsBlock2 K B) {t : G}
    (htB : t ∈ B) (ht : orderOf t = 3) : ⁅⁅Q, Subgroup.zpowers t⁆, Q⁆ = ⊥ := by
  obtain ⟨hshort, hBP, hsub⟩ := hB
  have hB2 := hshort.1
  have hBQ : B ≤ Subgroup.normalizer (Q : Set G) := hBP.trans hKQ
  have hQB : Q ≤ Subgroup.normalizer (B : Set G) :=
    normalizes_of_subnormal hBP hsub hB2 hQK hKQ hQ
  set A : Subgroup G := Subgroup.zpowers t with hAdef
  have hAB : A ≤ B := by rw [hAdef, Subgroup.zpowers_le]; exact htB
  have hAQ : A ≤ Subgroup.normalizer (Q : Set G) := hAB.trans hBQ
  set W : Subgroup G := ⁅Q, A⁆ with hWdef
  have hWQle : W ≤ Q := by
    refine Subgroup.commutator_le.2 fun q hq a ha => ?_
    have h1 : a * q⁻¹ * a⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.1 (hAQ ha) q⁻¹).1 (Q.inv_mem hq)
    have : ⁅q, a⁆ = q * (a * q⁻¹ * a⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [this]
    exact Q.mul_mem hq h1
  have hWle : W ≤ pCoreOf 2 B :=
    ((Subgroup.commutator_mono (le_refl Q) hAB).trans
      (commutator_le_inf_of_normalizes hBQ hQB)).trans (inf_le_pCoreOf hBP hKQ hQ)
  have hidem : ⁅W, A⁆ = W :=
    CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_idempotent 3 Nat.prime_three A Q
      (isPGroup_three_zpowers ht) hAQ (coprime_three_card hQ)
  have hWU : W ≤ blockU B := by
    calc W = ⁅W, A⁆ := hidem.symm
      _ ≤ blockU B := Subgroup.commutator_mono hWle hAB
  obtain ⟨hU1, -⟩ := hshort.2.2.1
  have hWab : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := by
    intro x hx y hy
    have hyC : y ∈ Subgroup.centralizer (blockQ B : Set G) := (hU1 (hWU hy)).2
    exact Subgroup.mem_centralizer_iff.1 hyC x (hWle hx)
  have hQW : Q ≤ Subgroup.normalizer (W : Set G) := Subgroup.normalizer_commutator_ge_left Q A
  have hAW : A ≤ Subgroup.normalizer (W : Set G) := Subgroup.normalizer_commutator_ge_right Q A
  have hWQ_Z : ⁅W, Q⁆ ≤ blockZ B :=
    (Subgroup.commutator_mono hWU (le_refl Q)).trans
      (commutator_blockU_le_blockZ hshort hBQ hQB hQ)
  have hWQ_W : ⁅W, Q⁆ ≤ W := by
    refine Subgroup.commutator_le.2 fun w hw q hq => ?_
    have h1 : q * w⁻¹ * q⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.1 (hQW hq) w⁻¹).1 (W.inv_mem hw)
    have : ⁅w, q⁆ = w * (q * w⁻¹ * q⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [this]
    exact W.mul_mem hw h1
  have hWQ_C : ⁅W, Q⁆ ≤ Subgroup.centralizer (A : Set G) :=
    hWQ_Z.trans (inf_le_right.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hAB)))
  have hWcard : Nat.Coprime (Nat.card A) (Nat.card W) := by
    have : Nat.card A = 3 := by rw [hAdef, Nat.card_zpowers, ht]
    rw [this]
    exact coprime_three_card (hQ.to_le hWQle)
  have hfit := fitting_commutator_inf_centralizer hWab hAW hWcard
  have hAWeq : ⁅A, W⁆ = W := by rw [Subgroup.commutator_comm]; exact hidem
  rw [hAWeq] at hfit
  refine le_bot_iff.1 ?_
  rw [← hfit]
  exact le_inf hWQ_W hWQ_C

end Block

section Quotient

theorem orderOf_map_eq_three_of_pGroup_ker {K Y : Type*} [Group K] [Group Y] (φ : K →* Y)
    (hN2 : IsPGroup 2 φ.ker) {b : K} (hb : orderOf b = 3) : orderOf (φ b) = 3 := by
  have hdvd3 : orderOf (φ b) ∣ 3 := by
    rw [← hb]
    exact orderOf_map_dvd φ b
  rcases (Nat.dvd_prime Nat.prime_three).1 hdvd3 with h1 | h1
  · exfalso
    have hmem : b ∈ φ.ker := by
      rw [MonoidHom.mem_ker, ← orderOf_eq_one_iff]
      exact h1
    obtain ⟨k, hk⟩ := hN2 ⟨b, hmem⟩
    have h2 : b ^ 2 ^ k = 1 := by
      have := congrArg (fun y : ↥φ.ker => (y : K)) hk
      simpa using this
    have h3' : 3 ∣ 2 ^ k := by
      rw [← hb]
      exact orderOf_dvd_of_pow_eq_one h2
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3') (by norm_num)
  · exact h1

theorem charTwo_noChi0_of_selfCentralizing {G : Type*} [Group G] [Finite G] {K : Subgroup G}
    {Y : Type*} [Group Y] (φ : ↥K →* Y) (hφ : Function.Surjective φ) (hN2 : IsPGroup 2 φ.ker)
    (Q : Subgroup Y) [Q.Normal] (hQ2 : IsPGroup 2 Q)
    (hcent : ∀ y : Y, (∀ q ∈ Q, y * q = q * y) → y ∈ Q)
    (hZ : ∀ z ∈ Q, (∀ q ∈ Q, z * q = q * z) → z ∈ ⁅Q, Q⁆) :
    CharTwo K ∧ ¬ HasChi0Block K := by
  classical
  have hYfin : Finite Y := Finite.of_surjective φ hφ
  set QK : Subgroup ↥K := Q.comap φ with hQK
  have hQKn : QK.Normal := Subgroup.Normal.comap inferInstance φ
  have hQK2 : IsPGroup 2 QK := by
    intro g
    obtain ⟨a, ha⟩ := hQ2 ⟨φ (g : ↥K), g.2⟩
    have h1 : φ ((g : ↥K) ^ 2 ^ a) = 1 := by
      have := congrArg Subtype.val ha
      simpa using this
    obtain ⟨c, hc⟩ := hN2 ⟨(g : ↥K) ^ 2 ^ a, h1⟩
    refine ⟨a + c, Subtype.ext ?_⟩
    have := congrArg (fun y : ↥φ.ker => ((y : ↥K) : ↥K)) hc
    simp only [OneMemClass.coe_one, SubgroupClass.coe_pow] at this
    simpa [pow_add, pow_mul] using this
  have hQKle : QK ≤ CFSG.pCore 2 ↥K := le_pCore_of_normal hQK2
  refine ⟨?_, ?_⟩
  · rw [charTwo_iff_internal]
    intro x hx
    apply hQKle
    show φ x ∈ Q
    apply hcent
    intro q hq
    obtain ⟨y, rfl⟩ := hφ q
    have hy : y ∈ QK := hq
    have := Subgroup.mem_centralizer_iff.1 hx y (hQKle hy)
    rw [← map_mul, ← map_mul]
    exact congrArg φ this.symm
  · rintro ⟨B, hB⟩
    obtain ⟨b, hbB, hord⟩ := exists_orderOf_three_of_isChi0Block hB
    have hBK : B ≤ K := hB.1.2.1
    have hbK : b ∈ K := hBK hbB
    set b' : ↥K := ⟨b, hbK⟩ with hb'
    have hordb' : orderOf b' = 3 := by
      rw [← hord, ← Subgroup.orderOf_coe b']
    have hordφ : orderOf (φ b') = 3 := orderOf_map_eq_three_of_pGroup_ker φ hN2 hordb'
    set Qt : Subgroup G := QK.map K.subtype with hQt
    have hQtK : Qt ≤ K := Subgroup.map_subtype_le QK
    have hsubK : Qt.subgroupOf K = QK := by
      rw [hQt, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective K.subtype_injective]
    have hKQt : K ≤ Subgroup.normalizer (Qt : Set G) := by
      rw [← Subgroup.normal_subgroupOf_iff_le_normalizer hQtK, hsubK]
      exact hQKn
    have hQt2 : IsPGroup 2 Qt := hQK2.map K.subtype
    have hcomm := block_commutator_zpowers_centralized hQtK hKQt hQt2 hB.1 hbB hord
    have hWK : ∀ w ∈ ⁅QK, Subgroup.zpowers b'⁆, ∀ l ∈ QK, w * l = l * w := by
      intro w hw l hl
      have hmapW : (⁅QK, Subgroup.zpowers b'⁆).map K.subtype = ⁅Qt, Subgroup.zpowers b⁆ := by
        rw [Subgroup.map_commutator, MonoidHom.map_zpowers]
        rfl
      have hwG : (w : G) ∈ ⁅Qt, Subgroup.zpowers b⁆ := by
        rw [← hmapW]
        exact ⟨w, hw, rfl⟩
      have hlG : (l : G) ∈ Qt := ⟨l, hl, rfl⟩
      have h2 : ⁅(w : G), (l : G)⁆ ∈ ⁅⁅Qt, Subgroup.zpowers b⁆, Qt⁆ :=
        Subgroup.commutator_mem_commutator hwG hlG
      rw [hcomm, Subgroup.mem_bot] at h2
      exact Subtype.ext (commutatorElement_eq_one_iff_mul_comm.1 h2)
    have hcQ : ⁅Q, Subgroup.zpowers (φ b')⁆ ≤ ⁅Q, Q⁆ := by
      rw [Subgroup.commutator_le]
      intro q hq a ha
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      obtain ⟨k, rfl⟩ := hφ q
      have hk : k ∈ QK := hq
      have hmem : ⁅k, b' ^ n⁆ ∈ ⁅QK, Subgroup.zpowers b'⁆ :=
        Subgroup.commutator_mem_commutator hk (Subgroup.mem_zpowers_iff.2 ⟨n, rfl⟩)
      have hz : ⁅φ k, φ b' ^ n⁆ = φ ⁅k, b' ^ n⁆ := by
        rw [map_commutatorElement, map_zpow]
      refine hZ _ ?_ ?_
      · exact Subgroup.commutator_le_left Q ⊤
          (Subgroup.commutator_mem_commutator hq (Subgroup.mem_top _))
      · intro p hp
        obtain ⟨l, rfl⟩ := hφ p
        have hl : l ∈ QK := hp
        have h1 := hWK _ hmem l hl
        rw [hz, ← map_mul, ← map_mul, h1]
    have hnormQ : φ b' ∈ Subgroup.normalizer (Q : Set Y) :=
      (Subgroup.normalizer_eq_top_iff.2 inferInstance : Subgroup.normalizer (Q : Set Y) = ⊤) ▸
        Subgroup.mem_top _
    have hcen := zpowers_le_centralizer_of_commutator_le hQ2 hordφ hnormQ hcQ
    have hcQ' : φ b' ∈ Q := by
      refine hcent _ fun q hq => ?_
      exact (Subgroup.mem_centralizer_iff.1 (hcen (Subgroup.mem_zpowers _)) q hq).symm
    obtain ⟨m, hm⟩ := hQ2 ⟨φ b', hcQ'⟩
    have hm' : φ b' ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    have h3 : 3 ∣ 2 ^ m := hordφ ▸ orderOf_dvd_of_pow_eq_one hm'
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)

end Quotient

section Facts

variable {X : Type*} [Group X] {P Q : Subgroup X}

theorem ParabolicFacts.goodLocal (hF : ParabolicFacts P Q) : GoodLocal P := by
  intro G _ _ K φ hφ hker
  have : (Q.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hF.le).2 hF.normalizes
  refine charTwo_noChi0_of_selfCentralizing φ hφ hker (Q.subgroupOf P) hF.pGroup.comap_subtype
    ?_ ?_
  · intro y hy
    refine hF.selfCentralizing ⟨y.2, Subgroup.mem_centralizer_iff.2 fun q hq => ?_⟩
    have h := hy ⟨q, hF.le hq⟩ hq
    exact (congrArg Subtype.val h).symm
  · intro z hz hzc
    have hzQ : (z : X) ∈ Q := hz
    have h1 : (z : X) ∈ ⁅Q, Q⁆ := by
      refine hF.center_le ⟨hzQ, Subgroup.mem_centralizer_iff.2 fun q hq => ?_⟩
      have h := hzc ⟨q, hF.le hq⟩ hq
      exact (congrArg Subtype.val h).symm
    have hmap : (⁅Q.subgroupOf P, Q.subgroupOf P⁆).map P.subtype = ⁅Q, Q⁆ := by
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hF.le]
    rw [← hmap] at h1
    obtain ⟨w, hw, hwz⟩ := h1
    have : w = z := Subtype.ext hwz
    rwa [this] at hw

end Facts

end CFSG.QuasithinUnique.Vol2Native.L239.Lie
