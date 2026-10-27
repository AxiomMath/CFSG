module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsBlocks
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSub

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

theorem exists_order_three_of_chi0 {G : Type*} [Group G] [Finite G] {K B : Subgroup G}
    (hB : IsChi0Block K B) : ∃ b ∈ B, orderOf b = 3 := by
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

theorem block_commutator_abelian {G : Type*} [Group G] [Finite G] {K B : Subgroup G}
    (hB : IsBlock2 K B) {Q : Subgroup G} (hQK : Q ≤ K) (hQn : (Q.subgroupOf K).Normal)
    (hQ : IsPGroup 2 Q) {b : G} (hbB : b ∈ B) (hord : orderOf b = 3) :
    ∀ x ∈ ⁅Q, Subgroup.zpowers b⁆, ∀ y ∈ ⁅Q, Subgroup.zpowers b⁆, x * y = y * x ∧ x * x = 1 := by
  classical
  obtain ⟨hshort, hBK, hsub⟩ := hB
  have hodd : Odd (orderOf b) := by rw [hord]; decide
  have hbK : b ∈ K := hBK hbB
  set C : Subgroup G := ⁅Q, Subgroup.zpowers b⁆ with hC
  have hQ' : IsPGroup 2 (Q.subgroupOf K) := hQ.comap_subtype
  have hb'K : (⟨b, hbK⟩ : ↥K) ∈ B.subgroupOf K := hbB
  have hoddK : Odd (orderOf (⟨b, hbK⟩ : ↥K)) := by
    rw [← Subgroup.orderOf_coe (⟨b, hbK⟩ : ↥K)]
    exact hodd
  have hmapQ : (Q.subgroupOf K).map K.subtype = Q := by
    rw [Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.2 hQK
  have hmapP : (Subgroup.zpowers (⟨b, hbK⟩ : ↥K)).map K.subtype = Subgroup.zpowers b :=
    MonoidHom.map_zpowers K.subtype _
  have hmapB : (B.subgroupOf K).map K.subtype = B := by
    rw [Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.2 hBK
  have hCmap : (⁅Q.subgroupOf K, Subgroup.zpowers (⟨b, hbK⟩ : ↥K)⁆).map K.subtype = C := by
    rw [Subgroup.map_commutator, hmapQ, hmapP]
  have hCB : C ≤ B := by
    have h1 := commutator_le_of_isSubnormal hsub hQ' hb'K hoddK
    have h2 := Subgroup.map_mono (f := K.subtype) h1
    rwa [hCmap, hmapB] at h2
  have hidem : ⁅C, Subgroup.zpowers b⁆ = C := by
    have h1 := commutator_zpowers_idem hQ' hoddK
    have h2 := congrArg (Subgroup.map K.subtype) h1
    rw [Subgroup.map_commutator, Subgroup.map_commutator, hmapQ, hmapP] at h2
    exact h2
  have hCQ : C ≤ Q := by
    rw [hC, Subgroup.commutator_le]
    intro q hq p hp
    have hpK : p ∈ K := by
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hp
      exact K.zpow_mem hbK n
    have hconj := (Subgroup.normal_subgroupOf_iff hQK).1 hQn
    have h1 : p * q⁻¹ * p⁻¹ ∈ Q := hconj (q⁻¹) p (Q.inv_mem hq) hpK
    have h2 : ⁅q, p⁆ = q * (p * q⁻¹ * p⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [h2]
    exact Q.mul_mem hq h1
  have hEn : ((Q ⊓ B).subgroupOf B).Normal := by
    rw [Subgroup.normal_subgroupOf_iff (inf_le_right : Q ⊓ B ≤ B)]
    intro h g hh hg
    refine ⟨?_, B.mul_mem (B.mul_mem hg hh.2) (B.inv_mem hg)⟩
    exact (Subgroup.normal_subgroupOf_iff hQK).1 hQn h g hh.1 (hBK hg)
  have hE2 : IsPGroup 2 (Q ⊓ B : Subgroup G) := hQ.to_le inf_le_left
  have hEle : Q ⊓ B ≤ pCoreOf 2 B :=
    CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 (Q ⊓ B) B inf_le_right hEn hE2
  have hCQb : C ≤ blockQ B := fun c hc => hEle (Subgroup.mem_inf.2 ⟨hCQ hc, hCB hc⟩)
  have hCU : C ≤ blockU B := by
    rw [← hidem]
    exact Subgroup.commutator_mono hCQb (Subgroup.zpowers_le.2 hbB)
  obtain ⟨hUle, hUexp⟩ := hshort.2.2.1
  intro x hx y hy
  have hxU := hCU hx
  have hyU := hCU hy
  refine ⟨?_, ?_⟩
  · exact Subgroup.mem_centralizer_iff.1 (hUle hyU).2 x (hUle hxU).1
  · rw [← pow_two]
    exact hUexp x hxU

theorem charTwo_noChi0_of_quotient_E {G : Type*} [Group G] [Finite G] {K : Subgroup G}
    {Y : Type*} [Group Y] (φ : ↥K →* Y) (hφ : Function.Surjective φ) (hN2 : IsPGroup 2 φ.ker)
    (Q : Subgroup Y) [Q.Normal] (hQ2 : IsPGroup 2 Q)
    (hcent : ∀ y : Y, (∀ q ∈ Q, y * q = q * y) → y ∈ Q)
    (hE : ∀ b : Y, orderOf b = 3 → ∃ x ∈ ⁅Q, Subgroup.zpowers b⁆,
      ∃ y ∈ ⁅Q, Subgroup.zpowers b⁆, x * y ≠ y * x ∨ x * x ≠ 1) :
    CharTwo K ∧ ¬ HasChi0Block K := by
  classical
  have hYfin : Finite Y := Finite.of_surjective φ hφ
  set QK : Subgroup ↥K := Q.comap φ with hQK
  have : QK.Normal := Subgroup.Normal.comap inferInstance φ
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
  have hQKim : QK.map φ = Q := Subgroup.map_comap_eq_self_of_surjective hφ Q
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
  · intro hblock
    obtain ⟨B, hB⟩ := hblock
    obtain ⟨b, hbB, hord⟩ := exists_order_three_of_chi0 hB
    have hBK : B ≤ K := hB.1.2.1
    have hbK : b ∈ K := hBK hbB
    set b' : ↥K := ⟨b, hbK⟩ with hb'
    have hordb' : orderOf b' = 3 := by
      rw [← hord, ← Subgroup.orderOf_coe b']
    have hordφ : orderOf (φ b') = 3 := by
      have hdvd3 : orderOf (φ b') ∣ 3 := by
        rw [← hordb']
        exact orderOf_map_dvd φ b'
      rcases (Nat.dvd_prime Nat.prime_three).1 hdvd3 with h1 | h1
      · exfalso
        have hmem : b' ∈ φ.ker := by
          rw [MonoidHom.mem_ker, ← orderOf_eq_one_iff]
          exact h1
        obtain ⟨k, hk⟩ := hN2 ⟨b', hmem⟩
        have h2 : b' ^ 2 ^ k = 1 := by
          have := congrArg (fun y : ↥φ.ker => (y : ↥K)) hk
          simpa using this
        have h3' : 3 ∣ 2 ^ k := by
          rw [← hordb']
          exact orderOf_dvd_of_pow_eq_one h2
        exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3') (by norm_num)
      · exact h1
    have hQKmap : QK.map K.subtype ≤ K := Subgroup.map_subtype_le QK
    have hsubK : ((QK.map K.subtype).subgroupOf K) = QK := by
      rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective K.subtype_injective]
    have hnormK : ((QK.map K.subtype).subgroupOf K).Normal := by
      rw [hsubK]
      infer_instance
    have hQK2' : IsPGroup 2 (QK.map K.subtype) := hQK2.map K.subtype
    have habel := block_commutator_abelian hB.1 hQKmap hnormK hQK2' hbB hord
    have hcommmap : ⁅Q, Subgroup.zpowers (φ b')⁆ = (⁅QK, Subgroup.zpowers b'⁆).map φ := by
      rw [Subgroup.map_commutator, hQKim, MonoidHom.map_zpowers]
    obtain ⟨x, hx, y, hy, hne⟩ := hE (φ b') hordφ
    rw [hcommmap] at hx hy
    obtain ⟨u, hu, rfl⟩ := hx
    obtain ⟨v, hv, rfl⟩ := hy
    have hu' : (u : G) ∈ ⁅QK.map K.subtype, Subgroup.zpowers b⁆ := by
      have h1 : (⁅QK, Subgroup.zpowers b'⁆).map K.subtype =
          ⁅QK.map K.subtype, Subgroup.zpowers b⁆ := by
        rw [Subgroup.map_commutator, MonoidHom.map_zpowers]
        rfl
      rw [← h1]
      exact ⟨u, hu, rfl⟩
    have hv' : (v : G) ∈ ⁅QK.map K.subtype, Subgroup.zpowers b⁆ := by
      have h1 : (⁅QK, Subgroup.zpowers b'⁆).map K.subtype =
          ⁅QK.map K.subtype, Subgroup.zpowers b⁆ := by
        rw [Subgroup.map_commutator, MonoidHom.map_zpowers]
        rfl
      rw [← h1]
      exact ⟨v, hv, rfl⟩
    obtain ⟨hcom, hsq⟩ := habel _ hu' _ hv'
    have hcom' : u * v = v * u := Subtype.ext hcom
    have hsq' : u * u = 1 := Subtype.ext hsq
    rcases hne with hne | hne
    · exact hne (by rw [← map_mul, ← map_mul, hcom'])
    · exact hne (by rw [← map_mul, hsq', map_one])

end CFSG.QuasithinUnique.Vol2Native.L239
