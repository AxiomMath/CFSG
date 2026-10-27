
module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporAlt3
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsBlocks

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

theorem chi0_typeN_data {G : Type*} [Group G] {B : Subgroup G}
    (h : (∃ n : ℕ, 1 < n ∧ IsLin2Type B n) ∨ IsAltType B 5) :
    ∃ (A : Type) (_ : Group A) (α : ↥B →* A) (n : ℕ), Function.Surjective α ∧
      α.ker = CFSG.pCore 2 ↥B ∧ 2 ≤ n ∧ Nat.card A = 2 ^ n * (4 ^ n - 1) := by
  rcases h with ⟨n, hn, F, hF, hFin, hcard, α, hαs, hαk, -⟩ | ⟨α, hαs, hαk, -⟩
  · have hq : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card]; exact hcard
    have h42 : (2 ^ n) ^ 2 = 4 ^ n := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    have hcardSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = 2 ^ n * (4 ^ n - 1) := by
      rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hq, h42]
    exact ⟨Matrix.SpecialLinearGroup (Fin 2) F, inferInstance, α, n, hαs, hαk, by omega, hcardSL⟩
  · have hc : Nat.card (alternatingGroup (Fin 5)) = 60 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]; decide
    exact ⟨alternatingGroup (Fin 5), inferInstance, α, 2, hαs, hαk, le_rfl, by rw [hc]; norm_num⟩

theorem card_dvd_of_block {G : Type*} [Group G] [Finite G] {K B : Subgroup G} (hBK : B ≤ K)
    {Z A : Type*} [Group Z] [Group A] (θ : ↥K →* Z) (hθ : IsPGroup 2 θ.ker) (α : ↥B →* A)
    (hαs : Function.Surjective α) (hαk : α.ker = CFSG.pCore 2 ↥B) [Finite Z] :
    Nat.card A ∣ Nat.card Z := by
  classical
  have : Finite A := Finite.of_surjective α hαs
  set θB : ↥B →* Z := θ.comp (Subgroup.inclusion hBK) with hθB
  have hκ2 : IsPGroup 2 θB.ker := by
    intro x
    obtain ⟨k, hk⟩ := hθ ⟨Subgroup.inclusion hBK (x : ↥B), x.2⟩
    have h1 : ((Subgroup.inclusion hBK (x : ↥B)) ^ 2 ^ k : ↥K) = 1 := by
      have := congrArg (fun y : ↥θ.ker => (y : ↥K)) hk
      simpa using this
    have h2 : (x : ↥B) ^ 2 ^ k = 1 := by
      apply Subgroup.inclusion_injective hBK
      rw [map_pow, map_one]
      exact h1
    exact ⟨k, Subtype.ext (by simpa using h2)⟩
  have : θB.ker.Normal := MonoidHom.normal_ker θB
  have hκle : θB.ker ≤ α.ker := by
    rw [hαk]
    exact le_pCore_of_normal hκ2
  have hdvd : Nat.card θB.ker ∣ Nat.card α.ker := Subgroup.card_dvd_of_le hκle
  obtain ⟨d, hd⟩ := hdvd
  have h1 := Subgroup.card_ker_mul_card_range θB
  have h2 := Subgroup.card_ker_mul_card_of_surjective hαs
  have hpos : 0 < Nat.card θB.ker := Nat.card_pos
  have h3 : Nat.card θB.range = d * Nat.card A := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [h1, ← mul_assoc, ← hd, h2]
  have h4 : Nat.card A ∣ Nat.card θB.range := ⟨d, by rw [h3, mul_comm]⟩
  exact h4.trans (Subgroup.card_subgroup_dvd_card θB.range)

theorem charTwo_noChi0_of_quotient {G : Type*} [Group G] [Finite G] {K : Subgroup G}
    {Y : Type*} [Group Y] (φ : ↥K →* Y) (hφ : Function.Surjective φ) (hN2 : IsPGroup 2 φ.ker)
    (Q : Subgroup Y) [Q.Normal] (hQ2 : IsPGroup 2 Q)
    (hcent : ∀ y : Y, (∀ q ∈ Q, y * q = q * y) → y ∈ Q)
    (hA3 : ∀ b : Y, orderOf b = 3 → 4 < Nat.card ↥⁅Q, Subgroup.zpowers b⁆)
    (hN : ∀ n : ℕ, 2 ≤ n → ¬ (2 ^ n * (4 ^ n - 1) ∣ Nat.card (Y ⧸ Q))) :
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
    obtain ⟨⟨hshort, hBK, hsub⟩, htype⟩ := hB
    rcases htype with ⟨n, hn, hlin⟩ | h3 | h5
    · obtain ⟨A, _, α, m, hαs, hαk, hm, hcardA⟩ := chi0_typeN_data (Or.inl ⟨n, hn, hlin⟩)
      let θ : ↥K →* Y ⧸ Q := (QuotientGroup.mk' Q).comp φ
      have hθ : θ.ker = QK := by
        ext x
        simp [θ, QuotientGroup.eq_one_iff, QK]
      have hdvd := card_dvd_of_block hBK θ (by rw [hθ]; exact hQK2) α hαs hαk
      rw [hcardA] at hdvd
      exact hN m hm hdvd
    ·
      have hQKmap : QK.map K.subtype ≤ K := Subgroup.map_subtype_le QK
      have hsubK : ((QK.map K.subtype).subgroupOf K) = QK := by
        rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective K.subtype_injective]
      have hnormK : ((QK.map K.subtype).subgroupOf K).Normal := by
        rw [hsubK]
        infer_instance
      have hQK2' : IsPGroup 2 (QK.map K.subtype) := hQK2.map K.subtype
      obtain ⟨b, hbK, hord, hcard⟩ := alt3_commutator_bound
        ⟨⟨hshort, hBK, hsub⟩, Or.inr (Or.inl h3)⟩ h3 hQKmap hnormK hQK2'
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
      have hcommmap : ⁅Q, Subgroup.zpowers (φ b')⁆ = (⁅QK, Subgroup.zpowers b'⁆).map φ := by
        rw [Subgroup.map_commutator, hQKim, MonoidHom.map_zpowers]
      have hcard' : Nat.card ↥(⁅QK, Subgroup.zpowers b'⁆) ≤ 4 := by
        have h1 : (⁅QK, Subgroup.zpowers b'⁆).map K.subtype =
            ⁅QK.map K.subtype, Subgroup.zpowers b⁆ := by
          rw [Subgroup.map_commutator, MonoidHom.map_zpowers]
          rfl
        rw [← Subgroup.card_map_of_injective K.subtype_injective, h1]
        exact hcard
      have h5 := hA3 (φ b') hordφ
      rw [hcommmap] at h5
      have h6 : Nat.card ↥((⁅QK, Subgroup.zpowers b'⁆).map φ) ≤
          Nat.card ↥(⁅QK, Subgroup.zpowers b'⁆) := by
        refine Nat.card_le_card_of_surjective (fun x => ?_) ?_
        · exact ⟨φ x.1, ⟨x.1, x.2, rfl⟩⟩
        · rintro ⟨_, x, hx, rfl⟩
          exact ⟨⟨x, hx⟩, rfl⟩
      omega
    · obtain ⟨A, _, α, m, hαs, hαk, hm, hcardA⟩ := chi0_typeN_data (Or.inr h5)
      let θ : ↥K →* Y ⧸ Q := (QuotientGroup.mk' Q).comp φ
      have hθ : θ.ker = QK := by
        ext x
        simp [θ, QuotientGroup.eq_one_iff, QK]
      have hdvd := card_dvd_of_block hBK θ (by rw [hθ]; exact hQK2) α hαs hαk
      rw [hcardA] at hdvd
      exact hN m hm hdvd

end CFSG.QuasithinUnique.Vol2Native.L239
