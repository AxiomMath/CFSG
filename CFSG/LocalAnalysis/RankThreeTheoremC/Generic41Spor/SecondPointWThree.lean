module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.SecondPointPSL2
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SmallRankOneLinTwo

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open Subgroup CFSG.AGLEmbedding
open scoped MatrixGroups

@[expose] def NormalizerThreeLines (p : ℕ) (K : Type) [Group K] [Finite K] : Prop :=
  ∀ S : Sylow p K, ∀ t ∈ (S : Subgroup K), t ≠ 1 →
    ∃ n₁ ∈ normalizer ((S : Subgroup K) : Set K), ∃ n₂ ∈ normalizer ((S : Subgroup K) : Set K),
      zpowers (n₁ * t * n₁⁻¹) ≠ zpowers t ∧ zpowers (n₂ * t * n₂⁻¹) ≠ zpowers t ∧
        zpowers (n₁ * t * n₁⁻¹) ≠ zpowers (n₂ * t * n₂⁻¹)

theorem normalizerThreeLines_of_transitive {p : ℕ} [Fact p.Prime] {K : Type} [Group K] [Finite K]
    (hpl : SylowIsPlane p K) (htr : NormalizerTransitive p K) : NormalizerThreeLines p K := by
  intro S t ht ht1
  have hp : p.Prime := Fact.out
  have hS := hpl S
  have htp : t ^ p = 1 := hS.1.2 t ht
  have hto : orderOf t = p := orderOf_eq_prime htp ht1
  have hcardt : Nat.card (zpowers t) = p := by rw [Nat.card_zpowers, hto]
  have hex : ∃ t₂ ∈ (S : Subgroup K), t₂ ∉ zpowers t := by
    by_contra hcon
    push Not at hcon
    have hle : (S : Subgroup K) ≤ zpowers t := fun x hx => hcon x hx
    have h1 := Subgroup.card_le_of_le hle
    rw [hS.2, hcardt] at h1
    have h2 := hp.two_le
    nlinarith
  obtain ⟨t₂, ht₂S, ht₂⟩ := hex
  have ht₂1 : t₂ ≠ 1 := fun h => ht₂ (by rw [h]; exact Subgroup.one_mem _)
  have ht₃S : t * t₂ ∈ (S : Subgroup K) := Subgroup.mul_mem _ ht ht₂S
  have ht₃ : t * t₂ ∉ zpowers t := by
    intro h
    apply ht₂
    have := Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers t)) h
    simpa using this
  have ht₃1 : t * t₂ ≠ 1 := fun h => ht₃ (by rw [h]; exact Subgroup.one_mem _)
  have hne : zpowers t₂ ≠ zpowers (t * t₂) := by
    intro h
    have hmem : t * t₂ ∈ zpowers t₂ := by rw [h]; exact Subgroup.mem_zpowers _
    have htm : t ∈ zpowers t₂ := by
      have := Subgroup.mul_mem _ hmem (Subgroup.inv_mem _ (Subgroup.mem_zpowers t₂))
      simpa using this
    have hle : zpowers t ≤ zpowers t₂ := (Subgroup.zpowers_le).2 htm
    have hcard₂ : Nat.card (zpowers t₂) = p := by
      rw [Nat.card_zpowers, orderOf_eq_prime ((hS.1.2 t₂ ht₂S)) ht₂1]
    have heq : zpowers t = zpowers t₂ :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcardt, hcard₂])
    exact ht₂ (by rw [heq]; exact Subgroup.mem_zpowers _)
  obtain ⟨n₁, hn₁, hn₁t⟩ := htr S t ht ht1 t₂ ht₂S ht₂1
  obtain ⟨n₂, hn₂, hn₂t⟩ := htr S t ht ht1 (t * t₂) ht₃S ht₃1
  refine ⟨n₁, hn₁, n₂, hn₂, ?_, ?_, ?_⟩
  · rw [hn₁t]
    intro h
    have hm := Subgroup.mem_zpowers t₂
    rw [h] at hm
    exact ht₂ hm
  · rw [hn₂t]
    intro h
    have hm := Subgroup.mem_zpowers (t * t₂)
    rw [h] at hm
    exact ht₃ hm
  · rw [hn₁t, hn₂t]
    exact hne

theorem normalizerThreeLines_of_equiv {p : ℕ} [Fact p.Prime] {Q K : Type} [Group Q] [Finite Q]
    [Group K] [Finite K] (e : Q ≃* K) (h : NormalizerThreeLines p K) : NormalizerThreeLines p Q := by
  intro S t ht ht1
  have hS := Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective S
  obtain ⟨n₁, hn₁, n₂, hn₂, h1, h2, h3⟩ := h (Sylow.mapSurjective (f := e.toMonoidHom) e.surjective S)
    (e t) (by rw [hS]; exact ⟨t, ht, rfl⟩) (by simpa using ht1)
  refine ⟨e.symm n₁, ?_, e.symm n₂, ?_, fun heq => h1 ?_, fun heq => h2 ?_, fun heq => h3 ?_⟩
  · rw [← psl2_mem_normalizer_map e, MulEquiv.apply_symm_apply]
    rwa [hS] at hn₁
  · rw [← psl2_mem_normalizer_map e, MulEquiv.apply_symm_apply]
    rwa [hS] at hn₂
  · have h' := congrArg (Subgroup.map e.toMonoidHom) heq
    rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers] at h'
    simpa using h'
  · have h' := congrArg (Subgroup.map e.toMonoidHom) heq
    rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers] at h'
    simpa using h'
  · have h' := congrArg (Subgroup.map e.toMonoidHom) heq
    rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers] at h'
    simpa using h'

theorem spw3_exists_int {F G : Type*} [Field F] [Group G] (ψ : Multiplicative F →* G)
    (hψ : Function.Injective ψ) {a b : Multiplicative F} (h : ψ b ∈ zpowers (ψ a)) :
    ∃ k : ℤ, (k : F) * Multiplicative.toAdd a = Multiplicative.toAdd b := by
  rw [← MonoidHom.map_zpowers] at h
  obtain ⟨b', hb, hbe⟩ := Subgroup.mem_map.1 h
  have hb' : b' = b := hψ hbe
  rw [hb'] at hb
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hb
  refine ⟨k, ?_⟩
  have h2 := congrArg Multiplicative.toAdd hk
  rw [toAdd_zpow, zsmul_eq_mul] at h2
  exact h2

theorem spw3_intCast_pow {p : ℕ} [Fact p.Prime] (k : ℤ) (hk : (k : GaloisField p 2) ≠ 0) :
    (k : GaloisField p 2) ^ (p - 1) = 1 := by
  have hkz : (k : ZMod p) ≠ 0 := by
    intro h0
    apply hk
    rw [← map_intCast (algebraMap (ZMod p) (GaloisField p 2)) k, h0, map_zero]
  have hfermat : (k : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hkz
  rw [← map_intCast (algebraMap (ZMod p) (GaloisField p 2)) k, ← map_pow, hfermat, map_one]

theorem spw3_gen_not_int {p : ℕ} [Fact p.Prime] (h5 : 5 ≤ p) {ω : (GaloisField p 2)ˣ}
    (hω : ∀ x, x ∈ zpowers ω) {m : ℕ} (hm0 : 0 < m) (hm4 : m ≤ 4) (k : ℤ) :
    (k : GaloisField p 2) ≠ (ω : GaloisField p 2) ^ m := by
  intro hk
  have hne : ((ω : GaloisField p 2) ^ m) ≠ 0 := pow_ne_zero _ ω.ne_zero
  have hk0 : (k : GaloisField p 2) ≠ 0 := by rw [hk]; exact hne
  have hferm := spw3_intCast_pow (p := p) k hk0
  rw [hk, ← pow_mul] at hferm
  have hu : ω ^ (m * (p - 1)) = 1 := by
    apply Units.ext
    simpa using hferm
  have hord : orderOf ω = p ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hω, Nat.card_units,
      GaloisField.card p 2 (by norm_num)]
  have hdvd : p ^ 2 - 1 ∣ m * (p - 1) := by
    rw [← hord]
    exact orderOf_dvd_of_pow_eq_one hu
  have hpos : 0 < m * (p - 1) := Nat.mul_pos hm0 (by omega)
  have hle := Nat.le_of_dvd hpos hdvd
  obtain ⟨q, hq⟩ : ∃ q, p = q + 5 := ⟨p - 5, by omega⟩
  have hsq : p ^ 2 - 1 = q ^ 2 + 10 * q + 24 := by
    have : p ^ 2 = q ^ 2 + 10 * q + 25 := by rw [hq]; ring
    omega
  have hp1 : p - 1 = q + 4 := by omega
  rw [hsq, hp1] at hle
  have hm' : m * (q + 4) ≤ 4 * (q + 4) := Nat.mul_le_mul_right _ hm4
  nlinarith [sq_nonneg q]

theorem normalizerThreeLines_psl2 {p : ℕ} [Fact p.Prime] (h5 : 5 ≤ p) :
    NormalizerThreeLines p (PSL(2, GaloisField p 2)) := by
  intro S t ht ht1
  have hp2 : p ≠ 2 := by omega
  obtain ⟨ψ, hψ, hψU, hψc⟩ := CFSG.AGLEmbedding.exists_torus_action hp2 (by norm_num : 1 ≤ 2) S
  have ht' : t ∈ ψ.range := by
    rw [hψU]
    exact ht
  obtain ⟨a, rfl⟩ := ht'
  obtain ⟨ω, hω⟩ := IsCyclic.exists_generator (α := (GaloisField p 2)ˣ)
  obtain ⟨c₁, hc₁N, hc₁⟩ := hψc ω
  obtain ⟨c₂, hc₂N, hc₂⟩ := hψc (ω ^ 2)
  have hx0 : Multiplicative.toAdd a ≠ 0 := by
    intro h0
    apply ht1
    rw [toAdd_eq_zero.1 h0, map_one]
  have hω0 : (ω : GaloisField p 2) ^ 2 ≠ 0 := pow_ne_zero _ ω.ne_zero
  have hc₂' : c₂ * ψ a * c₂⁻¹ =
      ψ (Multiplicative.ofAdd ((ω : GaloisField p 2) ^ 4 * Multiplicative.toAdd a)) := by
    have h4 : (((ω ^ 2 : (GaloisField p 2)ˣ) : GaloisField p 2)) ^ 2 = (ω : GaloisField p 2) ^ 4 := by
      push_cast
      ring
    rw [hc₂ a, h4]
  refine ⟨c₁, hc₁N, c₂, hc₂N, ?_, ?_, ?_⟩
  · rw [hc₁ a]
    intro heq
    have hm : ψ (Multiplicative.ofAdd ((ω : GaloisField p 2) ^ 2 * Multiplicative.toAdd a)) ∈
        zpowers (ψ a) := by
      rw [← heq]
      exact Subgroup.mem_zpowers _
    obtain ⟨k, hk⟩ := spw3_exists_int ψ hψ hm
    rw [toAdd_ofAdd] at hk
    exact spw3_gen_not_int h5 hω (by norm_num : 0 < 2) (by norm_num : 2 ≤ 4) k
      (mul_right_cancel₀ hx0 hk)
  · rw [hc₂']
    intro heq
    have hm : ψ (Multiplicative.ofAdd ((ω : GaloisField p 2) ^ 4 * Multiplicative.toAdd a)) ∈
        zpowers (ψ a) := by
      rw [← heq]
      exact Subgroup.mem_zpowers _
    obtain ⟨k, hk⟩ := spw3_exists_int ψ hψ hm
    rw [toAdd_ofAdd] at hk
    exact spw3_gen_not_int h5 hω (by norm_num : 0 < 4) (by norm_num : 4 ≤ 4) k
      (mul_right_cancel₀ hx0 hk)
  · rw [hc₁ a, hc₂']
    intro heq
    have hm : ψ (Multiplicative.ofAdd ((ω : GaloisField p 2) ^ 4 * Multiplicative.toAdd a)) ∈
        zpowers (ψ (Multiplicative.ofAdd
          ((ω : GaloisField p 2) ^ 2 * Multiplicative.toAdd a))) := by
      rw [heq]
      exact Subgroup.mem_zpowers _
    obtain ⟨k, hk⟩ := spw3_exists_int ψ hψ hm
    rw [toAdd_ofAdd, toAdd_ofAdd] at hk
    have hk' : (k : GaloisField p 2) * ((ω : GaloisField p 2) ^ 2 * Multiplicative.toAdd a) =
        (ω : GaloisField p 2) ^ 2 * ((ω : GaloisField p 2) ^ 2 * Multiplicative.toAdd a) := by
      rw [hk]
      ring
    exact spw3_gen_not_int h5 hω (by norm_num : 0 < 2) (by norm_num : 2 ≤ 4) k
      (mul_right_cancel₀ (mul_ne_zero hω0 hx0) hk')

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
