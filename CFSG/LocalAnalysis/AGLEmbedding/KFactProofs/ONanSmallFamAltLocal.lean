module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallLocalFacts
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallFamAltOrbits
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallFamAltPerm
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallFamAltTransport
import CFSG.LocalAnalysis.AGLEmbeddingD2.AltSurvivor

public section

namespace CFSG.AGLEmbedding.KFactProofs.SmallIdent

open CFSG.Open Equiv

variable {K : Type} [Group K] [Finite K] {p : ℕ}

theorem exists_inverting_of_isAltTwoP (hp : p.Prime) (hp2 : p ≠ 2) (hK : IsAltTwoP p K)
    (T : Sylow p K) : ∃ k : K, k ^ 2 = 1 ∧ ∀ t ∈ (T : Subgroup K), k * t * k⁻¹ = t⁻¹ := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨e⟩ := hK
  obtain ⟨hEab, hEcard⟩ := isElemAbelian_map_sylow hp hp2 e T
  obtain ⟨Φ, hsign, hmem⟩ := exists_altModel hp2 hEab hEcard
  set n0 : Perm (ZMod p × Fin 2) := altDg (-1) (-1) with hn0
  have hn0sign : Perm.sign n0 = 1 := by
    rw [hn0, sign_altDg]
    exact Int.units_mul_self _
  have hn0sq : n0 * n0 = 1 := by
    refine Equiv.ext fun ⟨k, s⟩ => ?_
    fin_cases s <;> simp [hn0, altDg_apply, Perm.mul_apply]
  have hn0conj : ∀ i j, n0 * altTr i j * n0⁻¹ = (altTr i j)⁻¹ := by
    intro i j
    rw [hn0, altDg_conj, altTr_inv]
    simp
  have hgsign : Perm.sign (Φ n0) = 1 := (hsign n0).trans hn0sign
  let k : K := e.symm ⟨Φ n0, Perm.mem_alternatingGroup.2 hgsign⟩
  have hιk : altPermEmbed e k = Φ n0 := by simp [k, altPermEmbed]
  refine ⟨k, ?_, ?_⟩
  · apply altPermEmbed_injective e
    rw [map_pow, hιk, sq, ← map_mul, hn0sq, map_one, map_one]
  · intro t ht
    apply altPermEmbed_injective e
    have htE : altPermEmbed e t ∈ ((T : Subgroup K).map (altPermEmbed e)) := ⟨t, ht, rfl⟩
    obtain ⟨x, hx⟩ := Φ.surjective (altPermEmbed e t)
    obtain ⟨i, j, rfl⟩ := (hmem x).1 (hx ▸ htE)
    simp only [map_mul, map_inv, hιk]
    rw [← hx, ← map_inv, ← map_mul, ← map_mul, hn0conj, map_inv]

theorem centralizer_le_of_isAltTwoP (hp : p.Prime) (hp2 : p ≠ 2) (hK : IsAltTwoP p K)
    (T : Sylow p K) {g : K} (hg : ∀ t ∈ (T : Subgroup K), g * t = t * g) :
    g ∈ (T : Subgroup K) := by
  have : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨e⟩ := hK
  obtain ⟨hEab, hEcard⟩ := isElemAbelian_map_sylow hp hp2 e T
  obtain ⟨a₁, ha₁, a₂, ha₂, O₁, O₂, hO₁, hO₂, hd, hm₁, hm₂⟩ :=
    CFSG.AGLEmbeddingD2.exists_cycles_of_isElemAbelian hp hp2 (by omega) hEab hEcard
  have hcomm : ∀ a ∈ (T : Subgroup K).map (altPermEmbed e),
      altPermEmbed e g * a = a * altPermEmbed e g := by
    intro a ha
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 ha
    rw [← map_mul, ← map_mul, hg t ht]
  obtain ⟨i, j, hij⟩ := CFSG.AGLEmbeddingD2.AltSurvivor.exists_zpow_mul_zpow_eq
    (isCycle_of_moves hp (hEab.2 a₁ ha₁) hO₁ hm₁) (isCycle_of_moves hp (hEab.2 a₂ ha₂) hO₂ hm₂)
    hm₁ hm₂ hd (mem_or_mem_of_card hO₁ hO₂ hd (Fintype.card_fin _)) (hcomm a₁ ha₁)
    (hcomm a₂ ha₂)
  have hmem : altPermEmbed e g ∈ (T : Subgroup K).map (altPermEmbed e) := by
    rw [hij]
    exact mul_mem (zpow_mem ha₁ i) (zpow_mem ha₂ j)
  obtain ⟨t, ht, hte⟩ := Subgroup.mem_map.1 hmem
  exact altPermEmbed_injective e hte ▸ ht

theorem pow_eq_one_of_mem_isAltTwoP (hp : p.Prime) (hp2 : p ≠ 2) (hK : IsAltTwoP p K)
    (T : Sylow p K) {t : K} (ht : t ∈ (T : Subgroup K)) : t ^ p = 1 := by
  obtain ⟨e⟩ := hK
  obtain ⟨hEab, -⟩ := isElemAbelian_map_sylow hp hp2 e T
  apply altPermEmbed_injective e
  rw [map_pow, map_one]
  exact hEab.2 _ ⟨t, ht, rfl⟩

theorem mul_comm_of_mem_isAltTwoP (hp : p.Prime) (hp2 : p ≠ 2) (hK : IsAltTwoP p K)
    (T : Sylow p K) {a b : K} (ha : a ∈ (T : Subgroup K)) (hb : b ∈ (T : Subgroup K)) :
    a * b = b * a := by
  obtain ⟨e⟩ := hK
  obtain ⟨hEab, -⟩ := isElemAbelian_map_sylow hp hp2 e T
  apply altPermEmbed_injective e
  rw [map_mul, map_mul]
  have := hEab.1.is_comm.comm
    (⟨altPermEmbed e a, a, ha, rfl⟩ : (T : Subgroup K).map (altPermEmbed e))
    ⟨altPermEmbed e b, b, hb, rfl⟩
  exact congrArg Subtype.val this

theorem eq_one_of_inverted (hp : p.Prime) (hp2 : p ≠ 2) (hK : IsAltTwoP p K) (T : Sylow p K)
    {t k : K} (ht : t ∈ (T : Subgroup K)) (hk : k * t * k⁻¹ = t⁻¹) (hkt : k * t = t * k) :
    t = 1 := by
  have hpt : t ^ p = 1 := pow_eq_one_of_mem_isAltTwoP hp hp2 hK T ht
  have h2 : t ^ 2 = 1 := by
    have h1 : t = t⁻¹ := by
      rw [← hk, hkt]
      group
    calc t ^ 2 = t * t := sq t
      _ = t * t⁻¹ := by rw [← h1]
      _ = 1 := mul_inv_cancel t
  have hord : orderOf t ∣ Nat.gcd p 2 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hpt) (orderOf_dvd_of_pow_eq_one h2)
  have hcop : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).2 hp2
  rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at hord
  exact hord

theorem torus_of_isAltTwoP (hp : p.Prime) (hp2 : p ≠ 2) (hK : IsAltTwoP p K) (T : Sylow p K) :
    ∃ T₀ : Subgroup K, T₀ ≤ Subgroup.normalizer ((T : Subgroup K) : Set K) ∧
      p.Coprime (Nat.card T₀) ∧ (T : Subgroup K) ⊓ Subgroup.centralizer (T₀ : Set K) = ⊥ := by
  obtain ⟨k, hk2, hkT⟩ := exists_inverting_of_isAltTwoP hp hp2 hK T
  have hkN : k ∈ Subgroup.normalizer ((T : Subgroup K) : Set K) := by
    apply Subgroup.mem_normalizer_fintype
    intro t ht
    rw [hkT t ht]
    exact Subgroup.inv_mem _ ht
  refine ⟨Subgroup.zpowers k, Subgroup.zpowers_le.2 hkN, ?_, ?_⟩
  · rw [Nat.card_zpowers]
    exact ((Nat.coprime_primes hp Nat.prime_two).2 hp2).coprime_dvd_right
      (orderOf_dvd_of_pow_eq_one hk2)
  · rw [eq_bot_iff]
    rintro t ⟨htT, htC⟩
    have hkt : k * t = t * k := Subgroup.mem_centralizer_iff.1 htC k (Subgroup.mem_zpowers k)
    exact Subgroup.mem_bot.2 (eq_one_of_inverted hp hp2 hK T htT (hkT t htT) hkt)

theorem center_eq_bot_of_isAltTwoP (hp : p.Prime) (hp2 : p ≠ 2) (hK : IsAltTwoP p K) :
    Subgroup.center K = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨T⟩ : Nonempty (Sylow p K) := inferInstance
  obtain ⟨k, -, hkT⟩ := exists_inverting_of_isAltTwoP hp hp2 hK T
  rw [eq_bot_iff]
  intro z hz
  have hzc : ∀ g : K, z * g = g * z := fun g => (Subgroup.mem_center_iff.1 hz g).symm
  have hzT : z ∈ (T : Subgroup K) :=
    centralizer_le_of_isAltTwoP hp hp2 hK T fun t _ => hzc t
  exact Subgroup.mem_bot.2 (eq_one_of_inverted hp hp2 hK T hzT (hkT z hzT) (hzc k).symm)

theorem invariant_of_isAltTwoP (hp : p.Prime) (hp2 : p ≠ 2) (hK : IsAltTwoP p K) (T : Sylow p K)
    {V : Subgroup K} (hVT : V ≤ (T : Subgroup K)) (hV : V ≠ ⊥)
    (hVN : Subgroup.normalizer ((T : Subgroup K) : Set K) ≤ Subgroup.normalizer (V : Set K)) :
    V = (T : Subgroup K) := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  set O : Set K := (V : Set K) \ {1} with hOdef
  have hO : O ⊆ (T : Set K) \ {1} := fun x hx => ⟨hVT hx.1, hx.2⟩
  have hinv : ∀ n ∈ Subgroup.normalizer ((T : Subgroup K) : Set K), ∀ t ∈ O, n * t * n⁻¹ ∈ O := by
    intro n hn t ht
    refine ⟨(Subgroup.mem_normalizer_iff.1 (hVN hn) t).1 ht.1, fun h => ht.2 ?_⟩
    have h1 : n * t * n⁻¹ = 1 := h
    simpa using h1
  have horb := orbits_of_isAltTwoP hp hp2 hK T O hO hinv
  have hcardV : Nat.card V = O.ncard + 1 := by
    have h1 : (1 : K) ∈ (V : Set K) := V.one_mem
    have h2 := Set.ncard_sdiff_singleton_add_one h1 (Set.toFinite _)
    have h3 : Nat.card V = (V : Set K).ncard := Nat.card_coe_set_eq (V : Set K)
    rw [h3, ← h2]
  have hT : Nat.card T = p ^ 2 := by
    obtain ⟨e⟩ := hK
    exact sylowSq_of_isAltTwoP hp hp2 ⟨e⟩ T
  have hdvd : Nat.card V ∣ p ^ 2 := hT ▸ Subgroup.card_dvd_of_le hVT
  obtain ⟨k, hk, hkV⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  have hVne : Nat.card V ≠ 1 := fun h => hV (Subgroup.eq_bot_of_card_eq _ h)
  refine Subgroup.eq_of_le_of_card_ge hVT ?_
  rw [hT]
  interval_cases k
  · exact absurd (by simpa using hkV) hVne
  · exfalso
    rw [pow_one] at hkV
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 3 := ⟨p - 3, by omega⟩
    have hpow1 : 1 ≤ (q + 3) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have hq1 : q + 3 - 1 = q + 2 := by omega
    rcases horb with h | h | h | h
    · rw [h] at hcardV
      omega
    · rw [h] at hcardV
      have := Nat.sub_add_cancel hpow1
      nlinarith
    · rw [h, hq1] at hcardV
      omega
    · rw [h, hq1] at hcardV
      nlinarith
  · rw [hkV]

theorem localFacts_of_isAltTwoP (hp : p.Prime) (hp2 : p ≠ 2) (hK : IsAltTwoP p K)
    (T : Sylow p K) : LocalFacts p K T :=
  { center := center_eq_bot_of_isAltTwoP hp hp2 hK
    centralizer_le := fun _ hg => centralizer_le_of_isAltTwoP hp hp2 hK T hg
    torus := torus_of_isAltTwoP hp hp2 hK T
    invariant := fun _ hVT hV hVN => Or.inl (invariant_of_isAltTwoP hp hp2 hK T hVT hV hVN) }

end CFSG.AGLEmbedding.KFactProofs.SmallIdent
