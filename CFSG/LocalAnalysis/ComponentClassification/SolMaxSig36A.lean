module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig32C

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem exists_conj_of_odd_mul {G : Type*} [Group G] {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hodd : Odd (orderOf (a * b))) : ∃ k : ℕ, (a * b) ^ k * a * ((a * b) ^ k)⁻¹ = b := by
  obtain ⟨k, hk⟩ := hodd
  refine ⟨k, ?_⟩
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have h0 : a * (a * b) ^ k * a⁻¹ = ((a * b)⁻¹) ^ k := by
    rw [← conj_pow]
    congr 1
    rw [mul_inv_rev, hainv, hbinv]
    calc a * (a * b) * a = (a * a) * b * a := by group
      _ = b * a := by rw [ha, one_mul]
  have h1 : a * ((a * b) ^ k)⁻¹ * a⁻¹ = (a * b) ^ k := by
    calc a * ((a * b) ^ k)⁻¹ * a⁻¹ = (a * (a * b) ^ k * a⁻¹)⁻¹ := by group
      _ = (((a * b)⁻¹) ^ k)⁻¹ := by rw [h0]
      _ = (a * b) ^ k := by rw [inv_pow, inv_inv]
  have h2 : (a * b) ^ (2 * k) = (a * b)⁻¹ := by
    have h3 : (a * b) ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one _
    rw [pow_succ] at h3
    exact eq_inv_of_mul_eq_one_left h3
  calc (a * b) ^ k * a * ((a * b) ^ k)⁻¹ =
      (a * b) ^ k * (a * ((a * b) ^ k)⁻¹ * a⁻¹) * a := by group
    _ = (a * b) ^ k * (a * b) ^ k * a := by rw [h1]
    _ = (a * b) ^ (2 * k) * a := by rw [two_mul, pow_add]
    _ = (a * b)⁻¹ * a := by rw [h2]
    _ = b := by rw [mul_inv_rev, hainv, hbinv, mul_assoc, ha, mul_one]

theorem cycleType_eq_replicate_of_four {m : ℕ} {σ : Perm (Fin m)} (hσ : σ * σ = 1)
    (h4 : σ.support.card = 4) : σ.cycleType = Multiset.replicate 2 2 := by
  have hne : σ ≠ 1 := by
    rintro rfl
    rw [Perm.support_one, Finset.card_empty] at h4
    omega
  have hord : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact hσ) hne
  obtain ⟨k, hk⟩ := Perm.cycleType_prime_order (σ := σ) (by rw [hord]; exact Nat.prime_two)
  rw [hord] at hk
  have hsum := Perm.sum_cycleType σ
  rw [hk, h4, Multiset.sum_replicate, smul_eq_mul] at hsum
  rw [hk, show k + 1 = 2 by omega]

theorem mem_alternatingGroup_of_four {m : ℕ} {σ : Perm (Fin m)} (hσ : σ * σ = 1)
    (h4 : σ.support.card = 4) : σ ∈ alternatingGroup (Fin m) := by
  rw [Perm.mem_alternatingGroup, Perm.sign_of_cycleType, cycleType_eq_replicate_of_four hσ h4,
    Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul]
  decide

theorem exists_alt_conj_of_four {m : ℕ} (hm : 6 ≤ m) {σ σ' : Perm (Fin m)} (hσ : σ * σ = 1)
    (hσ' : σ' * σ' = 1) (h4 : σ.support.card = 4) (h4' : σ'.support.card = 4) :
    ∃ π : alternatingGroup (Fin m), (π : Perm (Fin m)) * σ * (π : Perm (Fin m))⁻¹ = σ' := by
  have hc : IsConj σ σ' := by
    rw [Perm.isConj_iff_cycleType_eq, cycleType_eq_replicate_of_four hσ h4,
      cycleType_eq_replicate_of_four hσ' h4']
  have hc' := alternatingGroup.isConj_of (σ := ⟨σ, mem_alternatingGroup_of_four hσ h4⟩)
    (τ := ⟨σ', mem_alternatingGroup_of_four hσ' h4'⟩) hc (by rw [h4, Fintype.card_fin]; omega)
  obtain ⟨π, hπ⟩ := isConj_iff.mp hc'
  exact ⟨π, congrArg Subtype.val hπ⟩

theorem centralizer_conj_le {H : Subgroup X} {t c : X} (hc : c ∈ H)
    (hCt : centralizer ({t} : Set X) ≤ H) :
    centralizer ({c * t * c⁻¹} : Set X) ≤ H := by
  intro z hz
  have h1 : c⁻¹ * z * c ∈ centralizer ({t} : Set X) := by
    rw [mem_centralizer_singleton_iff] at hz ⊢
    calc c⁻¹ * z * c * t = c⁻¹ * (z * (c * t * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * t * c⁻¹) * z) * c := by rw [hz]
      _ = t * (c⁻¹ * z * c) := by group
  have h2 := mul_mem (mul_mem hc (hCt h1)) (inv_mem hc)
  have h3 : c * (c⁻¹ * z * c) * c⁻¹ = z := by group
  rwa [h3] at h2

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  (S : Sig36 X t J n e E D)
include S

theorem centralizer_le_of_conj_t (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    (hT13 : Sol76T13.SolomonThm13Simple) (hML : Sol78.MaximalityLemmaInput)
    (hSch : SolAltLit.SchurAlternatingMultiplierInput) {M : Subgroup X} {m : ℕ} (hm : 6 ≤ m)
    (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hHM : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X))
    (hker : normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
        UnbalancedLayer.coreActionKernel M ≤
      (pPrimeCore 2 ↥(normalizer (Sol78.signalizerCompletion E E : Set X))).map
        (normalizer (Sol78.signalizerCompletion E E : Set X)).subtype)
    {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin m)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin m)} (hρ : IsPermAction θ ρ)
    (htM : t ∈ normalizer (M : Set X)) (ht4 : (ρ ⟨t, htM⟩).support.card = 4) {x : X}
    (hxH : x ∈ normalizer (Sol78.signalizerCompletion E E : Set X)) (hx2 : x * x = 1)
    (hx4 : (ρ ⟨x, hHM hxH⟩).support.card = 4) :
    centralizer ({x} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X) := by
  classical
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  have hCt : centralizer ({t} : Set X) ≤ H :=
    S.centralizer_le_normalizer_completion h33 h35 hT13 hML hSch
  have htH : t ∈ H := hCt (mem_centralizer_singleton_iff.mpr rfl)
  have ht2 : t * t = 1 := by rw [← sq, ← S.pair.1.1, pow_orderOf_eq_one]
  have hsq : ∀ g : ↥(normalizer (M : Set X)), (g : X) * g = 1 → ρ g * ρ g = 1 := by
    intro g hg
    rw [← map_mul, show g * g = 1 from Subtype.ext hg, map_one]
  obtain ⟨π, hπ⟩ := exists_alt_conj_of_four hm (hsq _ ht2) (hsq _ hx2) ht4 hx4
  obtain ⟨q, hq⟩ := θ.surjective π
  obtain ⟨h₀, rfl⟩ := QuotientGroup.mk_surjective q
  have hρh₀ := hρ.apply_of_mem (by omega) h₀
  rw [hq] at hρh₀
  have hh₀N : (h₀ : X) ∈ normalizer (M : Set X) := le_normalizer h₀.2
  have hh₀H : (h₀ : X) ∈ H := hMH h₀.2
  set t' := (h₀ : X) * t * (h₀ : X)⁻¹ with ht'def
  have ht'N : t' ∈ normalizer (M : Set X) := mul_mem (mul_mem hh₀N htM) (inv_mem hh₀N)
  have ht'H : t' ∈ H := mul_mem (mul_mem hh₀H htH) (inv_mem hh₀H)
  have ht'2 : t' * t' = 1 := by
    rw [ht'def]
    calc (h₀ : X) * t * (h₀ : X)⁻¹ * ((h₀ : X) * t * (h₀ : X)⁻¹) =
        (h₀ : X) * (t * t) * (h₀ : X)⁻¹ := by group
      _ = 1 := by rw [ht2]; group
  have hρt' : ρ ⟨t', ht'N⟩ = ρ ⟨x, hHM hxH⟩ := by
    have h1 : (⟨t', ht'N⟩ : ↥(normalizer (M : Set X))) =
        ⟨h₀, hh₀N⟩ * ⟨t, htM⟩ * (⟨h₀, hh₀N⟩ : ↥(normalizer (M : Set X)))⁻¹ := rfl
    rw [h1, map_mul, map_mul, map_inv, hρh₀, ← hπ]
  have hprodN : t' * x ∈ normalizer (M : Set X) := mul_mem ht'N (hHM hxH)
  have hρprod : ρ ⟨t' * x, hprodN⟩ = 1 := by
    have h1 : (⟨t' * x, hprodN⟩ : ↥(normalizer (M : Set X))) = ⟨t', ht'N⟩ * ⟨x, hHM hxH⟩ :=
      rfl
    rw [h1, map_mul, hρt']
    exact hsq _ hx2
  have hK := hρ.mem_coreActionKernel hprodN hρprod
  have hO := hker (mem_inf.mpr ⟨mul_mem ht'H hxH, hK⟩)
  have hodd : Odd (orderOf (t' * x)) := by
    have hOodd : Odd (Nat.card ↥((pPrimeCore 2 ↥H).map H.subtype)) := by
      rw [card_map_of_injective H.subtype_injective]
      exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
    have h1 := orderOf_dvd_natCard (⟨t' * x, hO⟩ : ↥((pPrimeCore 2 ↥H).map H.subtype))
    rw [Subgroup.orderOf_mk] at h1
    exact hOodd.of_dvd_nat h1
  obtain ⟨k, hk⟩ := exists_conj_of_odd_mul ht'2 hx2 hodd
  have hcH : (t' * x) ^ k * (h₀ : X) ∈ H := mul_mem (pow_mem (mul_mem ht'H hxH) k) hh₀H
  have hxc : ((t' * x) ^ k * (h₀ : X)) * t * ((t' * x) ^ k * (h₀ : X))⁻¹ = x := by
    calc ((t' * x) ^ k * (h₀ : X)) * t * ((t' * x) ^ k * (h₀ : X))⁻¹ =
        (t' * x) ^ k * ((h₀ : X) * t * (h₀ : X)⁻¹) * ((t' * x) ^ k)⁻¹ := by group
      _ = x := hk
  have h := centralizer_conj_le hcH hCt
  rwa [hxc] at h

end Sig36

end CFSG.ComponentClassification.SolMax
