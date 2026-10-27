module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxDiagA
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig33B

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

theorem exists_apply_eq_of_odd_card {α : Type*} [Finite α] (hodd : Odd (Nat.card α))
    (σ : Perm α) (hσ : ∀ x, σ (σ x) = x) : ∃ x, σ x = x := by
  classical
  have := Fintype.ofFinite α
  by_contra h
  push Not at h
  have hσ2 : σ ^ 2 ^ 1 = 1 := by
    ext x
    simp [pow_two, hσ x]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := Perm.card_compl_support_modEq (p := 2) (n := 1) hσ2
  have hsupp : σ.supportᶜ = ∅ := by
    ext x
    simp [Perm.mem_support, h x]
  rw [hsupp, Finset.card_empty] at h1
  rw [Nat.card_eq_fintype_card] at hodd
  obtain ⟨k, hk⟩ := hodd
  rw [hk] at h1
  unfold Nat.ModEq at h1
  omega

variable {X : Type} [Group X]

theorem exists_commute_of_mem_coset [Finite X] {K : Subgroup X} (hK : Odd (Nat.card K))
    {t x : X} (htt : t * t = 1) (htK : ∀ k ∈ K, t * k * t⁻¹ ∈ K)
    (hx : x⁻¹ * (t * x * t⁻¹) ∈ K) : ∃ k ∈ K, t * (x * k) = x * k * t := by
  classical
  set k₀ := x⁻¹ * (t * x * t⁻¹) with hk₀
  have hk₀t : k₀ * (t * k₀ * t⁻¹) = 1 := by
    calc k₀ * (t * k₀ * t⁻¹) = x⁻¹ * (t * t) * x * (t * t)⁻¹ := by rw [hk₀]; group
      _ = 1 := by rw [htt]; group
  have hinv : ∀ k : X, k₀ * (t * (k₀ * (t * k * t⁻¹)) * t⁻¹) = k := by
    intro k
    calc k₀ * (t * (k₀ * (t * k * t⁻¹)) * t⁻¹) =
        (k₀ * (t * k₀ * t⁻¹)) * ((t * t) * k * (t * t)⁻¹) := by group
      _ = k := by rw [hk₀t, htt]; group
  let σ : Perm ↥K :=
    { toFun := fun k => ⟨k₀ * (t * k * t⁻¹), mul_mem hx (htK k k.2)⟩
      invFun := fun k => ⟨k₀ * (t * k * t⁻¹), mul_mem hx (htK k k.2)⟩
      left_inv := fun k => Subtype.ext (hinv k)
      right_inv := fun k => Subtype.ext (hinv k) }
  obtain ⟨k, hk⟩ := exists_apply_eq_of_odd_card hK σ fun k => Subtype.ext (hinv k)
  have hk' : k₀ * (t * (k : X) * t⁻¹) = k := congrArg Subtype.val hk
  refine ⟨k, k.2, ?_⟩
  have htx : t * x * t⁻¹ = x * k₀ := by rw [hk₀]; group
  calc t * (x * (k : X)) = (t * x * t⁻¹) * (t * (k : X) * t⁻¹) * t := by group
    _ = x * (k₀ * (t * (k : X) * t⁻¹)) * t := by rw [htx]; group
    _ = x * k * t := by rw [hk']

theorem mem_of_conj_mem [Finite X] {X₀ K : Subgroup X} (hodd : Odd (Nat.card X₀)) {t : X}
    (htt : t * t = 1) (htX : ∀ x ∈ X₀, t * x * t⁻¹ ∈ X₀) (htK : ∀ k ∈ K, t * k * t⁻¹ ∈ K)
    (hC : ∀ x ∈ X₀, t * x = x * t → x ∈ K) {x : X} (hx : x ∈ X₀)
    (hxK : x⁻¹ * (t * x * t⁻¹) ∈ K) : x ∈ K := by
  have hodd' : Odd (Nat.card ↥(X₀ ⊓ K)) := hodd.of_dvd_nat (card_dvd_of_le inf_le_left)
  have hmem : x⁻¹ * (t * x * t⁻¹) ∈ X₀ ⊓ K :=
    Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hx) (htX x hx), hxK⟩
  obtain ⟨k, hk, hkc⟩ := exists_commute_of_mem_coset hodd' htt
    (fun k hk => Subgroup.mem_inf.mpr
      ⟨htX k (Subgroup.mem_inf.mp hk).1, htK k (Subgroup.mem_inf.mp hk).2⟩) hmem
  have hk' := Subgroup.mem_inf.mp hk
  have h1 : x * k ∈ K := hC _ (mul_mem hx hk'.1) hkc
  have h2 : x = (x * k) * k⁻¹ := by group
  rw [h2]
  exact mul_mem h1 (inv_mem hk'.2)

theorem inf_centralizer_le_coreActionKernel (hbal : Sol78.BalanceTwoComponentInput) [Finite X]
    {t a : X} {J : Subgroup X} {n : ℕ} (ht1 : t ≠ 1) (htt : t * t = 1)
    (hJC : J ≤ centralizer ({t} : Set X))
    (hJpc : IsPComponent 2 (J.subgroupOf (centralizer ({t} : Set X))))
    {θ : ↥J ⧸ pPrimeCore 2 ↥J ≃* alternatingGroup (Fin n)}
    {ρ : ↥(normalizer (J : Set X)) →* Perm (Fin n)} (hρ : IsPermAction θ ρ)
    (ha : a ∈ normalizer (J : Set X)) (ha2 : a * a = 1) (ha1 : a ≠ 1) (hat : a * t = t * a)
    (h5 : 5 ≤ n - (ρ ⟨a, ha⟩).support.card) :
    (pPrimeCore 2 ↥(centralizer ({a} : Set X))).map (centralizer ({a} : Set X)).subtype ⊓
        centralizer ({t} : Set X) ≤ UnbalancedLayer.coreActionKernel J := by
  have hS : zpowers a ≠ ⊥ := fun h => ha1 (zpowers_eq_bot.mp h)
  have hT : zpowers t ≠ ⊥ := fun h => ht1 (zpowers_eq_bot.mp h)
  have hST : zpowers a ≤ centralizer ((zpowers t : Subgroup X) : Set X) := by
    rw [centralizer_zpowers_eq', zpowers_le, mem_centralizer_singleton_iff]
    exact hat
  obtain ⟨-, hbc, -⟩ := hbal X (zpowers a) (zpowers t) hS hT
    (IsElementaryAbelian.zpowers_of_pow_eq_one (by rw [sq]; exact ha2))
    (IsElementaryAbelian.zpowers_of_pow_eq_one (by rw [sq]; exact htt)) hST
  have hCt' : centralizer ((zpowers t : Subgroup X) : Set X) = centralizer ({t} : Set X) :=
    centralizer_zpowers_eq' t
  have hCa' : centralizer ((zpowers a : Subgroup X) : Set X) = centralizer ({a} : Set X) :=
    centralizer_zpowers_eq' a
  rw [hCt', hCa'] at hbc
  obtain ⟨hXN, -⟩ := hbc J ⟨hJC, hJpc⟩
  have hXNJ := le_normalizer_of_le_normalizer_sup hJC hJpc inf_le_right hXN
  exact hρ.le_coreActionKernel_of_fix ha ha2 h5 hXNJ inf_le_left

theorem not_le_coreActionKernel_of_le [Finite X] {N T : Subgroup X} (hTN : T ≤ N)
    (hTperf : ⁅T, T⁆ = T) (hTq : Nontrivial (↥T ⧸ pPrimeCore 2 ↥T)) :
    ¬ T ≤ UnbalancedLayer.coreActionKernel N := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hTK
  have hTO : T ≤ (pPrimeCore 2 ↥N).map N.subtype := by
    rw [← hTperf, commutator_le]
    intro g hg z hz
    have h1 := (UnbalancedLayer.mem_coreActionKernel.mp (hTK (inv_mem hz))).2 g⁻¹
      (inv_mem (hTN hg))
    rw [commutatorElement_def]
    simpa using h1
  have hodd : Nat.Coprime 2 (Nat.card T) := by
    have h1 : Nat.card T ∣ Nat.card ((pPrimeCore 2 ↥N).map N.subtype) := card_dvd_of_le hTO
    rw [card_map_of_injective N.subtype_injective] at h1
    exact Nat.Coprime.coprime_dvd_right h1 pPrimeCore_coprime_card
  have htop : pPrimeCore 2 ↥T = ⊤ := by
    rw [eq_top_iff]
    exact le_sSup ⟨inferInstance, by rwa [Subgroup.card_top]⟩
  have : Subsingleton (↥T ⧸ pPrimeCore 2 ↥T) := QuotientGroup.subsingleton_iff.mpr htop
  exact false_of_nontrivial_of_subsingleton (↥T ⧸ pPrimeCore 2 ↥T)

variable {N : Subgroup X} {r : ℕ} {ψ : ↥N ⧸ Open.fusionZStar ↥N ≃* alternatingGroup (Fin r)}
  {ρ : ↥(normalizer (N : Set X)) →* Perm (Fin r)}

theorem IsPermActionZ.eq_one_of_mem_coreActionKernel (hρ : IsPermActionZ ψ ρ) (hr : 4 ≤ r)
    {g : X} (hg : g ∈ UnbalancedLayer.coreActionKernel N) : ρ ⟨g, hg.1⟩ = 1 := by
  apply GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup r hr
  rw [map_one]
  refine MulEquiv.ext fun a => Subtype.ext ?_
  obtain ⟨q, rfl⟩ := ψ.surjective a
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  change ρ _ * _ * (ρ _)⁻¹ = (ψ (x : ↥N ⧸ Open.fusionZStar ↥N) : Perm (Fin r))
  rw [← hρ]
  have hgx : g * (x : X) * g⁻¹ ∈ N := (mem_normalizer_iff.mp hg.1 x).mp x.2
  have h2 : (N.normalizerMonoidHom ⟨g, hg.1⟩ x : ↥N) = ⟨g * x * g⁻¹, hgx⟩ := rfl
  rw [h2]
  have h3 := (UnbalancedLayer.mem_coreActionKernel.mp (inv_mem hg)).2 x x.2
  rw [inv_inv] at h3
  obtain ⟨o, ho, hoeq⟩ := h3
  have h4 : ((⟨g * x * g⁻¹, hgx⟩ : ↥N) : ↥N ⧸ Open.fusionZStar ↥N) =
      (x : ↥N ⧸ Open.fusionZStar ↥N) := by
    symm
    rw [QuotientGroup.eq]
    have h5 : x⁻¹ * ⟨g * x * g⁻¹, hgx⟩ = o := Subtype.ext (by
      change (x : X)⁻¹ * (g * x * g⁻¹) = (o : X)
      rw [show (x : X)⁻¹ * (g * x * g⁻¹) = (x : X)⁻¹ * g * x * g⁻¹ by group]
      exact hoeq.symm)
    rw [h5]
    exact Sol78.pPrimeCore_le_fusionZStar _ ho
  rw [h4]

theorem IsPermActionZ.mem_fusionZStar_of_eq_one (hρ : IsPermActionZ ψ ρ) (hr : 4 ≤ r)
    (m : ↥N) (h1 : ρ ⟨m, le_normalizer m.2⟩ = 1) : m ∈ Open.fusionZStar ↥N := by
  rw [hρ.apply_of_mem hr m] at h1
  have h2 : ψ (m : ↥N ⧸ Open.fusionZStar ↥N) = 1 := Subtype.ext h1
  rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] at h2
  exact h2

end CFSG.ComponentClassification.SolMax
