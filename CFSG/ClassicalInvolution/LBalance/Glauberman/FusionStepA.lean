module

public import CFSG.ClassicalInvolution.LBalance.Glauberman.SylowTools
public import CFSG.ClassicalInvolution.LBalance.Glauberman.ConjTools

public section

namespace CFSG.ClassicalInvolution.GlaubermanAut

open CFSG.ABGLocalTools

section StepA

variable {Ω : Type*} [Group Ω]

theorem conj_mem_centralizer_of_mem_normalizer {Q : Subgroup Ω} {g x : Ω}
    (hg : g ∈ Subgroup.normalizer (Q : Set Ω)) (hx : x ∈ Subgroup.centralizer (Q : Set Ω)) :
    g * x * g⁻¹ ∈ Subgroup.centralizer (Q : Set Ω) := by
  rw [Subgroup.mem_centralizer_iff] at hx ⊢
  intro q hq
  have hq' : g⁻¹ * q * g ∈ Q := by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hg) q).1 hq
    simpa using this
  have := hx _ hq'
  calc q * (g * x * g⁻¹) = g * ((g⁻¹ * q * g) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * q * g)) * g⁻¹ := by rw [this]
    _ = g * x * g⁻¹ * q := by group

theorem normalizer_le_normalizer_centralizer (Q : Subgroup Ω) :
    Subgroup.normalizer (Q : Set Ω) ≤
      Subgroup.normalizer (Subgroup.centralizer (Q : Set Ω) : Set Ω) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => conj_mem_centralizer_of_mem_normalizer hg hx, fun hx => ?_⟩
  have := conj_mem_centralizer_of_mem_normalizer (inv_mem hg) hx
  simpa [mul_assoc] using this

theorem inf_normalizer_le_normalizer_inf_centralizer (T Q : Subgroup Ω) :
    T ⊓ Subgroup.normalizer (Q : Set Ω) ≤
      Subgroup.normalizer ((T ⊓ Subgroup.centralizer (Q : Set Ω) : Subgroup Ω) : Set Ω) := by
  rintro g ⟨hgT, hgN⟩
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ g' : Ω, g' ∈ T → g' ∈ Subgroup.normalizer (Q : Set Ω) →
      ∀ x, x ∈ T ⊓ Subgroup.centralizer (Q : Set Ω) →
        g' * x * g'⁻¹ ∈ T ⊓ Subgroup.centralizer (Q : Set Ω) := by
    intro g' hg'T hg'N x hx
    exact ⟨T.mul_mem (T.mul_mem hg'T hx.1) (T.inv_mem hg'T),
      conj_mem_centralizer_of_mem_normalizer hg'N hx.2⟩
  intro x
  refine ⟨key g hgT hgN x, fun hx => ?_⟩
  have := key g⁻¹ (T.inv_mem hgT) (inv_mem hgN) _ hx
  simpa [mul_assoc] using this

variable [Finite Ω] {p : ℕ} [Fact p.Prime]

theorem exists_primePower_not_mem_normalizer {K E P : Subgroup Ω} (hEK : IsSylowOf p E K)
    (hEP : E ≤ Subgroup.normalizer (P : Set Ω)) {k : Ω} (hkK : k ∈ K)
    (hkP : k ∉ Subgroup.normalizer (P : Set Ω)) :
    ∃ h ∈ K, (∃ r : ℕ, r.Prime ∧ r ≠ p ∧ ∃ n : ℕ, orderOf h = r ^ n) ∧
      h ∉ Subgroup.normalizer (P : Set Ω) := by
  set NK : Subgroup Ω := K ⊓ Subgroup.normalizer (P : Set Ω) with hNK
  have hEK' : E ≤ K := hEK.le
  have hENK : E ≤ NK := le_inf hEK' hEP
  have hNKK : NK ≤ K := inf_le_left
  have h1 : E.relIndex NK * NK.relIndex K = E.relIndex K :=
    Subgroup.relIndex_mul_relIndex E NK K hENK hNKK
  have hpE : ¬ p ∣ E.relIndex K := ((isSylowOf_iff).1 hEK).2.2
  have hpNK : ¬ p ∣ NK.relIndex K := fun h => hpE (h1 ▸ Dvd.dvd.mul_left h _)
  have hne : NK.relIndex K ≠ 1 := by
    intro h
    rw [Subgroup.relIndex_eq_one] at h
    exact hkP (h hkK).2
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd hne
  have hrp : r ≠ p := by
    rintro rfl
    exact hpNK hrd
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨R, hR⟩ := exists_isSylowOf r K
  have hRK : R ≤ K := hR.le
  have hnot : ¬ R ≤ Subgroup.normalizer (P : Set Ω) := by
    intro hRP
    have hRNK : R ≤ NK := le_inf hRK hRP
    have h2 : R.relIndex NK * NK.relIndex K = R.relIndex K :=
      Subgroup.relIndex_mul_relIndex R NK K hRNK hNKK
    have hrR : ¬ r ∣ R.relIndex K := ((isSylowOf_iff).1 hR).2.2
    exact hrR (h2 ▸ Dvd.dvd.mul_left hrd _)
  obtain ⟨h, hhR, hhP⟩ := Set.not_subset.1 hnot
  refine ⟨h, hRK hhR, ⟨r, hr, hrp, ?_⟩, hhP⟩
  have hRp : IsPGroup r R := hR.isPGroup
  obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.1 hRp) ⟨h, hhR⟩
  exact ⟨n, by rwa [Subgroup.orderOf_mk] at hn⟩

theorem step_cd {H T P Q : Subgroup Ω} (hPT : T ≤ Subgroup.normalizer (P : Set Ω)) (hTH : T ≤ H)
    (hPQ : P ≤ Q) (hb : IsSylowOf p (T ⊓ Subgroup.normalizer (Q : Set Ω))
      (H ⊓ Subgroup.normalizer (Q : Set Ω)))
    {k₀ : Ω} (hk₀ : k₀ ∈ H ⊓ Subgroup.normalizer (Q : Set Ω))
    (hk₀P : k₀ ∉ Subgroup.normalizer (P : Set Ω)) :
    IsSylowOf p (T ⊓ Subgroup.normalizer (Q : Set Ω))
        (H ⊓ Subgroup.normalizer (Q : Set Ω) ⊓
          Subgroup.normalizer ((T ⊓ Subgroup.centralizer (Q : Set Ω) : Subgroup Ω) : Set Ω)) ∧
      ∃ h ∈ H ⊓ Subgroup.normalizer (Q : Set Ω) ⊓
          Subgroup.normalizer ((T ⊓ Subgroup.centralizer (Q : Set Ω) : Subgroup Ω) : Set Ω),
        (∃ r : ℕ, r.Prime ∧ r ≠ p ∧ ∃ n : ℕ, orderOf h = r ^ n) ∧
          h ∉ Subgroup.normalizer (P : Set Ω) := by
  set B : Subgroup Ω := H ⊓ Subgroup.normalizer (Q : Set Ω) with hB
  set E : Subgroup Ω := T ⊓ Subgroup.normalizer (Q : Set Ω) with hE
  set CT : Subgroup Ω := T ⊓ Subgroup.centralizer (Q : Set Ω) with hCT
  set Y : Subgroup Ω := H ⊓ Subgroup.centralizer (Q : Set Ω) with hY
  set K : Subgroup Ω := B ⊓ Subgroup.normalizer (CT : Set Ω) with hK
  have hEB : E ≤ B := inf_le_inf_right _ hTH
  have hEK : E ≤ K := le_inf hEB (inf_normalizer_le_normalizer_inf_centralizer T Q)
  have hKB : K ≤ B := inf_le_left
  have hc : IsSylowOf p E K := hb.of_le hEK hKB
  refine ⟨hc, ?_⟩
  have hYB : Y ≤ B := inf_le_inf_left _ (Subgroup.centralizer_le_normalizer _)
  have hBY : B ≤ Subgroup.normalizer (Y : Set Ω) :=
    inf_normalizer_le_normalizer_inf_centralizer H Q
  have hCTE : CT = E ⊓ Y := by
    ext x
    simp only [hCT, hE, hY, Subgroup.mem_inf]
    constructor
    · rintro ⟨hxT, hxC⟩
      exact ⟨⟨hxT, Subgroup.centralizer_le_normalizer _ hxC⟩, hTH hxT, hxC⟩
    · rintro ⟨⟨hxT, -⟩, -, hxC⟩
      exact ⟨hxT, hxC⟩
  have hCTY : IsSylowOf p CT Y := by
    rw [hCTE]
    exact hb.inf_of_le_normalizer hYB hBY
  have hk₀B : k₀ ∈ B := hk₀
  have hYcj : cj k₀⁻¹ Y = Y := by
    apply cj_of_mem_normalizer
    exact inv_mem (hBY hk₀B)
  have hA' : IsSylowOf p (cj k₀⁻¹ CT) Y := by
    have := (isSylowOf_cj_iff (p := p) (A := CT) (B := Y) k₀⁻¹).2 hCTY
    rwa [hYcj] at this
  obtain ⟨c, hcY, hcconj⟩ := isSylowOf_exists_conj hCTY hA'
  have hk'N : c⁻¹ * k₀ ∈ Subgroup.normalizer (CT : Set Ω) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := hcconj (k₀ * x * k₀⁻¹)
    simp only [mem_cj, inv_inv] at h1
    have e : k₀⁻¹ * (k₀ * x * k₀⁻¹) * k₀ = x := by group
    rw [e] at h1
    have e2 : c⁻¹ * k₀ * x * (c⁻¹ * k₀)⁻¹ = c⁻¹ * (k₀ * x * k₀⁻¹) * c := by group
    rw [e2]
    exact h1
  have hk'B : c⁻¹ * k₀ ∈ B := B.mul_mem (B.inv_mem (hYB hcY)) hk₀B
  have hk'P : c⁻¹ * k₀ ∉ Subgroup.normalizer (P : Set Ω) := by
    intro h
    have hcP : c ∈ Subgroup.normalizer (P : Set Ω) :=
      Subgroup.centralizer_le_normalizer _
        (Subgroup.centralizer_le (by exact_mod_cast hPQ) hcY.2)
    apply hk₀P
    have := Subgroup.mul_mem _ hcP h
    simpa using this
  have hE_P : E ≤ Subgroup.normalizer (P : Set Ω) := inf_le_left.trans hPT
  exact exists_primePower_not_mem_normalizer hc hE_P ⟨hk'B, hk'N⟩ hk'P

end StepA

end CFSG.ClassicalInvolution.GlaubermanAut
