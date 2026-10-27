module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36E

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

variable {M : Subgroup X} {r : ℕ} {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin r)}
  {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin r)}

theorem IsPermAction.exists_lift_of_two (hρ : IsPermAction θ ρ) [Finite X] {a : X}
    (ha : a ∈ normalizer (M : Set X)) (ha2 : IsPGroup 2 (zpowers a))
    {b : alternatingGroup (Fin r)} (hb : (b : Perm (Fin r)) * ρ ⟨a, ha⟩ = ρ ⟨a, ha⟩ * b) :
    ∃ x : ↥M, (x : X) ∈ Subgroup.centralizer ({a} : Set X) ∧
      θ (x : ↥M ⧸ pPrimeCore 2 ↥M) = b := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O : Subgroup X := (pPrimeCore 2 ↥M).map M.subtype with hOdef
  obtain ⟨q, hq⟩ := θ.surjective b
  obtain ⟨w₀, rfl⟩ := QuotientGroup.mk_surjective q
  have hzN : zpowers a ≤ normalizer (M : Set X) := zpowers_le.mpr ha
  have hfix : ∀ u ∈ zpowers a, (w₀ : X)⁻¹ * (u * w₀ * u⁻¹) ∈ O := by
    intro u hu
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hu
    have hcomm : (b : Perm (Fin r)) * ρ ⟨a ^ k, hzN hu⟩ = ρ ⟨a ^ k, hzN hu⟩ * b := by
      have h1 : (⟨a ^ k, hzN hu⟩ : ↥(normalizer (M : Set X))) = ⟨a, ha⟩ ^ k := rfl
      rw [h1, map_zpow]
      exact ((Commute.zpow_right hb k).eq)
    have h1 := hρ ⟨a ^ k, hzN hu⟩ w₀
    rw [hq] at h1
    have h2 : ((θ ((M.normalizerMonoidHom ⟨a ^ k, hzN hu⟩ w₀ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) :
        alternatingGroup (Fin r)) : Perm (Fin r)) = (b : Perm (Fin r)) := by
      rw [h1, ← hcomm, mul_assoc, mul_inv_cancel, mul_one]
    have h3 : θ ((M.normalizerMonoidHom ⟨a ^ k, hzN hu⟩ w₀ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) =
        θ (w₀ : ↥M ⧸ pPrimeCore 2 ↥M) := by
      rw [hq]
      exact Subtype.ext h2
    have h4 := QuotientGroup.eq.mp (θ.injective h3).symm
    refine ⟨_, h4, ?_⟩
    rw [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv,
      normalizerMonoidHom_apply_apply_coe]
  let α : ↥(zpowers a) →* MulAut X := MulAut.conj.comp (zpowers a).subtype
  have hcop : ¬ 2 ∣ Nat.card O := by
    rw [hOdef, card_map_of_injective M.subtype_injective]
    exact fun h => absurd (Nat.Coprime.coprime_dvd_right h pPrimeCore_coprime_card)
      (by decide)
  obtain ⟨c, hc, hcfix⟩ := (CFSG.Semidihedral.Principal.coprime_invariant_coset_fixed 2 ha2 α O
    hcop (w₀ : X)).2 (by
      intro u x hx
      have hON : (u : X) ∈ normalizer (O : Set X) := le_normalizer_pPrimeCore (hzN u.2)
      have h1 := (mem_normalizer_iff.mp hON _).mp hx
      have h2 := mul_mem (hfix u u.2) h1
      change (w₀ : X)⁻¹ * ((u : X) * x * (u : X)⁻¹) ∈ O
      have h3 : (w₀ : X)⁻¹ * ((u : X) * w₀ * (u : X)⁻¹) * ((u : X) * ((w₀ : X)⁻¹ * x) *
          (u : X)⁻¹) = (w₀ : X)⁻¹ * ((u : X) * x * (u : X)⁻¹) := by group
      rwa [h3] at h2)
  have hcM : c ∈ M := by
    have h1 : (w₀ : X) * ((w₀ : X)⁻¹ * c) ∈ M := mul_mem w₀.2 (map_subtype_le _ hc)
    rwa [mul_inv_cancel_left] at h1
  refine ⟨⟨c, hcM⟩, ?_, ?_⟩
  · rw [mem_centralizer_singleton_iff]
    have h1 := hcfix ⟨a, mem_zpowers a⟩
    change a * c * a⁻¹ = c at h1
    calc c * a = a * c * a⁻¹ * a := by rw [h1]
      _ = a * c := by group
  · rw [← hq]
    congr 1
    obtain ⟨o, ho, hoeq⟩ := hc
    have h1 : w₀⁻¹ * (⟨c, hcM⟩ : ↥M) = o := Subtype.ext (by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact hoeq.symm)
    have h2 : w₀⁻¹ * (⟨c, hcM⟩ : ↥M) ∈ pPrimeCore 2 ↥M := by rw [h1]; exact ho
    exact (QuotientGroup.eq.mpr h2).symm

theorem IsPermAction.exists_lift_oddCentGen_of_two (hρ : IsPermAction θ ρ) [Finite X] (hr : 4 ≤ r)
    {a : X} (ha : a ∈ normalizer (M : Set X)) (ha2 : IsPGroup 2 (zpowers a))
    {π : Perm (Fin r)}
    (hπ : π ∈ oddCentGen (ρ ⟨a, ha⟩)) :
    ∃ (q : X) (hq : q ∈ M), q ∈ oddGen (centralizer ({a} : Set X)) ∧
      ρ ⟨q, le_normalizer hq⟩ = π := by
  change π ∈ Subgroup.closure _ at hπ
  induction hπ using closure_induction with
  | mem π hπ' =>
    obtain ⟨hπA, hπσ, hodd⟩ := hπ'
    obtain ⟨x, hxa, hx⟩ := hρ.exists_lift_of_two ha ha2 (b := ⟨π, hπA⟩) hπσ
    have hρx : ρ ⟨x, le_normalizer x.2⟩ = π := by
      rw [hρ.apply_of_mem hr x, hx]
    let f : ↥M →* Perm (Fin r) := ρ.comp (Subgroup.inclusion le_normalizer)
    have hfx : f x = π := hρx
    obtain ⟨k, hk, hfk⟩ := exists_pow_odd_of_odd_map f x (by rw [hfx]; exact hodd)
    refine ⟨((x ^ k : ↥M) : X), (x ^ k).2, mem_oddGen ?_ ?_, ?_⟩
    · rw [Subgroup.coe_pow]
      exact pow_mem hxa k
    · rw [Subgroup.orderOf_coe]
      exact hk
    · rw [← hfx, ← hfk]
      rfl
  | one => exact ⟨1, one_mem _, one_mem _, map_one ρ⟩
  | mul π₁ π₂ _ _ h₁ h₂ =>
    obtain ⟨q₁, hq₁, hq₁o, hρ₁⟩ := h₁
    obtain ⟨q₂, hq₂, hq₂o, hρ₂⟩ := h₂
    refine ⟨q₁ * q₂, mul_mem hq₁ hq₂, mul_mem hq₁o hq₂o, ?_⟩
    rw [← hρ₁, ← hρ₂, ← map_mul]
    rfl
  | inv π _ h =>
    obtain ⟨q, hq, hqo, hρq⟩ := h
    refine ⟨q⁻¹, inv_mem hq, inv_mem hqo, ?_⟩
    rw [← hρq, ← map_inv]
    rfl

end CFSG.ComponentClassification.SolMax
