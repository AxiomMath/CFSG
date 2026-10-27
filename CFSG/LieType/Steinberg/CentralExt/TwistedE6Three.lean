module

public import CFSG.LieType.Steinberg.CentralExt.TwistedE6PosLift

public noncomputable section

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.ExceptionalCover CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Minuscule

namespace CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed

@[expose] def sepVecs : Fin 12 → Fin (Tag.rank .E6) → ℤ :=
  ![![0, 0, 0, 4, 0, 0], ![0, 4, 0, 0, 0, 0], ![0, 4, 4, 4, 12, 0], ![2, 0, 4, 0, 12, 6],
    ![2, 4, 1, 0, 3, 6], ![1, 0, 3, 0, 9, 3], ![0, 0, 4, 4, 12, 0], ![4, 4, 0, 4, 0, 12],
    ![1, 4, 3, 4, 9, 3], ![2, 0, 3, 0, 9, 6], ![0, 0, 1, 4, 3, 0], ![1, 0, 1, 4, 3, 3]]

theorem sepVecs_rho : ∀ (j : Fin 12) (a : Fin (Tag.rank .E6)),
    (8 : ℤ) ∣ sepVecs j (rhoPerm a) - 3 * sepVecs j a := by
  decide

set_option synthInstance.maxHeartbeats 0 in
set_option synthInstance.maxSize 1000000 in
theorem sep_three_cert : ∀ k₁ < (Tag.rootCertificate .E6).roots.length,
    ∀ k₂ < (Tag.rootCertificate .E6).roots.length,
    0 < ht ((Tag.rootCertificate .E6).root k₁) → 0 < ht ((Tag.rootCertificate .E6).root k₂) →
    proj ((Tag.rootCertificate .E6).root k₁) ≠ proj ((Tag.rootCertificate .E6).root k₂) →
    ∃ j : Fin 12, (8 : ℤ) ∣ ∑ i, sepVecs j i * cartanCoord ((Tag.rootCertificate .E6).root k₁) i ∧
      ¬ (8 : ℤ) ∣ ∑ i, sepVecs j i * cartanCoord ((Tag.rootCertificate .E6).root k₂) i := by
  decide +kernel

theorem sep_three {α α' : Fin (Tag.rank .E6) → ℤ} (hα : IsRoot .E6 α) (hα' : IsRoot .E6 α')
    (h0 : 0 < ht α) (h0' : 0 < ht α') (hne : proj α ≠ proj α') :
    ∃ j : Fin 12, (8 : ℤ) ∣ ∑ i, sepVecs j i * cartanCoord α i ∧
      ¬ (8 : ℤ) ∣ ∑ i, sepVecs j i * cartanCoord α' i := by
  obtain ⟨k₁, hk₁, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check .E6)).1 hα
  obtain ⟨k₂, hk₂, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check .E6)).1 hα'
  exact sep_three_cert k₁ hk₁ k₂ hk₂ h0 h0' hne

variable {k : Type} [Field k] (θ : k →+* k)

theorem isSymU_tvec_sepVecs {g : kˣ} (hg8 : orderOf g = 8)
    (hθg : Units.map (θ : k →* k) g = g ^ 3) (j : Fin 12) :
    IsSymU θ (AdjointClosed.tvec g (sepVecs j)) := by
  intro a
  change g ^ sepVecs j (rhoPerm a) = Units.map (θ : k →* k) (g ^ sepVecs j a)
  rw [map_zpow, hθg, ← zpow_natCast, ← zpow_mul, zpow_eq_zpow_iff_modEq, hg8,
    Int.modEq_iff_dvd]
  push_cast
  exact dvd_sub_comm.1 (sepVecs_rho j a)

theorem rootChar_tvec_eq_one_iff {g : kˣ} (hg8 : orderOf g = 8) (m α : Fin (Tag.rank .E6) → ℤ) :
    rootChar k α (AdjointClosed.tvec g m) = 1 ↔ (8 : ℤ) ∣ ∑ i, m i * cartanCoord α i := by
  rw [AdjointClosed.rootChar_tvec, ← orderOf_dvd_iff_zpow_eq_one, hg8]
  rfl

theorem twistedE6_three_exists_section_of_pKernel [Finite k] (hk : Nat.card k = 3 ^ 2)
    (hθq : ∀ c, θ c = c ^ 3) {p : ℕ} [Fact p.Prime] [CharP k p] {E : Type*} [Group E] [Finite E]
    {π : E →* fixedGroup k θ} (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (hpk : IsPGroup p π.ker) : ∃ s : fixedGroup k θ →* E, ∀ g, π (s g) = g := by
  have hθ : ∀ c, θ (θ c) = c := theta_theta_of_card hk hθq
  have hF := card_fixedSubfield_of_card θ hk hθq
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := kˣ)
  have hg8 : orderOf g = 8 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hk]
    norm_num
  have hθg : Units.map (θ : k →* k) g = g ^ 3 :=
    Units.ext (by rw [Units.coe_map, Units.val_pow_eq_pow_val]; exact hθq _)
  refine twistedE6_exists_section_of_torus θ hθ (by rw [hk]; norm_num) (by rw [hF]; norm_num)
    (fun j : Fin 12 => AdjointClosed.tvec g (sepVecs j)) (isSymU_tvec_sepVecs θ hg8 hθg) ?_ hπ
    hcen hpk
  intro a b hra ha hrb hb hab
  obtain ⟨hα, hpa⟩ := liftRoot_spec hra
  obtain ⟨hα', hpb⟩ := liftRoot_spec hrb
  obtain ⟨j, h1, h2⟩ := sep_three hα hα' (by rw [← ht_proj, hpa]; exact ha)
    (by rw [← ht_proj, hpb]; exact hb) (by rw [hpa, hpb]; exact hab)
  exact ⟨j, (rootChar_tvec_eq_one_iff hg8 _ _).2 h1,
    fun h => h2 ((rootChar_tvec_eq_one_iff hg8 _ _).1 h)⟩

theorem twistedE6_three_exists_section_of_central [Finite k]
    (hk : Nat.card k = 3 ^ 2) (hθq : ∀ c, θ c = c ^ 3) {E : Type} [Group E] [Finite E]
    {π : E →* fixedGroup k θ} (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) :
    ∃ s : fixedGroup k θ →* E, ∀ g, π (s g) = g := by
  have hθ : ∀ c, θ (θ c) = c := theta_theta_of_card hk hθq
  obtain ⟨p, _, _⟩ := TorusLift.exists_prime_charP (k := k)
  exact CoprimeSplit.exists_section_of_parts (p := p) hπ hcen
    (fun _ _ _ _ hπ' hcen' hp' => twistedE6_three_exists_section_of_pKernel θ hk hθq hπ' hcen'
      hp')
    (fun _ _ _ _ hπ' hcen' hc' => twistedE6_exists_section_of_coprime hθ hπ' hcen' hc')

end CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed
