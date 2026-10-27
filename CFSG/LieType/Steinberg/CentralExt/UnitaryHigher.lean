module

public import CFSG.LieType.Steinberg.CentralExt.UnitaryRankOne
public import CFSG.LieType.Steinberg.CentralExt.UnitaryRankOneLast
public import CFSG.LieType.Steinberg.CentralExt.UnitaryLift
public import CFSG.LieType.Steinberg.CentralExt.UnitaryThreeLift

public section

namespace CFSG.LieType.Steinberg

open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.LocalAnalysis.ComponentInitial

section Split

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

local notation "σ₀" => unitaryInvolution F p f

theorem exists_rankOne_section_SU (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2) {n : ℕ}
    (hn : 2 ≤ n) {E : Type*} [Group E] [Finite E] {π : E →* SU σ₀ n}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 π.ker)
    (k : Fin (n / 2)) :
    ∃ φ : ↥(CFSG.LieType.CurtisTits.rankOne
      (rootGroup σ₀ (unitaryInvolution_involutive hF) n) k) →* E, ∀ g, π (φ g) = g := by
  have hF2 : ringChar F ≠ 2 := by
    rw [ringChar.eq F p]
    exact hp2
  by_cases hk : k.val + 1 < n / 2
  · exact exists_rankOne_short_section hk hF2 hπ hcen h2
  by_cases he : Even n
  · obtain ⟨e⟩ := nonempty_rankOne_last_even_mulEquiv hF he hn hk
    obtain ⟨ζ, hζ0, hζ⟩ := exists_unitaryInvolution_eq_neg hF
    set e' := e.trans (hypEquiv hζ0 hζ).symm
    have hk2 : ringChar (fixedSubfield F p f) ≠ 2 := by
      rw [ringChar_fixedSubfield]
      exact hp2
    obtain ⟨ρ, hρ⟩ := CFSG.LieType.CentralExt.exists_lift hk2 hπ hcen h2
      ((Subgroup.subtype _).comp e'.symm.toMonoidHom)
    refine ⟨ρ.comp e'.toMonoidHom, fun g => ?_⟩
    have h := DFunLike.congr_fun hρ (e' g)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
      Subgroup.coe_subtype] at h
    exact h
  · obtain ⟨e⟩ := nonempty_rankOne_last_odd_mulEquiv hF he (by
      obtain ⟨m, hm⟩ := Nat.not_even_iff_odd.1 he
      omega) hk
    obtain ⟨ρ, hρ⟩ := exists_lift_SU_three hF hp2 hπ hcen h2
      ((Subgroup.subtype _).comp e.symm.toMonoidHom)
    refine ⟨ρ.comp e.toMonoidHom, fun g => ?_⟩
    have h := DFunLike.congr_fun hρ (e g)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
      Subgroup.coe_subtype] at h
    exact h

theorem su_central_two_extension_splitting (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2)
    {n : ℕ} (hn : 2 ≤ n) {E : Type*} [Group E] [Finite E] {π : E →* SU σ₀ n}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 π.ker) :
    ∃ s : SU σ₀ n →* E, (∀ x, π (s x) = x) ∧ (∀ τ : SU σ₀ n →* E, (∀ x, π (τ x) = x) → τ = s) ∧
      ∃ e : π.ker × s.range ≃* E, ∀ a, e a = (a.1 : E) * a.2 := by
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have hC : ¬ p ∣ Nat.card π.ker :=
    CFSG.LieType.CentralExt.not_dvd_card_of_isPGroup_two h2 Fact.out hp2
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  exact exists_section_mulEquiv_of_existsUnique hcen (existsUnique_section_of_rankOne_lift
    (D := rootDatum hF n) (isCTGroupDatum hF n hn ζ hζ) (steinbergExtras hF n hn ζ hζ)
    (fun γ hγ => isPGroup_rootGroup (unitaryInvolution_involutive hF)
      (SUExtras.toStd_ne_zero_of_mem_roots hγ)) hπ hcen hC
    (exists_rankOne_section_SU hF hp2 hn hπ hcen h2))

end Split

theorem nonempty_SU_mulEquiv_SUgram_blockJ {p f : ℕ} {K : Type} [Field K]
    (hK : UnitaryFieldData p f K) [Finite K] [Fact p.Prime] [CharP K p] {r ε : ℕ} (hε : ε ≤ 1) :
    Nonempty (SU (unitaryInvolution K p f) (2 * r + ε) ≃* SUgram hK.bar (blockJ K r ε)) := by
  have h1 : SUgram hK.bar (blockJ K r ε) =
      SUgram (unitaryInvolution K p f).toRingHom
        ((antidiag (2 * r + ε)).submatrix (blockPerm r ε) (blockPerm r ε)) := by
    rw [unitaryFieldData_bar_eq hK, antidiag_submatrix_blockPerm K hε]
  exact ⟨((MulEquiv.subgroupCongr (SUgram_antidiag _)).symm.trans
    (gramReindexEquiv (blockPerm r ε) _)).trans (MulEquiv.subgroupCongr h1.symm)⟩

theorem odd_unitary_higher_central_two_extension_splitting {p f : ℕ} {K : Type} [Field K]
    (hK : UnitaryFieldData p f K) (hp2 : p ≠ 2) {r ε : ℕ} (hr : 2 ≤ r) (hε : ε ≤ 1)
    {R : Type*} [Group R] [Finite R] {π : R →* SUgram hK.bar (blockJ K r ε)}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center R) (h2 : IsPGroup 2 π.ker) :
    ∃ s : SUgram hK.bar (blockJ K r ε) →* R, (∀ x, π (s x) = x) ∧
      (∀ t : SUgram hK.bar (blockJ K r ε) →* R, (∀ x, π (t x) = x) → t = s) ∧
      ∃ e : π.ker × s.range ≃* R, ∀ a, e a = (a.1 : R) * a.2 := by
  have := hK.finite
  have : Fact p.Prime := ⟨hK.prime⟩
  have := hK.charP
  obtain ⟨Φ⟩ := nonempty_SU_mulEquiv_SUgram_blockJ hK (r := r) hε
  have hker : (Φ.symm.toMonoidHom.comp π).ker = π.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff _ Φ.symm.injective]
  obtain ⟨s, hs, huniq, -⟩ := su_central_two_extension_splitting
    (card_eq_sq_of_unitaryFieldData hK) hp2 (n := 2 * r + ε) (by omega)
    (π := Φ.symm.toMonoidHom.comp π) (Φ.symm.surjective.comp hπ) (hker ▸ hcen) (hker ▸ h2)
  have hs' : ∀ x, π (s.comp Φ.symm.toMonoidHom x) = x := fun x => Φ.symm.injective (hs (Φ.symm x))
  refine exists_section_mulEquiv_of_existsUnique hcen ⟨s.comp Φ.symm.toMonoidHom, hs',
    fun t ht => ?_⟩
  have h := huniq (t.comp Φ.toMonoidHom) (fun x => by
    change Φ.symm (π (t (Φ x))) = x
    rw [ht, MulEquiv.symm_apply_apply])
  ext x
  have := DFunLike.congr_fun h (Φ.symm x)
  simpa using this

end CFSG.LieType.Steinberg
