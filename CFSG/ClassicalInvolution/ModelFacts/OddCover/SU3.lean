module

public import CFSG.ClassicalInvolution.ModelFacts.OddCover.SU3Basic
public import CFSG.ClassicalInvolution.ModelFacts.OddCover.Retract
public import CFSG.ClassicalInvolution.ModelFacts.OddCover.PPart

public section

namespace CFSG.ClassicalInvolution.ModelFacts.OddCover

open CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg CFSG.LieType.BorelTits
open scoped commutatorElement

section Extension

variable {K : Type} [Field K] {σ : K ≃+* K} {E : Type*} [Group E]

@[expose] def YhatSU (H : SUInv σ) (π : E →* SU σ 3) : Subgroup E := (Zsu H).comap π

@[expose] def UhatSU (H : SUInv σ) (π : E →* SU σ 3) : Subgroup E := (Usu H).comap π

variable (H : SUInv σ) {π : E →* SU σ 3}

theorem YhatSU_le_UhatSU : YhatSU H π ≤ UhatSU H π := fun _ hy => Zsu_le_Usu H hy

theorem ker_le_YhatSU : π.ker ≤ YhatSU H π := fun c hc =>
  ⟨0, by rw [MonoidHom.mem_ker.1 hc, zSU_zero]⟩

theorem commutator_mem_YhatSU {g h : E} (hg : g ∈ UhatSU H π) (hh : h ∈ UhatSU H π) :
    ⁅g, h⁆ ∈ YhatSU H π := by
  change π ⁅g, h⁆ ∈ Zsu H
  rw [map_commutatorElement]
  exact comm_mem_Zsu H hg hh

theorem conj_mem_UhatSU {g y : E} {t : Kˣ} (hg : π g = dSU H t) (hy : y ∈ UhatSU H π) :
    g * y * g⁻¹ ∈ UhatSU H π := by
  obtain ⟨a, β, hab⟩ := hy
  refine ⟨(t : K) ^ 2 / σ t * a, nrmSU H t β, ?_⟩
  rw [map_mul, map_mul, map_inv, hg, hab]
  calc dSU H t * (xSU H a * zSU H β) * (dSU H t)⁻¹
      = (dSU H t * xSU H a * (dSU H t)⁻¹) * (dSU H t * zSU H β * (dSU H t)⁻¹) := by group
    _ = _ := by rw [dSU_conj_xSU, dSU_conj_zSU]

theorem conj_mem_YhatSU {g y : E} {t : Kˣ} (hg : π g = dSU H t) (hy : y ∈ YhatSU H π) :
    g * y * g⁻¹ ∈ YhatSU H π := by
  obtain ⟨β, hβ⟩ := hy
  refine ⟨nrmSU H t β, ?_⟩
  rw [map_mul, map_mul, map_inv, hg, hβ, dSU_conj_zSU]

theorem YhatSU_comm (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) {y y' : E}
    (hy : y ∈ YhatSU H π) (hy' : y' ∈ YhatSU H π) : ⁅y, y'⁆ = 1 := by
  obtain ⟨β, hβ⟩ := hy
  obtain ⟨β', hβ'⟩ := hy'
  obtain ⟨a₁, a₂, hc⟩ := exists_comm_eq_zSU H β'
  obtain ⟨g₁, hg₁⟩ := hπ (xSU H a₁)
  obtain ⟨g₂, hg₂⟩ := hπ (xSU H a₂)
  have h1 : ⁅g₁, y⁆ ∈ Subgroup.center E := by
    refine comm_mem_center_of_commute_map hcen ?_
    rw [hg₁, hβ]
    exact (zSU_commute_xSU H β a₁).symm
  have h2 : ⁅g₂, y⁆ ∈ Subgroup.center E := by
    refine comm_mem_center_of_commute_map hcen ?_
    rw [hg₂, hβ]
    exact (zSU_commute_xSU H β a₂).symm
  have h3 := comm_comm_eq_one_of_mem_center h1 h2
  have hk : (⁅g₁, g₂⁆)⁻¹ * y' ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_commutatorElement, hg₁, hg₂, hc, hβ',
      inv_mul_cancel]
  have hy'e : y' = ⁅g₁, g₂⁆ * ((⁅g₁, g₂⁆)⁻¹ * y') := by group
  rw [hy'e, comm_mul_central_right (hcen hk), ← commutatorElement_inv, h3, inv_one]

theorem YhatSU_central (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    {t₀ : Kˣ} (hN : σ t₀ * t₀ = 1) (hlam : (t₀ : K) ^ 2 / σ t₀ ≠ 1) :
    ∀ y ∈ YhatSU H π, ∀ g ∈ UhatSU H π, ⁅g, y⁆ = 1 := by
  intro y hy g hg
  obtain ⟨h, hh⟩ := hπ (dSU H t₀)
  obtain ⟨β, hβ⟩ := hy
  have hy : y ∈ YhatSU H π := ⟨β, hβ⟩
  rw [← commutatorElement_inv]
  refine inv_eq_one.2 ?_
  refine comm_eq_one_of_conj_surj (s := y) (h := h) (Y := UhatSU H π) ?_ ?_ ?_ ?_ g hg
  · intro g' hg'
    refine comm_mem_center_of_commute_map hcen ?_
    rw [hβ]
    exact (commutatorElement_eq_one_iff_mul_comm.1 (zSU_comm_of_mem_Usu H hg' β)).symm
  · intro g' hg'
    exact conj_mem_UhatSU H hh hg'
  · refine comm_mem_center_of_commute_map hcen ?_
    change π h * π y = π y * π h
    rw [hh, hβ]
    exact (mul_inv_eq_iff_eq_mul.1 (dSU_conj_zSU_of_norm_one H hN β))
  · intro g' hg'
    obtain ⟨a, β', hab⟩ := hg'
    obtain ⟨a₁, γ, hγ⟩ := exists_mul_comm_eq H hlam a β'
    obtain ⟨g₁, hg₁⟩ := hπ (xSU H a₁)
    have hg₁U : g₁ ∈ UhatSU H π := ⟨a₁, 0, by rw [hg₁, zSU_zero, mul_one]⟩
    refine ⟨g₁, hg₁U, g' * (h * g₁ * h⁻¹ * g₁⁻¹)⁻¹, ?_, by group⟩
    have hw : g' * (h * g₁ * h⁻¹ * g₁⁻¹)⁻¹ ∈ YhatSU H π := by
      refine ⟨γ, ?_⟩
      rw [map_mul, map_inv, hab, hγ]
      simp only [map_mul, map_inv, hh, hg₁]
      group
    exact YhatSU_comm H hπ hcen ⟨β, hβ⟩ hw

theorem exists_kappaSU [Finite E] (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    {u₀ : Kˣ} (hu₀ : σ u₀ * u₀ = -1) (hmK : Nat.Coprime 2 (Nat.card π.ker))
    (hcent : ∀ y ∈ YhatSU H π, ∀ g ∈ UhatSU H π, ⁅g, y⁆ = 1) :
    ∃ κ : E → E, (∀ y ∈ YhatSU H π, κ y ∈ π.ker) ∧
      (∀ y ∈ YhatSU H π, ∀ y' ∈ YhatSU H π, κ (y * y') = κ y * κ y') ∧ (∀ c ∈ π.ker, κ c = c) ∧
      ∀ (t : Kˣ) (g : E), π g = dSU H t → ∀ y ∈ YhatSU H π, κ (g * y * g⁻¹) = κ y := by
  classical
  obtain ⟨z, hz⟩ := hπ (dSU H u₀)
  have hN : ∀ y ∈ YhatSU H π, normSum z y 2 ∈ π.ker := by
    rintro y ⟨β, hβ⟩
    have : normSum z y 2 = y * (z * y * z⁻¹) := by
      simp [normSum_succ]
    rw [this, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, hz, hβ,
      dSU_conj_zSU_of_norm_neg_one H hu₀, zSU_mul, add_neg_cancel, zSU_zero]
  have hYc : ∀ a ∈ YhatSU H π, ∀ b ∈ YhatSU H π, a * b = b * a := fun a ha b hb =>
    commutatorElement_eq_one_iff_mul_comm.1 (hcent b hb a (YhatSU_le_UhatSU H ha))
  obtain ⟨κ, hκK, hκmul, hκid, hκinv⟩ := exists_retraction_fun (Y := YhatSU H π) (K := π.ker)
    (ker_le_YhatSU H) hcen hYc (z := z) (fun y hy => conj_mem_YhatSU H hz hy)
    (fun y hy => by
      simpa using conj_mem_YhatSU H (g := z⁻¹) (t := u₀⁻¹) (by rw [map_inv, hz, map_inv]) hy)
    hmK hN
  refine ⟨κ, hκK, hκmul, hκid, fun t g hg y hy => ?_⟩
  refine hκinv g (fun y hy => conj_mem_YhatSU H hg hy) (fun y _ => ?_) y hy
  refine conj_conj_comm_of_comm_mem_center (comm_mem_center_of_commute_map hcen ?_) y
  change π g * π z = π z * π g
  rw [hg, hz, ← map_mul, ← map_mul, mul_comm]

theorem commutator_UhatSU_inf_ker_eq_bot [Finite E] (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) {t₀ u₀ : Kˣ} (hN : σ t₀ * t₀ = 1)
    (hlam : (t₀ : K) ^ 2 / σ t₀ ≠ 1) (hu₀ : σ u₀ * u₀ = -1)
    (hmK : Nat.Coprime 2 (Nat.card π.ker)) {F : Type} [Field F] [Module F K]
    (h5 : ∃ a : F, a ≠ 0 ∧ a + 1 ≠ 0 ∧ a ^ 2 + a + 1 ≠ 0)
    (hscal : ∀ μ : F, μ ≠ 0 → ∃ u : Kˣ, σ u = u ∧ ∀ a : K, μ • a = (u : K) * a) :
    ⁅UhatSU H π, UhatSU H π⁆ ⊓ π.ker = ⊥ := by
  classical
  have hcent := YhatSU_central H hπ hcen hN hlam
  obtain ⟨κ, hκK, hκmul, hκid, hκtor⟩ := exists_kappaSU H hπ hcen hu₀ hmK hcent
  have hlift : ∀ a : K, ∃ g : E, π g = xSU H a := fun a => hπ _
  choose ℓ hℓ using hlift
  refine commutator_inf_eq_bot_of_fun (Y := YhatSU H π)
    (fun g hg h hh => commutator_mem_YhatSU H hg hh) hκmul hκid ?_
  refine kappa_comm_eq_one (E := E) (G := UhatSU H π) (Y := YhatSU H π) (YhatSU_le_UhatSU H) hcent
    (fun g hg h hh => commutator_mem_YhatSU H hg hh) hκmul (fun y hy => hcen (hκK y hy))
    (F := F) (V := K) h5 ℓ (fun a => ⟨a, 0, by rw [hℓ, zSU_zero, mul_one]⟩) ?_ ?_ ?_
  · rintro g ⟨a, β, hg⟩
    refine ⟨a, (ℓ a)⁻¹ * g, ⟨β, ?_⟩, by group⟩
    rw [map_mul, map_inv, hℓ, hg, inv_mul_cancel_left]
  · intro a a'
    refine ⟨(ℓ a * ℓ a')⁻¹ * ℓ (a + a'), ⟨-gamSU H a a', ?_⟩, by group⟩
    rw [map_mul, map_inv, map_mul, hℓ, hℓ, hℓ, xSU_mul, _root_.mul_inv_rev, mul_assoc,
      inv_mul_cancel, mul_one, zSU_inv]
  · intro μ hμ
    obtain ⟨u, hσu, hu⟩ := hscal μ hμ
    obtain ⟨g, hg⟩ := hπ (dSU H u)
    refine ⟨g, fun y hy => hκtor u g hg y hy, fun a => ?_⟩
    have hk : (ℓ (μ • a))⁻¹ * (g * ℓ a * g⁻¹) ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, map_inv, hg, hℓ, hℓ,
        dSU_conj_xSU, hu, hσu]
      have : (u : K) ^ 2 / (u : K) = u := by
        have : (u : K) ≠ 0 := u.ne_zero
        field_simp
      rw [this]
      exact inv_mul_cancel _
    exact ⟨_, hcen hk, by group⟩

end Extension

section Unitary

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [hp : Fact p.Prime] [CharP F p]

theorem su3_ker_eq_bot_of_isPGroup (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (h5 : 5 ≤ p ^ f) {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    {π : E →* SU (unitaryInvolution F p f) 3} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) (hker : IsPGroup p π.ker) : π.ker = ⊥ := by
  classical
  have H : SUInv (unitaryInvolution F p f) := suInv_unitary hF hp2
  obtain ⟨t₀, hN, hord⟩ := exists_norm_one_orderOf_eq (F := F) (p := p) (f := f) hF
  have hlam : (t₀ : F) ^ 2 / unitaryInvolution F p f t₀ ≠ 1 := by
    intro h
    have hσt : unitaryInvolution F p f (t₀ : F) = (t₀ : F)⁻¹ := eq_inv_of_mul_eq_one_left hN
    rw [hσt, div_inv_eq_mul, ← pow_succ] at h
    have h3 : t₀ ^ 3 = 1 := Units.ext (by simpa using h)
    have := Nat.le_of_dvd (by norm_num) (hord ▸ orderOf_dvd_of_pow_eq_one h3)
    omega
  obtain ⟨u, hu⟩ := CFSG.LieType.Universal.Unitary.exists_norm_eq_neg_one (F := F) hF
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu
  have hmK : Nat.Coprime 2 (Nat.card π.ker) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hker
    rw [hk]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_two hp.out).2 (Ne.symm hp2))
  have h5F : 5 ≤ Nat.card (fixedSubfield F p f) := by
    rw [card_fixedSubfield hF]
    exact h5
  have hcomm := commutator_UhatSU_inf_ker_eq_bot H hπ hcen (t₀ := t₀) hN hlam
    (u₀ := Units.mk0 u hu0) hu hmK (F := fixedSubfield F p f) (exists_good_scalar h5F)
    (fun μ hμ => ⟨Units.mk0 (μ : F) (fun h => hμ (Subtype.ext h)), μ.2, fun a => rfl⟩)
  exact ker_eq_bot_of_commutator_inf_eq_bot π hπ hcen hker (isPGroup_Usu hF H)
    (not_dvd_index_Usu hF hf H) hcomm

end Unitary

end CFSG.ClassicalInvolution.ModelFacts.OddCover
