module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSixE32Ctx
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSixE32Dih
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSixGenBase

public section

namespace CFSG.ComponentClassification.SolMax.Sig36.E32

open CFSG Subgroup Equiv

variable {X : Type} [Group X] [Finite X] {M : Subgroup X}
  {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 9)}
  {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 9)} {t s : X} {H Q : Subgroup X}

private abbrev Yk (M : Subgroup X) (t : X) (H : Subgroup X) : Subgroup X :=
  centralizer ({t} : Set X) ⊓ (H ⊓ UnbalancedLayer.coreActionKernel M)

namespace Ctx

variable (Z : Ctx M θ ρ t s H Q)
include Z

theorem invol_conj :
    ∀ u ∈ Q ⊔ zpowers s, u ∉ Q → u * u = 1 → ∃ d ∈ Q ⊔ zpowers s, d * s * d⁻¹ = u :=
  dihedral_conj Z.hQ2 Z.hsQ Z.hsNQ Z.hs2 Z.htQ Z.ht2 Z.ht1 Z.hQt Z.hst Z.hR Z.hy

private theorem rhoX_eq_one_of_mem_cak {z : X} (hz : z ∈ UnbalancedLayer.coreActionKernel M) :
    rhoX ρ z = 1 := by
  rw [rhoX_of_mem hz.1]
  exact IsPermAction.eq_one_of_mem_coreActionKernel Z.hρ (by norm_num) hz

private theorem mem_cak_of_rhoX_eq_one {g : X} (hg : g ∈ normalizer (M : Set X))
    (h1 : rhoX ρ g = 1) : g ∈ UnbalancedLayer.coreActionKernel M :=
  Z.hρ.mem_coreActionKernel hg (by rw [← rhoX_of_mem hg]; exact h1)

private theorem s_not_mem_Yk : s ∉ Yk M t H := fun h => by
  have h1 := Z.rhoX_eq_one_of_mem_cak (mem_inf.mp (mem_inf.mp h).2).2
  have h6 := card_support_σ₀
  rw [← Z.hρs, h1, Perm.support_one, Finset.card_empty] at h6
  omega

private theorem s_mem_normalizer_Yk : s ∈ normalizer (Yk M t H : Set X) := by
  have hK : s ∈ normalizer (UnbalancedLayer.coreActionKernel M : Set X) := by
    rw [mem_normalizer_iff]
    intro h
    refine ⟨fun hh => Z.hρ.conj_mem_coreActionKernel (by norm_num) Z.s_mem_N hh, fun hh => ?_⟩
    have h1 := Z.hρ.conj_mem_coreActionKernel (by norm_num) (inv_mem Z.s_mem_N) hh
    have h2 : s⁻¹ * (s * h * s⁻¹) * s⁻¹⁻¹ = h := by group
    rwa [h2] at h1
  exact inf_normalizer_le_normalizer_inf (mem_inf.mpr ⟨le_normalizer Z.s_mem_C,
    inf_normalizer_le_normalizer_inf (mem_inf.mpr ⟨le_normalizer Z.hsH, hK⟩)⟩)

private theorem Q_le_Yk : Q ≤ Yk M t H := fun q hq =>
  mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr (Z.hQt q hq), Z.hQK hq⟩

private theorem Q_max_Yk :
    ∀ P : Subgroup X, P ≤ Yk M t H → IsPGroup 2 P → Nat.card P ≤ Nat.card Q := by
  intro P hPY hP2
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp hP2
  have hdvd : 2 ^ k ∣ Nat.card ↥(H ⊓ UnbalancedLayer.coreActionKernel M) := by
    rw [← hk]
    exact Subgroup.card_dvd_of_le (hPY.trans inf_le_right)
  have hkle := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp hdvd
  rw [hk, Z.hQcard]
  exact Nat.pow_le_pow_right (by norm_num) hkle

theorem fusion {b : X} (hbC : b ∈ centralizer ({t} : Set X)) (hb2 : b * b = 1)
    (hb6 : (rhoX ρ b).support.card = 6) :
    ∃ c ∈ centralizer ({t} : Set X), c * s * c⁻¹ = b := by
  have hbN : b ∈ normalizer (M : Set X) := Z.mem_normalizer_of_mem_C hbC
  have hρb2 : rhoX ρ b * rhoX ρ b = 1 := by
    rw [← rhoX_mul hbN hbN, hb2, rhoX_one]
  have hct : (rhoX ρ b).cycleType = σ₀.cycleType := by
    rw [SixGen.cycleType_of_mul_self (k := 3) hρb2 (by norm_num) hb6,
      SixGen.cycleType_of_mul_self (k := 3) σ₀_mul_self (by norm_num) card_support_σ₀]
  obtain ⟨π, hπ⟩ := isConj_iff.mp (Perm.isConj_iff_cycleType_eq.mpr hct)
  obtain ⟨c₁, hc₁C, hc₁ρ⟩ := Z.exists_rho_surj π
  have hc₁N : c₁ ∈ normalizer (M : Set X) := Z.mem_normalizer_of_mem_C hc₁C
  have hb'C : c₁ * b * c₁⁻¹ ∈ centralizer ({t} : Set X) :=
    mul_mem (mul_mem hc₁C hbC) (inv_mem hc₁C)
  have hb'N : c₁ * b * c₁⁻¹ ∈ normalizer (M : Set X) := Z.mem_normalizer_of_mem_C hb'C
  have hb'ρ : rhoX ρ (c₁ * b * c₁⁻¹) = σ₀ := by
    rw [rhoX_conj hc₁N hbN, hc₁ρ, hπ]
  have hb'2 : (c₁ * b * c₁⁻¹) * (c₁ * b * c₁⁻¹) = 1 := by
    calc (c₁ * b * c₁⁻¹) * (c₁ * b * c₁⁻¹) = c₁ * (b * b) * c₁⁻¹ := by group
      _ = 1 := by rw [hb2]; group
  have hkC : (c₁ * b * c₁⁻¹) * s ∈ centralizer ({t} : Set X) := mul_mem hb'C Z.s_mem_C
  have hkρ : rhoX ρ ((c₁ * b * c₁⁻¹) * s) = 1 := by
    rw [rhoX_mul hb'N Z.s_mem_N, hb'ρ, Z.hρs, σ₀_mul_self]
  have hkY : (c₁ * b * c₁⁻¹) * s ∈ Yk M t H :=
    mem_inf.mpr ⟨hkC, mem_inf.mpr ⟨Z.hCt hkC,
      Z.mem_cak_of_rhoX_eq_one (Z.mem_normalizer_of_mem_C hkC) hkρ⟩⟩
  have hb'Yss : c₁ * b * c₁⁻¹ ∈ Yk M t H ⊔ zpowers s := by
    have h1 := mul_mem (mem_sup_left hkY) (mem_sup_right (mem_zpowers s) : s ∈ Yk M t H ⊔ zpowers s)
    rwa [mul_assoc, Z.hs2, mul_one] at h1
  have hb'Y : c₁ * b * c₁⁻¹ ∉ Yk M t H := fun h => by
    apply Z.s_not_mem_Yk
    have h1 := mul_mem (inv_mem h) hkY
    rwa [inv_mul_cancel_left] at h1
  obtain ⟨c₂, hc₂, hc₂s⟩ := fusion_core Z.hs2 Z.s_not_mem_Yk Z.s_mem_normalizer_Yk Z.Q_le_Yk Z.hQ2
    Z.hsNQ Z.Q_max_Yk Z.invol_conj _ hb'Yss hb'Y hb'2
  have hc₂C : c₂ ∈ centralizer ({t} : Set X) :=
    (sup_le inf_le_left (zpowers_le.mpr Z.s_mem_C)) hc₂
  refine ⟨c₁⁻¹ * c₂, mul_mem (inv_mem hc₁C) hc₂C, ?_⟩
  calc c₁⁻¹ * c₂ * s * (c₁⁻¹ * c₂)⁻¹ = c₁⁻¹ * (c₂ * s * c₂⁻¹) * c₁ := by group
    _ = b := by rw [hc₂s]; group

theorem kernel_bound {R : Subgroup X} (hRt : R ≤ centralizer ({t} : Set X))
    (hRs : R ≤ centralizer ({s} : Set X)) (hR1 : ∀ r ∈ R, rhoX ρ r = 1) (hR2 : IsPGroup 2 R) :
    Nat.card R ≤ 2 := by
  have hRY : R ≤ Yk M t H := fun r hr =>
    mem_inf.mpr ⟨hRt hr, mem_inf.mpr ⟨Z.hCt (hRt hr),
      Z.mem_cak_of_rhoX_eq_one (Z.mem_normalizer_of_mem_C (hRt hr)) (hR1 r hr)⟩⟩
  exact kernel_two_bound Z.hs2 Z.s_not_mem_Yk Z.s_mem_normalizer_Yk Z.Q_le_Yk Z.hQ2 Z.hsNQ
    Z.Q_max_Yk Z.invol_conj Z.ht2 Z.hR hRY hRs hR2

end Ctx

end CFSG.ComponentClassification.SolMax.Sig36.E32
