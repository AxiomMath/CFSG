module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43GFree
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43GImage
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43GRho
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43GPsiE
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_10Core

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3S u3T u3K0)

variable {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {M : Subgroup G} {x : G} {J : Subgroup G}

theorem a10t1_pre_le_M {Q : Type} [Group Q] (ψ : ↥J →* Q) {O : Subgroup G}
    (hker : ψ.ker = O.subgroupOf J) (hOM : O ≤ M) {Λ : Subgroup Q}
    (hΛ : Λ ≤ ((M ⊓ J).subgroupOf J).map ψ) : a10Pre J ψ Λ ≤ M := by
  rintro g ⟨j, hj, rfl⟩
  obtain ⟨m, hm, hmj⟩ := hΛ (Subgroup.mem_comap.mp hj)
  have hmM : (m : G) ∈ M := (Subgroup.mem_subgroupOf.mp hm).1
  have h1 : m⁻¹ * j ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hmj, inv_mul_cancel]
  rw [hker, Subgroup.mem_subgroupOf] at h1
  have h2 : (m : G) * ((m⁻¹ * j : ↥J) : G) ∈ M := mul_mem hmM (hOM h1)
  simpa using h2

theorem a10t1_gamma_map_le {Q : Type} [Group Q] {W : Subgroup G} (hWM : W ≤ M)
    (hWN : W ≤ Subgroup.normalizer (J : Set G)) (ψ : ↥J →* Q) (ρ : ↥W →* MulAut Q)
    (hρ : ∀ (w : ↥W) (j : ↥J) (hj : (w : G) * (j : G) * (w : G)⁻¹ ∈ J),
      ρ w (ψ j) = ψ ⟨(w : G) * (j : G) * (w : G)⁻¹, hj⟩) (w : ↥W) :
    (((M ⊓ J).subgroupOf J).map ψ).map (ρ w).toMonoidHom ≤ ((M ⊓ J).subgroupOf J).map ψ := by
  rintro y ⟨z, ⟨j, hj, rfl⟩, rfl⟩
  have hjJ : (w : G) * (j : G) * (w : G)⁻¹ ∈ J :=
    (Subgroup.mem_normalizer_iff.mp (hWN w.2) (j : G)).mp j.2
  have hjM : (j : G) ∈ M := (Subgroup.mem_subgroupOf.mp hj).1
  have hwM : (w : G) ∈ M := hWM w.2
  have hwjM : (w : G) * (j : G) * (w : G)⁻¹ ∈ M := M.mul_mem (M.mul_mem hwM hjM) (M.inv_mem hwM)
  exact ⟨⟨(w : G) * (j : G) * (w : G)⁻¹, hjJ⟩,
    Subgroup.mem_subgroupOf.mpr ⟨hwjM, hjJ⟩, (hρ w j hjJ).symm⟩

theorem a10t1_gamma_map_eq {Q : Type} [Group Q] {W : Subgroup G} (hWM : W ≤ M)
    (hWN : W ≤ Subgroup.normalizer (J : Set G)) (ψ : ↥J →* Q) (ρ : ↥W →* MulAut Q)
    (hρ : ∀ (w : ↥W) (j : ↥J) (hj : (w : G) * (j : G) * (w : G)⁻¹ ∈ J),
      ρ w (ψ j) = ψ ⟨(w : G) * (j : G) * (w : G)⁻¹, hj⟩) (w : ↥W) :
    (((M ⊓ J).subgroupOf J).map ψ).map (ρ w).toMonoidHom = ((M ⊓ J).subgroupOf J).map ψ := by
  refine le_antisymm (a10t1_gamma_map_le hWM hWN ψ ρ hρ w) ?_
  intro y hy
  have hy' : (ρ w⁻¹) y ∈ ((M ⊓ J).subgroupOf J).map ψ :=
    a10t1_gamma_map_le hWM hWN ψ ρ hρ w⁻¹ ⟨y, hy, rfl⟩
  refine ⟨(ρ w⁻¹) y, hy', ?_⟩
  have h : ρ w * ρ w⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  calc (ρ w).toMonoidHom ((ρ w⁻¹) y) = (ρ w * ρ w⁻¹) y := rfl
    _ = y := by rw [h]; rfl

theorem a10_five_EK (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G) (hX : A10Facts) (hXe : A10Ext)
    (hc : PointConfig IsA10Type G 5 P M x J) {Q : Type} [Group Q] [Finite Q] (ψ : ↥J →* Q)
    (hψ : Function.Surjective ψ) (hker : ψ.ker = (rankThreePrimeCore 5 J).subgroupOf J)
    (hQ : IsA10Type 5 Q) {S : Sylow 5 Q} (hSyl : (S : Subgroup Q) = ((u3T P x J).subgroupOf J).map ψ)
    {Λ₁ Λ₂ : Subgroup Q} (hΛ : A10GammaStructAt Q (S : Subgroup Q) Λ₁ Λ₂) :
    ∀ w ∈ M ⊓ Subgroup.centralizer ({x} : Set G), (∃ k : ℕ, w ^ 5 ^ k = 1) →
      w ∈ (a10E J ψ Λ₁ ⊔ a10E J ψ Λ₂) ⊔ (M ⊓ Subgroup.centralizer ({x} : Set G) ⊓ u3K0 5 x J) := by
  intro w hw hw5
  obtain ⟨k, hk⟩ := hw5
  have hOM : rankThreePrimeCore 5 J ≤ M :=
    (u3main_core_facts hS hD1 hc.sigma hc.core hc.generic hc.le_cent hc.cent_le).1
  have hMJ := a10_MJ_image hS hD1 hU0 hX hXe hc ψ hψ hker hQ S hSyl
  obtain ⟨ρ, hρ1, -⟩ :=
    a10_rho hc ψ hψ hker (W := M ⊓ Subgroup.centralizer ({x} : Set G)) inf_le_right
  have hWM : M ⊓ Subgroup.centralizer ({x} : Set G) ≤ M := inf_le_left
  have hWN : M ⊓ Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (J : Set G) :=
    inf_le_right.trans hc.cent_le
  have hΓ : (A10Gamma Q (S : Subgroup Q)).map (ρ ⟨w, hw⟩).toMonoidHom = A10Gamma Q (S : Subgroup Q) := by
    rw [← hMJ]
    exact a10t1_gamma_map_eq hWM hWN ψ ρ hρ1 ⟨w, hw⟩
  have hφk : (ρ ⟨w, hw⟩) ^ 5 ^ k = 1 := by
    rw [← map_pow]
    have h1 : (⟨w, hw⟩ : ↥(M ⊓ Subgroup.centralizer ({x} : Set G))) ^ 5 ^ k = 1 := by
      apply Subtype.ext
      simpa using hk
    rw [h1, map_one]
  obtain ⟨q, hq, hφq⟩ := a10g_aut5 hX hXe hQ hΛ (ρ ⟨w, hw⟩) hΓ ⟨k, hφk⟩
  have hE₁ := a10_psi_E ψ hψ (a10g_five_gen hΛ).1
  have hE₂ := a10_psi_E ψ hψ (a10g_five_gen hΛ).2
  have hEJ₁ : a10E J ψ Λ₁ ≤ J := (a10E_le_pre ψ Λ₁).trans (a10Pre_le ψ Λ₁)
  have hEJ₂ : a10E J ψ Λ₂ ≤ J := (a10E_le_pre ψ Λ₂).trans (a10Pre_le ψ Λ₂)
  have hEM₁ : a10E J ψ Λ₁ ≤ M :=
    (a10E_le_pre ψ Λ₁).trans (a10t1_pre_le_M ψ hker hOM (hΛ.le_gamma₁.trans hMJ.ge))
  have hEM₂ : a10E J ψ Λ₂ ≤ M :=
    (a10E_le_pre ψ Λ₂).trans (a10t1_pre_le_M ψ hker hOM (hΛ.le_gamma₂.trans hMJ.ge))
  have hsup : ((a10E J ψ Λ₁ ⊔ a10E J ψ Λ₂).subgroupOf J).map ψ = Λ₁ ⊔ Λ₂ := by
    rw [Subgroup.subgroupOf_sup hEJ₁ hEJ₂, Subgroup.map_sup, hE₁, hE₂]
  have hqmem : q ∈ ((a10E J ψ Λ₁ ⊔ a10E J ψ Λ₂).subgroupOf J).map ψ := by
    rw [hsup]; exact hq
  obtain ⟨e, he', heq⟩ := hqmem
  have he : (e : G) ∈ a10E J ψ Λ₁ ⊔ a10E J ψ Λ₂ := Subgroup.mem_subgroupOf.mp he'
  have heW : (e : G) ∈ M ⊓ Subgroup.centralizer ({x} : Set G) :=
    ⟨(sup_le hEM₁ hEM₂) he, hc.le_cent e.2⟩
  have hcW : (e : G)⁻¹ * w ∈ M ⊓ Subgroup.centralizer ({x} : Set G) := mul_mem (inv_mem heW) hw
  have hcK : (e : G)⁻¹ * w ∈ u3K0 5 x J := by
    refine ⟨hcW.2, hc.cent_le hcW.2, fun j hj => ?_⟩
    have hwN : w ∈ Subgroup.normalizer (J : Set G) := hc.cent_le hw.2
    have hwj : w * j * w⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp hwN j).mp hj
    have hφj := hρ1 ⟨w, hw⟩ ⟨j, hj⟩ hwj
    rw [hφq] at hφj
    have h1 : ψ (e⁻¹ * (⟨w * j * w⁻¹, hwj⟩ : ↥J) * e * (⟨j, hj⟩ : ↥J)⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, heq, ← hφj]
      group
    have h2 : (e⁻¹ * (⟨w * j * w⁻¹, hwj⟩ : ↥J) * e * (⟨j, hj⟩ : ↥J)⁻¹ : ↥J) ∈ ψ.ker := h1
    rw [hker, Subgroup.mem_subgroupOf] at h2
    have h3 : (e : G)⁻¹ * w * j * ((e : G)⁻¹ * w)⁻¹ * j⁻¹ =
        ((e⁻¹ * (⟨w * j * w⁻¹, hwj⟩ : ↥J) * e * (⟨j, hj⟩ : ↥J)⁻¹ : ↥J) : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [h3]
    exact h2
  have hw_eq : w = (e : G) * ((e : G)⁻¹ * w) := by group
  rw [hw_eq]
  exact Subgroup.mul_mem_sup he ⟨hcW, hcK⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
