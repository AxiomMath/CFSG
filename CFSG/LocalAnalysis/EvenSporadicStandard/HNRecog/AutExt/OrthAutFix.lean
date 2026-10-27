module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.OrthCoord
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.OrthStab
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.OrthShapiro
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.IsoOn

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Equiv Equiv.Perm

variable {G : Type} [Group G]

theorem OrthCoord.exists_inner_of_fix {K M : Subgroup G} {ρ : ↥K →* Perm (Fin 5)} {θ : G → Fv5}
    (hC : OrthCoord K M ρ θ) {φ : G → G} (hφ : IsIsoOn K K φ) (hfix : ∀ x ∈ M, φ x = x) :
    ∃ c ∈ M, ∀ y ∈ K, φ y = c * y * c⁻¹ := by
  have hmem : ∀ l : ↥K, φ (l : G) * (l : G)⁻¹ ∈ M := by
    intro l
    have hconj : ∀ m ∈ M, (l : G)⁻¹ * φ (l : G) * m = m * ((l : G)⁻¹ * φ (l : G)) := by
      intro m hm
      have h1 : (l : G) * m * (l : G)⁻¹ ∈ M := hC.conj_mem' l.2 hm
      have h2 : φ ((l : G) * m * (l : G)⁻¹) = (l : G) * m * (l : G)⁻¹ := hfix _ h1
      rw [IsIsoOn.map_conj hφ l.2 (hC.le hm), hfix m hm] at h2
      calc (l : G)⁻¹ * φ (l : G) * m
          = (l : G)⁻¹ * (φ (l : G) * m * (φ (l : G))⁻¹) * φ (l : G) := by group
        _ = (l : G)⁻¹ * ((l : G) * m * (l : G)⁻¹) * φ (l : G) := by rw [h2]
        _ = m * ((l : G)⁻¹ * φ (l : G)) := by group
    have hzK : (l : G)⁻¹ * φ (l : G) ∈ K :=
      K.mul_mem (K.inv_mem l.2) (hφ.mem (l : G) l.2)
    have hzM : (l : G)⁻¹ * φ (l : G) ∈ M := hC.centralizer_le hzK hconj
    have hconj2 : φ (l : G) * (l : G)⁻¹
        = (l : G) * ((l : G)⁻¹ * φ (l : G)) * (l : G)⁻¹ := by group
    rw [hconj2]
    exact hC.conj_mem' l.2 hzM
  let D : ↥K → Fv5 := fun l => θ (φ (l : G) * (l : G)⁻¹)
  have hD : ∀ l l' : ↥K, D (l * l') = D l + fv5Act (ρ l) (D l') := by
    intro l l'
    have hA : φ (l : G) * (l : G)⁻¹ ∈ M := hmem l
    have hB : (l : G) * (φ (l' : G) * (l' : G)⁻¹) * (l : G)⁻¹ ∈ M :=
      hC.conj_mem l (hmem l')
    have hform : φ ((l * l' : ↥K) : G) * ((l * l' : ↥K) : G)⁻¹
        = (φ (l : G) * (l : G)⁻¹)
          * ((l : G) * (φ (l' : G) * (l' : G)⁻¹) * (l : G)⁻¹) := by
      have hcoe : ((l * l' : ↥K) : G) = (l : G) * (l' : G) := rfl
      rw [hcoe, hφ.map_mul (l : G) l.2 (l' : G) l'.2]
      group
    show θ (φ ((l * l' : ↥K) : G) * ((l * l' : ↥K) : G)⁻¹)
        = θ (φ (l : G) * (l : G)⁻¹) + fv5Act (ρ l) (θ (φ (l' : G) * (l' : G)⁻¹))
    rw [hform, hC.mul _ hA _ hB, hC.conj l _ (hmem l')]
  have hstab : ∀ k : ↥K, ρ k 0 = 0 → D k 0 = 0 := by
    refine stab_hom_zero ρ hC.sign_eq hC.surj (fun l => D l 0) ?_ ?_
    · intro k k' hk
      have hinv0 : (ρ k)⁻¹ 0 = 0 := by
        simpa [Equiv.Perm.inv_def, hk] using Equiv.symm_apply_apply (ρ k) 0
      calc D (k * k') 0 = (D k + fv5Act (ρ k) (D k')) 0 := by rw [hD]
        _ = D k 0 + fv5Act (ρ k) (D k') 0 := rfl
        _ = D k 0 + D k' ((ρ k)⁻¹ 0) := rfl
        _ = D k 0 + D k' 0 := by rw [hinv0]
    · intro k hk1
      have hkM : (k : G) ∈ M := (hC.ker k).mp hk1
      have hDk : D k = 0 := by
        show θ (φ (k : G) * (k : G)⁻¹) = 0
        rw [hfix _ hkM, mul_inv_cancel, hC.theta_one]
      rw [hDk]
      rfl
  obtain ⟨c, hceven, hc⟩ := shapiro5 ρ hC.exists_perm_trans D hD hstab
  obtain ⟨c₀, hc₀M, hc₀θ⟩ := hC.exists_eq c hceven
  have hc₀sq : c₀ * c₀ = 1 := hC.mul_self_eq_one hc₀M
  refine ⟨c₀, hc₀M, fun y hy => ?_⟩
  have hmain : ∀ l : ↥K, φ (l : G) = c₀ * (l : G) * c₀⁻¹ := by
    intro l
    have hB : (l : G) * c₀ * (l : G)⁻¹ ∈ M := hC.conj_mem l hc₀M
    have h1 : D l = θ c₀ + θ ((l : G) * c₀ * (l : G)⁻¹) := by
      rw [show D l = c + fv5Act (ρ l) c from hc l, ← hc₀θ, ← hC.conj l c₀ hc₀M]
    have h3 : θ (φ (l : G) * (l : G)⁻¹) = θ (c₀ * ((l : G) * c₀ * (l : G)⁻¹)) := by
      rw [show θ (φ (l : G) * (l : G)⁻¹) = D l from rfl, h1,
        hC.mul c₀ hc₀M _ hB]
    have h4 : φ (l : G) * (l : G)⁻¹ = c₀ * ((l : G) * c₀ * (l : G)⁻¹) :=
      hC.inj _ (hmem l) _ (M.mul_mem hc₀M hB) h3
    calc φ (l : G) = φ (l : G) * (l : G)⁻¹ * (l : G) := by group
      _ = c₀ * ((l : G) * c₀ * (l : G)⁻¹) * (l : G) := by rw [h4]
      _ = c₀ * (l : G) * c₀⁻¹ := by
        rw [inv_eq_of_mul_eq_one_left hc₀sq]
        group
  exact hmain ⟨y, hy⟩

end CFSG.EvenSporadicStandard.HNRecog.Section4
