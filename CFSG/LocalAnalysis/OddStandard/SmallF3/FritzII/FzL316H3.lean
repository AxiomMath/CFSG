module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316H4

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private theorem fzl_Q_map_mem_iff (h : Ctx t L S x₁ x₂ lam rho tau)
    (hK : Nat.card (twoCore t) = 2)
    {f : ↥(fzN2 t x₁ x₂) →* FzZ2xSigma4} (hF : FzF t x₁ x₂ f) (g : G) :
    g ∈ (fzlK4.comap f).map (fzN2 t x₁ x₂).subtype ↔
      ∃ hg : g ∈ fzN2 t x₁ x₂, f ⟨g, hg⟩ ∈ fzlK4 := by
  constructor
  · intro hg
    rw [Subgroup.mem_map] at hg
    obtain ⟨x, hx, rfl⟩ := hg
    rw [Subgroup.mem_comap] at hx
    exact ⟨x.2, hx⟩
  · rintro ⟨hg, hfg⟩
    rw [Subgroup.mem_map]
    exact ⟨⟨g, hg⟩, by rwa [Subgroup.mem_comap], rfl⟩

theorem fzl_Q_mem_iff (h : Ctx t L S x₁ x₂ lam rho tau) (hK : Nat.card (twoCore t) = 2)
    {f : ↥(fzN2 t x₁ x₂) →* FzZ2xSigma4} (hF : FzF t x₁ x₂ f) :
    ∀ g : G, g ∈ fzQ t x₁ x₂ rho ↔ ∃ hg : g ∈ fzN2 t x₁ x₂, f ⟨g, hg⟩ ∈ fzlK4 := by
  have hRleN : fzR t x₁ x₂ ≤ fzN2 t x₁ x₂ :=
    fun r hr => ((fzl_R_mem_iff h hK hF r).mp hr).1
  have hZleN : zpowers rho ≤ fzN2 t x₁ x₂ :=
    Subgroup.zpowers_le.mpr (fzl_rho_Z h).1
  have hQleN : fzQ t x₁ x₂ rho ≤ fzN2 t x₁ x₂ := by
    rw [fzQ]
    exact sup_le Subgroup.le_normalizer (Subgroup.commutator_le_of_le hRleN hZleN)
  have hEq : fzQ t x₁ x₂ rho = (fzlK4.comap f).map (fzN2 t x₁ x₂).subtype := by
    apply le_antisymm
    · rw [fzQ]
      apply sup_le
      · intro w hw
        rw [fzl_Q_map_mem_iff h hK hF]
        obtain ⟨hwN, hfw⟩ := (fzl_W_mem_iff hF w).mp hw
        exact ⟨hwN, by rw [hfw]; exact fzlK4.one_mem⟩
      · rw [Subgroup.commutator_le]
        intro r hr x hx
        rw [fzl_Q_map_mem_iff h hK hF]
        obtain ⟨hrN, hfrK8⟩ := (fzl_R_mem_iff h hK hF r).mp hr
        have hxN : x ∈ fzN2 t x₁ x₂ := hZleN hx
        have hcN : ⁅r, x⁆ ∈ fzN2 t x₁ x₂ := by
          rw [commutatorElement_def]
          exact (fzN2 t x₁ x₂).mul_mem
            ((fzN2 t x₁ x₂).mul_mem ((fzN2 t x₁ x₂).mul_mem hrN hxN)
              ((fzN2 t x₁ x₂).inv_mem hrN)) ((fzN2 t x₁ x₂).inv_mem hxN)
        refine ⟨hcN, ?_⟩
        have hval : f ⟨⁅r, x⁆, hcN⟩ = ⁅f ⟨r, hrN⟩, f ⟨x, hxN⟩⁆ := by
          have hsub : (⟨⁅r, x⁆, hcN⟩ : ↥(fzN2 t x₁ x₂)) =
              ⁅(⟨r, hrN⟩ : ↥(fzN2 t x₁ x₂)), (⟨x, hxN⟩ : ↥(fzN2 t x₁ x₂))⁆ :=
            Subtype.ext (by simp [commutatorElement_def])
          rw [hsub, map_commutatorElement]
        rw [hval, commutatorElement_def]
        exact fzl_K8_comm_mem_K4 _ hfrK8 _
    · intro g hg
      rw [fzl_Q_map_mem_iff h hK hF] at hg
      obtain ⟨hgN, hfgK4⟩ := hg
      have hrN : rho ∈ fzN2 t x₁ x₂ := (fzl_rho_Z h).1
      let rhoN : ↥(fzN2 t x₁ x₂) := ⟨rho, hrN⟩
      let a : FzZ2xSigma4 := f rhoN
      obtain ⟨ha3, ha1⟩ := fzl_f_rho h hK hF hrN
      obtain ⟨w, hwK4, hw⟩ := fzl_K4_comm_surj a ha3 ha1 (f ⟨g, hgN⟩) hfgK4
      obtain ⟨r₀, hr₀⟩ := hF.surj w
      have hr₀R : r₀.1 ∈ fzR t x₁ x₂ := by
        rw [fzl_R_mem_iff h hK hF]
        refine ⟨r₀.2, ?_⟩
        rw [show (⟨r₀.1, r₀.2⟩ : ↥(fzN2 t x₁ x₂)) = r₀ from rfl, hr₀]
        exact fzl_K4_le_K8 hwK4
      let c : G := ⁅r₀.1, rho⁆
      have hcQ : c ∈ fzQ t x₁ x₂ rho := by
        rw [fzQ]
        exact Subgroup.mem_sup_right
          (Subgroup.commutator_mem_commutator hr₀R (Subgroup.mem_zpowers rho))
      have hcN : c ∈ fzN2 t x₁ x₂ := hQleN hcQ
      have hfc : f ⟨c, hcN⟩ = f ⟨g, hgN⟩ := by
        have hsub : (⟨c, hcN⟩ : ↥(fzN2 t x₁ x₂)) = ⁅r₀, rhoN⁆ := by
          apply Subtype.ext
          simp [c, rhoN, commutatorElement_def]
        rw [hsub, map_commutatorElement, hr₀, commutatorElement_def]
        exact hw
      have hkerN : c⁻¹ * g ∈ fzN2 t x₁ x₂ :=
        (fzN2 t x₁ x₂).mul_mem ((fzN2 t x₁ x₂).inv_mem hcN) hgN
      have hfker : f ⟨c⁻¹ * g, hkerN⟩ = 1 := by
        have hsub : (⟨c⁻¹ * g, hkerN⟩ : ↥(fzN2 t x₁ x₂)) =
            (⟨c, hcN⟩ : ↥(fzN2 t x₁ x₂))⁻¹ * ⟨g, hgN⟩ :=
          Subtype.ext rfl
        rw [hsub, map_mul, map_inv, hfc]
        exact inv_mul_cancel _
      have hkerW : c⁻¹ * g ∈ ctxW t x₁ x₂ :=
        (fzl_W_mem_iff hF (c⁻¹ * g)).mpr ⟨hkerN, hfker⟩
      have hgEq : c * (c⁻¹ * g) = g := by group
      rw [← hgEq]
      exact (fzQ t x₁ x₂ rho).mul_mem hcQ (Subgroup.mem_sup_left hkerW)
  intro g
  rw [hEq]
  exact fzl_Q_map_mem_iff h hK hF g

theorem fzl_card_Q (h : Ctx t L S x₁ x₂ lam rho tau) (hK : Nat.card (twoCore t) = 2)
    {f : ↥(fzN2 t x₁ x₂) →* FzZ2xSigma4} (hF : FzF t x₁ x₂ f) :
    Nat.card (fzQ t x₁ x₂ rho) = 128 := by
  have hmem : ∀ g : G, g ∈ fzQ t x₁ x₂ rho ↔
      ∃ hg : g ∈ fzN2 t x₁ x₂, f ⟨g, hg⟩ ∈ fzlK4 := fzl_Q_mem_iff h hK hF
  have hEq : fzQ t x₁ x₂ rho = (fzlK4.comap f).map (fzN2 t x₁ x₂).subtype :=
    Subgroup.ext fun g => (hmem g).trans (fzl_Q_map_mem_iff h hK hF g).symm
  rw [hEq, Subgroup.card_map_of_injective (fzN2 t x₁ x₂).subtype_injective]
  have hW_le_N2 : ctxW t x₁ x₂ ≤ fzN2 t x₁ x₂ := Subgroup.le_normalizer
  have hWker : Nat.card f.ker = 32 := by
    rw [hF.ker]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW_le_N2).toEquiv]
    exact fzl_card_W h hK
  rw [fzl_card_comap f hF.surj fzlK4, hWker, fzl_card_K4]

end CFSG.OddStandard.SmallF3.FritzII
