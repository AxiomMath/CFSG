module

public import CFSG.LocalAnalysis.GH72.Sec5CO2
public import CFSG.LocalAnalysis.GH72.Sec4Bar
public import CFSG.LocalAnalysis.GH72.Sec4Residual
public import CFSG.LocalAnalysis.GH72.Sec5CBar
public import CFSG.LocalAnalysis.GH72.Sec5Roles

public section

namespace CFSG.GH72

open Subgroup CFSG.ABGLocalTools
open scoped commutatorElement

namespace Sec4Setting

variable {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G) (A : Subgroup G)

theorem prop_3_15_weaken
    (h315 : (∃ H₁ : Subgroup (Bar (C 𝔖.z₁)), bar (C 𝔖.z₁) 𝔖.S₁ ⊓ H₁ = ⊥ ∧
        bar (C 𝔖.z₁) 𝔖.S₁ ⊔ H₁ = ⊤ ∧
        H₁ ≤ centralizer (bar (C 𝔖.z₁) 𝔖.S₁ : Set (Bar (C 𝔖.z₁))) ∧
        bar (C 𝔖.z₁) 𝔖.S₂ ≤ ⁅H₁, H₁⁆ ∧ IsL2OrA7 (⁅H₁, H₁⁆ : Subgroup (Bar (C 𝔖.z₁))) 7) ∧
      (∃ K₁ : Subgroup (Bar (C 𝔖.z₂)), bar (C 𝔖.z₂) 𝔖.S₂ ⊓ K₁ = ⊥ ∧
        bar (C 𝔖.z₂) 𝔖.S₂ ⊔ K₁ = ⊤ ∧
        K₁ ≤ centralizer (bar (C 𝔖.z₂) 𝔖.S₂ : Set (Bar (C 𝔖.z₂))) ∧
        bar (C 𝔖.z₂) 𝔖.S₁ ≤ ⁅K₁, K₁⁆ ∧
        (IsL2OrA7 (⁅K₁, K₁⁆ : Subgroup (Bar (C 𝔖.z₂))) 5 ∨ ⁅K₁, K₁⁆ = bar (C 𝔖.z₂) 𝔖.S₁))) :
    (∃ H₁ : Subgroup (Bar (C 𝔖.z₁)), bar (C 𝔖.z₁) 𝔖.S₁ ⊓ H₁ = ⊥ ∧
        bar (C 𝔖.z₁) 𝔖.S₁ ⊔ H₁ = ⊤ ∧
        H₁ ≤ centralizer (bar (C 𝔖.z₁) 𝔖.S₁ : Set (Bar (C 𝔖.z₁))) ∧
        bar (C 𝔖.z₁) 𝔖.S₂ ≤ ⁅H₁, H₁⁆ ∧
        (IsL2OrA7 (⁅H₁, H₁⁆ : Subgroup (Bar (C 𝔖.z₁))) 5 ∨ ⁅H₁, H₁⁆ = bar (C 𝔖.z₁) 𝔖.S₂)) ∧
      (∃ K₁ : Subgroup (Bar (C 𝔖.z₂)), bar (C 𝔖.z₂) 𝔖.S₂ ⊓ K₁ = ⊥ ∧
        bar (C 𝔖.z₂) 𝔖.S₂ ⊔ K₁ = ⊤ ∧
        K₁ ≤ centralizer (bar (C 𝔖.z₂) 𝔖.S₂ : Set (Bar (C 𝔖.z₂))) ∧
        bar (C 𝔖.z₂) 𝔖.S₁ ≤ ⁅K₁, K₁⁆ ∧
        (IsL2OrA7 (⁅K₁, K₁⁆ : Subgroup (Bar (C 𝔖.z₂))) 5 ∨ ⁅K₁, K₁⁆ = bar (C 𝔖.z₂) 𝔖.S₁)) := by
  obtain ⟨⟨H₁, h₁, h₂, h₃, h₄, h₅⟩, h₆⟩ := h315
  exact ⟨⟨H₁, h₁, h₂, h₃, h₄, Or.inl (h₅.mono (by norm_num))⟩, h₆⟩

end Sec4Setting

namespace Sec5Roles

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} (ρ : Sec5Roles G A)

theorem commutator_S₁_M₀_le_O
    (h315i : ∃ H₁ : Subgroup (Bar (C ρ.z₁)), bar (C ρ.z₁) ρ.S₁ ⊓ H₁ = ⊥ ∧
      bar (C ρ.z₁) ρ.S₁ ⊔ H₁ = ⊤ ∧ H₁ ≤ centralizer (bar (C ρ.z₁) ρ.S₁ : Set (Bar (C ρ.z₁))) ∧
      bar (C ρ.z₁) ρ.S₂ ≤ ⁅H₁, H₁⁆ ∧ (IsL2OrA7 (⁅H₁, H₁⁆ : Subgroup (Bar (C ρ.z₁))) 5 ∨
        ⁅H₁, H₁⁆ = bar (C ρ.z₁) ρ.S₂)) :
    ⁅ρ.S₁, ρ.M₀⁆ ≤ O (C ρ.z₁) := by
  obtain ⟨H₁, hSH, htop, hHS, -, -⟩ := h315i
  have hS₁C : ρ.S₁ ≤ (C ρ.z₁) := ρ.hz₁.2.2
  have hMC : ρ.M ≤ (C ρ.z₁) := ρ.M_le_C ρ.z₁_mem_X
  have hM₀C : ρ.M₀ ≤ (C ρ.z₁) := ρ.M₀_le.trans hMC
  have hS₁2 : IsPGroup 2 (bar (C ρ.z₁) ρ.S₁) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨a, -, ⟨e⟩⟩ := ρ.dih₁
    refine isPGroup_bar_of_isPGroup (IsPGroup.of_card (n := a + 1) ?_)
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, DihedralGroup.card, pow_succ]
    ring
  set π := QuotientGroup.mk' (CFSG.oddCore (C ρ.z₁)) with hπdef
  set H₁G : Subgroup G := (H₁.comap π).map (C ρ.z₁).subtype with hH₁Gdef
  have hodd : ∀ g ∈ (C ρ.z₁), Odd (orderOf g) → g ∈ H₁G := by
    intro g hg ho
    refine ⟨⟨g, hg⟩, ?_, rfl⟩
    show π ⟨g, hg⟩ ∈ H₁
    refine mem_of_odd_orderOf_of_sup_eq_top hS₁2 hSH htop hHS ?_
    refine ho.of_dvd_nat ((orderOf_map_dvd π _).trans ?_)
    rw [Subgroup.orderOf_mk]
  have hM₀H : ρ.M₀ ≤ H₁G := by
    refine sup_le ?_ ?_
    · have hO2 : O2 ρ.M ≤ H₁G := by
        show CFSG.GorensteinWalter.twoResidualOf ρ.M ≤ H₁G
        rw [twoResidualOf_eq_closure]
        exact (Subgroup.closure_le _).mpr fun g hg => hodd g (hMC hg.1) hg.2
      exact (commutator_mono hO2 hO2).trans (commutator_le_self _)
    · intro g hg
      exact hodd g (hMC (O_le _ hg)) ((card_O_odd _).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hg))
  have hbarM₀ : bar (C ρ.z₁) ρ.M₀ ≤ H₁ := by
    refine (bar_mono hM₀H).trans ?_
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := Subtype.ext hyx
    rw [← this]
    exact hy
  have hbar : bar (C ρ.z₁) ⁅ρ.S₁, ρ.M₀⁆ = ⊥ := by
    rw [bar_commutator hS₁C hM₀C, commutator_eq_bot_iff_le_centralizer]
    exact le_centralizer_iff.mp (hbarM₀.trans hHS)
  have hcomm : ⁅ρ.S₁, ρ.M₀⁆ ≤ (C ρ.z₁) := commutator_le.mpr fun s hs m hm => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem (hS₁C hs) (hM₀C hm)) (inv_mem (hS₁C hs))) (inv_mem (hM₀C hm))
  exact fun x hx => bar_eq_bot_iff.mp hbar ⟨hx, hcomm hx⟩

theorem commutator_le_O_M_of_isSylowOf
    (h315i : ∃ H₁ : Subgroup (Bar (C ρ.z₁)), bar (C ρ.z₁) ρ.S₁ ⊓ H₁ = ⊥ ∧
      bar (C ρ.z₁) ρ.S₁ ⊔ H₁ = ⊤ ∧ H₁ ≤ centralizer (bar (C ρ.z₁) ρ.S₁ : Set (Bar (C ρ.z₁))) ∧
      bar (C ρ.z₁) ρ.S₂ ≤ ⁅H₁, H₁⁆ ∧ (IsL2OrA7 (⁅H₁, H₁⁆ : Subgroup (Bar (C ρ.z₁))) 5 ∨
        ⁅H₁, H₁⁆ = bar (C ρ.z₁) ρ.S₂))
    (hS₁ : IsSylowOf 2 ρ.S₁ ρ.N₀) (hS₁X : ρ.S₁ ≤ normalizer (ρ.X : Set G))
    {T : Subgroup G} (hT : IsSylowOf 2 T ρ.N₀) (hTX : T ≤ normalizer (ρ.X : Set G)) :
    ⁅T, ρ.M₀⁆ ≤ O ρ.M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS₁M₀ : ⁅ρ.S₁, ρ.M₀⁆ ≤ O ρ.M := by
    have h1 := ρ.commutator_S₁_M₀_le_O h315i
    have h2 : ⁅ρ.S₁, ρ.M₀⁆ ≤ ρ.M := by
      have := le_normalizer_iff_commutator_le_right.mp
        (hS₁X.trans ρ.normalizer_X_le_normalizer_M₀)
      exact this.trans ρ.M₀_le
    have h3 : O (C ρ.z₁) ⊓ ρ.M ≤ O ρ.M :=
      G5d.le_O_of_le_normalizer inf_le_right
        (fun m hm => inf_normalizer_le_normalizer_inf
          ⟨le_normalizer_O _ ((ρ.M_le_C ρ.z₁_mem_X) hm), le_normalizer hm⟩)
        ((card_O_odd _).of_dvd_nat (card_dvd_of_le inf_le_left))
    exact fun x hx => h3 ⟨h1 hx, h2 hx⟩
  set B : Subgroup G := ρ.N₀ ⊓ normalizer (ρ.X : Set G) with hBdef
  have hS₁B : IsSylowOf 2 ρ.S₁ B := hS₁.of_le (le_inf hS₁.le hS₁X) inf_le_left
  obtain ⟨c, hcB, hc⟩ := exists_mem_map_conj_le_of_isSylowOf hS₁B (le_inf hT.le hTX) hT.isPGroup
  have hceq : T.map (MulAut.conj c).toMonoidHom = ρ.S₁ := by
    refine eq_of_le_of_card_ge hc ?_
    rw [card_map_of_injective (MulAut.conj c).injective, hS₁.card_eq, hT.card_eq]
  have hTeq : T = ρ.S₁.map (MulAut.conj c⁻¹).toMonoidHom := by
    rw [← hceq, map_conj_inv_map_conj]
  have hcN : c⁻¹ ∈ normalizer (ρ.X : Set G) := inv_mem hcB.2
  rw [hTeq]
  have hM₀ : ρ.M₀.map (MulAut.conj c⁻¹).toMonoidHom = ρ.M₀ :=
    map_conj_eq_of_mem_normalizer (ρ.normalizer_X_le_normalizer_M₀ hcN)
  have hOM : (O ρ.M).map (MulAut.conj c⁻¹).toMonoidHom = O ρ.M :=
    map_conj_eq_of_mem_normalizer (ρ.normalizer_X_le_normalizer_O_M hcN)
  rw [← hM₀, ← map_commutator, ← hOM]
  exact map_mono hS₁M₀

end Sec5Roles

end CFSG.GH72
