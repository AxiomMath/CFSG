module

public import CFSG.GH74.GLS.Stage1.Main.BrFusedFour
public import CFSG.GH74.GLS.Stage2.Final.LayerFDerive
public import CFSG.GH74.GLS.Stage2.Final.ModelLayerBar
public import CFSG.GH74.GLS.Stage1.Main.Bridge

public section

namespace CFSG.GH74.GLS.Stage1.Main

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Final

structure FusedCtx {G : Type} [Group G] (z : G) (S : Subgroup G) (ε : Bool) (Gs : Type) [Group Gs]
    (p f : ℕ) where
  S₁ : Sylow 2 Gs
  z₁ : Gs
  E₁ : Subgroup Gs
  E₂ : Subgroup Gs
  t₁ : Gs
  u₁ : Gs
  n₁ : Gs
  pkg : FusedPkg Gs (p ^ f) (if ε then 1 else -1) z₁ S₁ E₁ E₂ t₁ u₁ n₁
  Ψ : ↥(Stage1.Thm3.Sec8.layerSBar z S) ≃* ↥(layerTimesSylow z₁ (S₁ : Subgroup Gs))
  hΨ : ∀ y : ↥(Stage1.Thm3.Sec8.layerSBar z S),
    (y : CentralizerBar z) ∈ barOf z S ↔
      ((Ψ y : ↥(layerTimesSylow z₁ (S₁ : Subgroup Gs))) : Gs) ∈ (S₁ : Subgroup Gs)

theorem exists_fused_psi {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} (hcen : Cen2 G z S)
    {Gs : Type} [Group Gs] [Finite Gs] {p f : ℕ} (hGsm : IsClassicalModel Gs p f)
    (hLU0 : LieModel Gs .PSL 4 p f ∨ LieModel Gs .PSU 4 p f) (S₁ : Sylow 2 Gs) (hSS₁ : Nonempty (↥S ≃* ↥(S₁ : Subgroup Gs)))
    {z₁ : Gs} (hz₁o : orderOf z₁ = 2) (hcen₁ : (center ↥(S₁ : Subgroup Gs)).map (S₁ : Subgroup Gs).subtype = zpowers z₁)
    (hC : ∀ (z' : Gs) (S' : Sylow 2 ↥(centralizer ({z'} : Set Gs))), IsCentralInvolution z' →
      ∀ S'' : Sylow 2 Gs, Nonempty (↥S ≃* ↥(S'' : Subgroup Gs)) →
        (S'' : Subgroup Gs) = (S' : Subgroup ↥(centralizer ({z'} : Set Gs))).map
            (centralizer ({z'} : Set Gs)).subtype →
          Nonempty (↥(Stage1.Thm3.Sec8.layerSBar z S) ≃* ↥(Stage1.Thm3.Sec8.layerSBar z' (S'' : Subgroup Gs)))) :
    ∃ Ψ : ↥(Stage1.Thm3.Sec8.layerSBar z S) ≃* ↥(layerTimesSylow z₁ (S₁ : Subgroup Gs)),
      ∀ y : ↥(Stage1.Thm3.Sec8.layerSBar z S), (y : CentralizerBar z) ∈ barOf z S ↔
        ((Ψ y : ↥(layerTimesSylow z₁ (S₁ : Subgroup Gs))) : Gs) ∈ (S₁ : Subgroup Gs) := by
  obtain ⟨hz₁S, hz₁c⟩ := comm_of_center hcen₁
  have hz₁cent : IsCentralInvolution z₁ := ⟨hz₁o, S₁, hz₁S, hz₁c⟩
  have hS₁C : (S₁ : Subgroup Gs) ≤ Cen z₁ := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hz₁c s hs)
  have hS₁G : CFSG.ABGLocalTools.IsSylowOf 2 (S₁ : Subgroup Gs) ⊤ := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_top, S₁.isPGroup', ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact S₁.not_dvd_index
  have hS₁C' : CFSG.ABGLocalTools.IsSylowOf 2 (S₁ : Subgroup Gs) (Cen z₁) := hS₁G.of_le hS₁C le_top
  obtain ⟨S'c, hS'c⟩ := hS₁C'
  obtain ⟨φ₀⟩ := hC z₁ S'c hz₁cent S₁ hSS₁ hS'c.symm
  have hSylX : CFSG.ABGLocalTools.IsSylowOf 2 (barOf z S) (Stage1.Thm3.Sec8.layerSBar z S) :=
    (isSylowOf_barOf hcen.sylow).of_le (by rw [layerSBar_eq_sup]; exact le_sup_right) le_top
  have hSylY : CFSG.ABGLocalTools.IsSylowOf 2 (barOf z₁ (S₁ : Subgroup Gs))
      (Stage1.Thm3.Sec8.layerSBar z₁ (S₁ : Subgroup Gs)) :=
    (isSylowOf_barOf ⟨S'c, hS'c⟩).of_le (by rw [layerSBar_eq_sup]; exact le_sup_right) le_top
  obtain ⟨PX, hPX⟩ := hSylX.exists_sylow_eq_subgroupOf
  obtain ⟨PY, hPY⟩ := hSylY.exists_sylow_eq_subgroupOf
  obtain ⟨φ, hφ'⟩ := exists_equiv_sylow φ₀ PX PY
  have hφ : ∀ y : ↥(Stage1.Thm3.Sec8.layerSBar z S),
      (y : CentralizerBar z) ∈ barOf z S ↔
        (φ y : CentralizerBar z₁) ∈ barOf z₁ (S₁ : Subgroup Gs) := by
    intro y
    have h1 := hφ' y
    rw [hPX, hPY] at h1
    exact h1
  obtain ⟨hN', hB'⟩ := modelLayerBar Gs p f S₁ z₁ hGsm hLU0 hz₁o hcen₁
  have hB'' : barOf z₁ (layerTimesSylow z₁ (S₁ : Subgroup Gs)) =
      Stage1.Thm3.Sec8.layerSBar z₁ (S₁ : Subgroup Gs) := by
    rw [layerSBar_eq_sup, layer_sup_barOf_eq_of_barOf_eq S₁.isPGroup' hS₁C hB', hB']
  have hAC := layerTimesSylow_le_Cen hS₁C
  have hSA : (S₁ : Subgroup Gs) ≤ layerTimesSylow z₁ (S₁ : Subgroup Gs) := le_sup_right
  let ι : ↥(layerTimesSylow z₁ (S₁ : Subgroup Gs)) ≃* ↥(Stage1.Thm3.Sec8.layerSBar z₁ (S₁ : Subgroup Gs)) :=
    (barEquiv z₁ _ hAC hN').trans (MulEquiv.subgroupCongr hB'')
  refine ⟨φ.trans ι.symm, fun y => ?_⟩
  rw [hφ y]
  have h1 := mem_iff_barOf z₁ _ (S₁ : Subgroup Gs) hAC hN' hSA (ι.symm (φ y))
  have h2 : ((barEquiv z₁ _ hAC hN' (ι.symm (φ y)) : ↥(barOf z₁ _)) : CentralizerBar z₁) =
      ((φ y : ↥(Stage1.Thm3.Sec8.layerSBar z₁ (S₁ : Subgroup Gs))) : CentralizerBar z₁) := by
    have := congrArg Subtype.val (ι.apply_symm_apply (φ y))
    exact this
  rw [h2] at h1
  exact h1.symm

theorem fused_ctx_of (hfus : FusedModelLeaf) {G : Type} [Group G] [Finite G] {z : G}
    {S : Subgroup G} (hcen : Cen2 G z S) {ε : Bool} {Gs : Type} [Group Gs] [Finite Gs] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hm : (ε = true ∧ p ^ f % 8 = 5 ∧ LieModel Gs .PSL 4 p f) ∨
      (ε = false ∧ p ^ f % 8 = 3 ∧ 3 < p ^ f ∧ LieModel Gs .PSU 4 p f))
    (hS : ∃ S' : Sylow 2 Gs, Nonempty (↥S ≃* ↥(S' : Subgroup Gs)))
    (hC : ∀ (z' : Gs) (S' : Sylow 2 ↥(centralizer ({z'} : Set Gs))), IsCentralInvolution z' →
      ∀ S'' : Sylow 2 Gs, Nonempty (↥S ≃* ↥(S'' : Subgroup Gs)) →
        (S'' : Subgroup Gs) = (S' : Subgroup ↥(centralizer ({z'} : Set Gs))).map
            (centralizer ({z'} : Set Gs)).subtype →
          Nonempty (↥(Stage1.Thm3.Sec8.layerSBar z S) ≃* ↥(Stage1.Thm3.Sec8.layerSBar z' (S'' : Subgroup Gs)))) :
    Nonempty (FusedCtx z S ε Gs p f) := by
  obtain ⟨S₁, hSS₁⟩ := hS
  have hq5 : 5 ≤ p ^ f ∧ 3 < p ^ f := by
    rcases hm with ⟨-, h8, -⟩ | ⟨-, h8, h3, -⟩ <;> omega
  have hGs : IsClassicalModel Gs p f ∧ (LieModel Gs .PSL 4 p f ∨ LieModel Gs .PSU 4 p f) := by
    rcases hm with ⟨-, h8, hL⟩ | ⟨-, h8, -, hL⟩
    · exact ⟨⟨hp, hp2, hq5.2, Or.inr (Or.inl ⟨by omega, hL⟩)⟩, Or.inl hL⟩
    · exact ⟨⟨hp, hp2, hq5.2, Or.inr (Or.inr ⟨by omega, hL⟩)⟩, Or.inr hL⟩
  obtain ⟨hGsm, hLU0⟩ := hGs
  obtain ⟨z₁, hz₁o, hcen₁⟩ := modelCenter Gs p f hGsm S₁
  obtain ⟨E₁, E₂, t₁, u₁, n₁, hpkg⟩ : ∃ (E₁ E₂ : Subgroup Gs) (t u n : Gs),
      FusedPkg Gs (p ^ f) (if ε then 1 else -1) z₁ S₁ E₁ E₂ t u n := by
    rcases hm with ⟨hε, h8, hL⟩ | ⟨hε, h8, -, hL⟩
    · subst hε
      simpa using (hfus Gs p f hp hp2 hq5.1 S₁ z₁ hcen₁).1 ⟨h8, hL⟩
    · subst hε
      simpa using (hfus Gs p f hp hp2 hq5.1 S₁ z₁ hcen₁).2 ⟨h8, hL⟩
  obtain ⟨Ψ, hΨ⟩ := exists_fused_psi hcen hGsm hLU0 S₁ hSS₁ hz₁o hcen₁ hC
  exact ⟨⟨S₁, z₁, E₁, E₂, t₁, u₁, n₁, hpkg, Ψ, hΨ⟩⟩

theorem fused_ctx (hfus : FusedModelLeaf) {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}
    (hcen : Cen2 G z S) {ε : Bool} (hE : L4U4TermTypeE ε G z S) :
    ∃ (Gs : Type) (_ : Group Gs) (_ : Finite Gs) (p f : ℕ), p.Prime ∧ p ≠ 2 ∧ 5 ≤ p ^ f ∧
      ((ε = true ∧ p ^ f % 8 = 5) ∨ (ε = false ∧ p ^ f % 8 = 3)) ∧
      Nonempty (FusedCtx z S ε Gs p f) := by
  obtain ⟨-, Gs, iGs, fGs, p, f, hp, hp2, hm, hS, hC⟩ := hE
  have hq5 : 5 ≤ p ^ f := by
    rcases hm with ⟨-, h8, -⟩ | ⟨-, h8, h3, -⟩ <;> omega
  have htag : (ε = true ∧ p ^ f % 8 = 5) ∨ (ε = false ∧ p ^ f % 8 = 3) := by
    rcases hm with ⟨h1, h8, -⟩ | ⟨h1, h8, -, -⟩
    · exact Or.inl ⟨h1, h8⟩
    · exact Or.inr ⟨h1, h8⟩
  exact ⟨Gs, iGs, fGs, p, f, hp, hp2, hq5, htag, fused_ctx_of hfus hcen hp hp2 hm hS hC⟩

end CFSG.GH74.GLS.Stage1.Main
