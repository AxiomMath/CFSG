module

public import CFSG.GH74.GLS.Stage1.Thm2.Recip.L286

public section

namespace CFSG.GH74.GLS.Stage1.Thm2.Recip

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage1.Thm6
  CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem lemma_28_7 (hBal : IG_balance_fAut) (h44 : II4_44) (hAut : II4_Aut) (h327 : IG_3_27) :
    ∀ (G : Type) [Group G] [Finite G] (x y : G) (L J : Subgroup G), RecipCfg G x y L J →
      x ∈ normalizer (J : Set G) → y ∈ normalizer (L : Set G) := by
  intro G _ _ x y L J cfg hxJ
  by_contra hyL
  have hf : ¬ (InducesFAut x J ∨ InducesFAut y L) := fun h =>
    hyL ((lemma_28_3 hBal G x y L J cfg h).2.2.1 hxJ)
  have hfx : ¬ InducesFAut x J := fun h => hf (Or.inl h)
  have hfy : ¬ InducesFAut y L := fun h => hf (Or.inr h)
  have hx1 := mul_self_eq_one_of_orderOf_eq_two cfg.hx
  have hy1 := mul_self_eq_one_of_orderOf_eq_two cfg.hy
  obtain ⟨hIcomp, hrk, -, -⟩ := h327 G cfg.simple x y cfg.hx cfg.hy cfg.comm L cfg.hL hyL
  obtain ⟨u, -, hu, -, hu2, -, -, -⟩ := exists_two_involutions_of_two_le_pRank hrk
  obtain ⟨g, hg1, hg2⟩ := lemma_28_6 hBal h44 hAut h327 G x y L J cfg hxJ hyL hfx hfy u hu hu2
  have huN : u ∈ normalizer (L : Set G) :=
    sup_conjugate_le_normalizer cfg.comm cfg.hL hyL (IDiag_le_sup y L hu)
  have hyu : y ≠ u := fun h => hyL (h ▸ huN)
  have huy : u * y = y * u := mem_centralizer_singleton_iff.mp (hIcomp.1 hu).2
  have hux : u * x = x * u := mem_centralizer_singleton_iff.mp (hIcomp.1 hu).1
  have hyY : y ∈ centralizer ({u} : Set G) := mem_centralizer_singleton_iff.mpr huy.symm
  have hxY : x ∈ centralizer ({u} : Set G) := mem_centralizer_singleton_iff.mpr hux.symm
  have hucJ : u ∈ cSec J := I_le_cSec h327 cfg hxJ hyL hu
  obtain ⟨N, hNle, -, -, -, hNW, h2el, hcov⟩ :=
    TwoThin.pumpup_cover (x := y) (y := u) hu2 cfg.hJ.1
      (hucJ : u ∈ centralizerSection J (pPrimeCoreOf 2 J))
  have hs2 : (⟨y, hyY⟩ : ↥(centralizer ({u} : Set G))) * ⟨y, hyY⟩ = 1 := Subtype.ext hy1
  have hyN : y ∈ N :=
    h2el y ⟨cfg.hJ.2.2, hyY⟩ ⟨1, by rw [pow_one, pow_two]; exact hy1⟩
  have hso := TwoThin.orderOf_mk_centralizer hyY cfg.hy
  have hNC := TwoThin.le_centralizer_mk (TwoThin.isPCompIn_two_iff.mp hNW).1 hyY
  have hN2 := TwoThin.isTwoComponent_centralizer_mk hNW hyY
  obtain ⟨-, -, L₀, hL₀, hcases, -, -, -⟩ := TwoThin.pumpupY_structure hso hNC hN2
  have hπs : TwoThin.barMk ↥(centralizer ({u} : Set G)) ⟨y, hyY⟩ ∈
      (N.subgroupOf (centralizer ({u} : Set G))).map (TwoThin.barMk ↥(centralizer ({u} : Set G))) :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hyN)
  have hcase1 : (N.subgroupOf (centralizer ({u} : Set G))).map
      (TwoThin.barMk ↥(centralizer ({u} : Set G))) ≤ L₀ := by
    rcases hcases with ⟨-, h⟩ | ⟨hne, hAB, hdiag⟩
    · exact h
    · exfalso
      obtain ⟨z, hz⟩ := hdiag hπs
      have hmem : TwoThin.barMk ↥(centralizer ({u} : Set G)) ⟨y, hyY⟩ ∈
          L₀ ⊔ conjSub (TwoThin.barMk ↥(centralizer ({u} : Set G)) ⟨y, hyY⟩)⁻¹ L₀ := by
        have h0 := swapDiag_mem_sup hAB z
        rw [hz] at h0
        exact h0
      have hle : L₀ ⊔ conjSub (TwoThin.barMk ↥(centralizer ({u} : Set G)) ⟨y, hyY⟩)⁻¹ L₀ ≤
          normalizer (L₀ : Set (TwoThin.barQ ↥(centralizer ({u} : Set G)))) := by
        refine sup_le (fun l hl => le_normalizer hl) ?_
        intro z' hz'
        have h1 := le_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 hAB)
        have h2 : z' ∈ centralizer
            (L₀ : Set (TwoThin.barQ ↥(centralizer ({u} : Set G)))) := h1 hz'
        exact Subgroup.centralizer_le_normalizer _ h2
      exact hne (Subgroup.mem_normalizer_iff_map_conj_eq.mp (inv_mem (hle hmem)))
  have hHne : ∀ H : Subgroup G, IsIntrinsic u H →
      (H.subgroupOf (centralizer ({u} : Set G))).map (TwoThin.barMk ↥(centralizer ({u} : Set G))) ≠
        L₀ := by
    intro H hH heq
    have hH2 : TwoComponents.IsTwoComponent (H.subgroupOf (centralizer ({u} : Set G))) :=
      (TwoThin.isPCompIn_two_iff.mp hH.1).2
    have hy_in : TwoThin.barMk ↥(centralizer ({u} : Set G)) ⟨y, hyY⟩ ∈
        (H.subgroupOf (centralizer ({u} : Set G))).map
          (TwoThin.barMk ↥(centralizer ({u} : Set G))) := by
      rw [heq]
      exact hcase1 hπs
    have hmem := mem_of_barMk_mem hH2 ⟨1, by rw [pow_one, pow_two]; exact hs2⟩ hy_in
    have hyH : y ∈ H := Subgroup.mem_subgroupOf.mp hmem
    exact hyu (hH.eq_of_involution hu2 hyH cfg.hy)
  have hHZ : ∀ H : Subgroup G, IsIntrinsic u H →
      H.subgroupOf (centralizer ({u} : Set G)) ≤
        (centralizer (L₀ : Set (TwoThin.barQ ↥(centralizer ({u} : Set G))))).comap
          (TwoThin.barMk ↥(centralizer ({u} : Set G))) := by
    intro H hH
    have hH2 : TwoComponents.IsTwoComponent (H.subgroupOf (centralizer ({u} : Set G))) :=
      (TwoThin.isPCompIn_two_iff.mp hH.1).2
    have c1 := TwoThin.isComponent_map_barMk hH2
    have hcomm := (CFSG.LocalCores.distinct_components_commute c1 hL₀).resolve_left (hHne H hH)
    have hle := commutator_eq_bot_iff_le_centralizer.1 hcomm
    intro q hq
    exact hle (Subgroup.mem_map_of_mem _ hq)
  have hH₁ : IsIntrinsic u (L.map (MulAut.conj g⁻¹).toMonoidHom) := by
    have h := isIntrinsic_map_conj cfg.hL g⁻¹
    rwa [inv_inv, hg2] at h
  have hH₂ : IsIntrinsic u ((conjugate L y).map (MulAut.conj g⁻¹).toMonoidHom) := by
    have h := isIntrinsic_map_conj (isIntrinsic_conjugate cfg.comm cfg.hL) g⁻¹
    rwa [inv_inv, hg2] at h
  have hxsup : x ∈ L.map (MulAut.conj g⁻¹).toMonoidHom ⊔
      (conjugate L y).map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [← Subgroup.map_sup]
    refine ⟨u, IDiag_le_sup y L hu, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact hg1
  have hxZ : (⟨x, hxY⟩ : ↥(centralizer ({u} : Set G))) ∈
      (centralizer (L₀ : Set (TwoThin.barQ ↥(centralizer ({u} : Set G))))).comap
        (TwoThin.barMk ↥(centralizer ({u} : Set G))) := by
    have h1 : (⟨x, hxY⟩ : ↥(centralizer ({u} : Set G))) ∈
        (L.map (MulAut.conj g⁻¹).toMonoidHom ⊔
          (conjugate L y).map (MulAut.conj g⁻¹).toMonoidHom).subgroupOf
          (centralizer ({u} : Set G)) := hxsup
    rw [Subgroup.subgroupOf_sup hH₁.1.1 hH₂.1.1] at h1
    exact (sup_le (hHZ _ hH₁) (hHZ _ hH₂)) h1
  have hcovD : ∀ k ∈ J, ∃ d ∈ J ⊓ centralizer ({u} : Set G), ∃ o ∈ pPrimeCoreOf 2 J,
      k = d * o := fun k hk => by
    obtain ⟨l, hl, o, ho, e⟩ := hcov k hk
    exact ⟨l, hNle hl, o, ho, e⟩
  have hcl : ∀ l ∈ N, l * x * l⁻¹ * x⁻¹ ∈ pPrimeCoreOf 2 J := by
    intro l hl
    have hlJ : l ∈ J := (hNle hl).1
    have hlY : l ∈ centralizer ({u} : Set G) := (hNle hl).2
    have hlbar : TwoThin.barMk ↥(centralizer ({u} : Set G)) ⟨l, hlY⟩ ∈ L₀ :=
      hcase1 (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hl))
    have hxZ' : TwoThin.barMk ↥(centralizer ({u} : Set G)) ⟨x, hxY⟩ ∈
        centralizer (L₀ : Set (TwoThin.barQ ↥(centralizer ({u} : Set G)))) := hxZ
    have hcomm := mem_centralizer_iff.mp hxZ' _ hlbar
    have hcJ : l * x * l⁻¹ * x⁻¹ ∈ J := by
      have h1 : x * l⁻¹ * x⁻¹ ∈ J := (mem_normalizer_iff.mp hxJ l⁻¹).mp (inv_mem hlJ)
      have : l * x * l⁻¹ * x⁻¹ = l * (x * l⁻¹ * x⁻¹) := by group
      rw [this]
      exact mul_mem hlJ h1
    have hcY : l * x * l⁻¹ * x⁻¹ ∈ centralizer ({u} : Set G) :=
      mul_mem (mul_mem (mul_mem hlY hxY) (inv_mem hlY)) (inv_mem hxY)
    have hc1 : TwoThin.barMk ↥(centralizer ({u} : Set G)) ⟨l * x * l⁻¹ * x⁻¹, hcY⟩ = 1 := by
      have e : (⟨l * x * l⁻¹ * x⁻¹, hcY⟩ : ↥(centralizer ({u} : Set G))) =
          ⟨l, hlY⟩ * ⟨x, hxY⟩ * ⟨l, hlY⟩⁻¹ * ⟨x, hxY⟩⁻¹ := rfl
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
      group
    exact mem_pPrimeCoreOf_of_cover (J := J) (D := J ⊓ centralizer ({u} : Set G))
      (Y := centralizer ({u} : Set G)) inf_le_left inf_le_right hcovD ⟨hcJ, hcY⟩
      ((hatMk_eq_one_iff (centralizer ({u} : Set G)) _).mp hc1)
  have hxc : x ∈ cSec J := by
    refine ⟨hxJ, TwoThin.mem_normalizer_pPrimeCoreOf hxJ, fun k hk => ?_⟩
    obtain ⟨l, hl, o, ho, hko⟩ := hcov k hk
    have hlJ : l ∈ J := (hNle hl).1
    have hcl' := hcl l hl
    have hox : o * (x * o⁻¹ * x⁻¹) ∈ pPrimeCoreOf 2 J :=
      mul_mem ho (TwoThin.mul_mem_pPrimeCoreOf_of_mem_normalizer hxJ (inv_mem ho))
    have hlox : l * (o * (x * o⁻¹ * x⁻¹)) * l⁻¹ ∈ pPrimeCoreOf 2 J :=
      TwoThin.mul_mem_pPrimeCoreOf_of_mem_normalizer (le_normalizer hlJ) hox
    have e : ⁅k, x⁆ = (l * (o * (x * o⁻¹ * x⁻¹)) * l⁻¹) * (l * x * l⁻¹ * x⁻¹) := by
      rw [hko]
      simp only [commutatorElement_def]
      group
    rw [e]
    exact mul_mem hlox hcl'
  exact hfx (inducesFAut_of_mem_cSec cfg.simple cfg.hy cfg.hJ.1 cfg.hJ.2.1 hxc)

end CFSG.GH74.GLS.Stage1.Thm2.Recip
