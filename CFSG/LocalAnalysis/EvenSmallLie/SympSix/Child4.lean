module

public import CFSG.LocalAnalysis.EvenSmallLie.StandardForm
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.CoverUnique
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3GSide
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixCyclicKernel

public section

namespace CFSG.EvenSmallLie.SympSix

open Subgroup CFSG.Blueprint CFSG.Sporadic.Schreier.Co3

theorem sp6Cover_standard_form
    {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hset : StandardSetting G L) (hZ : center L ≠ ⊥) (hX : LieModel (L ⧸ center L) .PSp 3 2 1) :
    ∃ t : G, orderOf t = 2 ∧ centralizer (L : Set G) = zpowers t ∧
      (center L).map L.subtype = zpowers t ∧ Nat.card (center L) = 2 ∧
      centralizer ({t} : Set G) = L ∧
      ∃ θ : co3M ≃* centralizer ({t} : Set G), (θ co3ZM : G) = t := by
  obtain ⟨t, ht, hC, hZt, hcard, hcent⟩ := std_standard_form_of_inner hset hZ
    (CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.exists_eq_conj_of_lieModel hX)
    (fun v hv => Sp6.sp62_J_condition hX v hv)
  obtain ⟨z, hz, hzt⟩ : t ∈ (center L).map L.subtype := hZt ▸ mem_zpowers t
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [map_one] at hzt
    rw [← hzt, orderOf_one] at ht
    exact absurd ht (by decide)
  obtain ⟨θ₀, hθ₀⟩ :=
    sp62_double_cover_unique_of_mem_center L hset.standard.1.1 hcard hX hz hz1
  refine ⟨t, ht, hC, hZt, hcard, hcent, θ₀.trans (MulEquiv.subgroupCongr hcent.symm), ?_⟩
  rw [MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply, hθ₀]
  exact hzt

@[expose] def FendelInputs :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → ∀ (s : G)
    (θ : co3M ≃* centralizer ({s} : Set G)), (θ co3ZM : G) = s →
    (∀ x : co3M, orderOf x = 2 → (IsConj s (θ x : G) ↔ x = co3ZM ∨ x ∈ Co3Ident.classA)) ∧
      Nat.card G = 495766656000

theorem childSp6Cover_of_inputs
    (hF : FendelInputs) : ChildSp6Cover := by
  intro G _ _ L hset hZ _ hX
  obtain ⟨t, -, -, -, -, -, θ, hθ⟩ := sp6Cover_standard_form hset hZ hX
  obtain ⟨hH2, hH3⟩ := hF G hset.simple t θ hθ
  exact Co3Ident.isSporadic_co3_of_centralizer θ hθ hH2 hH3

end CFSG.EvenSmallLie.SympSix
