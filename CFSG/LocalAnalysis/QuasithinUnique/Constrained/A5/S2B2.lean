module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S2A5

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.A5.S2 CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.AppC Equiv

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

namespace S2

omit [Finite G] in
theorem conjR_L_le_phi {x : G} (hxφ : x ∈ Subgroup.normalizer (s2Phi S L : Set G)) :
    conjR L x ≤ Subgroup.normalizer (s2Phi S L : Set G) := by
  rintro _ ⟨l, hl, rfl⟩
  have hl' := L_le_normalizer_phi (S := S) hl
  show x⁻¹ * l * x⁻¹⁻¹ ∈ _
  rw [inv_inv]
  exact mul_mem (mul_mem (inv_mem hxφ) hl') hxφ

namespace Ctx

variable {t : G} (c : Ctx T M H S L t)
include c

theorem Ux_le_R {x : G} (hxN : x ∈ Subgroup.normalizer (S : Set G)) :
    conjR (blockU L) x ≤ baum S := by
  have hxR : x⁻¹ ∈ Subgroup.normalizer (baum S : Set G) :=
    inv_mem (normalizer_le_normalizer_baum S hxN)
  have hRx : conjR (baum S) x = baum S := mem_normalizer_iff_cj.1 hxR
  have := Subgroup.map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) c.u₁R
  rwa [show Subgroup.map (MulAut.conj x⁻¹).toMonoidHom (baum S) = baum S from hRx] at this

theorem Ux_inf {P₂ : A5Pi (cj t L)} (hE : P₂.im (baum S) = Estd) (hI : P₂.im (s2I S L) = Estd)
    {x : G} (hxN : x ∈ Subgroup.normalizer (S : Set G))
    (hxφ : x ∈ Subgroup.normalizer (s2Phi S L : Set G))
    (hxU : ¬ conjR (blockU L) x ≤ s2Q1 S L) :
    conjR (blockU L) x ⊓ pCoreOf 2 (Subgroup.normalizer (s2Phi S L : Set G)) = ⊥ := by
  have h := c.data
  set Gi : Subgroup G := Subgroup.normalizer (s2Phi S L : Set G) with hGi
  have hLx : IsShort2 (conjR L x) := Lin2.IsShort2.map_equiv h.isShort (MulAut.conj x⁻¹)
  have h5x : IsAltType (conjR L x) 5 := L238.IsAltType.map_equiv h.alt5 (MulAut.conj x⁻¹)
  have hUx : blockU (conjR L x) = conjR (blockU L) x :=
    Lin2.blockU_map_equiv (MulAut.conj x⁻¹) L
  have hZx : blockZ (conjR L x) = ⊥ := AppC.blockZ_eq_bot_of_alt5 hLx h5x
  have hLxG : conjR L x ≤ Gi := conjR_L_le_phi hxφ
  have hLn : conjR L x ≤ Subgroup.normalizer
      ((conjR (blockU L) x ⊓ pCoreOf 2 Gi : Subgroup G) : Set G) := by
    intro y hy
    refine Subgroup.inf_normalizer_le_normalizer_inf ⟨?_, ?_⟩
    · rw [← hUx]
      exact C1.mem_normalizer_blockU (Subgroup.le_normalizer hy)
    · exact CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 Gi (hLxG hy)
  have hWU : conjR (blockU L) x ⊓ pCoreOf 2 Gi ≤ blockU (conjR L x) := by
    rw [hUx]
    exact inf_le_left
  rcases hLx.2.2.2.2.2 (conjR (blockU L) x ⊓ pCoreOf 2 Gi) (by rw [hZx]; exact bot_le) hWU
      hLn with hW | hW
  · rwa [hZx] at hW
  · exfalso
    apply hxU
    rw [hUx] at hW
    have hUxO : conjR (blockU L) x ≤ pCoreOf 2 Gi := by
      rw [← hW]
      exact inf_le_right
    have hUxR := c.Ux_le_R hxN
    have hSIφ : s2SI S L ≤ Gi := (c.SI_phi hE hI).le.trans (inf_le_right)
    set X : Subgroup G := L ⊔ s2SI S L with hX
    have hXG : X ≤ Gi := sup_le (L_le_normalizer_phi (S := S)) hSIφ
    have hUxX : conjR (blockU L) x ≤ X := hUxR.trans (c.R_le_SI.trans le_sup_right)
    have hXn : X ≤ Subgroup.normalizer (pCoreOf 2 Gi : Set G) :=
      hXG.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 Gi)
    have hN : pCoreOf 2 Gi ⊓ X ≤ pCoreOf 2 X := by
      refine le_pCoreOf_of_normalizes inf_le_right ?_
        ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 Gi).to_inf_left)
      intro y hy
      exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hXn hy, Subgroup.le_normalizer hy⟩
    have hLR : L ⊔ baum S ≤ X := sup_le le_sup_left (c.R_le_SI.trans le_sup_right)
    have hN' : pCoreOf 2 X ⊓ (L ⊔ baum S) ≤ pCoreOf 2 (L ⊔ baum S) := by
      refine le_pCoreOf_of_normalizes inf_le_right ?_
        ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 X).to_inf_left)
      intro y hy
      exact Subgroup.inf_normalizer_le_normalizer_inf
        ⟨CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 X (hLR hy),
          Subgroup.le_normalizer hy⟩
    intro z hz
    exact hN' ⟨hN ⟨hUxO hz, hUxX hz⟩, (le_sup_right : baum S ≤ L ⊔ baum S) (hUxR hz)⟩

end Ctx

end S2

end CFSG.QuasithinUnique.A5
