module

public import CFSG.GF2Type.SmithTypeE.E7.ClsMain
public import CFSG.GF2Type.SmithTypeE.E7.IdNoKc
public import CFSG.GF2Type.SmithTypeE.E7.IdGramPhi
public import CFSG.GF2Type.SmithTypeE.E7.OuterSwap

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E7

open Subgroup CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14 QuadraticMap
open CFSG.LargeExtraspecial.S14.SMK (Inputs10)
open CFSG.GF2Type.SmithTypeE.DMod
open CFSG.SmithD6

variable {G : Type} [Group G] [Finite G] {S : Setting G}

section Cert


theorem exists_model_equiv_of_setting [IsSimpleGroup G] (I : Inputs10)
    (hAS : AschbacherSmithWideInput) (hTI : WeaklyClosedTITransitive.{0}) (hw : S.width = 16)
    (ψ₀ : S.Mbar ≃* TD6) :
    ∃ (φ : S.Qt ≃ₗ[ZMod 2] (Fin 32 → ZMod 2)) (ψ : S.Mbar ≃* TD6),
      ∀ m : S.M, Phi S φ m = rhoMod (ψ (rhoM S m)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO : Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6) := ⟨ψ₀.trans omegaTD6.symm⟩
  obtain ⟨g, haQ, hne⟩ := exists_conj_mem_QG hAS hw hO
  have hno := noA2_of_insp5 I hw hO haQ hne
  have hirr := irreducible I.hDW hw hO haQ hne
  have hC := cons311_of hTI (by omega) haQ hne hno hirr
  obtain ⟨L, hL⟩ : ∃ L : Subgroup S.Mbar, L = (S.Lbar g).subgroupOf S.Mbar := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X : Subgroup TD6, X = L.map ψ₀.toMonoidHom := ⟨_, rfl⟩
  have hLel : CFSG.IsElementaryAbelian 2 L := by
    haveI := S.isElementaryAbelian_Lbar haQ
    rw [hL]
    exact CFSG.IsElementaryAbelian.subgroupOf (S.Lbar_le_Mbar g)
  have hXel : CFSG.IsElementaryAbelian 2 X := by
    haveI := hLel
    rw [hX]
    exact CFSG.IsElementaryAbelian.map _
  have hXcard : Nat.card X = 2 ^ 15 := by
    have h1 : Nat.card ↥L = Nat.card ↥(S.Lbar g) := by
      rw [hL]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (S.Lbar_le_Mbar g)).toEquiv
    rw [hX, Subgroup.card_map_of_injective ψ₀.injective, h1, hC.card_Lbar, hw]
  obtain ⟨Ph, hLP0⟩ := (S.isPGroup_Lbar_subgroupOf haQ).exists_le_sylow
  have hPN0 := S.le_normalizer_Lbar_of_isPGroup (by omega) haQ hne hno Ph.isPGroup' hLP0
  have hLP : L ≤ Ph := by
    rw [hL]
    exact hLP0
  have hPN1 : (Ph : Subgroup S.Mbar) ≤ Subgroup.normalizer (L : Set S.Mbar) := by
    rw [hL]
    exact hPN0
  let PS : Sylow 2 TD6 :=
    { toSubgroup := (Ph : Subgroup S.Mbar).map ψ₀.toMonoidHom
      isPGroup' := Ph.isPGroup'.map _
      is_maximal' := fun {Q} hQ hPQ =>
        isMax_map ψ₀ (fun Q hPQ hQ => Ph.is_maximal' hQ hPQ) Q hPQ hQ }
  have hXP : X ≤ (PS : Subgroup TD6) := by
    rw [hX]
    exact Subgroup.map_mono hLP
  have hPN : (PS : Subgroup TD6) ≤ Subgroup.normalizer (X : Set TD6) := by
    rw [hX]
    show (Ph : Subgroup S.Mbar).map ψ₀.toMonoidHom ≤ _
    have h := Subgroup.map_mono (f := ψ₀.toMonoidHom) hPN1
    rw [Subgroup.map_normalizer_eq_of_bijective L ψ₀.bijective] at h
    exact h
  obtain ⟨c, hc⟩ := elemAb_sylow_classification X hXel hXcard PS hXP hPN
  have hcomp : ∀ d : TD6, L.map (ψ₀.trans (MulAut.conj d)).toMonoidHom =
      X.map (MulAut.conj d).toMonoidHom := fun d => by
    rw [hX, Subgroup.map_map]
    rfl
  have hψ : ∃ ψ : S.Mbar ≃* TD6,
      ((S.Lbar g).subgroupOf S.Mbar).map ψ.toMonoidHom = K0 := by
    rcases hc with h | h | h
    · exact ⟨ψ₀.trans (MulAut.conj c), by rw [← hL, hcomp, h]⟩
    · refine ⟨(ψ₀.trans (MulAut.conj c)).trans gammaSwap, ?_⟩
      rw [← hL]
      have e : L.map ((ψ₀.trans (MulAut.conj c)).trans gammaSwap).toMonoidHom =
          (L.map (ψ₀.trans (MulAut.conj c)).toMonoidHom).map gammaSwap.toMonoidHom := by
        rw [Subgroup.map_map]
        rfl
      rw [e, hcomp, h, gammaSwap_UFix_Wp]
    · exfalso
      have h1 : X = (UFix Cc).map (MulAut.conj c⁻¹).toMonoidHom := by
        have e := map_conj_mul_gen X c⁻¹ c
        rw [inv_mul_cancel, map_conj_one, h] at e
        exact e
      exact not_conj_Kc I hTI hw ψ₀ haQ hne c⁻¹ (by rw [← hL, ← hX]; exact h1)
  obtain ⟨ψ, hψK⟩ := hψ
  obtain ⟨φ, hφ⟩ := exists_isModelPhi I hw ψ hψK haQ hne
  exact ⟨φ, ψ, hφ⟩

theorem clauses1235 [IsSimpleGroup G] (hTI : WeaklyClosedTITransitive.{0}) (I : Inputs10)
    (hAS : AschbacherSmithWideInput) (S : Setting G) (hw : S.width = 16)
    (hO : Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6)) :
    ∃ φ : S.Qt ≃ₗ[ZMod 2] (Fin 32 → ZMod 2), SmithE7Clauses1235 S φ := by
  obtain ⟨e⟩ := hO
  obtain ⟨φ, ψ, hΦ⟩ := exists_model_equiv_of_setting I hAS hTI hw (e.trans omegaTD6)
  exact ⟨φ, clauses1235_of_equiv I hAS hw ⟨e⟩ hΦ⟩

end Cert

end CFSG.GF2Type.SmithTypeE.E7
