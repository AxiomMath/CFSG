module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3312R
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3319A

public section
namespace CFSG.Quasithin.H13.L3319

open CFSG.Open (pCoreOf quasithinOmegaOneCenter)
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open Matrix
open scoped IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L D : Subgroup G}

theorem le_normalizer_of_hom_F4 (h : Hyp331 G T M L D) (h12 : Step3_3_12R_F4) {Y : Subgroup G}
    (hYL : Y ≤ L) (hY : ⁅Y, Y⁆ = Y) (hTY : T ≤ Subgroup.normalizer (Y : Set G))
    (hYZ : Y ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    {ψ : ↥Y →* SpecialLinearGroup (Fin 3) (ZMod 2)} (hψs : Function.Surjective ψ)
    (hψk : ψ.ker = CFSG.pCore 2 ↥Y) :
    Y ∈ lFamilyOf L T ∧ D ≤ Subgroup.normalizer (Y : Set G) := by
  have : IsSimpleGroup (SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    CFSG.QuasithinUnique.Vol2Native.A312L.sl_isSimple_of_card_two (Nat.card_zmod 2) le_rfl
  have hk : IsPGroup 2 ψ.ker := by
    rw [hψk]
    exact CFSG.pCore_isPGroup
  have hmem : Y ∈ lFamilyOf L T :=
    L3316.mem_lFamilyOf_of_hom h.sylow h.toSetup331.pCoreOf_ne_bot hYL hY hTY ψ hψs hk
  have ht : L3312.Type3312R (↥Y ⧸ CFSG.pCore 2 ↥Y) :=
    Or.inr (Or.inl (L3318.isPSL_of_hom le_rfl hψs hψk))
  refine ⟨hmem, ?_⟩
  obtain ⟨-, -, -, -, hDN | ⟨hpsl, -⟩⟩ := h12 G T M L D Y h hmem (pCoreOf_ne_bot h hYZ) ht
  · exact hDN
  · exact (L3318.not_isPSL_two_two le_rfl (by norm_num) hψs hψk hpsl).elim

theorem false_of_offender_F4
    (h : Hyp331 G T M L D) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (h12 : Step3_3_12R_F4)
    [IsMulCommutative ↥(vPlus L T)] {Y : Subgroup G} (hYL : Y ≤ L) (hY : ⁅Y, Y⁆ = Y)
    (hTY : T ≤ Subgroup.normalizer (Y : Set G))
    (hYZ : Y ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    {ψ : ↥Y →* SpecialLinearGroup (Fin 3) (ZMod 2)} (hψs : Function.Surjective ψ)
    (hψk : ψ.ker = CFSG.pCore 2 ↥Y)
    (hoff : ∀ B : Subgroup (MulAut ↥(vPlus L T)),
      IsFFStarOffender (autOn (L ⊔ T) (vPlus L T)) B →
        B ≤ autOn (pCoreOf 2 (Y ⊔ T)) (vPlus L T) → False) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hDY⟩ := le_normalizer_of_hom_F4 h h12 hYL hY hTY hYZ hψs hψk
  have hred := Hyp331.vPlus_reduced h.toSetup331
  set S := pCoreOf 2 (Y ⊔ T) with hS
  have hYTLT : Y ⊔ T ≤ L ⊔ T := sup_le_sup_right hYL T
  have hSLT : S ≤ L ⊔ T := (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hYTLT
  have hsylLT : IsSylowTwoOf T (L ⊔ T) := h.toSetup331.isSylowTwoOf
  have hRT : pCoreOf 2 (L ⊔ T) ≤ T := EscapingLocal.pCoreOf_le_of_isSylowTwoOf hsylLT
  have hRS : pCoreOf 2 (L ⊔ T) ≤ S := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (hRT.trans le_sup_right) (hYTLT.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  have hVS : vPlus L T ≤ S := (hred.1.trans inf_le_left).trans hRS
  exact false_of_thompsonJ_le h h38 h39 hYL hDY
    (thompsonJ_le_of_offender h hSLT hVS hoff)

end CFSG.Quasithin.H13.L3319
