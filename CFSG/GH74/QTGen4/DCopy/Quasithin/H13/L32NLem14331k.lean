module

public import CFSG.Quasithin.H13.L32NLem14331k
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14331g
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem1434

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

namespace L14328

open L14331

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V V₂ : Subgroup G} [IsMulCommutative ↥V]

namespace Ctx_F4
open Ctx
open CFSG.Quasithin.H13.L14328.Ctx_F4

variable {g z b l : G} (C : Ctx_F4 G T L V V₂ g z b l) (D : HatModelU (fsuU T V)) {e : G}
include C

theorem caseI_isSolvable_K_F4 (X : CaseI_F4 T L V g D e) :
    Group.IsSolvable ↥(kA T V (l⁻¹ * e * l)) := by
  obtain ⟨φ, hφ2, -⟩ := C.caseI_exists_phi_F4 D X
  have hKH := C.caseI_K_H_F4 D X
  have hN := L14332.l32nH_le_normalizer_fsuU T V
  set f : ↥(kA T V (l⁻¹ * e * l)) →* Equiv.Perm (Fin 3) :=
    (MonoidHom.fst _ _).comp (φ.toMonoidHom.comp ((L14332.imgHom D).comp
      (Subgroup.inclusion hKH))) with hf
  have hker : IsPGroup 2 ↥f.ker := by
    have hodd : ∀ x ∈ f.ker, Odd (orderOf x) → x = 1 := by
      intro x hx hxo
      have h1 : (φ (L14332.imgHom D ⟨x, hKH x.2⟩)).1 = 1 := hx
      have h2 := hφ2 _ x.2 (hKH x.2)
      have h3 : φ (L14332.imgHom D ⟨x, hKH x.2⟩) = 1 := Prod.ext h1 h2
      have h4 := congrArg Subtype.val (φ.injective (h3.trans φ.map_one.symm))
      rw [L14332.imgHom_apply] at h4
      have hxC := (L14332.rho_eq_one_iff_mem (D := D) (hKH x.2) (hN (hKH x.2))).mp h4
      exact Subtype.ext (C.eq_one_of_mem_cHat_F4 X.hQ (C.caseI_K_Z_F4 D X) x.2 hxC
        (by rwa [Subgroup.orderOf_coe]))
    intro x
    obtain ⟨n, hn⟩ := exists_two_pow_of_odd hodd x.2
    exact ⟨n, Subtype.ext (by simpa using hn)⟩
  have : Group.IsNilpotent ↥f.ker := hker.isNilpotent
  have : Group.IsSolvable (Equiv.Perm (Fin 3)) := Equiv.Perm.isSolvable (by simp)
  exact Group.isSolvable_of_ker_le_range f.ker.subtype f (by rw [Subgroup.range_subtype])

theorem caseI_K0_simple_F4 (h1434 : Lemma1434One_F4) (X : CaseI_F4 T L V g D e)
    {K₀ : Subgroup ↥(iKP T L V l e)} (hK₀ : K₀ ∈ cComp (⊤ : Subgroup ↥(iKP T L V l e)))
    (hZ : ⁅quasithinOmegaOneCenter T, K₀.map (iKP T L V l e).subtype⁆ ≠ ⊥) :
    IsSimpleGroup (↥K₀ ⧸ CFSG.Open.pCore 2 ↥K₀) ∧
      (Nat.card (↥K₀ ⧸ CFSG.Open.pCore 2 ↥K₀) = 60 ∨
        Nat.card (↥K₀ ⧸ CFSG.Open.pCore 2 ↥K₀) = 168) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsylI : IsSylowTwoOf T (iKP T L V l e) :=
    A5.isSylowTwoOf_of_le C.S.hH.sylow (le_sup_right.trans le_sup_left)
  have hL₀c := map_subtype_mem_cComp hK₀
  have hloc := isLocal_of_mem_cComp_of_sylow hsylI (C.caseI_pCoreOf_ne_bot_F4 D X) hL₀c
  have hf := Vol2.Ch11.SecS.isFaithfulLocal_of_omegaOneCenter C.hyp.fsu.qtke C.S.hH.sylow hloc hZ
  set K₀G := K₀.map (iKP T L V l e).subtype with hK₀G
  set ι : ↥K₀ ≃* ↥K₀G := K₀.equivMapOfInjective _ (iKP T L V l e).subtype_injective with hι
  have hιp : (CFSG.Open.pCore 2 ↥K₀).map ι.toMonoidHom = CFSG.Open.pCore 2 ↥K₀G :=
    CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 ι
  set q : ↥K₀ ⧸ CFSG.Open.pCore 2 ↥K₀ ≃* ↥K₀G ⧸ CFSG.Open.pCore 2 ↥K₀G :=
    QuotientGroup.congr _ _ ι hιp with hq
  set r : ↥K₀G ⧸ CFSG.pCore 2 ↥K₀G ≃* ↥K₀G ⧸ CFSG.Open.pCore 2 ↥K₀G :=
    QuotientGroup.quotientMulEquivOfEq (CFSG.Quasithin.BlueprintB2.pCore_eq_open_pCore 2 _)
    with hr
  rcases h1434 G T L C.hyp.hyp K₀G hf with h5 | h3
  · obtain ⟨e5⟩ := h5
    have : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
    have e' := (q.trans r.symm).trans e5
    refine ⟨(MulEquiv.isSimpleGroup_congr e').mpr this, Or.inl ?_⟩
    rw [Nat.card_congr e'.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    rfl
  · obtain ⟨eL⟩ := nonempty_equiv_SL32_of_lieModel h3
    have e' := (q.trans r.symm).trans eL
    refine ⟨(MulEquiv.isSimpleGroup_congr (q.trans r.symm)).mpr
      (isSimpleGroup_of_lieModel_psl32 h3), Or.inr ?_⟩
    rw [Nat.card_congr e'.toEquiv, Matrix.card_SL_field]
    simp [Fin.prod_univ_three]

end Ctx_F4

end L14328

end CFSG.Quasithin.H13
