module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoG2Ident
public import CFSG.LocalAnalysis.UniquenessCase.UC22S218Borel
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.GNQuotient
import CFSG.LocalAnalysis.UniquenessCase.UC22S218G2
import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem exists_pow_conj_mul_inv_mem_of_fieldBorel {G Y : Type} [Group G] [Group Y] [Finite Y]
    {n E : ℕ} (hY : CFSG.LocalAnalysis.UniquenessCase.UC22.FieldBorel Y n E)
    {S Ls : Subgroup G} (hSL : S ≤ Subgroup.normalizer (Ls : Set G)) (e : ↥Ls ≃* Y)
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf ((S ⊓ Ls).subgroupOf Ls) ⊤) :
    ∀ s ∈ S, ∃ j : ℕ, ∀ x ∈ Ls ⊓ Subgroup.normalizer ((S ⊓ Ls : Subgroup G) : Set G),
      s * x * s⁻¹ * (x ^ j)⁻¹ ∈ S ⊓ Ls := by
  classical
  haveI : Finite ↥Ls := Finite.of_equiv _ e.symm.toEquiv
  have hL : CFSG.LocalAnalysis.UniquenessCase.UC22.FieldBorel ↥Ls n E := hY.of_mulEquiv e.symm
  obtain ⟨H, F, D⟩ := hL.exists_of_sylow hU
  intro s hs
  set α : MulAut ↥Ls := Ls.normalizerMonoidHom ⟨s, hSL hs⟩ with hαdef
  have hα : ((S ⊓ Ls).subgroupOf Ls).map α.toMonoidHom = (S ⊓ Ls).subgroupOf Ls := by
    have hsN : s ∈ Subgroup.normalizer ((S ⊓ Ls : Subgroup G) : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hs, hSL hs⟩
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have h := (Subgroup.mem_normalizer_iff.mp hsN (y : G)).1
        (Subgroup.mem_subgroupOf.mp hy)
      exact Subgroup.mem_subgroupOf.mpr (by
        simpa only [hαdef, MulEquiv.coe_toMonoidHom,
          Subgroup.normalizerMonoidHom_apply_apply_coe] using h)
    · intro hx
      have hsinvN := Subgroup.inv_mem _ hsN
      have hsinvL := Subgroup.inv_mem _ (hSL hs)
      have hmem := (Subgroup.mem_normalizer_iff.mp hsinvN (x : G)).1 hx
      have hmemL := (Subgroup.mem_normalizer_iff.mp hsinvL (x : G)).1 x.2
      refine ⟨⟨s⁻¹ * (x : G) * (s⁻¹)⁻¹, hmemL⟩, Subgroup.mem_subgroupOf.mpr hmem, ?_⟩
      apply Subtype.ext
      simpa only [hαdef, MulEquiv.coe_toMonoidHom,
        Subgroup.normalizerMonoidHom_apply_apply_coe] using
        (show s * (s⁻¹ * (x : G) * (s⁻¹)⁻¹) * s⁻¹ = (x : G) by group)
  obtain ⟨k, hk⟩ := D.pow_action hα
  refine ⟨k, fun x hx => ?_⟩
  have hcomap : (Subgroup.normalizer ((S ⊓ Ls : Subgroup G) : Set G)).comap Ls.subtype =
      Subgroup.normalizer (((S ⊓ Ls).subgroupOf Ls : Subgroup ↥Ls) : Set ↥Ls) :=
    Subgroup.comap_normalizer_eq_of_le_range (by simp)
  have hb : (⟨x, hx.1⟩ : ↥Ls) ∈
      Subgroup.normalizer (((S ⊓ Ls).subgroupOf Ls : Subgroup ↥Ls) : Set ↥Ls) := by
    rw [← hcomap]
    exact Subgroup.mem_comap.mpr hx.2
  have hmem : ((α ⟨x, hx.1⟩ * (⟨x, hx.1⟩ ^ k)⁻¹ : ↥Ls) : G) ∈ S ⊓ Ls :=
    Subgroup.mem_subgroupOf.mp (hk ⟨x, hx.1⟩ hb)
  simpa [hαdef, Subgroup.normalizerMonoidHom_apply_apply_coe] using hmem

theorem exists_pow_conj_mul_inv_mem_of_gn_component_G2
    {X : Type} [Group X] [Finite X] {T : Subgroup X} (hX : GNSetting X T)
    {Ls : Subgroup (X ⧸ gnC T)} (hL : IsComponentOf Ls ⊤)
    (hinv : gnImg T T ≤ Subgroup.normalizer (Ls : Set (X ⧸ gnC T)))
    (d : TauCeti.ValidLieTypeIndex) (Q : TauCeti.PrimePower) (hd : d.1 = .G2 Q) (hQ : Q.p = 2)
    (hLd : Nonempty ((↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie d).Group)) :
    ∀ s ∈ gnImg T T, ∃ j : ℕ,
      ∀ x ∈ Ls ⊓ Subgroup.normalizer ((gnImg T T ⊓ Ls : Subgroup (X ⧸ gnC T)) : Set (X ⧸ gnC T)),
        s * x * s⁻¹ * (x ^ j)⁻¹ ∈ gnImg T T ⊓ Ls := by
  classical
  obtain ⟨hf, ⟨c⟩⟩ := exists_mulEquiv_cayleyGroup_of_gn_component_G2 hX hL d Q hd hQ hLd
  let K := GaloisField 2 Q.exponent
  have hK : Nat.card K = 2 ^ Q.exponent := GaloisField.card 2 Q.exponent (by omega)
  obtain ⟨c'⟩ := CFSG.Quasithin.B42G2Id.nonempty_cayleyGroup_mulEquiv_adjointQuotient hK hf
  have hZA : Subgroup.center ↥(CFSG.Blueprint.Chevalley.adjointGroup
      CFSG.Blueprint.Chevalley.Tag.G2 K) = ⊥ :=
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  let eC := (QuotientGroup.quotientMulEquivOfEq hZA).trans QuotientGroup.quotientBot
  have hYB : CFSG.LocalAnalysis.UniquenessCase.UC22.FieldBorel
      ↥(CFSG.Blueprint.Chevalley.adjointGroup CFSG.Blueprint.Chevalley.Tag.G2 K)
      Q.exponent (2 ^ Q.exponent - 1) :=
    ⟨_, _, _, CFSG.LocalAnalysis.UniquenessCase.UC22.uc22s218_g2_fieldBorelData_model hf hK⟩
  haveI : Finite ↥(CFSG.Blueprint.Chevalley.adjointGroup
      CFSG.Blueprint.Chevalley.Tag.G2 K) :=
    Finite.of_equiv _ (c.trans (c'.trans eC)).toEquiv
  have hS := CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.GNQuotient.isSylowTwoOf_gnImg_inf
    hX.sylow hL.2.1
  have hU : CFSG.QuasithinUnique.IsSylowTwoOf ((gnImg T T ⊓ Ls).subgroupOf Ls) ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · exact hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
    · rw [show (((gnImg T T ⊓ Ls).subgroupOf Ls).subgroupOf (⊤ : Subgroup ↥Ls)).index =
          ((gnImg T T ⊓ Ls).subgroupOf Ls).index from Subgroup.relIndex_top_right _]
      exact hS.2.2
  exact exists_pow_conj_mul_inv_mem_of_fieldBorel hYB hinv (c.trans (c'.trans eC)) hU

end CFSG.LocalAnalysis.RankThreeUC.S15

end
