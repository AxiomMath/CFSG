module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H2017LFacts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM7Lin
public import CFSG.RankThree.PartTwo.Census.Classical.Bridges

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 SFM7Lin

abbrev GF8 : Type := GaloisField 2 3

theorem card_GF8 : Nat.card GF8 = 8 := by
  rw [GaloisField.card 2 3 (by norm_num)]
  norm_num

theorem statedScalars_subgroupOf_statedSL4_eq_bot {K : Type} [Field K] [Finite K] (hK : Nat.card K = 8) :
    (StatedScalars (Fin 4) K).subgroupOf (StatedSL 4 K) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 hg
  have hdet := StatedAPI.mem_statedSL_iff.1
    (hc ▸ (g : StatedSL 4 K).2 : Matrix.GeneralLinearGroup.scalar (Fin 4) c ∈ StatedSL 4 K)
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_const] at hdet
  haveI := Fintype.ofFinite K
  have h7 : (c : K) ^ (Fintype.card K - 1) = 1 :=
    FiniteField.pow_card_sub_one_eq_one _ c.ne_zero
  have hcard : Fintype.card K - 1 = 7 := by
    rw [← Nat.card_eq_fintype_card, hK]
  rw [hcard] at h7
  have hgcd : (c : K) ^ (Nat.gcd 4 7) = 1 := pow_gcd_eq_one.2 ⟨hdet, h7⟩
  have hc1 : (c : K) = 1 := by simpa using hgcd
  have hc' : c = 1 := Units.ext hc1
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [Subgroup.coe_one, ← hc, hc', map_one]

noncomputable def statedProjSL4Equiv {K : Type} [Field K] [Finite K] (hK : Nat.card K = 8) :
    StatedProj (StatedSL 4 K) ≃* StatedSL 4 K :=
  (QuotientGroup.quotientMulEquivOfEq (statedScalars_subgroupOf_statedSL4_eq_bot hK)).trans
    QuotientGroup.quotientBot

theorem exists_injective_GL_of_catalog {S : Type} [Group S]
    (h : catalogIs S (onLie fun d => d = TauCeti.LieTypeIndex.A 3 gfEightPP)) :
    ∃ φ : S →* GL (Fin 4) GF8, Function.Injective φ := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic p k => exact hi.elim
  | alternating n k => exact hi.elim
  | sporadic s => exact hi.elim
  | lie j =>
    obtain ⟨d, hv⟩ := j
    have hd : d = TauCeti.LieTypeIndex.A 3 gfEightPP := hi
    subst hd
    haveI : Fact (Nat.Prime gfEightPP.p) := ⟨Nat.prime_two⟩
    let e2 : S ≃* CFSG.PGLModel.projSL (3 + 1) GF8 :=
      e.trans (CFSG.RankThree.PartTwo.Census.typeAGroupEquivProjSL 3 gfEightPP hv)
    let e3 : S ≃* StatedProj (StatedSL (3 + 1) GF8) :=
      e2.trans (CFSG.PGLModel.projSLEquivStatedProj (3 + 1) GF8)
    let e4 : S ≃* StatedSL 4 GF8 := e3.trans (statedProjSL4Equiv card_GF8)
    refine ⟨(StatedSL 4 GF8).subtype.comp e4.toMonoidHom, ?_⟩
    exact Subtype.val_injective.comp e4.injective

theorem I2017LieNoA7L48_holds :
    ∀ (S : Type) [Group S] [Finite S],
      catalogIs S (onLie fun d => d = TauCeti.LieTypeIndex.A 3 gfEightPP) →
        ∀ T : Subgroup S, IsPGroup 2 T → T ≠ ⊥ → ∀ H : Subgroup S, H ≤ Subgroup.normalizer (T : Set S) →
          ¬ Nonempty (↥H ≃* ↥(alternatingGroup (Fin 7))) := by
  intro S _ _ hcat T hT hT1 H hH hiso
  obtain ⟨eH⟩ := hiso
  obtain ⟨φ, hφ⟩ := exists_injective_GL_of_catalog hcat
  let ψ : alternatingGroup (Fin 7) →* S :=
    H.subtype.comp (eH.symm : alternatingGroup (Fin 7) ≃* H).toMonoidHom
  have hψ : Function.Injective ψ := Subtype.val_injective.comp eH.symm.injective
  have hn : ∀ a : alternatingGroup (Fin 7), ∀ t ∈ T, ψ a * t * (ψ a)⁻¹ ∈ T := by
    intro a t ht
    have hmem : ψ a ∈ Subgroup.normalizer (T : Set S) := hH (eH.symm a).2
    exact (Subgroup.mem_normalizer_iff.1 hmem t).1 ht
  exact core card_GF8 φ hφ ψ hψ T hT hT1 hn

end CFSG.LocalAnalysis.GLTheoremA
