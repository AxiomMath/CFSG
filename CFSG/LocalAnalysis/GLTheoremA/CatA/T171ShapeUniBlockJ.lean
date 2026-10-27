module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeUniBlockComm
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamInLinTransJ
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154UniPsu
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154UniMark
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeForm
public import CFSG.RankThree.Classical.SteinbergBJUnitaryTwoBlock
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeModel
public import CFSG.ClassicalGroups.Unitary.Simple
public import CFSG.RankThree.PartOne.KC.UnitaryPrimaryField
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniCore
public import CFSG.HardMathSupport.Dickson.Bal207.Glue
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.UnitaryInnerExport
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019UniBlocks

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA.S10
  CFSG.LieType.SemisimpleCentralizers.HeldLang CFSG.LocalAnalysis.GLTheoremA.K155X
  CFSG.ComponentClassification.Burgoyne.U CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.Classical
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCPrimary
open Polynomial
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup
  glaPComponent_map_fixSubgroup)
open scoped commutatorElement MatrixGroups

theorem isSimpleGroup_statedProj_statedSU_two {k : ℕ} {E : Type} [Field E] [Finite E]
    (hE : UnitaryFieldData 2 k E) (hk : 2 ≤ k) :
    IsSimpleGroup (LargeEvenProj (StatedSU 2 (2 ^ k) E)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP E 2 := hE.charP
  have hE2 : (2 : E) = 0 := CharP.cast_eq_zero E 2
  have hEcard : Nat.card E = (2 ^ k) ^ 2 := by
    calc Nat.card E = 2 ^ (2 * k) := hE.card
      _ = (2 ^ k) ^ 2 := by rw [Nat.mul_comm, pow_mul]
  have htriv : (StatedScalars (Fin 2) E).subgroupOf (StatedSU 2 (2 ^ k) E) = ⊥ :=
    CFSG.RankThree.PartOne.KFU.scalars_subgroupOf_eq_bot hEcard (by omega)
      (Nat.coprime_iff_gcd_eq_one.mp
        (Nat.coprime_two_left.mpr ((Nat.even_pow.mpr ⟨even_two, by omega⟩).add_one)))
  have hmap : (gramSU hE (idGram E 2)).map
      (Matrix.GeneralLinearGroup.toLin).toMonoidHom =
      sesqSpecialUnitaryGroup (idForm hE 2) := by
    ext g
    constructor
    · rintro ⟨M, hM, rfl⟩
      exact (toLin_mem_sesqSpecialUnitaryGroup_iff hE (idGram E 2) M).2 hM
    · intro hg
      refine ⟨(Matrix.GeneralLinearGroup.toLin).symm g, ?_, ?_⟩
      · exact (toLin_mem_sesqSpecialUnitaryGroup_iff hE (idGram E 2) _).1 (by
          rw [MulEquiv.apply_symm_apply]; exact hg)
      · exact (Matrix.GeneralLinearGroup.toLin).apply_symm_apply g
  have hV : Module.finrank E (Fin 2 → E) = 2 := by simp
  obtain ⟨⟨-, -, hsimp⟩, -⟩ :=
    CFSG.RankThree.Classical.unitary_two_block_quasisimple_structure hE (idForm hE 2)
      (idForm_isSymm hE 2) (idForm_separatingLeft hE 2) hV
  have hcenter : Subgroup.center (sesqSpecialUnitaryGroup (idForm hE 2)) = ⊥ := by
    ext g
    rw [mem_center_sesqSpecialUnitaryGroup_iff hE (idForm_isSymm hE 2)
      (idForm_separatingLeft hE 2) hV g]
    constructor
    · rintro ⟨c, hc2, hgc⟩
      have hc1 : c = 1 := by
        have hfac : (c - 1) ^ 2 = 0 := by linear_combination hc2 + (1 - c) * hE2
        exact sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 hfac)
      rw [Subgroup.mem_bot]
      apply Subtype.ext
      apply Units.ext
      rw [hgc, hc1, one_smul]
      rfl
    · rintro rfl
      refine ⟨1, one_pow 2, ?_⟩
      ext v
      simp
  haveI : IsSimpleGroup (sesqSpecialUnitaryGroup (idForm hE 2)) := by
    have h4 : 4 ≤ 2 ^ k := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    haveI : IsSimpleGroup
        (sesqSpecialUnitaryGroup (idForm hE 2) ⧸
          Subgroup.center (sesqSpecialUnitaryGroup (idForm hE 2))) := (hsimp h4).2.1
    exact (MulEquiv.isSimpleGroup_congr
      ((QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot)).mp
      inferInstance
  let e₁ : ↥(gramSU hE (idGram E 2)) ≃* sesqSpecialUnitaryGroup (idForm hE 2) :=
    ((Matrix.GeneralLinearGroup.toLin).subgroupMap (gramSU hE (idGram E 2))).trans
      (MulEquiv.subgroupCongr hmap)
  have e₂ : LargeEvenProj (StatedSU 2 (2 ^ k) E) ≃*
      sesqSpecialUnitaryGroup (idForm hE 2) :=
    ((QuotientGroup.quotientMulEquivOfEq htriv).trans QuotientGroup.quotientBot).trans
      ((MulEquiv.subgroupCongr (statedSU_eq_gramSU hE)).trans e₁)
  exact (MulEquiv.isSimpleGroup_congr e₂).mpr inferInstance

theorem uniJ_equiv_comm_core
    {p : ℕ} (hp : p.Prime) {Ω : Type} [Group Ω] [Finite Ω]
    {S : Subgroup Ω} {y : Ω} {J : Subgroup Ω} {X : Subgroup Ω}
    (hJ : GLAPComponent p X J) (hJS : J ≤ S)
    (hJy : y ∈ Subgroup.normalizer (J : Set Ω))
    {n d : ℕ} {K : Type} [Field K]
    (θ : ↥S ⧸ Subgroup.center ↥S ≃* LargeEvenProj (unitarySU 2 n K d))
    (ψ : MulAut (LargeEvenProj (unitarySU 2 n K d)))
    (hindy : LargeEvenInduces θ (conjRel y) ψ)
    {m : ℕ} {E : Type} [Field E] [Finite E]
    (Hm : Subgroup (GL (Fin m) E))
    (ιm : ↥Hm →* ↥(unitarySU 2 n K d))
    (B : GL (Fin d) K) (B₁ : GL (Fin m) E)
    (hsimple : IsSimpleGroup (LargeEvenProj Hm))
    (hmemB : ∀ P : ↥Hm, B * (ιm P : GL (Fin d) K) * B⁻¹ ∈ unitarySU 2 n K d)
    (hψ : ∀ P : ↥Hm, ψ (LargeEvenProjMk (unitarySU 2 n K d) (ιm P)) =
      LargeEvenProjMk (unitarySU 2 n K d) ⟨B * (ιm P : GL (Fin d) K) * B⁻¹, hmemB P⟩)
    (hconj_mem : ∀ P : ↥Hm, B₁ * (P : GL (Fin m) E) * B₁⁻¹ ∈ Hm)
    (hconj : ∀ P : ↥Hm,
      ((ιm ⟨B₁ * (P : GL (Fin m) E) * B₁⁻¹, hconj_mem P⟩ :
        ↥(unitarySU 2 n K d)) : GL (Fin d) K) = B * (ιm P : GL (Fin d) K) * B⁻¹)
    (hJPeq : (J.subgroupOf S).map
        (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥S))) =
      ιm.range.map (LargeEvenProjMk (unitarySU 2 n K d)))
    (hscal : ∀ P : ↥Hm, (∃ z : Kˣ, (ιm P : GL (Fin d) K) =
        Matrix.GeneralLinearGroup.scalar (Fin d) z) → ∃ w : Eˣ,
          (P : GL (Fin m) E) = Matrix.GeneralLinearGroup.scalar (Fin m) w) :
    ∃ e₀ : PSimple p J ≃* LargeEvenProj Hm,
      ∀ P : ↥Hm, MulAut.congr e₀ (MI.indAut p J y hJy) (LargeEvenProjMk Hm P) =
        LargeEvenProjMk Hm
          ⟨B₁ * (P : GL (Fin m) E) * B₁⁻¹, hconj_mem P⟩ := by
  classical
  have hJS' : J ≤ S := hJS
  let ρS : ↥S →* LargeEvenProj (unitarySU 2 n K d) :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥S))
  let ρJ : ↥J →* LargeEvenProj (unitarySU 2 n K d) := ρS.comp (Subgroup.inclusion hJS)
  let Ψ : ↥Hm →* LargeEvenProj (unitarySU 2 n K d) :=
    (LargeEvenProjMk (unitarySU 2 n K d)).comp ιm
  let q₁ : ↥Hm →* LargeEvenProj Hm := LargeEvenProjMk Hm
  have hperfJ : commutator ↥J = ⊤ := by
    have h1 := Subgroup.map_subtype_commutator J
    rw [CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53Ns.glaPComponent_perfect hJ] at h1
    have h2 : (⊤ : Subgroup ↥J).map J.subtype = J := by
      rw [Subgroup.map_top, Subgroup.range_subtype]
    exact Subgroup.map_injective J.subtype_injective (h1.trans h2.symm)
  have hρJmem : ∀ l : ↥J, ρJ l ∈ (J.subgroupOf S).map ρS := fun l =>
    Subgroup.mem_map.mpr ⟨⟨l.1, hJS l.2⟩, Subgroup.mem_subgroupOf.mpr l.2, rfl⟩
  have hmemJP : ∀ z ∈ (J.subgroupOf S).map ρS, ∃ l : ↥J, ρJ l = z := by
    intro z hz
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hz
    exact ⟨⟨s.1, Subgroup.mem_subgroupOf.mp hs⟩, rfl⟩
  have hρΨ : ∀ l : ↥J, ∃ m : ↥Hm, Ψ m = ρJ l := by
    intro l
    have h1 : ρJ l ∈ ιm.range.map (LargeEvenProjMk (unitarySU 2 n K d)) :=
      hJPeq ▸ hρJmem l
    obtain ⟨x, hx, hxq⟩ := Subgroup.mem_map.1 h1
    obtain ⟨P, rfl⟩ := hx
    refine ⟨P, ?_⟩
    change (LargeEvenProjMk (unitarySU 2 n K d)) (ιm P) = ρJ l
    exact hxq
  have hΨρ : ∀ m : ↥Hm, ∃ l : ↥J, ρJ l = Ψ m := by
    intro m
    have h1 : Ψ m ∈ (J.subgroupOf S).map ρS := by
      rw [hJPeq]
      exact Subgroup.mem_map.2 ⟨ιm m, MonoidHom.mem_range.mpr ⟨m, rfl⟩, rfl⟩
    exact hmemJP _ h1
  have hker₁ : ∀ P : ↥Hm, Ψ P = 1 → q₁ P = 1 := by
    intro P hP
    obtain ⟨c, hc⟩ := (l154_projMk_eq_iff (unitarySU 2 n K d) (ιm P) 1).1 hP
    simp only [Subgroup.coe_one, mul_one] at hc
    have hιscal : (ιm P : GL (Fin d) K) =
        Matrix.GeneralLinearGroup.scalar (Fin d) c⁻¹ := by
      calc (ιm P : GL (Fin d) K) = ((ιm P : GL (Fin d) K))⁻¹⁻¹ := (inv_inv _).symm
        _ = (Matrix.GeneralLinearGroup.scalar (Fin d) c)⁻¹ := by rw [← hc]
        _ = Matrix.GeneralLinearGroup.scalar (Fin d) c⁻¹ := by rw [← map_inv]
    obtain ⟨w, hw⟩ := hscal P ⟨c⁻¹, hιscal⟩
    refine (l154_projMk_eq_iff Hm P 1).2 ⟨w⁻¹, ?_⟩
    rw [Subgroup.coe_one, mul_one, hw, ← map_inv]
  obtain ⟨Θ, hΘ⟩ := l154_exists_hom_lift ρJ Ψ q₁ hρΨ hker₁
  have hΘsurj : Function.Surjective Θ := by
    intro r
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective r
    obtain ⟨l, hl⟩ := hΨρ m
    exact ⟨l, hΘ l m hl.symm⟩
  have hρJker : ρJ.ker ≤ Subgroup.center ↥J := by
    intro l hl
    rw [MonoidHom.mem_ker] at hl
    have h1 : QuotientGroup.mk' (Subgroup.center ↥S) ⟨l.1, hJS l.2⟩ = 1 := by
      apply θ.injective
      rw [map_one]
      exact hl
    have h2 : (⟨l.1, hJS l.2⟩ : ↥S) ∈ Subgroup.center ↥S := (QuotientGroup.eq_one_iff _).1 h1
    refine Subgroup.mem_center_iff.2 fun j => Subtype.ext ?_
    have h3 := Subgroup.mem_center_iff.1 h2 ⟨j.1, hJS j.2⟩
    exact congrArg (fun z : ↥S => (z : Ω)) h3
  have hcen₁ : ∀ P : ↥Hm, q₁ P = 1 → ∃ w : Eˣ,
      (P : GL (Fin m) E) = Matrix.GeneralLinearGroup.scalar (Fin m) w := by
    intro P hP
    obtain ⟨c, hc⟩ := (l154_projMk_eq_iff Hm P 1).1 hP
    simp only [Subgroup.coe_one, mul_one] at hc
    refine ⟨c⁻¹, ?_⟩
    calc (P : GL (Fin m) E) = ((P : GL (Fin m) E))⁻¹⁻¹ := (inv_inv _).symm
      _ = (Matrix.GeneralLinearGroup.scalar (Fin m) c)⁻¹ := by rw [← hc]
      _ = Matrix.GeneralLinearGroup.scalar (Fin m) c⁻¹ := by rw [← map_inv]
  have hΘker : Θ.ker ≤ Subgroup.center ↥J := by
    intro l hl
    rw [MonoidHom.mem_ker] at hl
    obtain ⟨P, hP⟩ := hρΨ l
    have hqm : q₁ P = 1 := by rw [← hΘ l P hP]; exact hl
    obtain ⟨w, hw⟩ := hcen₁ P hqm
    refine CFSG.HardMathSupport.Solomon.Coordinator.LieComp.mem_center_of_commutator_mem_center
      hperfJ fun j => ?_
    apply hρJker
    change ρJ ⁅l, j⁆ = 1
    rw [map_commutatorElement]
    obtain ⟨P', hP'⟩ := hρΨ j
    rw [← hP, ← hP', ← map_commutatorElement]
    have hce : ⁅P, P'⁆ = 1 := by
      apply commutatorElement_eq_one_iff_mul_comm.2
      apply Subtype.ext
      change (P : GL (Fin m) E) * (P' : GL (Fin m) E) =
        (P' : GL (Fin m) E) * (P : GL (Fin m) E)
      rw [hw]
      exact scalar_mul_comm w (P' : GL (Fin m) E)
    rw [hce, map_one]
  obtain ⟨e₀, he₀⟩ := l154_exists_pSimple_equiv hp hJ hsimple Θ hΘsurj hΘker
  refine ⟨e₀, fun P => ?_⟩
  obtain ⟨l, hl⟩ := hΨρ P
  have hyinv : y⁻¹ ∈ Subgroup.normalizer (J : Set Ω) := Subgroup.inv_mem _ hJy
  have hl'mem : y⁻¹ * (l : Ω) * y ∈ J := by
    have := (Subgroup.mem_normalizer_iff.1 hyinv (l : Ω)).1 l.2
    simpa using this
  let l' : ↥J := ⟨y⁻¹ * (l : Ω) * y, hl'mem⟩
  have hρl' : ρJ l' = ψ (ρJ l) := by
    have h := hindy ⟨l.1, hJS l.2⟩ ⟨l'.1, hJS l'.2⟩ (by
      show ((l'.1 : Ω)) = y⁻¹ * (l.1 : Ω) * y
      rfl)
    exact h.symm
  obtain ⟨Q', hQ'⟩ := hρΨ l'
  set X : ↥Hm := ⟨B₁ * (P : GL (Fin m) E) * B₁⁻¹, hconj_mem P⟩ with hX
  have e1 : q₁ P = e₀ (QuotientGroup.mk (QuotientGroup.mk l)) := by
    rw [he₀ l]
    exact (hΘ l P hl.symm).symm
  have e2 : q₁ Q' = e₀ (QuotientGroup.mk (QuotientGroup.mk l')) := by
    rw [he₀ l']
    exact (hΘ l' Q' hQ').symm
  have e3 : MI.indAut p J y hJy (QuotientGroup.mk (QuotientGroup.mk l)) =
      QuotientGroup.mk (QuotientGroup.mk l') :=
    MI.indAut_apply_mk hJy ⟨l, l', rfl, rfl, rfl⟩
  have hπeq : (LargeEvenProjMk (unitarySU 2 n K d)) (ιm Q') =
      (LargeEvenProjMk (unitarySU 2 n K d))
        ⟨B * (ιm P : GL (Fin d) K) * B⁻¹, hmemB P⟩ := by
    change Ψ Q' = (LargeEvenProjMk (unitarySU 2 n K d))
      ⟨B * (ιm P : GL (Fin d) K) * B⁻¹, hmemB P⟩
    rw [hQ', hρl', hl]
    exact hψ P
  have hπeqX : (LargeEvenProjMk (unitarySU 2 n K d)) (ιm Q') =
      (LargeEvenProjMk (unitarySU 2 n K d)) (ιm X) := by
    rw [hπeq]
    have hsub : (⟨B * (ιm P : GL (Fin d) K) * B⁻¹, hmemB P⟩ :
        ↥(unitarySU 2 n K d)) = ιm X := Subtype.ext (hconj P).symm
    rw [hsub]
  obtain ⟨c, hc⟩ :=
    (CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.projMk_eq_iff_uni (unitarySU 2 n K d)
      (ιm Q') (ιm X)).1 hπeqX
  have hscalprod : ∃ w : Eˣ, ((X⁻¹ * Q' : ↥Hm) : GL (Fin m) E) =
      Matrix.GeneralLinearGroup.scalar (Fin m) w := by
    refine hscal (X⁻¹ * Q') ⟨c⁻¹, ?_⟩
    have hXeq : (ιm X : GL (Fin d) K) =
        (ιm Q' : GL (Fin d) K) * Matrix.GeneralLinearGroup.scalar (Fin d) c := by
      calc (ιm X : GL (Fin d) K) =
          (ιm Q' : GL (Fin d) K) * ((ιm Q' : GL (Fin d) K)⁻¹ * (ιm X : GL (Fin d) K)) := by
            group
        _ = (ιm Q' : GL (Fin d) K) * Matrix.GeneralLinearGroup.scalar (Fin d) c := by
            rw [← hc]
    calc (ιm (X⁻¹ * Q') : GL (Fin d) K) =
          (ιm X : GL (Fin d) K)⁻¹ * (ιm Q' : GL (Fin d) K) := by
            rw [map_mul, map_inv]
            rfl
      _ = ((ιm Q' : GL (Fin d) K) * Matrix.GeneralLinearGroup.scalar (Fin d) c)⁻¹ *
            (ιm Q' : GL (Fin d) K) := by rw [hXeq]
      _ = (Matrix.GeneralLinearGroup.scalar (Fin d) c)⁻¹ *
            (ιm Q' : GL (Fin d) K)⁻¹ * (ιm Q' : GL (Fin d) K) := by rw [mul_inv_rev]
      _ = (Matrix.GeneralLinearGroup.scalar (Fin d) c)⁻¹ := by group
      _ = Matrix.GeneralLinearGroup.scalar (Fin d) c⁻¹ := by rw [← map_inv]
  obtain ⟨w, hw⟩ := hscalprod
  have hmemscal : Matrix.GeneralLinearGroup.scalar (Fin m) w ∈ Hm := by
    rw [← hw]
    exact (X⁻¹ * Q').2
  have hqscal : (LargeEvenProjMk Hm)
      ⟨Matrix.GeneralLinearGroup.scalar (Fin m) w, hmemscal⟩ = 1 := by
    refine (l154_projMk_eq_iff Hm _ 1).2 ⟨w⁻¹, ?_⟩
    rw [Subgroup.coe_one, mul_one, ← map_inv]
  have hQ'eq : Q' = X * ⟨Matrix.GeneralLinearGroup.scalar (Fin m) w, hmemscal⟩ := by
    apply Subtype.ext
    rw [Subgroup.coe_mul]
    have h := hw
    rw [Subgroup.coe_mul, Subgroup.coe_inv] at h
    calc (Q' : GL (Fin m) E) = (X : GL (Fin m) E) * ((X : GL (Fin m) E)⁻¹ *
          (Q' : GL (Fin m) E)) := by group
      _ = (X : GL (Fin m) E) * Matrix.GeneralLinearGroup.scalar (Fin m) w := by rw [h]
  have hqq : q₁ Q' = q₁ X := by
    calc q₁ Q' = q₁ (X * ⟨Matrix.GeneralLinearGroup.scalar (Fin m) w, hmemscal⟩) := by
          rw [hQ'eq]
      _ = q₁ X * q₁ ⟨Matrix.GeneralLinearGroup.scalar (Fin m) w, hmemscal⟩ := map_mul _ _ _
      _ = q₁ X := by rw [hqscal, mul_one]
  calc MulAut.congr e₀ (MI.indAut p J y hJy) (q₁ P) = q₁ Q' := by
        rw [e1, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
          MulEquiv.symm_apply_apply, e3, ← e2]
    _ = q₁ X := hqq


end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
