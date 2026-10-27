module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lSUSix
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lExcTwisted
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lSpFacts

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.OddStandard.SmallF3.HypA2 (TypU)
open scoped MatrixGroups

@[expose] def a2lTwistedE6ThreeSU6 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], LieModel X .twistedE6 0 3 1 →
    ∃ (T : Subgroup X) (z : X) (F : Type) (_ : Field F), Nat.card F = 9 ∧ orderOf z = 2 ∧
      CFSG.Assembly.IsComponentOf T (centralizer ({z} : Set X)) ∧
      ∃ (hz : z ∈ T) (e : T ≃* StatedSU 6 3 F),
        ((e ⟨z, hz⟩ : StatedSU 6 3 F) : GL (Fin 6) F) =
          Matrix.GeneralLinearGroup.scalar (Fin 6) (-1 : Fˣ)

section SU

variable {F : Type} [Field F]

theorem a2l_scalar_sq_su_six (hd : UnitaryFieldData 3 1 F) {c : Fˣ}
    (hc : Matrix.GeneralLinearGroup.scalar (Fin 6) c ∈ unitarySU 3 1 F 6) : c * c = 1 := by
  obtain ⟨hdet, huni⟩ := (mem_unitarySU_iff hd).1 hc
  have h6 : (c : F) ^ 6 = 1 := by
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal] at hdet
    simpa using hdet
  have h4 : (c : F) ^ 4 = 1 := by
    have h := congrFun (congrFun huni 0) 0
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_map
      (map_zero _), Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_apply_eq, Matrix.one_apply_eq, hd.bar_apply] at h
    calc (c : F) ^ 4 = (c : F) ^ 3 ^ 1 * c := by ring
      _ = 1 := h
  have h2 : (c : F) ^ 2 = 1 := by
    have := pow_gcd_eq_one.2 ⟨h6, h4⟩
    simpa using this
  exact Units.ext (by rw [Units.val_mul, Units.val_one, ← pow_two]; exact h2)

theorem a2l_typU_of_statedSU_six (hC : HypA2.ChevOddInChev2) (hF : Nat.card F = 9) {T : Type}
    [Group T] [Finite T] (hq : CFSG.IsQuasisimple T) (e : T ≃* StatedSU 6 3 F) : TypU T := by
  have hd : UnitaryFieldData 3 1 F := a2l_unitaryFieldData_three (by rw [hF]; norm_num)
  haveI := hd.finite
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK : Nat.card F = (3 ^ 1) ^ 2 := by rw [hF]; norm_num
  have hnq : ((6 : ℕ), 3 ^ 1) ≠ ((3 : ℕ), 2) := by decide
  have hperf : Group.IsPerfect (StatedSU 6 (3 ^ 1) F) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hK (by norm_num) hnq
  have hsimple : IsSimpleGroup (StatedProj (StatedSU 6 (3 ^ 1) F)) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F 3 1 hK 6 (by norm_num) hnq
  obtain ⟨-, hcen⟩ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU hperf hsimple
  let e' : T ≃* StatedSU 6 (3 ^ 1) F := e
  have hmap : (center T).map e'.toMonoidHom =
      (StatedScalars (Fin 6) F).subgroupOf (StatedSU 6 (3 ^ 1) F) :=
    (CFSG.LieType.Universal.Unitary.map_center_mulEquiv e').trans hcen
  have hLie : LieModel (T ⧸ center T) .PSU 6 3 1 :=
    GH74.lieModel_of_statedClassicalModel (by decide)
      ⟨⟨Nat.prime_three, le_rfl, by norm_num, hnq⟩, F, inferInstance, inferInstance, hK,
        ⟨QuotientGroup.congr _ _ e' hmap⟩⟩
  have hZ2 : IsPGroup 2 ↥(center T) := by
    intro g
    refine ⟨1, ?_⟩
    have hmem : e' (g : T) ∈ (center T).map e'.toMonoidHom := ⟨g, g.2, rfl⟩
    rw [hmap, Subgroup.mem_subgroupOf] at hmem
    obtain ⟨c, hc⟩ := hmem
    have hcc : c * c = 1 := a2l_scalar_sq_su_six hd (by rw [hc]; exact (e' (g : T)).2)
    rw [pow_one, pow_two]
    apply Subtype.ext
    apply e'.injective
    rw [Subgroup.coe_mul, map_mul, Subgroup.coe_one, map_one]
    apply Subtype.ext
    change ((e' (g : T) : GL (Fin 6) F) * (e' (g : T) : GL (Fin 6) F)) = 1
    rw [← hc, ← map_mul, hcc, map_one]
  have hI : ¬ GH74.GLS.InChev2 (T ⧸ center T) :=
    a2l_not_inChev2_of_card hC ⟨.PSU, 6, 1, hLie⟩ (by
      rw [GH74.card_of_lieModel_PSU (G := T ⧸ center T) (n := 6) (p := 3) (f := 1) (by norm_num)
        (by norm_num) hLie]
      decide)
  exact a2l_typU_of_chev3 hq hZ2 ⟨.PSU, 6, 1, hLie⟩ hI

end SU

theorem a2lTwistedE6Three_of_su6 (hC : HypA2.ChevOddInChev2) (h : a2lTwistedE6ThreeSU6) :
    a2lTwistedE6Three := by
  intro X _ _ hX
  obtain ⟨T, z, F, _, hF, hz2, hcomp, hzT, e, hez⟩ := h X hX
  have hq : CFSG.IsQuasisimple ↥T := (AssemblyBPredicates.isQuasisimple_iff_native _).1 hcomp.2.2
  obtain ⟨E, _, _, ψ, hEc, hψinj, hψneg⟩ := a2l_exists_sl2_27_statedSU hF
  let ψ' : SL(2, E) →* ↥T := e.symm.toMonoidHom.comp ψ
  have hψ'inj : Function.Injective ψ' := e.symm.injective.comp hψinj
  let ι : SL(2, E) →* X := T.subtype.comp ψ'
  have hιinj : Function.Injective ι := Subtype.val_injective.comp hψ'inj
  have hzι : z = ι (a2lNegOne E) := by
    have h1 : e ⟨z, hzT⟩ = ψ (a2lNegOne E) := Subtype.ext (hez.trans hψneg.symm)
    have h2 : (⟨z, hzT⟩ : ↥T) = ψ' (a2lNegOne E) := by
      change _ = e.symm (ψ (a2lNegOne E))
      rw [← h1, MulEquiv.symm_apply_apply]
    exact congrArg Subtype.val h2
  have hN : HarrisLit.IsSLTwoOver 27 ↥ι.range := by
    haveI := Fintype.ofFinite E
    exact ⟨E, inferInstance, inferInstance, by rw [← Nat.card_eq_fintype_card, hEc],
      ⟨(MonoidHom.ofInjective hιinj).symm⟩⟩
  refine ⟨27, T, ι.range, z, ⟨13, by norm_num⟩, by norm_num, hz2, ?_, ?_, hcomp.1, hcomp, hN,
    a2l_typU_of_statedSU_six hC hF hq e⟩
  · rw [hzι]
    exact ⟨_, rfl⟩
  · rintro _ ⟨x, rfl⟩
    exact (ψ' x).2

end CFSG.OddStandard.SmallF3.HypA2Leaves
