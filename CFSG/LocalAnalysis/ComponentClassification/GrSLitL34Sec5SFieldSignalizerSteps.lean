module

public import CFSG.Quasithin.Background.KGSchurMult2
import CFSG.Goldschmidt.Steps.G310TransQuot
import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma64
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SFieldCore

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup
open Matrix
open scoped MatrixGroups

theorem fusionZStar_eq_fusionOddCore_of_schurMult2L3 (hmult : Quasithin.SchurMult2L3)
    {X : Type} [Group X] [Finite X] [Group.IsPerfect X] {m : ℕ} (hm : 3 ≤ m)
    (hX : Blueprint.LieModel (X ⧸ Open.fusionZStar X) .PSL 3 2 m) :
    Open.fusionZStar X = Open.fusionOddCore X := by
  classical
  set O := Open.fusionOddCore X with hO
  set Z := Open.fusionZStar X with hZ
  have hOZ : O ≤ Z := fun x hx => by
    change QuotientGroup.mk' O x ∈ center (X ⧸ O)
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
    exact one_mem _
  set q : X ⧸ O →* X ⧸ Z := QuotientGroup.map O Z (MonoidHom.id X) hOZ with hqdef
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Z y
    exact ⟨QuotientGroup.mk' O x, rfl⟩
  have hker : q.ker = center (X ⧸ O) := by
    ext y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective O y
    rw [MonoidHom.mem_ker]
    change (QuotientGroup.mk' Z x = 1) ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    rfl
  have : Group.IsPerfect (X ⧸ O) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' O) (QuotientGroup.mk'_surjective O)
  let e : (X ⧸ O) ⧸ center (X ⧸ O) ≃* X ⧸ Z :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)
  have hcl : Open.StatedClassicalModel (X ⧸ Z) .PSL 3 2 m :=
    Blueprint.LieModel.statedClassicalModel_of_ne_zero (by decide) hX
  have : IsSimpleGroup (X ⧸ Z) := (LieType.Simplicity.fam_PSL_simplicity _ 3 2 m hcl).2
  have hqs : Open.IsQuasisimple (X ⧸ O) := ⟨Group.IsPerfect.commutator_eq_top, e.isSimpleGroup⟩
  have h2 : IsPGroup 2 (center (X ⧸ O)) := by
    refine Goldschmidt.G310.isPGroup_two_center fun N hN hN2 => ?_
    have hle : N ≤ Open.fusionOddCore (X ⧸ O) :=
      le_sSup ⟨hN, Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hN2)⟩
    rw [EvenSporadicStandard.Fin76b.fusionOddCore_quotient_eq_bot] at hle
    exact le_bot_iff.mp hle
  have hpsl : Quasithin.IsPSL 3 2 m ((X ⧸ O) ⧸ center (X ⧸ O)) := by
    obtain ⟨hadm, K, hK, hKf, hKc, ⟨ψ⟩⟩ := hcl
    exact ⟨hadm, K, hK, hKf, hKc, ⟨e.trans ψ⟩⟩
  have hcen := hmult m hm (X ⧸ O) hqs h2 hpsl
  change (center (X ⧸ O)).comap (QuotientGroup.mk' O) = O
  rw [hcen, MonoidHom.comap_bot, QuotientGroup.ker_mk']

theorem not_mem_of_l34FieldNormalSetting (hmult : Quasithin.SchurMult2L3) {G : Type}
    [Group G] [Finite G] {t : G} {P : Subgroup G} (h : L34FieldNormalSetting G t P) : t ∉ P := by
  obtain ⟨-, ht, hPC, hcomp, -, m, hm, -, hX⟩ := h
  intro htP
  have : Group.IsPerfect P := by
    have h1 := ClassicalInvolution.LBalanceProof.isPerfect_of_isPComponent hcomp
    exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hPC).toMonoidHom)
      (subgroupOfEquivOfLe hPC).surjective
  have hZO := fusionZStar_eq_fusionOddCore_of_schurMult2L3 hmult (X := P) (by omega) hX
  set t' : P := ⟨t, htP⟩ with ht'
  have hcen : t' ∈ center P := by
    rw [mem_center_iff]
    intro x
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp (hPC x.2)
  have hZ : t' ∈ Open.fusionZStar P := by
    change QuotientGroup.mk' (Open.fusionOddCore P) t' ∈ center (P ⧸ Open.fusionOddCore P)
    rw [mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ y
    rw [← map_mul, ← map_mul, mem_center_iff.mp hcen x]
  rw [hZO] at hZ
  have h2 : orderOf (⟨t', hZ⟩ : Open.fusionOddCore P) = 2 := by
    rw [Subgroup.orderOf_mk, ht', Subgroup.orderOf_mk, ht]
  have hdvd := orderOf_dvd_natCard (⟨t', hZ⟩ : Open.fusionOddCore P)
  rw [h2] at hdvd
  exact (Nat.not_even_iff_odd.mpr (EvenSporadicStandard.Fin76b.odd_natCard_fusionOddCore P))
    (even_iff_two_dvd.mpr hdvd)

end CFSG.ComponentClassification.GrSLit.L34Sec5S
