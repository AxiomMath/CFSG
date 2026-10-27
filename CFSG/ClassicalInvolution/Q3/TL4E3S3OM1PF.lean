module

public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM1Q8
public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM1SD
public import CFSG.LieType.Steinberg.CentralExt.SUOddClosed
public import CFSG.LieType.Steinberg.CentralExt.PerfectCover
public import CFSG.Open.StatedAPI
public import CFSG.ClassicalInvolution.Asc77.AscT8X4
public import CFSG.ClassicalInvolution.Asc77.AscT8YA3
public import CFSG.ClassicalInvolution.AschTight.S1916F2a
public import CFSG.ClassicalInvolution.AschTight.S19BCSW
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FStarBasic
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm7RCore
public import CFSG.ClassicalInvolution.Q3.Q3AMDBStmt
public import CFSG.ClassicalInvolution.Q3.Q3T6BSymEx
public import CFSG.ClassicalInvolution.Q3.Q3T6DCfg
public import CFSG.ClassicalInvolution.Q3.Q3T6DPart1
public import CFSG.ClassicalInvolution.Q3.Q3T6OpenSDEnd
public import CFSG.ClassicalInvolution.Q3.Q3T8B10
public import CFSG.ClassicalInvolution.Q3.Q3T8P26T01
public import CFSG.ClassicalInvolution.Q3.Q3T8P26T02
public import CFSG.ClassicalInvolution.Q3.Q3T8P26TH01
public import CFSG.ClassicalInvolution.Q3.Q3TIMain
public import CFSG.ClassicalInvolution.Q3.Q3TIYOAMain
public import CFSG.ClassicalInvolution.Q3.Q3TKMem
public import CFSG.ClassicalInvolution.Q3.TL3S8Gold
public import CFSG.ClassicalInvolution.Q3.TL3S8Sd
public import CFSG.ClassicalInvolution.Q3.TL4Conn26Ex
public import CFSG.ClassicalInvolution.Q3.TL4Conn26GAl
public import CFSG.ClassicalInvolution.Q3.TL4Conn274M
public import CFSG.ClassicalInvolution.Q3.TL4E3S3
public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM1RC
public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM1RD
public import CFSG.ClassicalInvolution.Q3.TL4SecIdDatum
public import CFSG.ClassicalInvolution.Q3.TL4SepSub
public import CFSG.ClassicalInvolution.SmallCases.NobqFinal
public import CFSG.Foundations
public import CFSG.Goldschmidt.Steps.G310Core2
public import CFSG.Goldschmidt.Steps.G37Core
public import CFSG.Goldschmidt75.TheoremB
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingCore
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingEscape
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingInherit
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingOddQuotient
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingThreeOne
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.Permutation.BurnsideSchur
public import CFSG.Timmesfeld.Moufang.Three

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.Blueprint
open scoped commutatorElement

namespace E3S3O

section Perfect

variable {W : Type} [Group W] [Finite W] {Φ : Set (Subgroup W)} {K K' : Subgroup W} {k k' : W}
  {Q : Type} [Group Q]

omit [Finite W] in
theorem fix_sigmaFixGen (K : Subgroup W) (σ : MulAut W) : ∀ y ∈ sigmaFixGen K σ, σ y = y := by
  have hle : sigmaFixGen K σ ≤ MonoidHom.eqLocus σ.toMonoidHom (MonoidHom.id W) :=
    iSup₂_le fun M hM x hx => hM.2 x hx
  intro y hy
  exact hle hy

theorem isPerfect_sigmaFixGen (h : TwinBase3 Φ K K' k k') (f : W →* Q)
    (hf : Function.Surjective f) (hf2 : IsPGroup 2 ↥f.ker) (hs : IsSimpleGroup Q)
    (hOS : Balance.oddCoreIn (Subgroup.centralizer ({f k} : Set Q)) = ⊥) {σ : MulAut W}
    (hperm : ∀ M ∈ Φ, M.map σ.toMonoidHom ∈ Φ) (hσ : f.ker.map σ.toMonoidHom = f.ker)
    (h3 : ∀ C ∈ CoreAssembly.conjClass (K.map f), (∀ c ∈ C, descend f hf σ hσ c = c) →
      ∃ y ∈ sigmaFixGen (K.map f) (descend f hf σ hσ), conjSub y C = C ∧ y ^ 3 = 1 ∧
        ∃ c ∈ C, y * c ≠ c * y) :
    Group.IsPerfect ↥(sigmaFixGen K σ) := by
  rw [Subgroup.isPerfect_iff]
  refine le_antisymm (Subgroup.commutator_le.mpr fun a ha b hb => ?_) ?_
  · rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
      (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)
  have hker := ker_eq_center_of_simple h f hf hf2 hs
  obtain ⟨hquat, -, heq⟩ := members_of_simple h f hf hf2 hs hOS
  have hY := map_sigmaFixGen h f hf hf2 hs hOS hperm hσ
  have hσb := descend_apply f hf σ hσ
  have hfixY := fix_sigmaFixGen K σ
  refine iSup₂_le fun M hM => ?_
  obtain ⟨⟨g, hg⟩, hfixM⟩ := hM
  have hg' : conjSub g K = M := hg
  subst hg'
  have hMY : conjSub g K ≤ sigmaFixGen K σ :=
    le_iSup₂ (f := fun M (_ : M ∈ {M : Subgroup W | M ∈ CoreAssembly.conjClass K ∧
      ∀ x ∈ M, σ x = x}) => M) (conjSub g K) ⟨⟨g, rfl⟩, hfixM⟩
  have hC : (conjSub g K).map f ∈ CoreAssembly.conjClass (K.map f) :=
    ⟨f g, (AscQuot.map_conjSub f g K).symm⟩
  have hCfix : ∀ c ∈ (conjSub g K).map f, descend f hf σ hσ c = c := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hσb, hfixM x hx]
  obtain ⟨yb, hybY, hybC, hyb3, c, hc, hybc⟩ := h3 _ hC hCfix
  rw [← hY] at hybY
  obtain ⟨y, hyY, rfl⟩ := hybY
  have hyM : conjSub y (conjSub g K) = conjSub g K := by
    rw [← conjSub_mul]
    refine heq (y * g) g ?_
    rw [conjSub_mul, AscQuot.map_conjSub]
    exact hybC
  have hy3 : ∀ m ∈ conjSub g K, y ^ 3 * m = m * y ^ 3 := by
    intro m _
    have h1 : y ^ 3 ∈ Subgroup.center W := by
      rw [← hker, MonoidHom.mem_ker, map_pow]
      exact hyb3
    exact (Subgroup.mem_center_iff.mp h1 m).symm
  have hyc : ∃ m ∈ conjSub g K, y * m ≠ m * y := by
    obtain ⟨m, hm, rfl⟩ := hc
    refine ⟨m, hm, fun h1 => hybc ?_⟩
    rw [← map_mul, ← map_mul, h1]
  exact le_commutator_of_q8 (hquat g).some hMY hyY hyM hy3 hyc

end Perfect

section Multiplier

theorem det_eq_one_of_mem_statedSU {n q : ℕ} {F : Type} [Field F] {A : GL (Fin n) F}
    (hA : A ∈ CFSG.Assembly.LowTwoRank.StatedSU n q F) :
    Matrix.GeneralLinearGroup.det A = 1 :=
  MonoidHom.mem_ker.1 ((CFSG.Open.StatedAPI.statedSL_eq_ker_det n F).le
    (CFSG.Open.StatedAPI.statedSU_le_statedSL n q F hA))


theorem ker_eq_bot_of_psu33 {P X : Type} [Group P] [Finite P] [Group.IsPerfect P] [Group X]
    (η : P →* X) (hη : Function.Surjective η) (hcen : η.ker ≤ Subgroup.center P)
    (h2 : IsPGroup 2 ↥η.ker) (hX : LieModel X .PSU 3 3 1) : η.ker = ⊥ := by
  have hcl : (.PSU : Assembly.LowTwoRank.StatedLieTag) ∈ classicalTags := by decide
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := Upgrade.statedClassicalModel_of_lieModel hcl hX
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : CharP F 3 := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_three (k := 2) (by norm_num) (by rw [hF]; norm_num)
  set H := CFSG.Assembly.LowTwoRank.StatedSU 3 (3 ^ 1) F with hH
  set Z := (CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) F).subgroupOf H with hZ
  let β : ↥H →* X := e.symm.toMonoidHom.comp (QuotientGroup.mk' Z)
  have hβ : Function.Surjective β := e.symm.surjective.comp (QuotientGroup.mk'_surjective _)
  have hdvd := CFSG.LieType.Steinberg.card_ker_dvd_of_isPerfect (K := ↥H) (P := P) (β := β)
    (η := η) (fun E _ _ π hπ hcen' _ =>
      CFSG.LieType.Steinberg.CentralExt.SUOdd.statedSU_odd_exists_section_of_central hF le_rfl
        (n := 3) (by norm_num) (by decide) (by decide) hπ hcen') hβ hη hcen h2
  have hβ3 : IsPGroup 3 ↥β.ker := by
    intro x
    refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
    have hx : (x : ↥H) ∈ Z := by
      have h1 : β x = 1 := x.2
      rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_eq_one_iff _ e.symm.injective,
        QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    obtain ⟨u, hu⟩ := Subgroup.mem_subgroupOf.mp hx
    have hdet := det_eq_one_of_mem_statedSU (x : ↥H).2
    rw [← hu] at hdet
    have hu3 : u ^ 3 = 1 := by
      apply Units.ext
      have h1 := congrArg Units.val hdet
      rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.coe_scalar,
        Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin] at h1
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      exact h1
    show ((((x : ↥H) : GL (Fin 3) F) ^ 3 ^ 1 : GL (Fin 3) F)) = 1
    rw [← hu, pow_one, ← map_pow, hu3, map_one]
  obtain ⟨a, ha⟩ := hβ3.exists_card_eq
  obtain ⟨b, hb⟩ := h2.exists_card_eq
  rw [ha, hb] at hdvd
  have hcop : Nat.Coprime (2 ^ b) (3 ^ a) := Nat.Coprime.pow b a (by norm_num)
  have h1 : 2 ^ b = 1 := Nat.Coprime.eq_one_of_dvd hcop hdvd
  rw [h1] at hb
  exact Subgroup.card_eq_one.mp hb

end Multiplier

end E3S3O

end CFSG.ClassicalInvolution.Q3.TL4
