module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P47Plus
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL3Cases
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL3CharCls
public import CFSG.GH74.GLS.Stage2.Signalizer.L46EAutC
public import CFSG.GH74.GLS.Stage2.Signalizer.Bridge
public import CFSG.GroupTheory.ABGLocalTools.PStabilityQDickson
public import CFSG.CharacterTheory.Blocks.Defs
public import CFSG.GH74.GLS.Stage2.Local.Statements
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Defs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpE4Defs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpE4Final
public import CFSG.GH74.GLS.Stage2.Signalizer.Stmt42
public import CFSG.GH74.GLS.Stage2.Signalizer.Stmt5
public import CFSG.GH74.Generic.S3.LeavesFine
public import CFSG.GH74.Generic.S3.Lem37
public import CFSG.GH74.KGroups.L3EpsNoNormalThree
public import CFSG.GH74.KGroups.L3EpsOutExp
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearDescentFixedBasis
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherScalarSquareSplit
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Critical

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Matrix Subgroup CFSG CFSG.GH74.GLS.Stage2.Local CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.GH74.KGroups.L3Eps CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

section Model

theorem p47_center_odd {K : Type} [Group K] [Finite K] {p n : ℕ}
    (hLie : LieModel (K ⧸ pPrimeCore 2 K) .PSL 3 p n) : Odd (Nat.card (Subgroup.center K)) := by
  obtain ⟨F, _, _, -, ⟨ι⟩⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel hLie
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : Subgroup.center K ≤ pPrimeCore 2 K := by
    intro x hx
    have hmk : (QuotientGroup.mk x : K ⧸ pPrimeCore 2 K) ∈ Subgroup.center (K ⧸ pPrimeCore 2 K) := by
      rw [Subgroup.mem_center_iff]
      intro q
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.1 hx g]
    have h1 : ι (QuotientGroup.mk x) ∈ Subgroup.center (projectiveSL 3 F) := by
      rw [← Subgroup.map_center_eq ι]
      exact Subgroup.mem_map_of_mem ι.toMonoidHom hmk
    rw [center_projectiveSL_three_eq_bot (K := F), Subgroup.mem_bot] at h1
    have : (QuotientGroup.mk x : K ⧸ pPrimeCore 2 K) = 1 := ι.injective (by rw [h1, map_one])
    exact (QuotientGroup.eq_one_iff x).1 this
  have hcop : ¬ 2 ∣ Nat.card (pPrimeCore 2 K) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 pPrimeCore_coprime_card
  have hdvd : Nat.card (Subgroup.center K) ∣ Nat.card (pPrimeCore 2 K) :=
    Subgroup.card_dvd_of_le hle
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  exact fun h => hcop (h.trans hdvd)

theorem p47_exists_phi {Y : Type} [Group Y] {K : Subgroup Y} {b : Y} (hbK : b ∈ K) (hb2 : b * b = 1)
    (hb1 : b ≠ 1) {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hLie : LieModel (↥K ⧸ Subgroup.center ↥K) .PSL 3 p n) [Finite ↥K]
    (hodd : Odd (Nat.card ↥(Subgroup.center ↥K))) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (φ : ↥K →* projectiveSL 3 F), Nat.card F = p ^ n ∧
      Function.Surjective φ ∧ φ.ker = Subgroup.center ↥K ∧ φ ⟨b, hbK⟩ = tInv := by
  obtain ⟨F, iF, fF, hFcard, ⟨ι⟩⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel hLie
  have hoddF : Odd (Nat.card F) := hFcard ▸ (hp.odd_of_ne_two hp2).pow
  have h2 : (2 : F) ≠ 0 := CFSG.ABGLocalTools.two_ne_zero_of_odd_card hoddF
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set b' : ↥K := ⟨b, hbK⟩ with hb'
  have hb'2 : b' * b' = 1 := Subtype.ext hb2
  have hb'1 : b' ≠ 1 := fun h => hb1 (congrArg Subtype.val h)
  have hy2 : (QuotientGroup.mk b' : ↥K ⧸ Subgroup.center ↥K) *
      (QuotientGroup.mk b' : ↥K ⧸ Subgroup.center ↥K) = 1 := by
    rw [← QuotientGroup.mk_mul, hb'2, QuotientGroup.mk_one]
  have hy1 : (QuotientGroup.mk b' : ↥K ⧸ Subgroup.center ↥K) ≠ 1 := by
    intro h
    have hmem : b' ∈ Subgroup.center ↥K := (QuotientGroup.eq_one_iff b').1 h
    have hord : orderOf b' = 2 := orderOf_eq_prime (by rw [sq]; exact hb'2) hb'1
    have hd : orderOf b' ∣ Nat.card ↥(Subgroup.center ↥K) :=
      Subgroup.orderOf_dvd_natCard (Subgroup.center ↥K) hmem
    rw [hord] at hd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hd)
  obtain ⟨ι', hι'⟩ := exists_equiv_tInv h2 ι hy2 hy1
  refine ⟨F, iF, fF, ι'.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K)), hFcard,
    ι'.surjective.comp (QuotientGroup.mk'_surjective _), ?_, hι'⟩
  ext k
  rw [MonoidHom.mem_ker]
  show ι' (QuotientGroup.mk k) = 1 ↔ _
  rw [map_eq_one_iff ι' ι'.injective, QuotientGroup.eq_one_iff]

end Model

section Classify

variable {Y : Type} [Group Y]

theorem p47_map_ne_bot {X : Subgroup Y} (hq : IsQuasisimple ↥(ncl X)) {F : Type} [Field F]
    (φ : ↥(ncl X) →* projectiveSL 3 F) (hker : φ.ker = Subgroup.center ↥(ncl X)) :
    (X.subgroupOf (ncl X)).map φ ≠ ⊥ := by
  have hn : (ncl X).Normal := Subgroup.normalClosure_normal
  have hXK : X ≤ ncl X := Subgroup.subset_normalClosure
  intro hbot
  have hXc : X.subgroupOf (ncl X) ≤ Subgroup.center ↥(ncl X) := by
    intro x hx
    have : φ x ∈ (X.subgroupOf (ncl X)).map φ := Subgroup.mem_map_of_mem φ hx
    rw [hbot, Subgroup.mem_bot] at this
    rw [← hker]
    exact this
  set Zc : Subgroup Y := (Subgroup.center ↥(ncl X)).map (ncl X).subtype with hZc
  have hZn : Zc.Normal := ⟨fun n hn' g => by
    obtain ⟨z₀, hz₀, rfl⟩ := hn'
    refine ⟨MulAut.conjNormal g z₀,
      CFSG.GH74.GLS.Stage2.Signalizer.L46E.AutC.mulAut_mem_center (MulAut.conjNormal g) hz₀, ?_⟩
    exact MulAut.conjNormal_apply g z₀⟩
  have hXZ : (X : Set Y) ⊆ Zc := by
    intro x hx
    exact ⟨⟨x, hXK hx⟩, hXc (show (⟨x, hXK hx⟩ : ↥(ncl X)) ∈ X.subgroupOf (ncl X) from hx), rfl⟩
  have hKZ : ncl X ≤ Zc := Subgroup.normalClosure_le_normal hXZ
  have hcentral : ∀ k : ↥(ncl X), k ∈ Subgroup.center ↥(ncl X) := by
    intro k
    obtain ⟨z₀, hz₀, hz₀k⟩ := hKZ k.2
    have : z₀ = k := Subtype.ext hz₀k
    exact this ▸ hz₀
  obtain ⟨-, -, a, b, hab⟩ := hq
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  exact congrArg QuotientGroup.mk (Subgroup.mem_center_iff.1 (hcentral a) b).symm

theorem p47_classify {K : Subgroup Y} [Finite ↥K] {b : Y} (hbK : b ∈ K) (hb2 : b * b = 1)
    {X : Subgroup Y} (hXK : X ≤ K) {p : ℕ} [Fact p.Prime] (hXp : IsPGroup p ↥X)
    (hXinv : ∀ c : ↥K, (c : Y) * b = b * (c : Y) → (c : Y) ∈ normalizer (X : Set Y))
    (hodd : Odd (Nat.card ↥(Subgroup.center ↥K))) {F : Type} [Field F] [Finite F] [CharP F p]
    (h2 : (2 : F) ≠ 0) (φ : ↥K →* projectiveSL 3 F) (hs : Function.Surjective φ)
    (hker : φ.ker = Subgroup.center ↥K) (hφb : φ ⟨b, hbK⟩ = tInv)
    (hne : (X.subgroupOf K).map φ ≠ ⊥) :
    (X.subgroupOf K).map φ = (radP F).map (proj 3 F) ∨
      (X.subgroupOf K).map φ = (radM F).map (proj 3 F) := by
  set X₀ : Subgroup ↥K := X.subgroupOf K with hX₀
  have hXp₀ : IsPGroup p ↥X₀ :=
    hXp.of_injective (Subgroup.subgroupOfEquivOfLe hXK).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hXK).injective
  refine classify_p_subgroup h2 p (X₀.map φ) (hXp₀.map φ) hne ?_
  intro g hg
  obtain ⟨a, ha⟩ := hs (proj 3 F g)
  set b' : ↥K := ⟨b, hbK⟩ with hb'
  have hb'2 : b' * b' = 1 := Subtype.ext hb2
  have hgd : dNeg * g = g * dNeg := Subgroup.mem_centralizer_iff.1 hg dNeg (Set.mem_singleton _)
  have hcomm : φ b' * φ a = φ a * φ b' := by
    rw [hφb, ha, tInv, ← map_mul, ← map_mul, hgd]
  have hmk : (QuotientGroup.mk b' : ↥K ⧸ Subgroup.center ↥K) * QuotientGroup.mk a =
      QuotientGroup.mk a * QuotientGroup.mk b' := by
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, ← hker,
      MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [hcomm, inv_mul_cancel]
  obtain ⟨c, hcb, hcmk⟩ := exists_lift_centralizer (Subgroup.center ↥K) hodd hb'2 hmk
  have hφc : φ c = φ a := by
    have h1 : c⁻¹ * a ∈ Subgroup.center ↥K := QuotientGroup.eq.1 hcmk
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1
  have hcN : (c : Y) ∈ normalizer (X : Set Y) := hXinv c (congrArg Subtype.val hcb)
  have hcN₀ : c ∈ normalizer (X₀ : Set ↥K) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [hX₀, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.mp hcN (x : Y)
  rw [← ha, ← hφc]
  exact Subgroup.le_normalizer_map φ ⟨c, hcN₀, rfl⟩

end Classify

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
