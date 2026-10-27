module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneGMS28Trans
public import CFSG.LocalAnalysis.SeitzReduction.RankOneDegreeEightPerm
public import CFSG.CharacterTheory.Wreathed.NonabelianCentralizer
public import CFSG.Foundations
public import CFSG.Goldschmidt.Statements
public import CFSG.Goldschmidt.StatementsG4
public import CFSG.Goldschmidt.StatementsH
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.LieType.Chevalley.RootCommutator
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3SixCaseOne
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3SixProper
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedPointHull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointFullTransport
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Alt
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Native
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Five
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SeitzReduction.RankOneLinearStageZero
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureConjugation
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPair
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyData
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyProper
public import CFSG.Milestones.CL_LIT_Goldschmidt_strongly_closed_abelian_models
public import CFSG.Quasithin.Background.A1cModuleCoprime
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3Structure312
public import CFSG.Quasithin.Background.OrderingMax
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Sporadic.Bridge.M11CheckInputs
public import CFSG.Sporadic.Schreier.J4SSylow
public import CFSG.Walter.J1
public import CFSG.Walter.J1Recog
public import CFSG.Walter.Ree.Thompson2.BaseFin
public import CFSG.Walter.ReeOrder.WardLocal
public import CFSG.Walter.W67.Section8.Prop83
public import CFSG.Walter.W67.W2Lemma26A
public import Certificates.Certificate110
public import Certificates.Certificate7000
public import Certificates.Certificate7001
public import Certificates.Certificate7002
public import Certificates.Certificate7003
public import Certificates.Certificate7004
public import Certificates.Certificate7005
public import Certificates.Certificate7006
public import Certificates.Certificate7007
public import Certificates.Certificate7008
public import Certificates.Certificate7009
public import Certificates.Certificate7010
public import Certificates.Certificate7011
public import Certificates.Certificate8026Base
public import Certificates.Certificate8046
public import Certificates.Certificate8049
public import Certificates.Certificate8052

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.SteinbergBV CFSG.LocalAnalysis.SteinbergBX
open scoped LinearAlgebra.Projectivization CFSG.SeitzReduction.RankOne.DegreeEight

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Defs

variable {D : Type*} [Group D]

@[expose] def SmallRootStage (R X U P : Subgroup D) (n : ℕ) : Prop :=
  GMSNormalRootData R R X U P n ∧ Nat.card R = 2 ∧
    normalizer (R : Set D) ⊓ centralizer (U : Set D) = U ⊔ R

@[expose] def GMSHasRegularNormal (U R : Subgroup D) : Prop :=
  ∃ E : Subgroup (Equiv.Perm (gmsRootConjugates (U ⊔ R) R)),
    E ≤ (gmsRootConjugateAction (U ⊔ R) R).range ∧
    (E.subgroupOf (gmsRootConjugateAction (U ⊔ R) R).range).Normal ∧
    ∀ Q Z : gmsRootConjugates (U ⊔ R) R, ∃! a : E,
      (a : Equiv.Perm (gmsRootConjugates (U ⊔ R) R)) Q = Z

@[expose] def GMSProjectiveEight (U R : Subgroup D) : Prop :=
  ∃ β : gmsRootConjugates (U ⊔ R) R ≃ ℙ (ZMod 7) (Fin 2 → ZMod 7),
    ∀ σ : Equiv.Perm (gmsRootConjugates (U ⊔ R) R),
      σ ∈ (gmsRootConjugateAction (U ⊔ R) R).range ↔
        ∃ g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7), ∀ Q, β (σ Q) = g • β Q

abbrev StageQuot (U : Subgroup D) : Type _ :=
  ↥(normalizer (U : Set D)) ⧸ U.subgroupOf (normalizer (U : Set D))

@[expose] def stageImg (U K : Subgroup D) : Subgroup (StageQuot U) :=
  (K.subgroupOf (normalizer (U : Set D))).map (QuotientGroup.mk' _)

end Defs

section Tight

variable {D : Type*} [Group D]

theorem card_inf_conj_eq_one_of_card_eq_two [Finite D] {R : Subgroup D} (hR : Nat.card R = 2)
    {g : D} (hg : g ∉ normalizer (R : Set D)) :
    Nat.card (R ⊓ R.map (MulAut.conj g⁻¹).toMonoidHom : Subgroup D) = 1 := by
  set Rg := R.map (MulAut.conj g⁻¹).toMonoidHom with hRg
  have hRgcard : Nat.card Rg = 2 := by
    rw [hRg, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hR]
  have hle : (R ⊓ Rg : Subgroup D) ≤ R := inf_le_left
  have hdvd : Nat.card (R ⊓ Rg : Subgroup D) ∣ 2 := hR ▸ Subgroup.card_dvd_of_le hle
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · exact h1
  · exfalso
    apply hg
    have hR1 : R ⊓ Rg = R := Subgroup.eq_of_le_of_card_ge hle (by rw [h2, hR])
    have hR2 : R ⊓ Rg = Rg := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h2, hRgcard])
    have hRR : Rg = R := hR2.symm.trans hR1
    have hgi : g⁻¹ ∈ normalizer (R : Set D) := by
      rw [← map_conj_eq_self_iff]
      exact hRR
    simpa using inv_mem hgi

theorem gmsNormalRootData_self_of_card_eq_two [Finite D] {J R X U P : Subgroup D} {n : ℕ}
    (h : GMSNormalRootData J R X U P n) (hR : Nat.card R = 2) :
    GMSNormalRootData R R X U P n := by
  obtain ⟨hn, -, ⟨hRel, -, -⟩, hX, hU, hS, hP⟩ := h
  refine ⟨hn, ⟨?_, fun g hg => ?_⟩, ⟨hRel, le_rfl, ?_⟩, hX, hU, hS, hP⟩
  · rw [hR]
    exact even_two
  · rw [card_inf_conj_eq_one_of_card_eq_two hR hg]
    exact odd_one
  · have hp : IsPGroup 2 (⊤ : Subgroup R) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Subgroup.card_top, hR, pow_one]
    refine ⟨hp.toSylow (by simp), ?_⟩
    rw [IsPGroup.toSylow_coe, Subgroup.subgroupOf_self]

end Tight

theorem eq_one_of_odd_orderOf_of_sq_eq_one {G : Type*} [Monoid G] {x : G}
    (hx : Odd (orderOf x)) (h2 : x ^ 2 = 1) : x = 1 := by
  rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h2) with h1 | h1
  · exact orderOf_eq_one_iff.mp h1
  · rw [h1] at hx
    exact absurd (Nat.odd_iff.mp hx) (by norm_num)

namespace SmallRootStage

variable {D : Type*} [Group D] {R X U P : Subgroup D} {n : ℕ}

theorem of_gmsNormalRootData [Finite D] {J : Subgroup D} (h : GMSNormalRootData J R X U P n)
    (hR : Nat.card R = 2) (hC : normalizer (R : Set D) ⊓ centralizer (U : Set D) = U ⊔ R) :
    SmallRootStage R X U P n :=
  ⟨gmsNormalRootData_self_of_card_eq_two h hR, hR, hC⟩

theorem card_eq_two (h : SmallRootStage R X U P n) : Nat.card R = 2 := h.2.1

theorem normalizer_inf_centralizer (h : SmallRootStage R X U P n) :
    normalizer (R : Set D) ⊓ centralizer (U : Set D) = U ⊔ R := h.2.2

theorem three_le (h : SmallRootStage R X U P n) : 3 ≤ n := h.1.1

theorem exists_ne_one [Finite D] (h : SmallRootStage R X U P n) : ∃ t ∈ R, t ≠ 1 := by
  have : Nontrivial R := Finite.one_lt_card_iff_nontrivial.mp (by rw [h.card_eq_two]; norm_num)
  obtain ⟨⟨t, htR⟩, ht1⟩ := exists_ne (1 : R)
  exact ⟨t, htR, fun h1 => ht1 (Subtype.ext h1)⟩

theorem setup (h : SmallRootStage R X U P n) (h3 : 3 ≤ (gmsRootConjugates (U ⊔ R) R).ncard)
    {t : D} (htR : t ∈ R) (ht1 : t ≠ 1) : GMS28.Setup R R X U P n t :=
  ⟨h.1, htR, ht1, h.2.1, h3⟩

theorem inf_X_V [Finite D] (h : SmallRootStage R X U P n) : X ⊓ (U ⊔ R) = U := by
  rw [inf_comm]
  exact gms_inf_X h.1

theorem X_centralizer_U [Finite D] (h : SmallRootStage R X U P n) :
    X ⊓ centralizer (U : Set D) = U := by
  have hXV := h.inf_X_V
  obtain ⟨-, -, -, ⟨hXN, -, -⟩, ⟨-, hUX, -, -⟩, -⟩ := h.1
  refine le_antisymm (fun x hx => ?_) (le_inf hUX fun u hu => mem_centralizer_iff.mpr
    fun v hv => gms_comm_V h.1 v (mem_sup_left hv) u (mem_sup_left hu))
  have hxV : x ∈ U ⊔ R := by
    rw [← h.normalizer_inf_centralizer]
    exact mem_inf.mpr ⟨hXN (mem_inf.mp hx).1, (mem_inf.mp hx).2⟩
  rw [← hXV]
  exact mem_inf.mpr ⟨(mem_inf.mp hx).1, hxV⟩

theorem exists_singer [Finite D] (h : SmallRootStage R X U P n) :
    ∃ d ∈ X ⊓ normalizer (U : Set D), orderOf d = 2 ^ n - 1 ∧
      X ⊓ normalizer (U : Set D) = U ⊔ zpowers d ∧
      (∀ a ∈ U, ∀ b ∈ U, a ≠ 1 → b ≠ 1 → ∃ k : ℕ, d ^ k * a * (d ^ k)⁻¹ = b) ∧
      ∀ k : ℕ, ∀ a ∈ U, a ≠ 1 → d ^ k * a * (d ^ k)⁻¹ = a → d ^ k = 1 := by
  classical
  have hCXU := h.X_centralizer_U
  obtain ⟨hn3, -, -, -, ⟨-, hUX, -, hUcard⟩, ⟨hcyc, hcard, hregU⟩, -⟩ := h.1
  have hsqU : ∀ u ∈ U, u ^ 2 = 1 := fun u hu => gms_sq_V h.1 u (mem_sup_left hu)
  have hUcomm : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb =>
    gms_comm_V h.1 a (mem_sup_left ha) b (mem_sup_left hb)
  have h8 : 8 ≤ 2 ^ n :=
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
  have hodd : Odd (2 ^ n - 1) := by
    have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    exact Nat.odd_iff.mpr (by omega)
  have hmk1 : ∀ g : (X ⊓ normalizer (U : Set D) : Subgroup D),
      (QuotientGroup.mk g : GMSNormalizerQuotient X U) = 1 ↔ (g : D) ∈ U := by
    intro g
    rw [QuotientGroup.eq_one_iff, mem_subgroupOf, hCXU]
  have hact : ∀ g, gmsQuotConjAct X U (QuotientGroup.mk g) = gmsConjAct X U g := fun _ => rfl
  have hcoe : ∀ (g : (X ⊓ normalizer (U : Set D) : Subgroup D)) (j : ℕ) (u : U),
      (((gmsConjAct X U g ^ j) u : U) : D) = (g : D) ^ j * u * ((g : D) ^ j)⁻¹ := by
    intro g j u
    rw [← map_pow, SteinbergBT.gmsConjAct_coe_apply]
    simp
  obtain ⟨c₀, hc₀⟩ := hcyc.exists_generator
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective c₀
  have hg₀q : (QuotientGroup.mk g₀ : GMSNormalizerQuotient X U) ^ (2 ^ n - 1) = 1 := by
    rw [← hcard]
    exact pow_card_eq_one'
  have hg₀m : ∀ w ∈ U, (g₀ : D) ^ (2 ^ n - 1) * w * ((g₀ : D) ^ (2 ^ n - 1))⁻¹ = w := by
    intro w hw
    have h1 : ((g₀ ^ (2 ^ n - 1) : (X ⊓ normalizer (U : Set D) : Subgroup D)) : D) ∈ U := by
      rw [← hmk1, QuotientGroup.mk_pow]
      exact hg₀q
    rw [coe_pow] at h1
    rw [hUcomm _ h1 w hw, mul_inv_cancel_right]
  obtain ⟨d, hd, hdodd, hdact⟩ := GMS28.exists_odd_of_pow_conj_eq (W := U) hodd hg₀m
  have hdN : d ∈ X ⊓ normalizer (U : Set D) := zpowers_le.mpr g₀.2 hd
  set dd : (X ⊓ normalizer (U : Set D) : Subgroup D) := ⟨d, hdN⟩ with hdd
  have hmkd : (QuotientGroup.mk dd : GMSNormalizerQuotient X U) = QuotientGroup.mk g₀ := by
    rw [QuotientGroup.eq, mem_subgroupOf]
    refine mem_inf.mpr ⟨mul_mem (inv_mem (mem_inf.mp hdN).1) (mem_inf.mp g₀.2).1,
      mem_centralizer_iff.mpr fun u hu => ?_⟩
    have hgu : (g₀ : D) * u * (g₀ : D)⁻¹ = d * u * d⁻¹ := (hdact u hu).symm
    change u * (d⁻¹ * g₀) = d⁻¹ * g₀ * u
    calc u * (d⁻¹ * g₀) = d⁻¹ * (d * u * d⁻¹) * g₀ := by group
      _ = d⁻¹ * ((g₀ : D) * u * (g₀ : D)⁻¹) * g₀ := by rw [hgu]
      _ = d⁻¹ * g₀ * u := by group
  have hpow : ∀ c : GMSNormalizerQuotient X U, ∃ j : ℕ,
      (QuotientGroup.mk dd : GMSNormalizerQuotient X U) ^ j = c := fun c => by
    rw [hmkd]
    exact (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 (hc₀ c))
  have hgen : ∀ c : GMSNormalizerQuotient X U,
      c ∈ zpowers (QuotientGroup.mk dd : GMSNormalizerQuotient X U) := fun c => by
    obtain ⟨j, rfl⟩ := hpow c
    exact pow_mem (mem_zpowers _) j
  have hordQ : orderOf (QuotientGroup.mk dd : GMSNormalizerQuotient X U) = 2 ^ n - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hgen, hcard]
  have hdpowU : ∀ j : ℕ, (QuotientGroup.mk dd : GMSNormalizerQuotient X U) ^ j = 1 →
      d ^ j = 1 := by
    intro j hj
    have h1 : ((dd ^ j : (X ⊓ normalizer (U : Set D) : Subgroup D)) : D) ∈ U := by
      rw [← hmk1, QuotientGroup.mk_pow]
      exact hj
    rw [coe_pow] at h1
    exact eq_one_of_odd_orderOf_of_sq_eq_one (hdodd.of_dvd_nat (orderOf_pow_dvd j)) (hsqU _ h1)
  have hdord : orderOf d = 2 ^ n - 1 := by
    refine Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one (hdpowU _ ?_)) ?_
    · rw [← hordQ]
      exact pow_orderOf_eq_one _
    · rw [← hordQ]
      refine orderOf_dvd_of_pow_eq_one ?_
      rw [← QuotientGroup.mk_pow]
      have : dd ^ orderOf d = 1 := Subtype.ext (by rw [coe_pow]; exact pow_orderOf_eq_one d)
      rw [this, QuotientGroup.mk_one]
  have hdj : ∀ (j : ℕ) (u : U), ((gmsQuotConjAct X U
      ((QuotientGroup.mk dd : GMSNormalizerQuotient X U) ^ j) u : U) : D) =
        d ^ j * u * (d ^ j)⁻¹ := by
    intro j u
    rw [map_pow, hact, hcoe]
  refine ⟨d, hdN, hdord, le_antisymm (fun g hg => ?_)
    (sup_le (le_inf hUX le_normalizer) (zpowers_le.mpr hdN)), fun a ha b hb ha1 hb1 => ?_,
    fun k a ha ha1 hk => ?_⟩
  · obtain ⟨j, hj⟩ := hpow (QuotientGroup.mk ⟨g, hg⟩)
    have h1 : (QuotientGroup.mk (dd ^ j)⁻¹ * QuotientGroup.mk ⟨g, hg⟩ :
        GMSNormalizerQuotient X U) = 1 := by
      rw [← hj, QuotientGroup.mk_inv, QuotientGroup.mk_pow, inv_mul_cancel]
    rw [← QuotientGroup.mk_mul, hmk1] at h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_pow] at h1
    have e : g = d ^ j * ((d ^ j)⁻¹ * g) := by group
    rw [e]
    exact mul_mem (mem_sup_right (pow_mem (mem_zpowers d) j)) (mem_sup_left h1)
  · obtain ⟨c, hc, -⟩ := hregU ⟨a, ha⟩ ⟨b, hb⟩ (fun h1 => ha1 (congrArg Subtype.val h1))
      (fun h1 => hb1 (congrArg Subtype.val h1))
    obtain ⟨j, rfl⟩ := hpow c
    refine ⟨j, ?_⟩
    have h1 := congrArg Subtype.val hc
    rw [hdj] at h1
    exact h1
  · obtain ⟨c, -, hcu⟩ := hregU ⟨a, ha⟩ ⟨a, ha⟩ (fun h1 => ha1 (congrArg Subtype.val h1))
      (fun h1 => ha1 (congrArg Subtype.val h1))
    have e1 := hcu ((QuotientGroup.mk dd : GMSNormalizerQuotient X U) ^ k)
      (Subtype.ext (by rw [hdj]; exact hk))
    have e2 := hcu 1 (by
      show gmsQuotConjAct X U 1 ⟨a, ha⟩ = ⟨a, ha⟩
      rw [map_one]
      rfl)
    exact hdpowU k (e1.trans e2.symm)

end SmallRootStage

end CFSG.SeitzReduction.RankOne
