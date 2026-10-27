module

public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeCharCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.PrimeCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.SevenCharE8
public import CFSG.RankThree.PartOne.KE.SigmaCentralizer
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.E78Sylow
public import CFSG.LieType.Chevalley.E6EvenRootTorus
public import CFSG.LieType.Chevalley.ParabolicSylowSubsystem
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.SubsystemRank
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.Chevalley.SteinbergBNF4Block
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG CFSG.Open CFSG.Blueprint CFSG.LieType CFSG.LocalAnalysis.GLTheoremA
open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Timmesfeld.Steinberg CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped commutatorElement

@[expose] def e8NodeZeroToral {K : Type} [Field K] (ζ : Kˣ) : Fin Tag.E8.rank → Kˣ :=
  fun i => if i = 0 then ζ else 1

theorem rootChar_e8NodeZeroToral {K : Type} [Field K] (ζ : Kˣ) (α : Fin Tag.E8.rank → ℤ) :
    rootChar (τ := Tag.E8) (e8NodeZeroToral ζ) α = ζ ^ (α 0) := by
  classical
  simp only [rootChar]
  calc ∏ i : Fin 8, (e8NodeZeroToral ζ i) ^ α i
      = (e8NodeZeroToral ζ 0) ^ α 0 :=
        Finset.prod_eq_single (0 : Fin Tag.E8.rank)
          (fun i _ hi => by simp [e8NodeZeroToral, hi])
          (fun h => absurd (Finset.mem_univ _) h)
    _ = ζ ^ (α 0) := by simp [e8NodeZeroToral]

private theorem e8_root_nodeZero_coord_bounds (α : Fin Tag.E8.rank → ℤ) (hα : IsRoot .E8 α) :
    α 0 ≤ 2 ∧ -2 ≤ α 0 := by
  have h : ∀ β ∈ rootFinset .E8, β 0 ≤ 2 ∧ -2 ≤ β 0 := by decide +kernel
  exact h α (mem_rootFinset.2 hα)

theorem rootChar_eq_one_iff_e8NodeZeroToral {K : Type} [Field K] {q : ℕ} {ζ : Kˣ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hζ : orderOf ζ = q) {α : Fin Tag.E8.rank → ℤ}
    (hα : IsRoot .E8 α) :
    rootChar (τ := Tag.E8) (e8NodeZeroToral ζ) α = 1 ↔ α 0 = 0 := by
  rw [rootChar_e8NodeZeroToral, ← orderOf_dvd_iff_zpow_eq_one, hζ]
  constructor
  · intro hdvd
    obtain ⟨hle, hge⟩ := e8_root_nodeZero_coord_bounds α hα
    have hq3 : (3 : ℤ) ≤ q := by
      have := hq.two_le
      omega
    obtain ⟨k, hk⟩ := hdvd
    have hk0 : k = 0 := by
      rcases lt_trichotomy k 0 with h | h | h
      · have : (q : ℤ) * k ≤ 3 * k := by nlinarith
        omega
      · exact h
      · have : 3 * k ≤ (q : ℤ) * k := by nlinarith
        omega
    rw [hk0, mul_zero] at hk
    exact hk
  · intro h
    rw [h]
    exact dvd_zero _

theorem rootCharKernel_e8NodeZeroToral_eq_parabolicRoots {K : Type} [Field K] {q : ℕ}
    {ζ : Kˣ} (hq : q.Prime) (hq2 : q ≠ 2) (hζ : orderOf ζ = q) :
    rootCharKernel (τ := Tag.E8) (e8NodeZeroToral ζ) =
      parabolicRoots Tag.E8 {i : Fin Tag.E8.rank | i ≠ 0} := by
  ext α
  change (IsRoot Tag.E8 α ∧ rootChar (τ := Tag.E8) (e8NodeZeroToral ζ) α = 1) ↔
    (IsRoot Tag.E8 α ∧ ∀ i ∉ {i : Fin Tag.E8.rank | i ≠ 0}, α i = 0)
  constructor
  · rintro ⟨hα, hroot⟩
    exact ⟨hα, fun i hi => by
      have hi0 : i = 0 := by simpa using hi
      rw [hi0]
      exact (rootChar_eq_one_iff_e8NodeZeroToral hq hq2 hζ hα).1 hroot⟩
  · rintro ⟨hα, h⟩
    exact ⟨hα, (rootChar_eq_one_iff_e8NodeZeroToral hq hq2 hζ hα).2 (h 0 (by simp))⟩

theorem e8NodeZeroToral_ne_one {K : Type} [Field K] {q : ℕ} {ζ : Kˣ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hζ : orderOf ζ = q) : e8NodeZeroToral ζ ≠ 1 := by
  intro h
  have h0 : ζ = 1 := by
    have := congrArg (fun a : Fin Tag.E8.rank → Kˣ => a 0) h
    simpa [e8NodeZeroToral] using this
  have hq1 : q = 1 := by
    rw [← hζ, h0]
    simp
  exact hq.ne_one hq1

private theorem toralCentralizer_eq_toralRootGroup_of_not_dvd {K : Type} [Field K] {q : ℕ}
    (hq : q.Prime) (hord : ¬ q ∣ Nat.card (WeylGroup .E8)) {a : Fin Tag.E8.rank → Kˣ}
    (hpow : ∀ i, a i ^ q = 1) (ha1 : a ≠ 1) :
    toralCentralizer Tag.E8 K a = toralRootGroup Tag.E8 K a := by
  have hneg : ∀ α : Fin Tag.E8.rank → ℤ, rootChar (τ := Tag.E8) a (-α) =
      (rootChar (τ := Tag.E8) a α)⁻¹ := by
    intro α
    simp only [rootChar]
    change ∏ i : Fin 8, a i ^ (-(α i)) = (∏ i : Fin 8, a i ^ α i)⁻¹
    simp only [zpow_neg, Finset.prod_inv_distrib]
  refine le_antisymm (fun g hg => ?_) (toralRootGroup_le (τ := Tag.E8) (K := K) a)
  exact toralCentralizer_le_sup_rootSpan (τ := Tag.E8) (L := K) (p := q) (hp := hq)
    (hord := hord) (a := a) (hap := hpow) (ha1 := ha1)
    (S := rootCharKernel (τ := Tag.E8) a) (hS := fun α hα => hα.1)
    (hSn := fun α hα => by
      simp only [rootCharKernel, Set.mem_setOf_eq] at hα ⊢
      exact ⟨IsRoot.neg hα.1, by rw [hneg, hα.2, inv_one]⟩)
    (hker := fun _ h => h) hg

theorem toralCentralizer_e8NodeZeroToral_eq_toralRootGroup {K : Type} [Field K] {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) {ζ : Kˣ} (hζ : orderOf ζ = q) :
    toralCentralizer Tag.E8 K (e8NodeZeroToral ζ) =
      toralRootGroup Tag.E8 K (e8NodeZeroToral ζ) := by
  have hpow : ∀ i, (e8NodeZeroToral ζ i) ^ q = 1 := by
    intro i
    have hζq : (ζ : Kˣ) ^ (q : ℤ) = 1 := by
      rw [zpow_natCast, ← hζ]; exact pow_orderOf_eq_one ζ
    by_cases hi : i = 0
    · subst hi
      simp only [e8NodeZeroToral, if_pos rfl]
      simpa using hζq
    · simp [e8NodeZeroToral, hi]
  rcases eq_or_ne q 3 with h3 | h3
  · subst h3
    exact toralCentralizer_eq_toralRootGroup_E8_three K (e8NodeZeroToral ζ) hpow
  rcases eq_or_ne q 5 with h5 | h5
  · subst h5
    exact toralCentralizer_eq_toralRootGroup_E8_five K (e8NodeZeroToral ζ) hpow
  rcases eq_or_ne q 7 with h7 | h7
  · subst h7
    exact toralCentralizer_eq_toralRootGroup_of_stabilizer_le Tag.E8 K (e8NodeZeroToral ζ)
      (rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E8_seven (e8NodeZeroToral ζ) hpow).le
  refine toralCentralizer_eq_toralRootGroup_of_not_dvd hq ?_ hpow (e8NodeZeroToral_ne_one hq hq2 hζ)
  rw [CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.card_weylGroup_E8']
  have hfac : (696729600 : ℕ) = 2 ^ 14 * 3 ^ 5 * 5 ^ 2 * 7 := by norm_num
  rw [hfac]
  intro hd
  have h2 : q = 2 := by
    rcases hq.dvd_mul.mp hd with h | h
    · rcases hq.dvd_mul.mp h with h | h
      · rcases hq.dvd_mul.mp h with h | h
        · exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h)
        · exact absurd ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1
            (hq.dvd_of_dvd_pow h)) h3
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).1
          (hq.dvd_of_dvd_pow h)) h5
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).1 h) h7
  exact hq2 h2

theorem toralCentralizer_e8NodeZeroToral_eq_torusGroup_sup_subsystemGroup {K : Type} [Field K]
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {ζ : Kˣ} (hζ : orderOf ζ = q) :
    toralCentralizer Tag.E8 K (e8NodeZeroToral ζ) =
      torusGroup Tag.E8 K ⊔ subsystemGroup Tag.E8 K {i : Fin Tag.E8.rank | i ≠ 0} := by
  rw [toralCentralizer_e8NodeZeroToral_eq_toralRootGroup hq hq2 hζ]
  simp only [toralRootGroup]
  rw [rootCharKernel_e8NodeZeroToral_eq_parabolicRoots hq hq2 hζ,
    ← subsystemGroup_eq_rootSpan (J := {i : Fin Tag.E8.rank | i ≠ 0})]

private theorem commutator_mem_of_eq_sup_of_normalizes {G : Type} [Group G] {H Q C : Subgroup G}
    (hC : C = H ⊔ Q) (hN : H ≤ Subgroup.normalizer (Q : Set G))
    (hHab : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    {g h : G} (hg : g ∈ C) (hh : h ∈ C) :
    g * h * g⁻¹ * h⁻¹ ∈ Q := by
  have hHC : H ≤ C := by rw [hC]; exact le_sup_left
  have hQC : Q ≤ C := by rw [hC]; exact le_sup_right
  have hCN : C ≤ Subgroup.normalizer (Q : Set G) := by
    rw [hC]; exact sup_le hN Subgroup.le_normalizer
  let Qc := Q.subgroupOf C
  haveI hQcN : Qc.Normal := ⟨fun x hx y => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact (Subgroup.mem_normalizer_iff.1 (hCN y.2) (x : G)).1 hx⟩
  have htop : H.subgroupOf C ⊔ Qc = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hHC hQC]
    rw [show H ⊔ Q = C from hC.symm]
    exact Subgroup.subgroupOf_self C
  have hcommq : ∀ a b : ↥C, (QuotientGroup.mk a : ↥C ⧸ Qc) * QuotientGroup.mk b =
      QuotientGroup.mk b * QuotientGroup.mk a := by
    intro a b
    obtain ⟨ha1, hha1, qa, hqa, rfl⟩ := Subgroup.mem_sup_of_normal_right.1
      (show a ∈ H.subgroupOf C ⊔ Qc by rw [htop]; exact Subgroup.mem_top a)
    obtain ⟨hb1, hhb1, qb, hqb, rfl⟩ := Subgroup.mem_sup_of_normal_right.1
      (show b ∈ H.subgroupOf C ⊔ Qc by rw [htop]; exact Subgroup.mem_top b)
    have hqa1 : (QuotientGroup.mk qa : ↥C ⧸ Qc) = 1 := by
      rw [QuotientGroup.eq_one_iff]; exact hqa
    have hqb1 : (QuotientGroup.mk qb : ↥C ⧸ Qc) = 1 := by
      rw [QuotientGroup.eq_one_iff]; exact hqb
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, hqa1, hqb1, mul_one, mul_one]
    have hhab : (ha1 : ↥C) * (hb1 : ↥C) = (hb1 : ↥C) * (ha1 : ↥C) :=
      Subtype.ext (hHab (ha1 : G) hha1 (hb1 : G) hhb1)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hhab]
  have hcommAll : ∀ a b : ↥C ⧸ Qc, a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with
    | H a =>
      induction b using QuotientGroup.induction_on with
      | H b => exact hcommq a b
  haveI : IsMulCommutative (↥C ⧸ Qc) := ⟨⟨hcommAll⟩⟩
  have hcomm : commutator ↥C ≤ Qc :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance
  have hmem : ⁅(⟨g, hg⟩ : ↥C), (⟨h, hh⟩ : ↥C)⁆ ∈ Qc :=
    hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
  rw [Subgroup.mem_subgroupOf] at hmem
  simpa [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv] using hmem

theorem commutator_mem_toralCentralizer_e8NodeZeroToral {K : Type} [Field K] {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) {ζ : Kˣ} (hζ : orderOf ζ = q) {g h : ModGL Tag.E8 K}
    (hg : g ∈ toralCentralizer Tag.E8 K (e8NodeZeroToral ζ))
    (hh : h ∈ toralCentralizer Tag.E8 K (e8NodeZeroToral ζ)) :
    g * h * g⁻¹ * h⁻¹ ∈ subsystemGroup Tag.E8 K {i : Fin Tag.E8.rank | i ≠ 0} := by
  have hC := toralCentralizer_e8NodeZeroToral_eq_torusGroup_sup_subsystemGroup hq hq2 hζ
  have hN : torusGroup Tag.E8 K ≤
      Subgroup.normalizer (subsystemGroup Tag.E8 K {i : Fin Tag.E8.rank | i ≠ 0} :
        Set (ModGL Tag.E8 K)) :=
    CFSG.LieType.Chevalley.ParSylow.torusGroup_le_normalizer_subsystemGroup
      {i : Fin Tag.E8.rank | i ≠ 0}
  exact commutator_mem_of_eq_sup_of_normalizes hC hN
    (fun a ha b hb => CFSG.LieType.Chevalley.RootTorus.torusGroup_mul_comm ha hb) hg hh

end CFSG.LocalAnalysis.GLTheoremA.Y10F
