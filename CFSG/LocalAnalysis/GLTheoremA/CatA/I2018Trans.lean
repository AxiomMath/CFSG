module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma31Proof
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.GLTheoremA.S10.Defs
public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2018

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.HardMathSupport.Solomon.LocalBalance (mem_glaPPrimeCoreOf_iff)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem catalogIs_congr' {X Y : Type} [Group X] [Group Y] {Q : TauCeti.CFSGIndex → Prop} (e : X ≃* Y)
    (h : catalogIs X Q) : catalogIs Y Q := by
  obtain ⟨i, hi, ⟨f⟩⟩ := h
  exact ⟨i, hi, ⟨e.symm.trans f⟩⟩

theorem fixSubgroup_one_eq_top {H : Type} [Group H] :
    CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (1 : MulAut H) = ⊤ := by
  ext h
  simp [CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup]

theorem le_normalizer_of_commutator_eq {S : Type} [Group S] {A B : Subgroup S} (h : ⁅A, B⁆ = A) :
    B ≤ Subgroup.normalizer (A : Set S) := by
  have key : ∀ u ∈ B, ∀ h' ∈ A, u * h' * u⁻¹ ∈ A := by
    intro u hu h' hh'
    have hc : ⁅h', u⁆ ∈ A := by
      rw [← h]
      exact Subgroup.commutator_mem_commutator hh' hu
    have e : u * h' * u⁻¹ = ⁅h', u⁆⁻¹ * h' := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact A.mul_mem (A.inv_mem hc) hh'
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h'
  constructor
  · intro hh'
    exact key g hg h' hh'
  · intro hh'
    have hk := key g⁻¹ (B.inv_mem hg) _ hh'
    have e2 : g⁻¹ * (g * h' * g⁻¹) * g⁻¹⁻¹ = h' := by group
    rw [e2] at hk
    exact hk

theorem chevTransfer_ne_bot {K J S₀ : Subgroup G} (hJK : J ≤ K) (hS₀K : S₀ ≤ K)
    (hJS : ⁅S₀, J⁆ = S₀) (hn : ¬ S₀ ≤ GLAPPrimeCoreOf 3 K) : chevTransfer 3 K S₀ ≠ ⊥ := by
  intro h
  apply hn
  rw [← hJS, Subgroup.commutator_le]
  intro s hs j hj
  have hsK : s ∈ K := hS₀K hs
  have hjK : j ∈ K := hJK hj
  have hmem : (⟨s, hsK⟩ : ↥K) ∈ S₀.subgroupOf K := Subgroup.mem_subgroupOf.2 hs
  have h1 : chevQuotHom 3 K ⟨s, hsK⟩ = 1 := by
    have hT : chevQuotHom 3 K ⟨s, hsK⟩ ∈ chevTransfer 3 K S₀ := Subgroup.mem_map_of_mem _ hmem
    rw [h] at hT
    exact Subgroup.mem_bot.1 hT
  have hcen : pQuotHom 3 K ⟨s, hsK⟩ ∈ Subgroup.center (PQuot 3 K) := by
    unfold chevQuotHom at h1
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  have hc : pQuotHom 3 K ⁅(⟨s, hsK⟩ : ↥K), ⟨j, hjK⟩⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact ((Subgroup.mem_center_iff.1 hcen) _).symm
  have hmemK : (⁅(⟨s, hsK⟩ : ↥K), ⟨j, hjK⟩⁆ : ↥K) ∈ GLAPPrimeCore 3 ↥K := by
    rw [← ker_pQuotHom 3 K, MonoidHom.mem_ker]
    exact hc
  have hG := (mem_glaPPrimeCoreOf_iff (p := 3) (C := K) ⁅(⟨s, hsK⟩ : ↥K), ⟨j, hjK⟩⁆).2 hmemK
  simpa [commutatorElement_def] using hG

theorem chevTransfer_commutator {K J S₀ : Subgroup G} (hJK : J ≤ K) (hS₀K : S₀ ≤ K)
    (hJS : ⁅S₀, J⁆ = S₀) :
    ⁅chevTransfer 3 K S₀, chevTransfer 3 K J⁆ = chevTransfer 3 K S₀ := by
  have hA : ⁅(S₀.subgroupOf K), (J.subgroupOf K)⁆ = S₀.subgroupOf K := by
    apply Subgroup.map_injective (f := K.subtype) (K.subtype_injective)
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.2 hS₀K, inf_eq_left.2 hJK, hJS]
  unfold chevTransfer
  rw [← Subgroup.map_commutator, hA]

theorem isPGroup_chevTransfer {K S₀ : Subgroup G} (hS₀2 : IsPGroup 2 S₀) (hS₀K : S₀ ≤ K) :
    IsPGroup 2 (chevTransfer 3 K S₀) := by
  rw [isPGroup_iff_pow_pow_eq_one]
  rintro ⟨g, hg⟩
  obtain ⟨u, hu, hug⟩ := Subgroup.mem_map.1 hg
  obtain ⟨k, hk⟩ := (isPGroup_iff_pow_pow_eq_one.1 hS₀2) ⟨u.1, Subgroup.mem_subgroupOf.1 hu⟩
  have hu2 : u ^ 2 ^ k = 1 := by
    apply Subtype.ext
    have := congrArg Subtype.val hk
    simpa using this
  refine ⟨k, Subtype.ext ?_⟩
  simp only [Subgroup.coe_pow, Subgroup.coe_one]
  rw [← hug, ← map_pow, hu2, map_one]

theorem twoPart_le_of_dvd {a b : ℕ} (hb : b ≠ 0) (h : a ∣ b) : twoPart a ≤ twoPart b := by
  unfold twoPart
  apply Nat.pow_le_pow_right (by norm_num)
  have ha : a ≠ 0 := by
    rintro rfl
    exact hb (zero_dvd_iff.1 h)
  exact Finsupp.le_def.1 ((Nat.factorization_le_iff_dvd ha hb).2 h) 2

theorem twoPart_pSimple_le_card2 (K : Subgroup G) :
    twoPart (Nat.card (PSimple 3 K)) ≤ card2 3 K := by
  unfold card2
  apply twoPart_le_of_dvd (Nat.card_pos (α := PQuot 3 K)).ne'
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center (PQuot 3 K))]
  exact Dvd.intro _ rfl

theorem gla_marking_of_raw {K : Subgroup G} (hq : CFSG.Open.IsQuasisimple (PQuot 3 K))
    (lab : CFSG.Assembly.LargeEvenLabel) (hlab : CFSG.Assembly.LargeEvenInLambda2 lab)
    (hbd : (lab.n = 1 ∧ 2 ^ 6 < card2 3 K) ∨ (lab.n = 3 ∧ 2 ^ 18 < card2 3 K))
    (hraw : CFSG.Assembly.LargeEvenRawDatum lab
      (fun R _ _ _ => IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧ Nonempty (PSimple 3 K ≃* R))) :
    GLAMarking (PQuot 3 K) (fun lab _ _ _ _ _ =>
      (lab.n = 1 ∧ 2 ^ 6 < card2 3 K) ∨ (lab.n = 3 ∧ 2 ^ 18 < card2 3 K)) := by
  refine ⟨hq.1, lab, hlab, ?_⟩
  convert hraw using 1
  funext R _ I F
  apply propext
  constructor
  · rintro ⟨h1, h2, θ, -⟩
    exact ⟨h1, h2, ⟨θ⟩⟩
  · rintro ⟨h1, h2, ⟨θ⟩⟩
    exact ⟨h1, h2, θ, hbd⟩

end CFSG.LocalAnalysis.GLTheoremA.I2018

end
